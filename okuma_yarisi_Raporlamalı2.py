# -*- coding: utf-8 -*-
"""
OKUMA YARIŞI - Roketler Güneşe!
--------------------------------
Akıllı tahta için ilkokul okuma yarışması programı.

Çalıştırma:   python okuma_yarisi.py
Gereksinim:   Sadece Python 3 (tkinter Python ile birlikte gelir, ek kurulum yok)

Kullanım:
  * Ekranın altında her öğrencinin adı ve altında kelime sayısı kutusu vardır.
  * Öğretmen okunan toplam kelime sayısını kutuya yazıp Enter'a basar.
    Enter'a basınca imleç otomatik olarak bir sonraki öğrenciye geçer.
  * Roket, hedef kelime sayısına oranla güneşe yaklaşır.
  * Tüm öğrencilerin sayısı girildikten sonra en çok okuyan KAZANAN ilan edilir.
  * Sol üstteki "Ayarlar" düğmesinden isimler ve hedef kelime sayısı girilir.
  * Sol üstteki ZAMANLAYICI: dakika/saniye ayarlanır, Başlat ile okuyan öğrenci için
    süre başlar; süre bitince uyarı sesi çalar. Sıfırla sesi durdurur.
  * GELİŞİM RAPORU: Girilen kelime sayıları tarihiyle otomatik kaydedilir. Bir öğrencinin ismine ya da
    roketine dokunun (veya "Raporlar" düğmesi): haftalık/aylık/dönemlik grafik ve tablo açılır,
    "PDF Kaydet" ile çıktı alınır.
  * F11: tam ekran aç/kapat, Esc: tam ekrandan çık.
Veriler okuma_yarisi.json dosyasına otomatik kaydedilir.
"""

import io
import json
import math
import os
import random
import re
import shutil
import subprocess
import tempfile
import textwrap
import threading
import time
import tkinter as tk
import wave
from array import array
from datetime import date, datetime, timedelta
from tkinter import filedialog, messagebox, simpledialog, ttk

DOSYA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "okuma_yarisi.json")
KARE_MS = 33  # yaklaşık 30 kare/sn

# --- Süre bitiş zili ("DİİİİİT") ayarları ---
ALARM_FREKANS = 2000   # Hz  (büyütürsen daha tiz, küçültürsen daha kalın ses)
ALARM_UZUNLUK = 2.0    # saniye, her bir uzun "diiiit"
ALARM_TEKRAR = 3       # kaç kez çalsın
ALARM_ARA = 0.4        # tekrarlar arası sessizlik (saniye)

RENKLER = ["#e63946", "#2a9df4", "#2ecc71", "#f4a261", "#9b5de5",
           "#f15bb5", "#00bbf9", "#ffd60a", "#ff6b35", "#06d6a0"]

ARKA = "#050816"
PANEL = "#0b1233"


# ----------------------------------------------------------------- yardımcılar
def hex_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def rgb_hex(rgb):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v))) for v in rgb)


def karisim(a, b, t):
    """a ve b renkleri (hex ya da rgb) arasında t (0..1) oranında geçiş."""
    if isinstance(a, str):
        a = hex_rgb(a)
    if isinstance(b, str):
        b = hex_rgb(b)
    return rgb_hex([a[i] + (b[i] - a[i]) * t for i in range(3)])


def koyulastir(renk, oran=0.6):
    return karisim(renk, "#000000", 1 - oran)


_alarm_wav = None


def alarm_wav_uret():
    """Sınav bitişi gibi, keskin ve uzun 'diiiit' sesini bellekte WAV olarak üretir."""
    global _alarm_wav
    if _alarm_wav is not None:
        return _alarm_wav
    sr = 22050
    n = int(sr * ALARM_UZUNLUK)
    atak, birak = int(sr * 0.008), int(sr * 0.03)
    diit = array("h")
    for i in range(n):
        t = i / sr
        w = 2 * math.pi * ALARM_FREKANS * t
        # kare dalgaya yakın (tek harmonikli) -> sert, elektronik zil tınısı
        x = math.sin(w) + math.sin(3 * w) / 3 + math.sin(5 * w) / 5
        zarf = min(1.0, i / atak, (n - i) / birak)
        diit.append(int(32767 * 0.85 * x * zarf))
    ara = array("h", [0]) * int(sr * ALARM_ARA)
    toplam = array("h")
    for _ in range(ALARM_TEKRAR):
        toplam.extend(diit)
        toplam.extend(ara)
    tampon = io.BytesIO()
    with wave.open(tampon, "wb") as f:
        f.setnchannels(1)
        f.setsampwidth(2)
        f.setframerate(sr)
        f.writeframes(toplam.tobytes())
    _alarm_wav = tampon.getvalue()
    return _alarm_wav


class Ogrenci:
    def __init__(self, ad, kelime=0, girildi=False):
        self.ad = ad
        self.kelime = kelime        # bugünkü okuma (o güne ait kelime sayısı)
        self.girildi = girildi      # öğretmen bu yarışta bu öğrencinin sayısını girdi mi?
        self.gosterilen = 0.0       # ekranda gösterilen ilerleme (0..1), yumuşak hareket için


# ----------------------------------------------------------------- gelişim raporu: hesaplamalar
GUN_ADLARI = ["Pazartesi", "Salı", "Çarşamba", "Perşembe", "Cuma", "Cumartesi", "Pazar"]
TURLER = ("Haftalık", "Aylık", "Dönemlik", "Tümü")
ZEMIN = "#10163a"


def tarih_goster(d):
    return "%02d.%02d.%d" % (d.day, d.month, d.year)


def kisa_tarih(d):
    return "%02d.%02d" % (d.day, d.month)


def iso_coz(s):
    try:
        return date.fromisoformat(s)
    except (ValueError, TypeError):
        return None


def aralik_hesapla(tur, bugun, ilk):
    """Rapor türüne göre (başlangıç, bitiş) tarihlerini verir."""
    if tur == "Haftalık":
        return bugun - timedelta(days=6), bugun
    if tur == "Aylık":
        return bugun - timedelta(days=29), bugun
    if tur == "Dönemlik":  # 1. dönem: Eylül-Ocak, 2. dönem: Şubat-Haziran (yaklaşık)
        if bugun.month >= 9:
            bas = date(bugun.year, 9, 1)
        elif bugun.month == 1:
            bas = date(bugun.year - 1, 9, 1)
        else:
            bas = date(bugun.year, 2, 1)
        return bas, bugun
    return (ilk or bugun), bugun


def gunluk_degerler(gecmis, ad, bas, bit):
    """{tarih: okunan kelime}. ad=None ise tüm sınıfın toplamı."""
    sonuc = {}
    for ds, kayit in gecmis.items():
        d = iso_coz(ds)
        if d is None or not (bas <= d <= bit) or not isinstance(kayit, dict):
            continue
        v = sum(kayit.values()) if ad is None else kayit.get(ad, 0)
        if v > 0:
            sonuc[d] = v
    return sonuc


def guzel_ust(m):
    if m <= 5:
        return 5
    if m <= 10:
        return 10
    ust = 10 ** math.floor(math.log10(m))
    for k in (1, 1.5, 2, 2.5, 3, 4, 5, 6, 8, 10):
        if m <= k * ust:
            return k * ust
    return 10 * ust


def degisim_metni(deg):
    return "—" if deg is None else "%+d%%" % round(deg)


def ort_hesapla(g):
    return sum(g.values()) / float(len(g)) if g else 0


def yorum_uret(tur, gun, degisim, ogrenci_modu):
    if gun == 0:
        return "Bu aralıkta okuma kaydı yok."
    parca = []
    if degisim is not None:
        if degisim >= 10:
            parca.append("Önceki döneme göre günlük okuma ortalaması belirgin şekilde arttı; bu tempoyu desteklemek güzel olur.")
        elif degisim <= -10:
            parca.append("Önceki döneme göre günlük okuma ortalaması düştü; nedenini konuşmak ve motive etmek faydalı olabilir.")
        else:
            parca.append("Günlük okuma ortalaması önceki döneme yakın seyrediyor.")
    if ogrenci_modu and ((tur == "Haftalık" and gun <= 1) or (tur == "Aylık" and gun <= 3)):
        parca.append("Okuma sıklığı düşük; daha düzenli okumaya teşvik edilebilir.")
    return ("Gözlem: " + " ".join(parca)) if parca else ""


def rapor_uret(gecmis, adlar, ad, tur, bugun):
    """Ekranda ve PDF'te kullanılan rapor verisini üretir. ad=None -> tüm sınıf.
    Her günün kelime sayısı ayrı ayrı gösterilir (günler toplanmaz)."""
    tarihler = [d for d in (iso_coz(k) for k in gecmis) if d]
    bas, bit = aralik_hesapla(tur, bugun, min(tarihler) if tarihler else None)
    uz = (bit - bas).days + 1
    karsilastir = tur in ("Haftalık", "Aylık")
    onceki_etiket = "Önceki %d güne göre" % uz

    def donem(a):
        g = gunluk_degerler(gecmis, a, bas, bit)
        ort = ort_hesapla(g)
        onc = None
        if karsilastir:
            onc = ort_hesapla(gunluk_degerler(gecmis, a, bas - timedelta(days=uz), bas - timedelta(days=1)))
        deg = (ort - onc) * 100.0 / onc if onc else None
        return g, ort, deg, onc

    def en_iyi(g):
        if not g:
            return "—"
        d, v = max(g.items(), key=lambda kv: kv[1])
        return "%s (%d)" % (tarih_goster(d), v)

    satirlar = []
    if ad is not None:
        g, ort, deg, _ = donem(ad)
        gun = len(g)
        ozet = ["Okuma günü: %d" % gun]
        if gun:
            ozet.append("Günlük ortalama: %d kelime" % round(ort))
            ozet.append("En iyi gün: " + en_iyi(g))
        if karsilastir:
            if deg is None:
                ozet.append("%s: önceki dönemde kayıt yok" % onceki_etiket)
            else:
                ozet.append("%s (günlük ortalama): %s" % (onceki_etiket, degisim_metni(deg)))
        onceki_v = None
        for d in sorted(g):
            v = g[d]
            if onceki_v is None:
                fark = "—"
            else:
                fark = "%+d" % (v - onceki_v) if v != onceki_v else "0"
            satirlar.append((d.isoformat(), (tarih_goster(d), GUN_ADLARI[d.weekday()], v, fark)))
            onceki_v = v
        sutunlar = [("Tarih", 170, 3), ("Gün", 170, 3), ("Okunan kelime", 190, 3), ("Önceki okumaya göre", 230, 3)]
        kapsam = ad
        kutular = []
        d = bas
        while d <= bit:
            kutular.append((kisa_tarih(d), g.get(d, 0)))
            d += timedelta(days=1)
        grafik_baslik = "Günlük okunan kelime"
        etiket_px, etiket_pt = 46, 30
    else:
        ekstra = sorted({k for kayit in gecmis.values() if isinstance(kayit, dict) for k in kayit} - set(adlar))
        liste, ortlar, onclar = [], [], []
        for isim in list(adlar) + ekstra:
            gi, oi, di, onc = donem(isim)
            if isim in ekstra and not gi:
                continue
            if gi:
                ortlar.append(oi)
            if onc:
                onclar.append(onc)
            satir = [isim, len(gi), round(oi), en_iyi(gi)]
            if karsilastir:
                satir.append(degisim_metni(di))
            liste.append((oi, isim, tuple(satir)))
        liste.sort(key=lambda x: (-x[0], x[1]))
        satirlar = [(isim, satir) for _, isim, satir in liste]
        gun = len(ortlar)
        ozet = ["Okuyan öğrenci: %d / %d" % (gun, len(adlar))]
        deg = None
        if ortlar:
            sinif_ort = sum(ortlar) / len(ortlar)
            ozet.append("Sınıf ortalaması (okuyan öğrenci başına günlük): %d kelime" % round(sinif_ort))
            if karsilastir and onclar:
                onc_ort = sum(onclar) / len(onclar)
                deg = (sinif_ort - onc_ort) * 100.0 / onc_ort
                ozet.append("%s (sınıf ortalaması): %s" % (onceki_etiket, degisim_metni(deg)))
        sutunlar = [("Öğrenci", 230, 3), ("Okuma günü", 120, 2), ("Günlük ortalama", 160, 3), ("En iyi gün", 210, 4)]
        if karsilastir:
            sutunlar.append((onceki_etiket, 210, 4))
        kapsam = "Tüm sınıf"
        kutular = [(isim.split()[0][:10], s[2]) for _, isim, s in liste]
        grafik_baslik = "Okuma günü başına ortalama kelime (öğrenci karşılaştırması)"
        etiket_px, etiket_pt = 80, 50

    dolu = [v for _, v in kutular if v > 0]
    return dict(kapsam=kapsam, ad=ad, tur=tur, aralik="%s - %s" % (tarih_goster(bas), tarih_goster(bit)),
                ozet=ozet, yorum=yorum_uret(tur, gun, deg, ad is not None),
                kutular=kutular, grafik_baslik=grafik_baslik,
                ortalama=(sum(dolu) / len(dolu)) if dolu else 0,
                sutunlar=sutunlar, satirlar=satirlar, renk="#2a9df4",
                etiket_px=etiket_px, etiket_pt=etiket_pt)


# ----------------------------------------------------------------- PDF (ek kütüphane gerektirmez)
TR_KODLAR = {"ğ": 0x80, "Ğ": 0x81, "ş": 0x82, "Ş": 0x83, "İ": 0x84, "ı": 0x85}


def pdf_metin_kodla(s):
    b = bytearray()
    for ch in s:
        if ch in TR_KODLAR:
            b.append(TR_KODLAR[ch])
        else:
            try:
                kod = ch.encode("cp1252")
            except UnicodeEncodeError:
                kod = b"?"
            if kod and 0x80 <= kod[0] <= 0x85:
                kod = b"?"
            b += kod
    return bytes(b).replace(b"\\", b"\\\\").replace(b"(", b"\\(").replace(b")", b"\\)").decode("latin-1")


class Pdf:
    """Çok basit PDF yazıcı: A4, Helvetica (Türkçe karakter destekli), metin/çizgi/dikdörtgen."""
    W, H = 595, 842

    def __init__(self):
        self.sayfalar = []
        self.akim = None
        self.yeni_sayfa()

    def yeni_sayfa(self):
        self.akim = []
        self.sayfalar.append(self.akim)

    @staticmethod
    def _renk(rgb):
        return "%.3f %.3f %.3f" % tuple(c / 255.0 for c in rgb)

    @staticmethod
    def genislik(s, boyut, kalin=False):
        t = 0.0
        for ch in s:
            if ch.isdigit():
                t += 0.556
            elif ch == " ":
                t += 0.278
            elif ch in "ilI.,:;|'!ıj()-/":
                t += 0.27
            elif ch.isupper():
                t += 0.68
            else:
                t += 0.53
        return t * boyut * (1.06 if kalin else 1.0)

    def metin(self, x, y, s, boyut=10, kalin=False, renk=(0, 0, 0), hizala="sol"):
        gen = self.genislik(s, boyut, kalin)
        if hizala == "sag":
            x -= gen
        elif hizala == "orta":
            x -= gen / 2
        self.akim.append("BT /%s %.1f Tf %s rg %.1f %.1f Td (%s) Tj ET" % (
            "F2" if kalin else "F1", boyut, self._renk(renk), x, y, pdf_metin_kodla(s)))

    def dikdortgen(self, x, y, w, h, dolgu):
        self.akim.append("%s rg %.1f %.1f %.1f %.1f re f" % (self._renk(dolgu), x, y, w, h))

    def cizgi(self, x1, y1, x2, y2, renk=(0, 0, 0), kalinlik=0.5, kesikli=False):
        d = "[4 3] 0 d" if kesikli else "[] 0 d"
        self.akim.append("%s RG %.2f w %s %.1f %.1f m %.1f %.1f l S" % (
            self._renk(renk), kalinlik, d, x1, y1, x2, y2))

    def kaydet(self, dosya):
        n = len(self.sayfalar)
        for i, akim in enumerate(self.sayfalar):
            self.akim = akim
            self.metin(self.W / 2, 22, "Sayfa %d / %d" % (i + 1, n), 8, False, (130, 130, 130), "orta")
        nesneler = [
            b"<< /Type /Catalog /Pages 2 0 R >>",
            ("<< /Type /Pages /Kids [%s] /Count %d >>" % (
                " ".join("%d 0 R" % (6 + 2 * i) for i in range(n)), n)).encode(),
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding 5 0 R >>",
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding 5 0 R >>",
            b"<< /Type /Encoding /BaseEncoding /WinAnsiEncoding /Differences "
            b"[128 /gbreve /Gbreve /scedilla /Scedilla /Idotaccent /dotlessi] >>",
        ]
        for i, akim in enumerate(self.sayfalar):
            nesneler.append(("<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %d %d] "
                             "/Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> /Contents %d 0 R >>"
                             % (self.W, self.H, 7 + 2 * i)).encode())
            veri = "\n".join(akim).encode("latin-1")
            nesneler.append(b"<< /Length %d >>\nstream\n" % len(veri) + veri + b"\nendstream")
        cikti = bytearray(b"%PDF-1.4\n")
        konumlar = []
        for no, nesne in enumerate(nesneler, 1):
            konumlar.append(len(cikti))
            cikti += b"%d 0 obj\n" % no + nesne + b"\nendobj\n"
        xref = len(cikti)
        cikti += b"xref\n0 %d\n0000000000 65535 f \n" % (len(nesneler) + 1)
        for k in konumlar:
            cikti += b"%010d 00000 n \n" % k
        cikti += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(nesneler) + 1, xref)
        with open(dosya, "wb") as f:
            f.write(bytes(cikti))


def pdf_kisalt(s, maxw, boyut):
    s = str(s)
    if Pdf.genislik(s, boyut) <= maxw:
        return s
    while len(s) > 1 and Pdf.genislik(s + "..", boyut) > maxw:
        s = s[:-1]
    return s + ".."


def rapor_pdf_yaz(veri, dosya, bugun):
    p = Pdf()
    W, H = p.W, p.H
    sol, sag = 40, W - 40
    lacivert, gri = (20, 30, 90), (90, 90, 90)
    y = H - 50
    p.metin(sol, y, "Okuma Yarışı - Gelişim Raporu", 19, True, lacivert)
    y -= 24
    p.metin(sol, y, "%s   |   %s raporu   |   %s" % (veri["kapsam"], veri["tur"], veri["aralik"]), 11, False, (40, 40, 40))
    y -= 15
    p.metin(sol, y, "Rapor tarihi: " + tarih_goster(bugun), 9, False, (120, 120, 120))
    y -= 22
    for satir in veri["ozet"]:
        p.metin(sol, y, satir, 10.5)
        y -= 15
    if veri["yorum"]:
        y -= 3
        for parca in textwrap.wrap(veri["yorum"], 100):
            p.metin(sol, y, parca, 10, False, (20, 110, 60))
            y -= 14
    y -= 14

    # --- grafik
    p.metin(sol, y, veri["grafik_baslik"], 10, True, lacivert)
    ust = y - 14
    alt = ust - 160
    gx0, gx1 = sol + 34, sag
    pw, ph = gx1 - gx0, ust - alt
    kutular = veri["kutular"]
    maks = max((v for _, v in kutular), default=0)
    if maks <= 0:
        p.metin((gx0 + gx1) / 2, (ust + alt) / 2, "Bu aralıkta okuma kaydı yok", 12, False, gri, "orta")
    else:
        tavan = guzel_ust(maks * 1.05)
        for k in range(6):
            yy = alt + ph * k / 5.0
            p.cizgi(gx0, yy, gx1, yy, (0.85 * 255,) * 3, 0.4)
            p.metin(gx0 - 4, yy - 3, "%d" % round(tavan * k / 5.0), 8, False, gri, "sag")
        n = len(kutular)
        slot = pw / float(n)
        bw = min(slot * 0.7, 26)
        hx = veri["renk"].lstrip("#")
        renk = tuple(int(hx[i:i + 2], 16) for i in (0, 2, 4))
        adim = max(1, int(math.ceil(n * float(veri.get("etiket_pt", 30)) / pw)))
        for i, (etiket, v) in enumerate(kutular):
            cx = gx0 + slot * (i + 0.5)
            if v > 0:
                h = ph * v / float(tavan)
                p.dikdortgen(cx - bw / 2, alt, bw, h, renk)
                if slot >= 16:
                    p.metin(cx, alt + h + 2, str(v), 7, False, (40, 40, 40), "orta")
            if i % adim == 0:
                p.metin(cx, alt - 11, etiket, 7.5, False, gri, "orta")
        if veri["ortalama"] > 0:
            ya = alt + ph * veri["ortalama"] / float(tavan)
            p.cizgi(gx0, ya, gx1, ya, (200, 60, 50), 0.9, True)
            p.metin(sag, ust + 4, "- - Ortalama: %d" % round(veri["ortalama"]), 9, True, (200, 60, 50), "sag")
    p.cizgi(gx0, alt, gx1, alt, (60, 60, 60), 0.8)
    p.cizgi(gx0, alt, gx0, ust, (60, 60, 60), 0.8)
    y = alt - 34

    # --- tablo
    sut = veri["sutunlar"]
    toplam_w = float(sum(w for _, _, w in sut))
    genler = [(sag - sol) * w / toplam_w for _, _, w in sut]
    xler = [sol + sum(genler[:i]) for i in range(len(genler))]

    def baslik_ciz(yy):
        p.dikdortgen(sol, yy - 5, sag - sol, 18, (30, 43, 100))
        for (b, _, _), x, g in zip(sut, xler, genler):
            p.metin(x + g / 2, yy, b, 9, True, (255, 255, 255), "orta")

    baslik_ciz(y)
    y -= 19
    for sira, (_, hucreler) in enumerate(veri["satirlar"]):
        if y < 55:
            p.yeni_sayfa()
            y = H - 50
            baslik_ciz(y)
            y -= 19
        if sira % 2 == 0:
            p.dikdortgen(sol, y - 5, sag - sol, 17, (238, 241, 250))
        for j, (h, x, g) in enumerate(zip(hucreler, xler, genler)):
            metin = pdf_kisalt(h, g - 8, 9.5)
            if j == 0 and veri["ad"] is None:
                p.metin(x + 5, y, metin, 9.5)
            else:
                p.metin(x + g / 2, y, metin, 9.5, False, (0, 0, 0), "orta")
        y -= 17
    if not veri["satirlar"]:
        p.metin(sol, y, "Bu aralıkta kayıt yok.", 10, False, gri)
    p.kaydet(dosya)


def dosyayi_ac(yol):
    try:
        if os.name == "nt":
            os.startfile(yol)
        else:
            subprocess.Popen(["xdg-open", yol], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:
        pass


# ----------------------------------------------------------------- gelişim raporu: pencere
class RaporPenceresi:
    def __init__(self, app, ad=None):
        self.app = app
        self.veri = None
        pen = self.pen = tk.Toplevel(app.root)
        pen.title("Gelişim Raporu")
        pen.configure(bg=ZEMIN)
        pen.geometry("1120x800")
        pen.minsize(800, 600)
        try:
            pen.state("zoomed")
        except tk.TclError:
            pass
        pen.protocol("WM_DELETE_WINDOW", self.kapat)
        pen.option_add("*TCombobox*Listbox.font", ("Segoe UI", 14))

        st = ttk.Style(pen)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("Rapor.Treeview", background="#0f1a4a", fieldbackground="#0f1a4a", foreground="white",
                     rowheight=30, font=("Segoe UI", 12), borderwidth=0)
        st.configure("Rapor.Treeview.Heading", background="#1d2b64", foreground="white",
                     font=("Segoe UI", 12, "bold"), relief="flat")
        st.map("Rapor.Treeview", background=[("selected", "#2d44a0")])
        st.map("Rapor.Treeview.Heading", background=[("active", "#2d44a0")])

        ust = tk.Frame(pen, bg=ZEMIN)
        ust.pack(fill="x", padx=14, pady=(12, 4))
        tk.Label(ust, text="Öğrenci:", bg=ZEMIN, fg="white", font=("Segoe UI", 14, "bold")).pack(side="left")
        self.kisi_var = tk.StringVar(value=ad if ad else "Tüm sınıf")
        self.kisi_kutu = ttk.Combobox(ust, textvariable=self.kisi_var, state="readonly", width=24,
                                      font=("Segoe UI", 14))
        self.kisi_kutu.pack(side="left", padx=(8, 22))
        self.kisi_kutu.bind("<<ComboboxSelected>>", lambda e: self.yenile())
        self.tur_var = tk.StringVar(value="Aylık")
        for t in TURLER:
            tk.Radiobutton(ust, text=t, value=t, variable=self.tur_var, indicatoron=False, command=self.yenile,
                           font=("Segoe UI", 13, "bold"), bg="#1d2b64", fg="white", selectcolor="#2d44a0",
                           activebackground="#2d44a0", activeforeground="white", relief="flat",
                           padx=14, pady=6, cursor="hand2").pack(side="left", padx=3)

        self.ozet_lbl = tk.Label(pen, bg=ZEMIN, fg="white", font=("Segoe UI", 13), justify="left", anchor="w",
                                 wraplength=1000)
        self.ozet_lbl.pack(fill="x", padx=14, pady=(6, 0))
        self.yorum_lbl = tk.Label(pen, bg=ZEMIN, fg="#7dffa0", font=("Segoe UI", 13, "bold"), justify="left",
                                  anchor="w", wraplength=1000)
        self.yorum_lbl.pack(fill="x", padx=14)
        pen.bind("<Configure>", self.boyut_degisti)

        self.grafik = tk.Canvas(pen, bg="#0b1233", highlightthickness=0, height=280)
        self.grafik.pack(fill="both", expand=True, padx=14, pady=8)
        self.grafik.bind("<Configure>", lambda e: self.grafik_ciz())

        tablo = tk.Frame(pen, bg=ZEMIN)
        tablo.pack(fill="both", expand=True, padx=14)
        self.tree = ttk.Treeview(tablo, style="Rapor.Treeview", show="headings", height=7)
        kay = ttk.Scrollbar(tablo, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=kay.set)
        self.tree.pack(side="left", fill="both", expand=True)
        kay.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", self.satir_cift_tik)

        alt = tk.Frame(pen, bg=ZEMIN)
        alt.pack(fill="x", padx=14, pady=10)

        def dugme(metin, komut, renk, yan="left"):
            tk.Button(alt, text=metin, command=komut, font=("Segoe UI", 13, "bold"), bg=renk, fg="white",
                      activeforeground="white", relief="flat", padx=16, pady=6,
                      cursor="hand2").pack(side=yan, padx=(0, 8))

        dugme("PDF Kaydet", self.pdf_kaydet, "#2ecc71")
        dugme("Kayıt Ekle", self.kayit_ekle, "#1d2b64")
        dugme("Geçmişi Sıfırla", self.gecmisi_sifirla, "#d97706")
        dugme("Kapat", self.kapat, "#e63946", "right")
        self.ipucu = tk.Label(alt, bg=ZEMIN, fg="#9aa7d6", font=("Segoe UI", 11))
        self.ipucu.pack(side="left", padx=10)

        self.adlari_yenile()
        self.yenile()

    # -- yardımcılar
    def adlari_yenile(self):
        adlar = [o.ad for o in self.app.ogrenciler]
        ekstra = sorted({k for kayit in self.app.gecmis.values() if isinstance(kayit, dict) for k in kayit} - set(adlar))
        self.kisi_kutu["values"] = ["Tüm sınıf"] + adlar + ekstra

    def secili_ad(self):
        s = self.kisi_var.get()
        return None if s == "Tüm sınıf" else s

    def sec(self, ad):
        self.kisi_var.set(ad if ad else "Tüm sınıf")
        self.adlari_yenile()
        self.yenile()
        try:
            self.pen.deiconify()
            self.pen.lift()
        except tk.TclError:
            pass

    def kapat(self):
        self.app.rapor = None
        self.pen.destroy()

    def boyut_degisti(self, e):
        if e.widget is self.pen:
            w = max(300, e.width - 40)
            self.ozet_lbl.configure(wraplength=w)
            self.yorum_lbl.configure(wraplength=w)

    # -- içerik
    def yenile(self):
        ad = self.secili_ad()
        adlar = [o.ad for o in self.app.ogrenciler]
        self.veri = rapor_uret(self.app.gecmis, adlar, ad, self.tur_var.get(), date.today())
        if ad is None:
            self.veri["renk"] = "#ffd60a"
        elif ad in adlar:
            self.veri["renk"] = RENKLER[adlar.index(ad) % len(RENKLER)]
        v = self.veri
        self.ozet_lbl.configure(text="%s  (%s: %s)\n%s" % (v["kapsam"], v["tur"], v["aralik"], "   |   ".join(v["ozet"])))
        self.yorum_lbl.configure(text=v["yorum"])
        self.ipucu.configure(text="Satıra çift tıklayın: " + (
            "kaydı düzeltin." if ad else "öğrencinin raporunu açın."))
        self.tree.delete(*self.tree.get_children())
        self.tree["columns"] = [str(i) for i in range(len(v["sutunlar"]))]
        for i, (baslik, px, _) in enumerate(v["sutunlar"]):
            self.tree.heading(str(i), text=baslik)
            self.tree.column(str(i), width=px, anchor="w" if (i == 0 and ad is None) else "center")
        for iid, hucreler in v["satirlar"]:
            self.tree.insert("", "end", iid=iid, values=hucreler)
        self.grafik_ciz()

    def grafik_ciz(self):
        c = self.grafik
        c.delete("all")
        W, H = c.winfo_width(), c.winfo_height()
        v = self.veri
        if W < 120 or H < 100 or not v:
            return
        kutular = v["kutular"]
        sol, sag, ust, alt = 64, 24, 40, 44
        pw, ph = W - sol - sag, H - ust - alt
        c.create_text(W / 2, 18, text=v["grafik_baslik"], fill="white", font=("Segoe UI", 13, "bold"))
        maks = max((x for _, x in kutular), default=0)
        if maks <= 0:
            c.create_text(W / 2, H / 2, text="Bu aralıkta okuma kaydı yok", fill="#9aa7d6", font=("Segoe UI", 18))
            return
        tavan = guzel_ust(maks * 1.05)
        for k in range(6):
            yy = ust + ph - ph * k / 5.0
            c.create_line(sol, yy, W - sag, yy, fill="#24306a")
            c.create_text(sol - 8, yy, text="%d" % round(tavan * k / 5.0), anchor="e", fill="#cfd8ff",
                          font=("Segoe UI", 11))
        n = len(kutular)
        slot = pw / float(n)
        bw = min(slot * 0.7, 60)
        adim = max(1, int(math.ceil(n * float(v.get("etiket_px", 46)) / pw)))
        for i, (etiket, x) in enumerate(kutular):
            cx = sol + slot * (i + 0.5)
            if x > 0:
                h = ph * x / float(tavan)
                c.create_rectangle(cx - bw / 2, ust + ph - h, cx + bw / 2, ust + ph, fill=v["renk"], outline="")
                if slot >= 26:
                    c.create_text(cx, ust + ph - h - 9, text=str(x), fill="white", font=("Segoe UI", 10, "bold"))
            if i % adim == 0:
                c.create_text(cx, ust + ph + 16, text=etiket, fill="#cfd8ff", font=("Segoe UI", 10))
        if v["ortalama"] > 0:
            ya = ust + ph - ph * v["ortalama"] / float(tavan)
            c.create_line(sol, ya, W - sag, ya, fill="#ff5a36", dash=(8, 6), width=2)
            c.create_text(W - sag, 18, text="- - Ortalama: %d" % round(v["ortalama"]), anchor="e", fill="#ff8a6a",
                          font=("Segoe UI", 12, "bold"))
        c.create_line(sol, ust + ph, W - sag, ust + ph, fill="#8d99ae", width=2)

    # -- etkileşim
    def satir_cift_tik(self, _e=None):
        sec = self.tree.selection()
        if not sec:
            return
        ad = self.secili_ad()
        if ad is None:  # sınıf tablosu: öğrencinin raporunu aç
            self.sec(sec[0])
            return
        iso = sec[0]
        eski = self.app.gecmis.get(iso, {}).get(ad, 0)
        yeni = simpledialog.askinteger(
            "Kaydı düzelt", "%s - %s\nOkunan kelime sayısı (silmek için 0):" % (ad, tarih_goster(iso_coz(iso))),
            initialvalue=eski, minvalue=0, maxvalue=99999, parent=self.pen)
        if yeni is None:
            return
        self.app.gecmis_ayarla(iso, ad, yeni)
        self.yenile()

    def kayit_ekle(self):
        ad = self.secili_ad()
        if ad is None:
            messagebox.showinfo("Kayıt Ekle", "Önce yukarıdan bir öğrenci seçin.", parent=self.pen)
            return
        ds = simpledialog.askstring("Kayıt Ekle", "%s için tarih (gg.aa.yyyy):" % ad,
                                    initialvalue=tarih_goster(date.today()), parent=self.pen)
        if not ds:
            return
        try:
            d = datetime.strptime(ds.strip(), "%d.%m.%Y").date()
        except ValueError:
            messagebox.showwarning("Uyarı", "Tarihi gg.aa.yyyy biçiminde yazın (örn. 05.10.2026).", parent=self.pen)
            return
        v = simpledialog.askinteger("Kayıt Ekle", "%s - %s\nOkunan kelime sayısı:" % (ad, tarih_goster(d)),
                                    minvalue=0, maxvalue=99999, parent=self.pen)
        if v is None:
            return
        self.app.gecmis_ayarla(d.isoformat(), ad, v)
        self.yenile()

    def gecmisi_sifirla(self):
        ad = self.secili_ad()
        pen = tk.Toplevel(self.pen)
        pen.title("Geçmişi Sıfırla")
        pen.configure(bg=ZEMIN)
        pen.geometry("580x470")
        pen.transient(self.pen)
        pen.grab_set()
        tk.Label(pen, text="Hangi geçmiş kayıtlar silinsin?", bg=ZEMIN, fg="white",
                 font=("Segoe UI", 15, "bold")).pack(anchor="w", padx=16, pady=(16, 8))
        secim = tk.StringVar(value="tum")

        def radio(metin, deger, durum="normal"):
            tk.Radiobutton(pen, text=metin, value=deger, variable=secim, bg=ZEMIN, fg="white",
                           selectcolor="#2d44a0", activebackground=ZEMIN, activeforeground="white",
                           disabledforeground="#6b7599", font=("Segoe UI", 13), anchor="w", justify="left",
                           wraplength=520, state=durum).pack(fill="x", padx=24, pady=3)

        radio("Tüm öğrencilerin tüm geçmişi", "tum")
        radio("Sadece seçili öğrencinin geçmişi: %s" % ad if ad else "Sadece seçili öğrencinin geçmişi (önce yukarıdan bir öğrenci seçin)",
              "ogr", "normal" if ad else "disabled")
        radio("Şu tarihe kadar olan tüm kayıtlar (bu tarih dahil):", "tarih")
        tarih_var = tk.StringVar(value=tarih_goster(date.today()))
        tk.Entry(pen, textvariable=tarih_var, width=14, font=("Segoe UI", 14), justify="center").pack(
            anchor="w", padx=52, pady=(0, 8))
        tk.Label(pen, text="UYARI : Silmeden hemen önce programın klasörüne JSON formatında \notomatik bir yedek dosyası kaydedilir. \nAma yine de raporu PDF olarak kaydetmenizi öneririz. ",
                 bg=ZEMIN, fg="#ffd60a", font=("Segoe UI", 12), justify="left").pack(anchor="w", padx=24, pady=8)

        def sil():
            hedef_ad, kadar = None, None
            if secim.get() == "ogr":
                hedef_ad = ad
                tanim = "%s adlı öğrencinin TÜM geçmişi" % ad
            elif secim.get() == "tarih":
                try:
                    kadar = datetime.strptime(tarih_var.get().strip(), "%d.%m.%Y").date()
                except ValueError:
                    messagebox.showwarning("Uyarı", "Tarihi gg.aa.yyyy biçiminde yazın (örn. 05.10.2026).", parent=pen)
                    return
                tanim = "%s tarihine kadar olan tüm kayıtlar" % tarih_goster(kadar)
            else:
                tanim = "TÜM öğrencilerin TÜM geçmişi"
            if not messagebox.askyesno("Emin misiniz?", "Silinecek: %s\n\nBu işlem geri alınamaz. Devam edilsin mi?" % tanim,
                                       icon="warning", parent=pen):
                return
            try:
                yol = self.app.gecmis_yedekle()
            except OSError as hata:
                messagebox.showerror("Hata", "Yedek alınamadığı için silme yapılmadı:\n%s" % hata, parent=pen)
                return
            self.app.gecmisi_sil(hedef_ad, kadar)
            pen.destroy()
            self.adlari_yenile()
            self.yenile()
            messagebox.showinfo("Silindi", "Seçilen geçmiş kayıtlar silindi.\nYedek dosyası:\n%s" % yol, parent=self.pen)

        alt = tk.Frame(pen, bg=ZEMIN)
        alt.pack(fill="x", padx=24, pady=10)
        tk.Button(alt, text="Sil", command=sil, font=("Segoe UI", 13, "bold"), bg="#e63946", fg="white",
                  relief="flat", padx=24, pady=6, cursor="hand2").pack(side="left")
        tk.Button(alt, text="Vazgeç", command=pen.destroy, font=("Segoe UI", 13, "bold"), bg="#1d2b64", fg="white",
                  relief="flat", padx=24, pady=6, cursor="hand2").pack(side="left", padx=10)

    def pdf_kaydet(self):
        if not self.veri:
            return
        temiz = re.sub(r"[^0-9A-Za-zÇĞİÖŞÜçğıöşü_-]+", "_", self.veri["kapsam"]).strip("_") or "rapor"
        onerilen = "okuma_raporu_%s_%s_%s.pdf" % (temiz, self.veri["tur"], date.today().isoformat())
        yol = filedialog.asksaveasfilename(parent=self.pen, title="PDF olarak kaydet", defaultextension=".pdf",
                                           initialfile=onerilen, initialdir=os.path.expanduser("~"),
                                           filetypes=[("PDF dosyası", "*.pdf")])
        if not yol:
            return
        try:
            rapor_pdf_yaz(self.veri, yol, date.today())
        except OSError as hata:
            messagebox.showerror("Hata", "PDF kaydedilemedi:\n%s" % hata, parent=self.pen)
            return
        if messagebox.askyesno("PDF hazır", "Kaydedildi:\n%s\n\nŞimdi açılsın mı?" % yol, parent=self.pen):
            dosyayi_ac(yol)


# ----------------------------------------------------------------- uygulama
class Uygulama:
    def __init__(self, root):
        self.root = root
        root.title("Okuma Yarışı - Roketler Güneşe!")
        root.geometry("1280x800")
        root.minsize(800, 600)
        root.configure(bg=ARKA)
        try:
            root.state("zoomed")  # Windows'ta büyütülmüş açılır
        except tk.TclError:
            pass

        self.hedef = 100
        self.ogrenciler = []
        self.kazananlar = []
        self.afis_goster = True
        self.konfeti = []
        self.konfeti_aktif = False
        self.zaman = 0.0
        self.hazir = False
        self.W, self.H = 1280, 800
        self._boyut_id = None
        self.vars, self.girisler, self.widgetlar = [], [], []
        self.parlak_yildizlar = []
        self.tam_ekran = False

        self.gecmis = {}       # {"2026-10-12": {"Ali": 120}}  -> o gün okunan kelime
        self.rapor = None
        self.roket_konum = []
        self.aktif_gun = date.today().isoformat()
        self.kayitli_gun = None

        # zamanlayıcı durumu
        self.sure_ayar = 60
        self.calisiyor = False
        self.durakladi = False
        self.zm_bitti = False
        self.bitis = 0.0
        self.alarm_dur = False
        self.ses_proc = None
        self.zm_etiket = None
        self.zm_btn = None

        self.yukle()
        if self.kayitli_gun and self.kayitli_gun != self.aktif_gun:  # yeni gün: yeni yarış
            for o in self.ogrenciler:
                o.kelime = 0
                o.girildi = False
        self.zafer_guncelle()
        alarm_wav_uret()  # zil sesi önceden hazırlansın
        self.kalan = float(self.sure_ayar)
        self.dk_var = tk.StringVar(value="%02d" % (self.sure_ayar // 60))
        self.sn_var = tk.StringVar(value="%02d" % (self.sure_ayar % 60))

        self.canvas = tk.Canvas(root, highlightthickness=0, bg=ARKA)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", self.yeniden_boyutlandir)
        self.canvas.bind("<Button-1>", self.tikla)
        root.bind("<F11>", self.tam_ekran_degistir)
        root.bind("<Escape>", self.tam_ekrandan_cik)

        self.dongu()

    # ------------------------------------------------------------ veri
    def yukle(self):
        try:
            with open(DOSYA, "r", encoding="utf-8") as f:
                veri = json.load(f)
            self.hedef = int(veri.get("hedef", 100))
            self.sure_ayar = max(0, min(int(veri.get("sure", 60)), 99 * 60 + 59))
            g = veri.get("gecmis", {})
            if isinstance(g, dict):
                self.gecmis = g
            self.kayitli_gun = veri.get("gun")
            self.ogrenciler = [Ogrenci(o["ad"], int(o.get("kelime", 0)),
                                       bool(o.get("girildi", int(o.get("kelime", 0)) > 0)))
                               for o in veri.get("ogrenciler", [])]
        except (OSError, ValueError, KeyError, TypeError):
            pass
        if not self.ogrenciler:
            self.ogrenciler = [Ogrenci("Öğrenci %d" % i) for i in range(1, 9)]

    def kaydet(self):
        veri = {"hedef": self.hedef, "sure": self.sure_ayar, "gecmis": self.gecmis, "gun": self.aktif_gun,
                "ogrenciler": [{"ad": o.ad, "kelime": o.kelime, "girildi": o.girildi} for o in self.ogrenciler]}
        try:
            with open(DOSYA, "w", encoding="utf-8") as f:
                json.dump(veri, f, ensure_ascii=False, indent=2)
        except OSError:
            pass

    # ------------------------------------------------------------ yarış mantığı
    def zafer_guncelle(self):
        """Kazanan, ancak TÜM öğrencilerin sayısı girildikten sonra belirlenir (en çok okuyan)."""
        yeni = []
        if self.ogrenciler and all(o.girildi for o in self.ogrenciler):
            en = max(o.kelime for o in self.ogrenciler)
            if en > 0:
                yeni = [o for o in self.ogrenciler if o.kelime == en]
        if [id(o) for o in yeni] != [id(o) for o in self.kazananlar]:
            self.kazananlar = yeni
            self.afis_goster = True
            self.konfeti = []
            self.konfeti_aktif = False

    def girilen_sayisi(self):
        return sum(1 for o in self.ogrenciler if o.girildi)

    def ilerleme(self, o):
        """Roketin yüzdesi: en çok okuyan, hedefe ulaştıysa güneşe değer; diğerleri oranla geride kalır."""
        payda = max(1, self.hedef, max((x.kelime for x in self.ogrenciler), default=0))
        return min(1.0, o.kelime / float(payda))

    def kazanan_hazir(self):
        return bool(self.kazananlar) and all(abs(o.gosterilen - self.ilerleme(o)) < 0.01 for o in self.kazananlar)

    def gun_kontrol(self):
        """Gece yarısını geçince yeni gün başlar: kutular sıfırlanır, geçmiş kayıtlar korunur."""
        bugun = date.today().isoformat()
        if bugun == self.aktif_gun:
            return
        self.aktif_gun = bugun
        for o in self.ogrenciler:
            o.kelime = 0
            o.girildi = False
        for v in self.vars:
            v.set("0")
        self.zafer_guncelle()
        self.kaydet()

    def sayi_uygula(self, i, ilerle=False, onayla=False):
        if i >= len(self.vars) or i >= len(self.ogrenciler):
            return
        o = self.ogrenciler[i]
        try:
            v = int(self.vars[i].get().strip() or 0)
        except ValueError:
            v = o.kelime
        v = max(0, min(v, 99999))
        fark = v - o.kelime
        o.kelime = v
        if fark:
            # o günün kaydı, girilen sayıdır (günler birbirine eklenmez)
            self.gecmis_ayarla(self.aktif_gun, o.ad, v, kaydet=False)
        if fark or onayla:  # değer değiştiyse ya da Enter ile onaylandıysa "girildi" sayılır
            o.girildi = True
        self.vars[i].set(str(v))
        self.zafer_guncelle()
        self.kaydet()
        if ilerle and self.girisler:
            sonraki = self.girisler[(i + 1) % len(self.girisler)]
            sonraki.focus_set()
            sonraki.select_range(0, "end")

    # ------------------------------------------------------------ yerleşim
    def yeniden_boyutlandir(self, e):
        self.W, self.H = max(e.width, 400), max(e.height, 400)
        if self._boyut_id:
            self.root.after_cancel(self._boyut_id)
        self._boyut_id = self.root.after(120, self.yerlesimi_kur)

    def yerlesimi_kur(self):
        self.hesapla()
        self.arka_plan_ciz()
        self.panel_kur()
        self.hazir = True

    def hesapla(self):
        W, H = self.W, self.H
        n = max(1, len(self.ogrenciler))
        self.panel_h = max(110, int(H * 0.15))
        self.R = min(W, H) * 0.12
        self.sun_x = W / 2
        self.sun_y = self.R + 18
        self.lane_w = W / n
        mesafe = H - self.panel_h - (self.sun_y + self.R)
        rw0 = min(self.lane_w * 0.42, 64)
        self.rh = max(40, min(rw0 * 2.6, mesafe * 0.3))
        self.rw = self.rh / 2.6
        self.cy_start = H - self.panel_h - self.rh * 1.03 - 4
        self.cy_end = self.sun_y + self.R + self.rh * 0.38
        if self.cy_end > self.cy_start - 20:
            self.cy_end = self.cy_start - 20

    def arka_plan_ciz(self):
        c = self.canvas
        c.delete("bg")
        W, H = self.W, self.H
        adim = 60
        ust, orta, alt = (52, 24, 30), (8, 12, 42), (3, 5, 18)
        for i in range(adim):
            t = i / (adim - 1)
            col = karisim(ust, orta, t / 0.5) if t < 0.5 else karisim(orta, alt, (t - 0.5) / 0.5)
            y0 = int(H * i / adim)
            y1 = int(H * (i + 1) / adim) + 1
            c.create_rectangle(0, y0, W, y1, fill=col, outline=col, tags="bg")

        rnd = random.Random(7)
        track_alt = H - self.panel_h
        for _ in range(int(W * H / 5500)):
            x, y = rnd.randint(0, W), rnd.randint(0, track_alt)
            r = rnd.choice([0.7, 0.9, 1.1, 1.4])
            col = karisim("#5a6a9a", "#ffffff", rnd.random())
            c.create_oval(x - r, y - r, x + r, y + r, fill=col, outline="", tags="bg")
        self.parlak_yildizlar = [(rnd.randint(10, W - 10), rnd.randint(int(self.sun_y + self.R), track_alt - 10),
                                  rnd.random() * 6.28) for _ in range(30)]

        # şerit çizgileri ve bitiş çizgisi
        n = len(self.ogrenciler)
        bitis_y = self.sun_y + self.R
        for i in range(1, n):
            x = self.lane_w * i
            c.create_line(x, bitis_y, x, track_alt, fill="#141d4a", tags="bg")
        c.create_line(0, bitis_y, W, bitis_y, fill="#ffb627", dash=(12, 9), width=2, tags="bg")

        # alt panel
        c.create_rectangle(0, track_alt, W, H, fill=PANEL, outline="", tags="bg")
        c.create_line(0, track_alt, W, track_alt, fill="#3a4a8a", width=3, tags="bg")
        for i in range(1, n):
            x = self.lane_w * i
            c.create_line(x, track_alt + 8, x, H - 8, fill="#1d2a66", tags="bg")
        c.tag_lower("bg")

    def panel_kur(self):
        for w in self.widgetlar:
            w.destroy()
        self.widgetlar, self.girisler, self.vars = [], [], []
        self.canvas.delete("win")
        c = self.canvas
        W, H, ph = self.W, self.H, self.panel_h
        n = len(self.ogrenciler)

        # üst düğmeler
        def dugme(metin, komut, x):
            b = tk.Button(self.root, text=metin, command=komut, font=("Segoe UI", 13, "bold"),
                          bg="#1d2b64", fg="white", activebackground="#2d44a0", activeforeground="white",
                          relief="flat", padx=14, pady=6, cursor="hand2")
            c.create_window(x, 14, window=b, anchor="nw", tags="win")
            self.widgetlar.append(b)

        dugme("Ayarlar", self.ayarlar_ac, 14)
        dugme("Sıfırla", self.sifirla, 130)
        dugme("Tam Ekran", self.tam_ekran_degistir, 240)
        dugme("Raporlar", self.rapor_ac, 390)
        self.zamanlayici_kur()

        if n == 0:
            return
        fs_ad = max(9, min(18, int(self.lane_w / 8)))
        fs_sayi = max(11, min(26, int(self.lane_w / 6)))
        for i, o in enumerate(self.ogrenciler):
            cx = self.lane_w * (i + 0.5)
            lbl = tk.Label(self.root, text=o.ad, bg=PANEL, fg=RENKLER[i % len(RENKLER)],
                           font=("Segoe UI", fs_ad, "bold"), wraplength=int(self.lane_w - 10))
            lbl.configure(cursor="hand2")
            lbl.bind("<Button-1>", lambda ev, ad=o.ad: self.rapor_ac(ad))
            c.create_window(cx, H - ph * 0.68, window=lbl, width=int(self.lane_w - 8), tags="win")
            var = tk.StringVar(value=str(o.kelime))
            ent = tk.Entry(self.root, textvariable=var, justify="center",
                           font=("Segoe UI", fs_sayi, "bold"), bg="#fff4c2", fg="#111111",
                           relief="flat", insertbackground="#111111")
            c.create_window(cx, H - ph * 0.26, window=ent, width=int(self.lane_w - 14), tags="win")
            ent.bind("<Return>", lambda ev, i=i: self.sayi_uygula(i, ilerle=True, onayla=True))
            ent.bind("<KP_Enter>", lambda ev, i=i: self.sayi_uygula(i, ilerle=True, onayla=True))
            ent.bind("<FocusOut>", lambda ev, i=i: self.sayi_uygula(i))
            ent.bind("<FocusIn>", lambda ev: ev.widget.after(10, lambda w=ev.widget: w.select_range(0, "end")))
            self.widgetlar += [lbl, ent]
            self.vars.append(var)
            self.girisler.append(ent)

    # ------------------------------------------------------------ çizim
    def dongu(self):
        self.zaman += KARE_MS / 1000
        self.gun_kontrol()
        self.zamanlayici_guncelle()
        if self.hazir:
            try:
                self.ciz()
            except tk.TclError:
                return
        self.root.after(KARE_MS, self.dongu)

    def ciz(self):
        c = self.canvas
        c.delete("dyn")
        t = self.zaman
        self.yildizlari_ciz(t)
        self.gunes_ciz(t)

        W = self.W
        n = len(self.ogrenciler)
        enuygun = max((o.kelime for o in self.ogrenciler), default=0)
        payda = max(1, self.hedef, enuygun)
        fs_rozet = max(10, min(22, int(self.lane_w / 6)))
        self.roket_konum = []

        for i, o in enumerate(self.ogrenciler):
            renk = RENKLER[i % len(RENKLER)]
            p_hedef = min(1.0, o.kelime / float(payda))
            fark = p_hedef - o.gosterilen
            if abs(fark) < 0.0008:
                o.gosterilen = p_hedef
                hareket = False
            else:
                o.gosterilen += fark * 0.06
                hareket = True
            cx = self.lane_w * (i + 0.5)
            cy = self.cy_start + (self.cy_end - self.cy_start) * o.gosterilen

            if hareket and fark > 0:
                alev = 1.0
            elif o.gosterilen >= 0.999:
                alev = 0.6
            else:
                alev = 0.35
            if hareket:
                cx += random.uniform(-1.0, 1.0)

            if o in self.kazananlar and o.kelime >= self.hedef and self.kazanan_hazir():
                for k in range(5):
                    r = self.rh * (0.9 - k * 0.12) + 6 * math.sin(t * 6)
                    c.create_oval(cx - r, cy - r, cx + r, cy + r,
                                  fill=karisim("#ffd60a", "#3a2a00", 0.35 + k * 0.15),
                                  outline="", tags="dyn")
            self.roket_ciz(cx, cy, self.rw, self.rh, renk, alev)
            self.roket_konum.append((cx, cy))

            # kelime sayısı rozeti (roketin yanında)
            metin = str(o.kelime)
            gen = len(metin) * fs_rozet * 0.72 + 12
            bx = cx + self.rw * 0.95 + 3
            c.create_rectangle(bx, cy - fs_rozet * 0.9, bx + gen, cy + fs_rozet * 0.9,
                               fill=PANEL, outline=renk, width=2, tags="dyn")
            c.create_text(bx + gen / 2, cy, text=metin, fill="#ffe066",
                          font=("Segoe UI", fs_rozet, "bold"), tags="dyn")


        # başlık
        c.create_text(W - 22, 14, text="OKUMA YARIŞI", anchor="ne", fill="#ffd60a",
                      font=("Segoe UI", 26, "bold"), tags="dyn")
        c.create_text(W - 22, 56, text="Hedef: %d kelime" % self.hedef, anchor="ne",
                      fill="#cfd8ff", font=("Segoe UI", 16), tags="dyn")
        c.create_text(W - 22, 84, text="Girilen öğrenci: %d / %d" % (self.girilen_sayisi(), n), anchor="ne",
                      fill="#9aa7d6", font=("Segoe UI", 14), tags="dyn")

        self.kazanan_ciz()

    def yildizlari_ciz(self, t):
        for x, y, faz in self.parlak_yildizlar:
            r = 1.6 + 1.2 * math.sin(t * 2 + faz)
            self.canvas.create_oval(x - r, y - r, x + r, y + r, fill="#ffffff", outline="", tags="dyn")

    def gunes_ciz(self, t):
        c = self.canvas
        x, y, R, W = self.sun_x, self.sun_y, self.R, self.W
        # geniş ısı sisi
        for k in range(7):
            u = k / 6
            rx = W * 0.62 * (1 - 0.1 * k)
            ry = R * 2.7 * (1 - 0.09 * k)
            c.create_oval(x - rx, y - ry, x + rx, y + ry,
                          fill=karisim((58, 26, 32), (120, 55, 20), u ** 1.4), outline="", tags="dyn")
        # parlama halkaları
        puls = 1 + 0.03 * math.sin(t * 2)
        for k in range(12):
            u = k / 11
            r = R * (1.9 - 0.9 * u) * puls
            c.create_oval(x - r, y - r, x + r, y + r,
                          fill=karisim((95, 38, 22), (255, 150, 30), u ** 1.6), outline="", tags="dyn")
        # ışınlar
        for j in range(18):
            aci = t * 0.15 + j * (2 * math.pi / 18)
            uzun = R * (1.38 + 0.12 * math.sin(t * 3 + j * 1.7))
            a1, a2 = aci - 0.07, aci + 0.07
            c.create_polygon(x + R * 1.0 * math.cos(a1), y + R * 1.0 * math.sin(a1),
                             x + uzun * math.cos(aci), y + uzun * math.sin(aci),
                             x + R * 1.0 * math.cos(a2), y + R * 1.0 * math.sin(a2),
                             fill="#ffb627", outline="", tags="dyn")
        # çekirdek (turuncudan beyaz-sarıya)
        for j in range(9):
            r = R * (1 - 0.085 * j)
            col = karisim((255, 120, 15), (255, 250, 205), j / 8)
            c.create_oval(x - r, y - r, x + r, y + r, fill=col, outline="", tags="dyn")
        # yüzey lekeleri
        for j in range(9):
            a = t * 0.08 + j * 0.7
            d = R * (0.2 + 0.5 * ((j * 37) % 10) / 10)
            sx, sy = x + d * math.cos(a * 1.3 + j), y + d * math.sin(a + j)
            r = R * (0.05 + 0.03 * (j % 3))
            c.create_oval(sx - r, sy - r * 0.8, sx + r, sy + r * 0.8,
                          fill="#ffa21a", outline="", tags="dyn")

    def roket_ciz(self, cx, cy, rw, rh, renk, alev):
        c = self.canvas
        w = rw / 2
        ust = cy - rh / 2
        alt = cy + rh / 2
        gövde_ust = ust + rh * 0.30
        meme = alt + rh * 0.07

        # alev (titreşimli)
        fl = rh * 0.45 * alev * (0.85 + 0.3 * random.random())
        for oran_g, oran_u, col in ((0.50, 1.00, "#ff6a00"), (0.34, 0.72, "#ffc300"), (0.18, 0.42, "#fffbe0")):
            a = w * oran_g * 2
            u = fl * oran_u
            c.create_polygon(cx - a, meme, cx - a * 0.9, meme + u * 0.4, cx, meme + u,
                             cx + a * 0.9, meme + u * 0.4, cx + a, meme,
                             fill=col, outline="", smooth=True, tags="dyn")
        # kanatçıklar
        koyu = koyulastir(renk, 0.6)
        c.create_polygon(cx - w * 0.9, alt - rh * 0.35, cx - w * 1.75, alt + rh * 0.05, cx - w * 0.9, alt - rh * 0.04,
                         fill=renk, outline=koyu, width=1, tags="dyn")
        c.create_polygon(cx + w * 0.9, alt - rh * 0.35, cx + w * 1.75, alt + rh * 0.05, cx + w * 0.9, alt - rh * 0.04,
                         fill=renk, outline=koyu, width=1, tags="dyn")
        # gövde
        c.create_polygon(cx - w, gövde_ust, cx + w, gövde_ust, cx + w * 0.9, alt, cx - w * 0.9, alt,
                         fill="#f1f3f8", outline="#8d99ae", tags="dyn")
        c.create_polygon(cx + w * 0.4, gövde_ust, cx + w, gövde_ust, cx + w * 0.9, alt, cx + w * 0.35, alt,
                         fill="#c6cddc", outline="", tags="dyn")
        # burun konisi
        c.create_polygon(cx - w, gövde_ust, cx - w * 0.85, gövde_ust - rh * 0.12, cx - w * 0.4, ust + rh * 0.05,
                         cx, ust, cx + w * 0.4, ust + rh * 0.05, cx + w * 0.85, gövde_ust - rh * 0.12,
                         cx + w, gövde_ust, fill=renk, outline=koyu, smooth=True, tags="dyn")
        # şerit
        c.create_rectangle(cx - w * 0.97, gövde_ust + rh * 0.50, cx + w * 0.93, gövde_ust + rh * 0.56,
                           fill=renk, outline="", tags="dyn")
        # pencere
        py = gövde_ust + rh * 0.20
        r = w * 0.48
        c.create_oval(cx - r - 3, py - r - 3, cx + r + 3, py + r + 3, fill="#6c7a93", outline="#4a5568", tags="dyn")
        c.create_oval(cx - r, py - r, cx + r, py + r, fill="#1d6fb8", outline="", tags="dyn")
        c.create_oval(cx - r * 0.55, py - r * 0.6, cx - r * 0.05, py - r * 0.1, fill="#cfe9ff", outline="", tags="dyn")
        # nozul
        c.create_polygon(cx - w * 0.6, alt, cx + w * 0.6, alt, cx + w * 0.45, meme, cx - w * 0.45, meme,
                         fill="#4a4e69", outline="#22223b", tags="dyn")

    def kazanan_ciz(self):
        if not self.kazanan_hazir():  # tüm öğrenciler girilmeden duyuru yapılmaz
            self.konfeti_aktif = False
            self.konfeti = []
            return
        kl = self.kazananlar
        hedefe_ulasti = kl[0].kelime >= self.hedef
        c = self.canvas
        W, H = self.W, self.H
        if hedefe_ulasti:
            if not self.konfeti_aktif:
                self.konfeti_aktif = True
                self.konfeti = [dict(x=random.uniform(0, W), y=random.uniform(-H, 0),
                                     vx=random.uniform(-1.5, 1.5), vy=random.uniform(2.5, 6),
                                     s=random.uniform(5, 11), renk=random.choice(RENKLER)) for _ in range(160)]
            for p in self.konfeti:
                p["y"] += p["vy"]
                p["x"] += p["vx"] + math.sin(self.zaman * 3 + p["s"])
                if p["y"] > H + 10:
                    p["y"] = -10
                    p["x"] = random.uniform(0, W)
                c.create_rectangle(p["x"], p["y"], p["x"] + p["s"], p["y"] + p["s"] * 0.6,
                                   fill=p["renk"], outline="", tags="dyn")
        if not self.afis_goster:
            return
        cok = len(kl) > 1
        if hedefe_ulasti:
            baslik = "KAZANANLAR" if cok else "KAZANAN"
            alt = "%d kelime okudu!" % kl[0].kelime
        else:
            baslik = "EN ÇOK OKUYANLAR" if cok else "EN ÇOK OKUYAN"
            alt = "%d kelime okudu (hedefe ulaşan olmadı)" % kl[0].kelime
        isimler = ", ".join(o.ad for o in kl)
        bw, bh = min(W * 0.8, 1000), 200
        cx, cy = W / 2, H * 0.5
        c.create_rectangle(cx - bw / 2, cy - bh / 2, cx + bw / 2, cy + bh / 2,
                           fill="#101a4a", outline="#ffd60a", width=5, tags="dyn")
        c.create_text(cx, cy - 62, text=baslik, fill="#ffd60a", font=("Segoe UI", 24, "bold"), tags="dyn")
        boyut = int(max(16, min(60, bw / (len(isimler) * 0.62 + 1))))
        c.create_text(cx, cy - 2, text=isimler, fill="white", font=("Segoe UI", boyut, "bold"), tags="dyn")
        c.create_text(cx, cy + 52, text=alt, fill="#cfd8ff", font=("Segoe UI", 16), tags="dyn")
        c.create_text(cx, cy + 80, text="(kapatmak için dokun)", fill="#8d99ae", font=("Segoe UI", 12), tags="dyn")

    # ------------------------------------------------------------ zamanlayıcı
    @staticmethod
    def sure_metni(sn):
        m, s = divmod(int(math.ceil(sn)), 60)
        return "%02d:%02d" % (m, s)

    def zamanlayici_kur(self):
        cerceve = tk.Frame(self.root, bg=PANEL, highlightbackground="#3a4a8a", highlightthickness=2)
        self.zm_etiket = tk.Label(cerceve, text=self.sure_metni(self.kalan), bg=PANEL, fg="white",
                                  font=("Consolas", 36, "bold"))
        self.zm_etiket.pack(padx=10, pady=(2, 0))
        satir = tk.Frame(cerceve, bg=PANEL)
        satir.pack(padx=8, pady=(0, 6))

        def spin(degisken, ust):
            sp = tk.Spinbox(satir, from_=0, to=ust, textvariable=degisken, wrap=True, width=3,
                            format="%02.0f", font=("Segoe UI", 14, "bold"), justify="center",
                            command=self.zm_ayar_degisti)
            sp.bind("<KeyRelease>", self.zm_ayar_degisti)
            sp.bind("<FocusOut>", self.zm_ayar_degisti)
            return sp

        spin(self.dk_var, 99).pack(side="left")
        tk.Label(satir, text=":", bg=PANEL, fg="white", font=("Segoe UI", 16, "bold")).pack(side="left", padx=2)
        spin(self.sn_var, 59).pack(side="left")
        self.zm_btn = tk.Button(satir, text="Başlat", command=self.zm_basla_duraklat, width=8,
                                font=("Segoe UI", 12, "bold"), bg="#2ecc71", fg="white",
                                activebackground="#27ae60", activeforeground="white",
                                relief="flat", cursor="hand2")
        self.zm_btn.pack(side="left", padx=(10, 4))
        tk.Button(satir, text="Sıfırla", command=self.zm_sifirla, width=7,
                  font=("Segoe UI", 12, "bold"), bg="#e63946", fg="white",
                  activebackground="#c1121f", activeforeground="white",
                  relief="flat", cursor="hand2").pack(side="left")
        self.canvas.create_window(14, 64, window=cerceve, anchor="nw", tags="win")
        self.widgetlar.append(cerceve)

    def zm_ayar_oku(self):
        try:
            dk = max(0, min(int(self.dk_var.get()), 99))
            sn = max(0, min(int(self.sn_var.get()), 59))
        except ValueError:
            return None
        return dk * 60 + sn

    def zm_ayar_degisti(self, _e=None):
        if self.calisiyor or self.durakladi:
            return
        s = self.zm_ayar_oku()
        if s is None:
            return
        self.sure_ayar = s
        self.kalan = float(s)
        self.zm_bitti = False
        self.kaydet()

    def zm_basla_duraklat(self):
        if self.calisiyor:  # duraklat
            self.kalan = max(0.0, self.bitis - time.monotonic())
            self.calisiyor = False
            self.durakladi = True
            return
        if self.durakladi:  # devam et
            self.bitis = time.monotonic() + self.kalan
            self.calisiyor = True
            self.durakladi = False
            return
        self.alarm_durdur()  # yeni başlat
        s = self.zm_ayar_oku()
        if s is None or s <= 0:
            messagebox.showwarning("Uyarı", "Önce süreyi ayarlayın.", parent=self.root)
            return
        self.sure_ayar = s
        self.kaydet()
        self.kalan = float(s)
        self.zm_bitti = False
        self.bitis = time.monotonic() + s
        self.calisiyor = True

    def zm_sifirla(self):
        self.alarm_durdur()
        self.calisiyor = False
        self.durakladi = False
        self.zm_bitti = False
        s = self.zm_ayar_oku()
        if s is not None:
            self.sure_ayar = s
            self.kaydet()
        self.kalan = float(self.sure_ayar)

    def zamanlayici_guncelle(self):
        if self.calisiyor:
            self.kalan = max(0.0, self.bitis - time.monotonic())
            if self.kalan <= 0:
                self.calisiyor = False
                self.zm_bitti = True
                self.alarm_cal()
        if self.zm_etiket is None:
            return
        if self.zm_bitti:
            metin = "SÜRE BİTTİ!"
            renk = "#ff3b30" if int(self.zaman * 3) % 2 == 0 else "#ffd60a"
        else:
            metin = self.sure_metni(self.kalan)
            if self.calisiyor and self.kalan <= 10:
                renk = "#ff5a36"
            elif self.durakladi:
                renk = "#9aa7d6"
            else:
                renk = "#7dffa0" if self.calisiyor else "white"
        if self.calisiyor:
            btn = "Duraklat"
        elif self.durakladi:
            btn = "Devam"
        else:
            btn = "Başlat"
        try:
            self.zm_etiket.configure(text=metin, fg=renk)
            if self.zm_btn is not None:
                self.zm_btn.configure(text=btn)
        except tk.TclError:
            pass  # pencere yeniden kuruluyor

    def alarm_durdur(self):
        self.alarm_dur = True
        try:
            import winsound
            winsound.PlaySound(None, winsound.SND_PURGE)  # Windows: çalan sesi hemen kes
        except Exception:
            pass
        if self.ses_proc is not None and self.ses_proc.poll() is None:  # Linux/Pardus
            try:
                self.ses_proc.terminate()
            except OSError:
                pass

    def zil_yedek(self):
        for k in range(8):
            self.root.after(k * 350, self.root.bell)

    def alarm_cal(self):
        self.alarm_dur = False
        try:
            import winsound
        except ImportError:
            winsound = None

        if winsound is None:  # Linux (Pardus) / macOS: sistemdeki ses çalıcıyı kullan
            for ad in ("paplay", "pw-play", "aplay", "afplay", "play"):
                yol = shutil.which(ad)
                if yol:
                    break
            else:
                self.zil_yedek()
                return
            try:
                dosya = os.path.join(tempfile.gettempdir(), "okuma_yarisi_zil.wav")
                with open(dosya, "wb") as f:
                    f.write(alarm_wav_uret())
                komut = [yol, "-q", dosya] if ad == "aplay" else [yol, dosya]
                self.ses_proc = subprocess.Popen(komut, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except OSError:
                self.zil_yedek()
            return

        def calis():
            try:
                winsound.PlaySound(alarm_wav_uret(), winsound.SND_MEMORY)
            except Exception:
                try:
                    winsound.MessageBeep()
                except Exception:
                    pass

        threading.Thread(target=calis, daemon=True).start()

    # ------------------------------------------------------------ olaylar / pencereler
    def tikla(self, e):
        self.canvas.focus_set()  # kutudaki değer uygulanır
        if self.afis_goster and self.kazanan_hazir():
            self.afis_goster = False
            return
        for i, (cx, cy) in enumerate(self.roket_konum):  # roketa dokununca o öğrencinin raporu
            if i < len(self.ogrenciler) and abs(e.x - cx) <= self.rw * 1.1 + 12 and abs(e.y - cy) <= self.rh * 0.75:
                self.rapor_ac(self.ogrenciler[i].ad)
                return

    # ------------------------------------------------------------ geçmiş kayıtları
    def gecmis_ayarla(self, iso, ad, deger, kaydet=True):
        """Bir öğrencinin belirli bir güne ait kelime sayısını yazar (0 ise kaydı siler)."""
        kayit = self.gecmis.setdefault(iso, {})
        if deger > 0:
            kayit[ad] = deger
        else:
            kayit.pop(ad, None)
        if not kayit:
            self.gecmis.pop(iso, None)
        if kaydet:
            self.kaydet()

    def gecmis_yedekle(self):
        yol = os.path.join(os.path.dirname(DOSYA), "okuma_yarisi_yedek_%s.json" % datetime.now().strftime("%Y%m%d_%H%M%S"))
        with open(yol, "w", encoding="utf-8") as f:
            json.dump({"gecmis": self.gecmis}, f, ensure_ascii=False, indent=2)
        return yol

    def gecmisi_sil(self, ad=None, kadar=None):
        """ad verilirse sadece o öğrencinin, kadar (tarih) verilirse o tarihe kadar olan kayıtlar silinir."""
        for iso in list(self.gecmis):
            d = iso_coz(iso)
            if kadar is not None and (d is None or d > kadar):
                continue
            if ad is None:
                del self.gecmis[iso]
            else:
                self.gecmis[iso].pop(ad, None)
                if not self.gecmis[iso]:
                    del self.gecmis[iso]
        self.kaydet()

    def rapor_ac(self, ad=None):
        self.canvas.focus_set()
        if self.rapor is not None:
            try:
                self.rapor.sec(ad)
                return
            except tk.TclError:
                self.rapor = None
        self.rapor = RaporPenceresi(self, ad)

    def tam_ekran_degistir(self, _e=None):
        self.tam_ekran = not self.tam_ekran
        self.root.attributes("-fullscreen", self.tam_ekran)

    def tam_ekrandan_cik(self, _e=None):
        if self.tam_ekran:
            self.tam_ekran = False
            self.root.attributes("-fullscreen", False)

    def sifirla(self):
        if messagebox.askyesno("Sıfırla", "Tüm kelime sayıları 0 yapılsın mı?\n(Yeni yarış başlar. Geçmiş günlerin kayıtları silinmez.)", parent=self.root):
            for o in self.ogrenciler:
                o.kelime = 0
                o.girildi = False
            self.zafer_guncelle()
            self.kaydet()
            for v in self.vars:
                v.set("0")

    def ayarlar_ac(self):
        pen = tk.Toplevel(self.root)
        pen.title("Ayarlar")
        pen.configure(bg="#10163a")
        pen.geometry("460x600")
        pen.transient(self.root)
        pen.grab_set()

        tk.Label(pen, text="Öğrenci isimleri (her satıra bir isim):", bg="#10163a", fg="white",
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", padx=14, pady=(14, 4))
        metin = tk.Text(pen, font=("Segoe UI", 13), height=16, width=34)
        metin.pack(padx=14, fill="both", expand=True)
        metin.insert("1.0", "\n".join(o.ad for o in self.ogrenciler))

        satir = tk.Frame(pen, bg="#10163a")
        satir.pack(fill="x", padx=14, pady=12)
        tk.Label(satir, text="Hedef kelime sayısı:", bg="#10163a", fg="white",
                 font=("Segoe UI", 13, "bold")).pack(side="left")
        hedef_var = tk.StringVar(value=str(self.hedef))
        tk.Entry(satir, textvariable=hedef_var, width=8, font=("Segoe UI", 14), justify="center").pack(side="left", padx=10)

        def kaydet_kapat():
            isimler = [s.strip() for s in metin.get("1.0", "end").splitlines() if s.strip()]
            if not isimler:
                messagebox.showwarning("Uyarı", "En az bir öğrenci ismi girin.", parent=pen)
                return
            try:
                hedef = int(hedef_var.get().strip())
                if hedef <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showwarning("Uyarı", "Hedef, 0'dan büyük bir sayı olmalı.", parent=pen)
                return
            eskiler = {o.ad: o for o in self.ogrenciler}
            self.ogrenciler = [eskiler.get(ad) or Ogrenci(ad) for ad in isimler]
            self.hedef = hedef
            self.zafer_guncelle()
            self.kaydet()
            pen.destroy()
            self.yerlesimi_kur()

        tk.Button(pen, text="Kaydet", command=kaydet_kapat, font=("Segoe UI", 14, "bold"),
                  bg="#2ecc71", fg="white", relief="flat", padx=20, pady=6).pack(pady=(0, 14))


def main():
    root = tk.Tk()
    Uygulama(root)
    root.mainloop()


if __name__ == "__main__":
    main()
