# -*- coding: utf-8 -*-
"""
Entspannt Reisen 3.5 – Bahn-Lernplaner, KI-Zusammenfasser & Echtzeit-DB-Sync
=============================================================================
• Großes, leserfreundliches Design mit abgerundeten Buttons (CustomTkinter).
• Aktive Status-Erkennung in Echtzeit:
    Weiß immer aktiv, ob du dich noch in der 🏠 VORBEREITUNG (vor der Abfahrt)
    oder 🚆 AKTIV IM ZUG / UNTERWEGS befindest – und synchronisiert Phase & Timer.
• Echte Zugverbindung im Minutentakt aktualisiert (DB IRIS-TTS Echtzeit-API):
    Solange Entspannt Reisen geöffnet ist, werden Verspätungen deiner Züge jede
    Minute (alle 60 Sek.) automatisch live von der Deutschen Bahn abgefragt
    und in den Lern-Zeitplan & Timer eingerechnet (keine manuelle Eingabe nötig!).
• Automatischer Offline-Fallback im Funkloch:
    Fällt im Zug das Internet aus, läuft der große Lern-Timer nahtlos asynchron
    weiter und du kannst Verspätungen manuell per Klick (+5/+10/+15/+25 Min.)
    eintragen. Sobald wieder Netz da ist, übernimmt wieder der Live-Sync.
• Intelligente Umstiegs- & Regio-Regeln:
    - Normale Umstiege (< 25 Min.) = 100 % Lernpause ☕
    - Lange Umstiege (>= 25 Min.) = 15 Min. Umstiegs-Pause ☕ + Restzeit als Lernblock 📖
    - Mittlere Regio-Verbindung = Enger-Bahn-Modus 📱 (KEIN Laptop! Nur Auswendiglernen/Pause)
    - Verpasster Anschluss (< 3 Min. Umstieg) = Automatisch +30 Min. Extra-Pause
    - Neue Verbindung wählen & alte löschen = Bisherige Zeit gilt als erledigt ✅
"""

import base64
import datetime
import html
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import tkinter as tk
from tkinter import messagebox
import customtkinter as ctk

try:
    import ctypes
    ctypes.windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    pass
try:
    ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("winte.EntspanntReisen")
except Exception:
    pass

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

# --------------------------------------------------------------------------
# Pfade & Konfiguration
# --------------------------------------------------------------------------
ROOT = os.path.dirname(os.path.abspath(__file__))
if not os.path.exists(os.path.join(ROOT, "Marketing [V] (HWS 2026)")):
    ROOT = r"C:\Users\winte\OneDrive - students.uni-mannheim.de\Desktop\uni"

FONTS_DIR = os.path.join(ROOT, "fonts")


def init_db_fonts():
    """Lädt und registriert die originalen Schriften der Deutschen Bahn (DB Screen Head & DB Screen Sans)."""
    f_head = "Segoe UI"
    f_body = "Segoe UI"
    try:
        os.makedirs(FONTS_DIR, exist_ok=True)
        needed = {
            "DBScreenHead-900.ttf": ("DBScreenHead", "900"),
            "DBScreenSans-700.ttf": ("DBScreenSans", "700"),
            "DBScreenSans-400.ttf": ("DBScreenSans", "400"),
        }
        missing = [fn for fn in needed if not os.path.isfile(os.path.join(FONTS_DIR, fn))]
        if missing:
            try:
                from fontTools.ttLib import TTFont
                import urllib.request
                import base64
                url = "https://www.bahn.de/.resources/bahn-common-light/webresources/css/main-DMnPTxpq.css"
                req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
                css = urllib.request.urlopen(req, timeout=8).read().decode("utf-8", errors="ignore")
                for ff in re.findall(r'@font-face\s*\{([^}]+)\}', css):
                    nm = re.search(r'font-family:\s*([^;]+)', ff)
                    wm = re.search(r'font-weight:\s*([^;]+)', ff)
                    bm = re.search(r'base64,([A-Za-z0-9+/=]+)', ff)
                    if nm and bm:
                        fam = nm.group(1).strip().replace("'", "").replace('"', '')
                        w = wm.group(1).strip() if wm else "400"
                        fname = f"{fam}-{w}.ttf"
                        if fname in needed:
                            wpath = os.path.join(FONTS_DIR, f"{fam}-{w}.woff2")
                            tpath = os.path.join(FONTS_DIR, fname)
                            with open(wpath, "wb") as wf:
                                wf.write(base64.b64decode(bm.group(1)))
                            tt = TTFont(wpath)
                            tt.flavor = None
                            tt.save(tpath)
            except Exception:
                pass

        if os.name == "nt":
            import ctypes
            FR_PRIVATE = 0x10
            for fn in os.listdir(FONTS_DIR):
                if fn.endswith(".ttf"):
                    ctypes.windll.gdi32.AddFontResourceExW(os.path.join(FONTS_DIR, fn), FR_PRIVATE, 0)

        import tkinter.font as tkfont
        # Create a hidden dummy root if needed to query families
        _t = tk.Tk()
        _t.withdraw()
        fams = tkfont.families(_t)
        _t.destroy()
        if "DB Screen Head Black" in fams:
            f_head = "DB Screen Head Black"
        elif "DB Screen Sans" in fams:
            f_head = "DB Screen Sans"
        if "DB Screen Sans" in fams:
            f_body = "DB Screen Sans"
    except Exception:
        pass
    return f_head, f_body


FONT_HEAD, FONT_BODY = init_db_fonts()

OUTPUT_ROOT = os.path.join(ROOT, "Entspannt Reisen")
CONFIG_PATH = os.path.join(ROOT, ".entspannt_reisen.json")
LOCAL_APP_DIR = os.path.join(os.environ.get("LOCALAPPDATA", tempfile.gettempdir()), "EntspanntReisen")
DB_PROFILE_DIR = os.path.join(LOCAL_APP_DIR, "db_browser_profile")
NO_WINDOW = 0x08000000 if os.name == "nt" else 0

LONG_TRANSFER_THRESHOLD_MIN = 25
LONG_TRANSFER_BREAK_MIN = 15
MISSED_CONNECTION_PENALTY_MIN = 30
LIVE_POLL_INTERVAL_SEC = 60

# Auswendiglern-Priorität für volle Züge (🧠 Stehplatz / Voll): 1. Wifo, 2. Marketing, 3. FGdI
MEMO_PRIORITY = ["wifo", "marketing", "fgdi"]
# Merksatz-PDF fürs Handy wird direkt in OneDrive gespeichert (synchronisiert aufs Handy)
ONEDRIVE_PHONE_DIR = r"C:\Users\winte\OneDrive - students.uni-mannheim.de"
WEEKDAY_FULL_DE = ["Montag", "Dienstag", "Mittwoch", "Donnerstag", "Freitag", "Samstag", "Sonntag"]

GROUPS = [
    {"id": "pi1", "module": "Praktische Informatik I", "category": "Große Übung (Wochenordner)",
     "parent_dir": os.path.join(ROOT, "Praktische Informatik I [Ü] [1. PG] (HWS 2026)", "Dateien"), "icon": "💻"},
    {"id": "pp1_grosse_uebung", "module": "Programmierpraktikum I", "category": "Große Übung",
     "parent_dir": os.path.join(ROOT, "Programmierpraktikum I, Große Übung [Ü] (HWS 2026)", "Große Übung"), "icon": "⚙️"},
    {"id": "pp1_projekt", "module": "Programmierpraktikum I", "category": "Projektblätter (Tutorium)",
     "parent_dir": os.path.join(ROOT, "Programmierpraktikum I, Große Übung [Ü] (HWS 2026)", "Tutorien", "Projektblätter"), "icon": "📝"},
    {"id": "marketing", "module": "Marketing", "category": "Übungen (PDFs)",
     "parent_dir": os.path.join(ROOT, "Marketing [V] (HWS 2026)", "Dateien", "Übung"), "icon": "📈"},
    {"id": "fgdi", "module": "Formale Grundlagen der Informatik", "category": "Übungsblätter (PDFs)",
     "parent_dir": os.path.join(ROOT, "Formale Grundlagen der Informatik [V] (HWS 2026)", "Übungsblätter"), "icon": "📐"},
    {"id": "wifo", "module": "Wirtschaftsinformatik I (IS 201)", "category": "Tutorien (Ordner)",
     "parent_dir": os.path.join(ROOT, "IS 201 Wirtschaftsinformatik I- Einführung und Grundlagen [V] (HWS 2026)", "Tutorium"), "icon": "🏢"},
]

DONE_PREFIXES = ["☑️ ", "☑ ", "✅ "]
OPEN_PREFIX = "⬜ "
TEXT_EXT = {".txt", ".md", ".java", ".c", ".h", ".cpp", ".py", ".hs", ".sql", ".csv", ".tex", ".js", ".html", ".xml", ".json", ".sh"}
MAX_FILES = 25
MAX_TOTAL_BYTES = 45 * 1024 * 1024

LEG_MODES = [
    ("focus", "💻 Sitzplatz (Aufgaben)"),
    ("regio_memo", "🧠 Stehplatz (Theorie)"),
    ("rest", "☕ Pause (Nichts lernen)"),
]
LEG_MODE_LABELS = dict(LEG_MODES)
LEG_LABEL_TO_MODE = {label: code for code, label in LEG_MODES}
LEG_LABEL_TO_MODE.update({
    "💻 Sitzplatz (Laptop & Aufgaben)": "focus",
    "💻 Sitzplatz (Aufgaben)": "focus",
    "📖 Sitzplatz / Leicht (Lesen)": "focus",
    "🧠 Stehplatz / Voll (Nur Theorie)": "regio_memo",
    "🧠 Stehplatz (Theorie)": "regio_memo",
    "☕ Pause (Nichts lernen)": "rest",
    "🟢 Zug frei / Platz: Laptop & Aufgaben": "focus",
    "🟡 Mittelvoll: Leichtes Lesen (wenig Platz)": "focus",
    "🟠 Zug VOLL (Enger Regio): Nur Auswendiglernen (Kein Laptop!)": "regio_memo",
    "🔴 Zug ZU VOLL / Pause: Gar nichts lernen": "rest",
})


def short_module_name(mod_str):
    return (
        (mod_str or "")
        .replace("Praktische Informatik I", "Praktische Info I")
        .replace("Programmierpraktikum I", "Programmierpraktikum")
        .replace("Formale Grundlagen der Informatik", "Formale Grundlagen")
        .replace("Wirtschaftsinformatik I (IS 201)", "Wirtschaftsinfo I")
    )


def short_item_name(item_str):
    s = (item_str or "").strip()
    s = os.path.splitext(s)[0]
    m_w = re.match(r"^W(\d+)\b", s, re.I)
    if m_w:
        return f"W{m_w.group(1)}"
    m_b = re.search(r"Blatt[_\s-]*(\d+)", s, re.I)
    if m_b:
        return f"B{int(m_b.group(1)):02d}"
    m_p = re.search(r"Projekt(?:blatt)?[_\s-]*(\d+)", s, re.I)
    if m_p:
        return f"P{int(m_p.group(1)):02d}"
    return s[:14]

DEFAULT_TRIP = {
    "title": "Mannheim Hbf → Ulm Hbf (2× Umsteigen)",
    "date": "06.11.2026",
    "source": "Aus DB-Konto (bahn.de) geladen – Gemerkte Reise",
    "extra_pause_min": 0,
    "extra_pause_after_leg": 0,
    "completed_group_ids": [],
    "legs": [
        {
            "train": "S3",
            "type": "REGIO",
            "from_station": "Mannheim Hbf",
            "to_station": "Karlsruhe-Durlach",
            "planned_dep": "12:30",
            "planned_arr": "13:30",
            "dep": "12:30",
            "arr": "13:30",
            "duration_min": 60,
            "transfer_after_min": 7,
            "delay_min": 0,
            "mode": "focus",
        },
        {
            "train": "RE1 (19017)",
            "type": "REGIO",
            "from_station": "Karlsruhe-Durlach",
            "to_station": "Stuttgart Hbf",
            "planned_dep": "13:37",
            "planned_arr": "14:27",
            "dep": "13:37",
            "arr": "14:27",
            "duration_min": 50,
            "transfer_after_min": 12,
            "delay_min": 0,
            "mode": "regio_memo",
        },
        {
            "train": "RE5 (4221)",
            "type": "REGIO",
            "from_station": "Stuttgart Hbf",
            "to_station": "Ulm Hbf",
            "planned_dep": "14:39",
            "planned_arr": "15:43",
            "dep": "14:39",
            "arr": "15:43",
            "duration_min": 64,
            "transfer_after_min": 0,
            "delay_min": 0,
            "mode": "focus",
        },
    ],
}

PRESET_TRIPS = [DEFAULT_TRIP]

DEFAULT_CONFIG = {
    "enabled": {g["id"]: True for g in GROUPS},
    "provider": "auto",
    "gemini_cli_model": "gemini-4-argon-medium",
    "claude_cli_model": "opus",
    "gemini_api_key": "",
    "anthropic_api_key": "",
    "overwrite": False,
    "db_username": "",
    "db_password": "",
    "db_logged_in": False,
    "current_trip": DEFAULT_TRIP,
    "saved_trips": [DEFAULT_TRIP],
}


def ensure_planned_times(trip):
    """Stellt sicher, dass jeder Zugabschnitt planned_dep und planned_arr besitzt."""
    if not isinstance(trip, dict):
        return
    for leg in trip.get("legs", []):
        if not leg.get("planned_dep"):
            leg["planned_dep"] = leg.get("dep", "09:00")
        if not leg.get("planned_arr"):
            leg["planned_arr"] = leg.get("arr", "09:45")
        leg.setdefault("delay_min", 0)


def is_corrupted_trip(trip):
    """Erkennt fehlerhaft geparste Platzhalter-Reisen (z.B. 'Sa' als Zugname)."""
    if not isinstance(trip, dict):
        return True
    legs = trip.get("legs") or []
    if not legs:
        return True
    first_train = (legs[0].get("train") or "").strip().lower()
    first_from = (legs[0].get("from_station") or "").strip().lower()
    if first_train in ("sa", "so", "mo", "di", "mi", "do", "fr") or "gemerkte reise" in first_from:
        return True
    return False


def trip_identity_key(trip):
    if not isinstance(trip, dict):
        return ""
    legs = trip.get("legs") or []
    first_dep = legs[0].get("planned_dep") or legs[0].get("dep", "") if legs else ""
    last_arr = legs[-1].get("planned_arr") or legs[-1].get("arr", "") if legs else ""
    first_st = legs[0].get("from_station", "") if legs else ""
    last_st = legs[-1].get("to_station", "") if legs else ""
    return f"{trip.get('date', '')}|{first_dep}|{last_arr}|{first_st}|{last_st}|{len(legs)}"


def register_trip_in_saved_list(cfg, trip):
    if not isinstance(trip, dict) or is_corrupted_trip(trip):
        return
    ensure_planned_times(trip)
    saved = cfg.setdefault("saved_trips", [])
    saved = [t for t in saved if isinstance(t, dict) and not is_corrupted_trip(t)]
    key = trip_identity_key(trip)
    replaced = False
    for idx, existing in enumerate(saved):
        if trip_identity_key(existing) == key:
            saved[idx] = json.loads(json.dumps(trip))
            replaced = True
            break
    if not replaced:
        saved.insert(0, json.loads(json.dumps(trip)))
    cfg["saved_trips"] = saved[:15]


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    try:
        if os.path.isfile(CONFIG_PATH):
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            for k, v in data.items():
                if k == "enabled" and isinstance(v, dict):
                    cfg["enabled"].update(v)
                elif k == "current_trip" and isinstance(v, dict) and v.get("legs"):
                    if is_corrupted_trip(v):
                        v = json.loads(json.dumps(DEFAULT_TRIP))
                    for dk, dv in DEFAULT_TRIP.items():
                        v.setdefault(dk, dv)
                    ensure_planned_times(v)
                    cfg["current_trip"] = v
                elif k == "saved_trips" and isinstance(v, list):
                    clean_list = []
                    for item in v:
                        if isinstance(item, dict) and not is_corrupted_trip(item):
                            ensure_planned_times(item)
                            clean_list.append(item)
                    if clean_list:
                        cfg["saved_trips"] = clean_list
                elif k == "gemini_cli_model":
                    cfg[k] = "gemini-4-argon-medium" if v in ("pro", "auto", "") else v
                else:
                    cfg[k] = v
    except Exception:
        pass
    ensure_planned_times(cfg.get("current_trip"))
    register_trip_in_saved_list(cfg, cfg.get("current_trip"))
    return cfg


def save_config(cfg):
    try:
        register_trip_in_saved_list(cfg, cfg.get("current_trip"))
        if os.path.isfile(CONFIG_PATH) and os.name == "nt":
            subprocess.run(["attrib", "-h", CONFIG_PATH], creationflags=NO_WINDOW)
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        if os.name == "nt":
            subprocess.run(["attrib", "+h", CONFIG_PATH], creationflags=NO_WINDOW)
    except Exception:
        pass


# --------------------------------------------------------------------------
# Zeit-, Status-, Umstiegs- & Verspätungs-Logik
# --------------------------------------------------------------------------
def parse_hhmm_to_min(hhmm):
    m = re.match(r"^(\d{1,2}):(\d{2})$", (hhmm or "").strip())
    if not m:
        return None
    return int(m.group(1)) * 60 + int(m.group(2))


def min_to_hhmm(total_min):
    total_min = int(total_min) % (24 * 60)
    return f"{total_min // 60:02d}:{total_min % 60:02d}"


def diff_minutes(dep_hhmm, arr_hhmm, fallback=35):
    d = parse_hhmm_to_min(dep_hhmm)
    a = parse_hhmm_to_min(arr_hhmm)
    if d is None or a is None:
        return fallback
    diff = a - d
    if diff < 0:
        diff += 24 * 60
    return max(1, diff)


def now_minutes_of_day():
    now = datetime.datetime.now()
    return now.hour * 60 + now.minute + (now.second / 60.0)


def parse_trip_date(date_str):
    s = (date_str or "").strip()
    m = re.search(r"(\d{1,2}\.\d{1,2}\.\d{2,4}|\d{4}-\d{2}-\d{2})", s)
    if m:
        s = m.group(1)
    for fmt in ("%d.%m.%Y", "%Y-%m-%d", "%d.%m.%y"):
        try:
            return datetime.datetime.strptime(s, fmt).date()
        except Exception:
            pass
    return datetime.date.today()


WEEKDAY_SHORT_DE = ["Mo", "Di", "Mi", "Do", "Fr", "Sa", "So"]


def format_date_with_weekday(date_str, short=False):
    dt = parse_trip_date(date_str)
    wd = WEEKDAY_SHORT_DE[dt.weekday()]
    if short:
        return f"{wd}, {dt.strftime('%d.%m.')}"
    return f"{wd}, {dt.strftime('%d.%m.%Y')}"


def format_trip_dropdown_label(trip, idx=None):
    legs = (trip or {}).get("legs") or []
    date_lbl = format_date_with_weekday((trip or {}).get("date"), short=True)
    if legs:
        dep_s = legs[0].get("dep", "09:00")
        arr_s = legs[-1].get("arr", "12:00")
        from_s = legs[0].get("from_station", "Start")
        to_s = legs[-1].get("to_station", "Ziel")
        trains = ", ".join(l.get("train", "Zug") for l in legs)
        prefix = f"{idx}. " if idx is not None else ""
        return f"{prefix}{date_lbl} ({dep_s}–{arr_s}) · {from_s} → {to_s} [{trains}]"
    return f"{date_lbl} · {(trip or {}).get('title', 'Reise')}"


def detect_trip_live_state(trip):
    """
    Erkennt sekundengenau, ob sich der Nutzer aktuell:
      - 'vorbereitung'            -> Vor der Reise (heute vor Abfahrt oder an einem Folgetag)
      - 'im_zug'                  -> Aktiv im Zug (in Abschnitt X)
      - 'umstieg'                 -> Aktiv unterwegs (im Umstieg zwischen Abschnitt X und X+1)
      - 'vorbereitung_vergangen'  -> Eingetragene Uhrzeit heute ist bereits vorbei (Vorbereitung / Vorlage)
    befindet.
    """
    legs = (trip or {}).get("legs") or DEFAULT_TRIP["legs"]
    trip_date = parse_trip_date((trip or {}).get("date"))
    today = datetime.date.today()
    now_m = now_minutes_of_day()

    first_dep = parse_hhmm_to_min(legs[0].get("dep", "09:00")) or 540
    last_arr = parse_hhmm_to_min(legs[-1].get("arr", "12:00")) or 720
    if last_arr < first_dep:
        last_arr += 1440

    from_first = legs[0].get("from_station", "Start")
    to_last = legs[-1].get("to_station", "Ziel")
    dep_first_s = legs[0].get("dep", "09:00")
    short_date_lbl = format_date_with_weekday((trip or {}).get("date"), short=True)
    route_short = f"{from_first} → {to_last}"

    if trip_date > today:
        days = (trip_date - today).days
        return {
            "state": "vorbereitung",
            "is_in_train": False,
            "active_leg_idx": None,
            "wait_sec": int(days * 86400 + (first_dep - now_m) * 60),
            "badge": f"📅 Nächste Fahrt: {short_date_lbl} ({dep_first_s} Uhr) · {route_short}",
            "sub": f"Start in {days} Tag(en) am {trip_date.strftime('%d.%m.%Y')} um {dep_first_s} Uhr ({len(legs)} Züge)",
            "color": "#ff4d5e",
            "bg": "#221115",
        }

    if trip_date < today:
        return {
            "state": "vorbereitung_vergangen",
            "is_in_train": False,
            "active_leg_idx": None,
            "wait_sec": 0,
            "badge": f"📅 Gespeicherte Fahrt: {short_date_lbl} ({dep_first_s} Uhr) · {route_short}",
            "sub": f"Datum ({trip_date.strftime('%d.%m.%Y')}) liegt in der Vergangenheit.",
            "color": "#9ca3af",
            "bg": "#181b22",
        }

    # trip_date == today
    if now_m < first_dep:
        wait_sec = max(0, int((first_dep - now_m) * 60))
        h, rem = divmod(wait_sec, 3600)
        m, s = divmod(rem, 60)
        countdown_txt = f"{h}h {m:02d}m" if h > 0 else f"{m}m {s:02d}s"
        return {
            "state": "vorbereitung",
            "is_in_train": False,
            "active_leg_idx": None,
            "wait_sec": wait_sec,
            "badge": f"📅 Nächste Fahrt: Heute ({dep_first_s} Uhr · in {countdown_txt}) · {route_short}",
            "sub": f"Ab {from_first} mit {legs[0].get('train', 'Zug')} · Live-Timer startet automatisch bei Abfahrt.",
            "color": "#ff4d5e",
            "bg": "#221115",
        }

    if now_m >= last_arr:
        return {
            "state": "vorbereitung_vergangen",
            "is_in_train": False,
            "active_leg_idx": None,
            "wait_sec": 0,
            "badge": f"📅 Fahrt heute ({dep_first_s}–{legs[-1].get('arr', '')} Uhr) beendet · {route_short}",
            "sub": "Klicke rechts auf „⚡ Fahrt jetzt starten“, falls du gerade fährst.",
            "color": "#9ca3af",
            "bg": "#181b22",
        }

    # Wir sind mitten in der Reisezeit (first_dep <= now_m < last_arr)!
    cur_cursor = first_dep
    for i, leg in enumerate(legs):
        dep_m = parse_hhmm_to_min(leg.get("dep", ""))
        arr_m = parse_hhmm_to_min(leg.get("arr", ""))
        dur = int(leg.get("duration_min") or 35)
        if dep_m is None:
            dep_m = cur_cursor
        if arr_m is None or arr_m < dep_m:
            arr_m = dep_m + dur

        if dep_m <= now_m < arr_m:
            rem_min = max(1, int(round(arr_m - now_m)))
            d_min = int(leg.get("delay_min", 0))
            d_txt = f" +{d_min}m" if d_min > 0 else ""
            return {
                "state": "im_zug",
                "is_in_train": True,
                "active_leg_idx": i,
                "wait_sec": 0,
                "badge": f"🚆 Im Zug ({leg.get('train', 'Zug')}{d_txt}): {leg.get('from_station', '')} → {leg.get('to_station', '')} (noch {rem_min} Min.)",
                "sub": f"Abschnitt {i + 1}/{len(legs)} · {leg.get('dep', '')}–{leg.get('arr', '')} Uhr",
                "color": "#4ade80",
                "bg": "#062417",
            }

        if i < len(legs) - 1:
            nxt = legs[i + 1]
            nxt_dep = parse_hhmm_to_min(nxt.get("dep", ""))
            if nxt_dep is None or nxt_dep < arr_m:
                nxt_dep = arr_m + int(leg.get("transfer_after_min", 15))
            if arr_m <= now_m < nxt_dep:
                rem_tr = max(1, int(round(nxt_dep - now_m)))
                return {
                    "state": "umstieg",
                    "is_in_train": True,
                    "active_leg_idx": i,
                    "wait_sec": 0,
                    "badge": f"☕ Umstieg in {leg.get('to_station', 'Bahnhof')} (noch {rem_tr} Min. bis {nxt.get('train', 'Anschluss')})",
                    "sub": f"Weiterfahrt um {nxt.get('dep', '')} Uhr nach {nxt.get('to_station', 'Ziel')}",
                    "color": "#fbbf24",
                    "bg": "#271705",
                }
            cur_cursor = nxt_dep

    return {
        "state": "im_zug",
        "is_in_train": True,
        "active_leg_idx": 0,
        "wait_sec": 0,
        "badge": f"🚆 Aktiv unterwegs · {route_short}",
        "sub": "Timer läuft synchron zur echten Zugverbindung.",
        "color": "#4ade80",
        "bg": "#062417",
    }


def shift_trip_to_start_now(trip):
    """
    Setzt den Abfahrtszeitpunkt der aktuellen Reise auf die jetzige Uhrzeit (JETZT),
    damit man auch bei spontanen Fahrten (z.B. Deutschlandticket ohne gebuchtes Ticket)
    sofort live & synchron im Zug starten kann.
    """
    legs = trip.get("legs", [])
    if not legs:
        return
    now = datetime.datetime.now()
    trip["date"] = now.strftime("%d.%m.%Y")
    trip["extra_pause_min"] = 0
    trip["extra_pause_after_leg"] = 0
    cur_m = now.hour * 60 + now.minute

    for i, leg in enumerate(legs):
        dur = int(leg.get("duration_min") or diff_minutes(leg.get("dep"), leg.get("arr"), 35))
        tr = int(leg.get("transfer_after_min") or (15 if i < len(legs) - 1 else 0))
        dep_s = min_to_hhmm(cur_m)
        arr_s = min_to_hhmm(cur_m + dur)
        leg["planned_dep"] = dep_s
        leg["planned_arr"] = arr_s
        leg["dep"] = dep_s
        leg["arr"] = arr_s
        leg["duration_min"] = dur
        leg["delay_min"] = 0
        cur_m = cur_m + dur + tr


def classify_train_type(train_name):
    t = (train_name or "").upper()
    if any(k in t for k in ("ICE", "IC ", "IC/", "EC ", "TGV", "RJ", "FLX", "FERN")) or re.match(r"^(ICE|IC|EC)\b", t):
        return "ICE"
    return "REGIO"


def apply_consecutive_full_train_rule(legs):
    """
    Regel: Gibt es zwei volle Zugverbindungen (Stehplatz) nacheinander,
    findet bei der ersten automatisch Pause (Nichts lernen) statt.
    Gibt die Indizes der geänderten Züge zurück.
    """
    if not legs or len(legs) < 2:
        return []
    changed = []
    for i in range(len(legs) - 1):
        if legs[i].get("mode") == "regio_memo" and legs[i + 1].get("mode") == "regio_memo":
            legs[i]["mode"] = "rest"
            changed.append(i)
    return changed


def assign_smart_leg_modes(legs):
    """
    Setzt automatisch die Lern-Modi (Sitzplatz, Stehplatz oder Pause) anhand von DB-Auslastung & Zugtyp:
    - Kurze Abschnitte (< 12 Min.) -> 'rest' (☕ Pause (Nichts lernen))
    - Hohe Auslastung (DB-Echtzeitdaten) oder enger mittlerer Regio -> 'regio_memo' (🧠 Stehplatz (Theorie))
    - Geringe Auslastung / ICE -> 'focus' (💻 Sitzplatz (Aufgaben))
    - Regel: Bei zwei vollen Zügen nacheinander pausiert man im ersten Zug ('rest')!
    """
    n = len(legs)
    for i, leg in enumerate(legs):
        ttype = classify_train_type(leg.get("train", ""))
        leg["type"] = ttype
        dur = int(leg.get("duration_min") or diff_minutes(leg.get("dep"), leg.get("arr"), 35))
        leg["duration_min"] = dur
        leg.setdefault("delay_min", 0)
        leg.setdefault("planned_dep", leg.get("dep", "09:00"))
        leg.setdefault("planned_arr", leg.get("arr", "09:45"))

        db_occ = str(leg.get("db_occupancy") or "")
        is_middle = (n >= 3 and 0 < i < n - 1) or (n == 2 and i == 1 and ttype == "REGIO")

        if dur < 12:
            leg["mode"] = "rest"
        elif "hohe" in db_occ.lower() or "voll" in db_occ.lower():
            leg["mode"] = "regio_memo"
        elif "frei" in db_occ.lower() or ttype == "ICE":
            leg["mode"] = "focus"
        elif is_middle and ttype == "REGIO":
            leg["mode"] = "regio_memo"
        else:
            leg["mode"] = "focus"

    apply_consecutive_full_train_rule(legs)
    return legs


# --------------------------------------------------------------------------
# Echtzeit-DB-Abfrage im Minutentakt (DB IRIS-TTS Live-API + Offline-Erkennung)
# --------------------------------------------------------------------------
EVA_CACHE = {}


def resolve_station_eva(station_name):
    """Löst einen Bahnhofsnamen über die offizielle DB IRIS-TTS Schnittstelle in die EVA-Nummer auf."""
    if not station_name:
        return None
    clean = station_name.strip()
    low = clean.lower()
    if low in (
        "startbahnhof", "zielbahnhof", "umsteigebahnhof 1", "umsteigebahnhof 2",
        "start", "ziel", "umstieg 1", "umstieg 2", "bahnhof", "start hbf", "ziel hbf"
    ):
        return None
    if clean in EVA_CACHE:
        return EVA_CACHE[clean]

    candidates = [clean]
    no_parens = re.sub(r"\s*\([^)]*\)", "", clean).strip()
    if no_parens and no_parens not in candidates:
        candidates.append(no_parens)
    first_part = re.split(r"[,/-]", clean)[0].strip()
    if first_part and first_part not in candidates:
        candidates.append(first_part)

    for cand in candidates:
        url = "https://iris.noncd.db.de/iris-tts/timetable/station/" + urllib.parse.quote(cand)
        req = urllib.request.Request(url, headers={"User-Agent": "EntspanntReisen/3.5"})
        try:
            with urllib.request.urlopen(req, timeout=4) as r:
                xml_data = r.read().decode("utf-8", errors="ignore")
            root = ET.fromstring(xml_data)
        except (urllib.error.HTTPError, ET.ParseError):
            continue
        st = root.find("station")
        if st is not None and st.attrib.get("eva"):
            EVA_CACHE[clean] = st.attrib["eva"]
            return st.attrib["eva"]
    return None


def parse_iris_ts(ts_str):
    if not ts_str or len(ts_str) != 10 or not ts_str.isdigit():
        return None
    return datetime.datetime(
        2000 + int(ts_str[0:2]),
        int(ts_str[2:4]),
        int(ts_str[4:6]),
        int(ts_str[6:8]),
        int(ts_str[8:10]),
    )


def normalize_train_tokens(train_str):
    s = (train_str or "").upper().strip()
    paren_m = re.search(r"\((\d+)\)", s)
    extra_num = paren_m.group(1) if paren_m else ""
    s_clean = re.sub(r"\([^)]*\)", "", s).strip()
    m = re.match(r"^([A-Z]+)\s*(\d+[A-Z]?)", s_clean)
    if m:
        return m.group(1), m.group(2), extra_num
    return s_clean, "", extra_num


def detect_db_auslastung(data_dict, raw_text=""):
    """
    Liest aus DB-API-Daten oder Seitentexten ab, ob ein Zug voll (hohe Auslastung)
    oder frei (Sitzplätze verfügbar) ist.
    """
    if not isinstance(data_dict, dict):
        data_dict = {}

    meldungen = data_dict.get("auslastungsmeldungen")
    if isinstance(meldungen, list):
        stufen = []
        for m in meldungen:
            if isinstance(m, dict) and m.get("stufe") is not None:
                if m.get("klasse") == "KLASSE_2" or not m.get("klasse"):
                    stufen.insert(0, m.get("stufe"))
                else:
                    stufen.append(m.get("stufe"))
        for st in stufen:
            if str(st) in ("3", "4", "99"):
                return "Hohe Auslastung"
            if str(st) in ("1", "2"):
                return "Sitzplätze frei"

    candidates = [
        data_dict.get("auslastung"),
        data_dict.get("auslastungsgrad"),
        data_dict.get("auslastungsStufe"),
        data_dict.get("auslastungsmeldung"),
        data_dict.get("auslastung2Klasse"),
        data_dict.get("auslastung1Klasse"),
        data_dict.get("occupancy"),
        data_dict.get("loadFactor"),
        data_dict.get("auslastungswarnung"),
    ]
    vm = data_dict.get("verkehrsmittel") or {}
    if isinstance(vm, dict):
        candidates.extend([vm.get("auslastung"), vm.get("auslastungsgrad"), vm.get("auslastungsStufe")])

    for c in candidates:
        if c is None:
            continue
        c_str = str(c).upper().strip()
        if any(h in c_str for h in ("HOCH", "SEHR_HOCH", "STUFE_3", "STUFE_4", "HIGH", "MAX", "VOLL", "UEBERBESETZT", "ÜBERBESETZT")) or c_str in ("3", "4"):
            return "Hohe Auslastung"
        if any(low in c_str for low in ("GERING", "NIEDRIG", "MITTEL", "STUFE_1", "STUFE_2", "LOW", "MEDIUM", "FREI")) or c_str in ("1", "2"):
            return "Sitzplätze frei"

    if raw_text:
        low_txt = raw_text.lower()
        if any(k in low_txt for k in ("sehr hohe auslastung", "hohe auslastung", "außergewöhnlich hohe auslastung", "zug ist voll", "überbesetzung")):
            return "Hohe Auslastung"
        if any(k in low_txt for k in ("geringe auslastung", "mittlere auslastung", "viele freie plätze")):
            return "Sitzplätze frei"

    return ""


def query_leg_live_delay_iris(station_name, planned_hhmm, trip_date_str, train_name, is_arrival=False):
    """
    Fragt für einen Bahnhof (station_name), die geplante Uhrzeit (planned_hhmm) und den Zugnamen
    die aktuellen Echtzeit-Daten (Verspätung in Minuten + Ausfall-Status) von DB IRIS-TTS ab.
    """
    eva = resolve_station_eva(station_name)
    if not eva:
        return None
    dt_date = parse_trip_date(trip_date_str)
    hm = re.match(r"^(\d{1,2}):(\d{2})$", (planned_hhmm or "").strip())
    if not hm:
        return None
    planned_dt = datetime.datetime(dt_date.year, dt_date.month, dt_date.day, int(hm.group(1)), int(hm.group(2)))
    yymmdd = planned_dt.strftime("%y%m%d")
    hh = planned_dt.strftime("%H")

    url_plan = f"https://iris.noncd.db.de/iris-tts/timetable/plan/{eva}/{yymmdd}/{hh}"
    url_fchg = f"https://iris.noncd.db.de/iris-tts/timetable/fchg/{eva}"

    try:
        req_p = urllib.request.Request(url_plan, headers={"User-Agent": "EntspanntReisen/3.5"})
        with urllib.request.urlopen(req_p, timeout=4) as r:
            plan_root = ET.fromstring(r.read().decode("utf-8", errors="ignore"))
    except urllib.error.HTTPError:
        # Plan-Stunde evtl. noch nicht im IRIS-Fenster
        return None

    req_f = urllib.request.Request(url_fchg, headers={"User-Agent": "EntspanntReisen/3.5"})
    with urllib.request.urlopen(req_f, timeout=4) as r:
        fchg_root = ET.fromstring(r.read().decode("utf-8", errors="ignore"))

    want_cat, want_num, extra_num = normalize_train_tokens(train_name)
    tag_name = "ar" if is_arrival else "dp"

    best_sid = None
    best_pt_dt = None
    best_score = -1

    for s in plan_root.findall("s"):
        sid = s.attrib.get("id")
        tl = s.find("tl")
        ev = s.find(tag_name)
        if ev is None:
            continue
        pt_dt = parse_iris_ts(ev.attrib.get("pt"))
        if pt_dt is None:
            continue
        diff_min = abs((pt_dt - planned_dt).total_seconds()) / 60.0
        if diff_min > 20:
            continue

        cat = (tl.attrib.get("c", "") if tl is not None else "").upper()
        num = (tl.attrib.get("n", "") if tl is not None else "").upper()
        line = (ev.attrib.get("l", "") or "").upper()

        score = 0
        if diff_min == 0:
            score += 50
        elif diff_min <= 2:
            score += 30
        elif diff_min <= 10:
            score += 10

        if extra_num and extra_num == num:
            score += 120
        elif want_num and (want_num == num or want_num == line or f"{want_cat}{want_num}" == f"{cat}{line}"):
            score += 100
        elif want_cat and want_cat == cat:
            score += 40

        if score > best_score:
            best_score = score
            best_sid = sid
            best_pt_dt = pt_dt

    if not best_sid or best_score < 30:
        return None

    delay_min = 0
    cancelled = False
    occ_hint = ""
    for s in fchg_root.findall("s"):
        if s.attrib.get("id") == best_sid:
            ev = s.find(tag_name)
            if ev is not None:
                if ev.attrib.get("cs") == "c":
                    cancelled = True
                ct_dt = parse_iris_ts(ev.attrib.get("ct"))
                if ct_dt is not None and best_pt_dt is not None:
                    delay_min = max(0, int(round((ct_dt - best_pt_dt).total_seconds() / 60.0)))
            for m in s.findall("m"):
                m_txt = (m.text or m.attrib.get("cat") or m.attrib.get("head") or "").lower()
                if any(k in m_txt for k in ("hohe auslastung", "überbesetzung", "aussergewöhnlich hoch", "außergewöhnlich hoch", "zug ist voll")):
                    occ_hint = "Hohe Auslastung"
                    break
            break

    return {"delay_min": delay_min, "cancelled": cancelled, "occupancy": occ_hint, "matched_sid": best_sid, "score": best_score}


def _sync_transfer_before(trip, leg_index):
    """Passt die Umstiegszeit VOR diesem Zug an seine neue Abfahrt an (außer bei Extra-Pause nach verpasstem Anschluss)."""
    legs = trip.get("legs", [])
    if leg_index <= 0 or leg_index >= len(legs):
        return
    if int(trip.get("extra_pause_min") or 0) > 0 and trip.get("extra_pause_after_leg") == leg_index - 1:
        return
    prev = legs[leg_index - 1]
    prev["transfer_after_min"] = diff_minutes(prev.get("arr"), legs[leg_index].get("dep"), prev.get("transfer_after_min") or 12)


def set_leg_live_delay(trip, leg_index, dep_delay_min, arr_delay_min, cancelled=False):
    """
    Setzt die exakte Live-Verspätung eines Zugabschnitts relativ zu planned_dep / planned_arr.
    Prüft automatisch, ob ein Anschluss (< 3 Min. Umstiegszeit) oder Zugausfall vorliegt,
    und rechnet dann automatisch +30 Min. als Extra-Pause hinzu.
    Gibt (changed: bool, missed_conn: bool, message: str) zurück.
    """
    legs = trip.get("legs", [])
    if not (0 <= leg_index < len(legs)):
        return False, False, ""

    leg = legs[leg_index]
    ensure_planned_times(trip)
    old_dep = leg.get("dep")
    old_arr = leg.get("arr")
    old_delay = int(leg.get("delay_min", 0))

    p_dep = parse_hhmm_to_min(leg.get("planned_dep") or leg.get("dep", "09:00")) or 540
    p_arr = parse_hhmm_to_min(leg.get("planned_arr") or leg.get("arr", "09:45")) or 585

    new_dep_m = p_dep + int(dep_delay_min)
    new_arr_m = p_arr + int(arr_delay_min)
    new_delay = max(int(dep_delay_min), int(arr_delay_min))

    leg["dep"] = min_to_hhmm(new_dep_m)
    leg["arr"] = min_to_hhmm(new_arr_m)
    leg["delay_min"] = new_delay
    leg["duration_min"] = diff_minutes(leg["dep"], leg["arr"], leg.get("duration_min", 35))
    _sync_transfer_before(trip, leg_index)

    changed = (leg["dep"] != old_dep) or (leg["arr"] != old_arr) or (new_delay != old_delay) or cancelled

    if cancelled:
        if leg.get("live_cancelled"):
            return False, False, ""
        leg["live_cancelled"] = True
        msg = trigger_missed_connection_plus_30(trip, leg_index)
        return True, True, f"🚨 LIVE-DB-MELDUNG: {leg.get('train', 'Zug')} fällt aus! {msg}"

    if leg_index < len(legs) - 1:
        next_leg = legs[leg_index + 1]
        next_dep_m = parse_hhmm_to_min(next_leg.get("dep", "10:00")) or (new_arr_m + 15)
        rem_transfer = next_dep_m - new_arr_m
        if rem_transfer < -720:
            rem_transfer += 1440

        if rem_transfer < 3:
            trip["extra_pause_min"] = MISSED_CONNECTION_PENALTY_MIN
            trip["extra_pause_after_leg"] = leg_index
            leg["transfer_after_min"] = MISSED_CONNECTION_PENALTY_MIN
            shift = (new_arr_m + MISSED_CONNECTION_PENALTY_MIN) - next_dep_m
            for j in range(leg_index + 1, len(legs)):
                jd = parse_hhmm_to_min(legs[j].get("dep", "10:00")) or 600
                ja = parse_hhmm_to_min(legs[j].get("arr", "10:45")) or 645
                legs[j]["dep"] = min_to_hhmm(jd + shift)
                legs[j]["arr"] = min_to_hhmm(ja + shift)
            return True, True, (
                f"⚠️ LIVE-DB-UPDATE: {leg.get('train', 'Zug')} hat +{new_delay} Min. Verspätung — "
                f"Anschluss in {leg.get('to_station', 'Bahnhof')} nicht mehr erreichbar! "
                f"Automatisch +{MISSED_CONNECTION_PENALTY_MIN} Min. Extra-Pause eingerechnet."
            )
        else:
            leg["transfer_after_min"] = rem_transfer
            if changed:
                return True, False, (
                    f"🌐 Live-DB-Update: {leg.get('train', 'Zug')} jetzt mit +{new_delay} Min. "
                    f"(Ankunft {leg['arr']} Uhr · Umstieg {rem_transfer} Min.)."
                )
    elif changed:
        return True, False, f"🌐 Live-DB-Update: {leg.get('train', 'Zug')} jetzt mit +{new_delay} Min. (Ankunft {leg['arr']} Uhr)."

    return False, False, ""


def poll_live_trip_delays(trip):
    """
    Wird jede Minute (alle 60 Sekunden) im Hintergrund ausgeführt:
    1. Prüft die Internetverbindung zur DB-Echtzeitschnittstelle (iris.noncd.db.de).
    2. Falls OFFLINE -> gibt online=False zurück (App schaltet Timer automatisch auf asynchron + manuelle Eingabe).
    3. Falls ONLINE  -> prüft für alle Zugabschnitte die aktuelle Echtzeit-Verspätung und aktualisiert den Zeitplan.
    """
    try:
        ping_req = urllib.request.Request(
            "https://iris.noncd.db.de/iris-tts/timetable/station/8000244",
            headers={"User-Agent": "EntspanntReisen/3.5"},
        )
        with urllib.request.urlopen(ping_req, timeout=4) as r:
            _ = r.read(64)
    except Exception:
        return {
            "online": False,
            "updated": False,
            "matched_count": 0,
            "messages": [],
            "summary": "📡 Offline (Kein Internet) – Timer läuft asynchron weiter · Verspätung manuell eintragbar",
        }

    ensure_planned_times(trip)
    legs = trip.get("legs", [])
    trip_date_str = trip.get("date", datetime.date.today().strftime("%d.%m.%Y"))
    messages = []
    updated_any = False
    matched_count = 0
    max_delay = 0

    for i, leg in enumerate(legs):
        # Nach einem verpassten Anschluss / Ausfall fährst du nicht mehr mit den geplanten Folgezügen
        if int(trip.get("extra_pause_min") or 0) > 0 and i > int(trip.get("extra_pause_after_leg") or 0):
            break
        try:
            dep_res = query_leg_live_delay_iris(
                leg.get("from_station", ""),
                leg.get("planned_dep", leg.get("dep", "")),
                trip_date_str,
                leg.get("train", ""),
                is_arrival=False,
            )
        except Exception:
            dep_res = None

        try:
            arr_res = query_leg_live_delay_iris(
                leg.get("to_station", ""),
                leg.get("planned_arr", leg.get("arr", "")),
                trip_date_str,
                leg.get("train", ""),
                is_arrival=True,
            )
        except Exception:
            arr_res = None

        if dep_res or arr_res:
            matched_count += 1
            dep_d = dep_res["delay_min"] if dep_res else (arr_res["delay_min"] if arr_res else 0)
            arr_d = arr_res["delay_min"] if arr_res else dep_d
            is_canc = bool((dep_res and dep_res.get("cancelled")) or (arr_res and arr_res.get("cancelled")))
            max_delay = max(max_delay, dep_d, arr_d)
            
            # DB-Auslastung aus Live-Meldungen übernehmen
            live_occ = (dep_res.get("occupancy") if dep_res else None) or (arr_res.get("occupancy") if arr_res else None)
            if live_occ:
                if leg.get("db_occupancy") != live_occ:
                    leg["db_occupancy"] = live_occ
                    if live_occ == "Hohe Auslastung":
                        leg["mode"] = "regio_memo"
                        apply_consecutive_full_train_rule(legs)
                    updated_any = True
                    messages.append(f"👥 Live-DB-Info: {leg.get('train', 'Zug')} meldet {live_occ}.")

            chg, missed, msg = set_leg_live_delay(trip, i, dep_d, arr_d, cancelled=is_canc)
            if chg:
                updated_any = True
                if msg:
                    messages.append(msg)

    now_str = datetime.datetime.now().strftime("%H:%M:%S")
    if matched_count > 0:
        if max_delay == 0:
            summary = f"🌐 Live-DB-Sync aktiv ({now_str} Uhr): Alle überwachten Züge pünktlich (±0 Min.)"
        else:
            summary = f"🌐 Live-DB-Sync aktiv ({now_str} Uhr): Echtzeit-Verspätung (+{max_delay} Min.) automatisch synchronisiert"
    else:
        summary = f"🌐 Live-DB-Sync aktiv (Check {now_str} Uhr · Minutentakt läuft – DB-Echtzeitdaten ab ~2h vor Abfahrt verfügbar)"

    return {
        "online": True,
        "updated": updated_any,
        "matched_count": matched_count,
        "messages": messages,
        "summary": summary,
    }


def apply_delay_to_trip(trip, leg_index, add_delay_min):
    """
    Manuelles Hinzufügen einer Verspätung (+5, +10, +15, +25 Min.) – besonders für den Offline-Modus
    oder wenn man unterwegs selbst eine Durchsage im Zug hört.
    """
    legs = trip.get("legs", [])
    if not (0 <= leg_index < len(legs)):
        return False, "Ungültiger Abschnitt."

    ensure_planned_times(trip)
    leg = legs[leg_index]
    leg["delay_min"] = int(leg.get("delay_min", 0)) + int(add_delay_min)
    dep_m = parse_hhmm_to_min(leg.get("dep", "09:00")) or 540
    arr_m = parse_hhmm_to_min(leg.get("arr", "09:45")) or (dep_m + int(leg.get("duration_min", 45)))
    new_dep_m = dep_m + int(add_delay_min)
    new_arr_m = arr_m + int(add_delay_min)
    leg["dep"] = min_to_hhmm(new_dep_m)
    leg["arr"] = min_to_hhmm(new_arr_m)
    _sync_transfer_before(trip, leg_index)

    if leg_index < len(legs) - 1:
        next_leg = legs[leg_index + 1]
        next_dep_m = parse_hhmm_to_min(next_leg.get("dep", "10:00")) or (new_arr_m + 15)
        remaining_transfer = next_dep_m - new_arr_m
        if remaining_transfer < -720:
            remaining_transfer += 1440

        if remaining_transfer < 3:
            trip["extra_pause_min"] = MISSED_CONNECTION_PENALTY_MIN
            trip["extra_pause_after_leg"] = leg_index
            leg["transfer_after_min"] = MISSED_CONNECTION_PENALTY_MIN
            shift = (new_arr_m + MISSED_CONNECTION_PENALTY_MIN) - next_dep_m
            for j in range(leg_index + 1, len(legs)):
                jd = parse_hhmm_to_min(legs[j].get("dep", "10:00")) or 600
                ja = parse_hhmm_to_min(legs[j].get("arr", "10:45")) or 645
                legs[j]["dep"] = min_to_hhmm(jd + shift)
                legs[j]["arr"] = min_to_hhmm(ja + shift)
            return True, (
                f"⚠️ Anschluss in {leg.get('to_station', 'Umsteigebahnhof')} durch +{add_delay_min} Min. Verspätung "
                f"nicht mehr möglich! Es wurden automatisch +{MISSED_CONNECTION_PENALTY_MIN} Min. als Pause hinzugerechnet."
            )
        else:
            leg["transfer_after_min"] = remaining_transfer
            return False, (
                f"⏱️ +{add_delay_min} Min. Verspätung eingetragen. Umstieg in {leg.get('to_station', '')} "
                f"beträgt jetzt {remaining_transfer} Min."
            )
    return False, f"⏱️ +{add_delay_min} Min. Verspätung für {leg.get('train', 'Zug')} eingetragen (Ankunft neu: {leg['arr']})."


def trigger_missed_connection_plus_30(trip, leg_index=None):
    legs = trip.get("legs", [])
    if not legs:
        return "Keine Zugabschnitte vorhanden."

    if leg_index is None:
        now_m = now_minutes_of_day()
        leg_index = 0
        for i, l in enumerate(legs[:-1]):
            arr_m = parse_hhmm_to_min(l.get("arr", ""))
            if arr_m is not None and now_m <= arr_m + 30:
                leg_index = i
                break

    leg = legs[leg_index]
    arr_m = parse_hhmm_to_min(leg.get("arr", "10:00")) or int(now_minutes_of_day())
    leg["transfer_after_min"] = int(leg.get("transfer_after_min", 0)) + MISSED_CONNECTION_PENALTY_MIN
    trip["extra_pause_min"] = int(trip.get("extra_pause_min", 0)) + MISSED_CONNECTION_PENALTY_MIN
    trip["extra_pause_after_leg"] = leg_index

    for j in range(leg_index + 1, len(legs)):
        jd = parse_hhmm_to_min(legs[j].get("dep", "10:00")) or (arr_m + 30)
        ja = parse_hhmm_to_min(legs[j].get("arr", "10:45")) or (jd + 45)
        legs[j]["dep"] = min_to_hhmm(jd + MISSED_CONNECTION_PENALTY_MIN)
        legs[j]["arr"] = min_to_hhmm(ja + MISSED_CONNECTION_PENALTY_MIN)

    return (
        f"⚠️ Verbindung nicht mehr möglich: +{MISSED_CONNECTION_PENALTY_MIN} Min. Extra-Pause nach "
        f"„{leg.get('train', 'Zug')}“ hinzugefügt und nachfolgende Zeiten verschoben!"
    )


def get_elapsed_completed_groups(trip, active_jobs, current_min=None):
    """
    Prüft anhand der aktuellen Uhrzeit (current_min), welche Lernblöcke in der
    vergangenen Fahrtzeit bereits abgeschlossen wurden.
    """
    if current_min is None:
        current_min = now_minutes_of_day()
    already_done = set(trip.get("completed_group_ids") or []) | set(trip.get("progress_done_ids") or [])
    blocks, _ = build_study_schedule(trip, active_jobs, ignore_completed=False)
    for b in blocks:
        end_m = b.get("end_min")
        gid = b.get("group_id")
        if gid and end_m is not None and current_min >= end_m:
            already_done.add(gid)
    return list(already_done)


LAPTOP_PRIORITY = ["pi1", "pp1_projekt", "pp1_grosse_uebung", "fgdi", "wifo", "marketing"]


def _pick_memo_priority_job(jobs_list):
    """
    Wählt für volle Züge ('regio_memo' / Nur Auswendiglernen) das Modul nach der gewünschten Hierarchie:
    1. Wirtschaftsinformatik ('wifo')
    2. Marketing ('marketing')
    3. Formale Grundlagen der Informatik ('fgdi')
    (nur wenn das jeweilige Modul angehakt/aktiv ist; sonst Fallback auf erstes aktives Modul).
    """
    if not jobs_list:
        return None
    for prio_id in MEMO_PRIORITY:
        for pair in jobs_list:
            if pair[0]["id"] == prio_id:
                return pair
    return None


def _slot_max_modules(net_minutes, mode="focus"):
    """
    Berechnet realistisch, wie viele Module in einem Sitzplatz-Zugabschnitt ('focus'/'light')
    sinnvoll bearbeitet werden können:
    - Unter 18 Min.: 0 Module (zu kurz für ein komplettes Übungsblatt -> Puffer/Wiederholung)
    - 18 bis 69 Min.: 1 Modul (volle Konzentration auf 1 Blatt statt hektisches Springen)
    - 70 bis 114 Min.: max. 2 Module (z.B. längere ICE-Fahrt)
    - Ab 115 Min.: max(2, net_minutes // 45) Module
    """
    if mode != "focus" or net_minutes < 18:
        return 0
    if net_minutes < 70:
        return 1
    if net_minutes < 115:
        return 2
    return max(2, int(net_minutes // 45))


def _select_laptop_jobs(candidates, max_count):
    """
    Wählt aus den verbleibenden aktiven Modulen automatisch nur so viele aus, wie für die Fahrtzeit
    und Sitzplatz-Verfügbarkeit sinnvoll sind (`max_count`).
    - Wenn sowohl 'pp1_projekt' als auch 'pp1_grosse_uebung' aktiv sind und Platz knapp ist,
      wird zunächst nur eins der beiden Programmierpraktikum-Blätter eingeplant, damit andere Fächer
      nicht verdrängt werden bzw. bei Zeitmangel nur eins von beiden vorbereitet wird.
    """
    if max_count <= 0 or not candidates:
        return []
    if len(candidates) <= max_count:
        return list(candidates)

    by_id = {g["id"]: (g, it) for g, it in candidates}
    primary = []
    deferred_pp1 = []

    has_both_pp1 = ("pp1_projekt" in by_id and "pp1_grosse_uebung" in by_id)
    for pid in LAPTOP_PRIORITY:
        if pid in by_id:
            if has_both_pp1 and pid == "pp1_grosse_uebung":
                deferred_pp1.append(by_id[pid])
            else:
                primary.append(by_id[pid])

    for pair in candidates:
        if pair not in primary and pair not in deferred_pp1:
            primary.append(pair)

    ordered = primary + deferred_pp1
    chosen_set = {g["id"] for g, _ in ordered[:max_count]}
    # Reihenfolge entsprechend der ursprünglichen Modul-Liste beibehalten
    return [(g, it) for g, it in candidates if g["id"] in chosen_set]


def get_skipped_jobs_info(trip, active_jobs, job_allocations):
    """
    Ermittelt automatisch, welche angehakten Module wegen vollen Zügen oder zu knapper Fahrtzeit
    auf dieser Reise NICHT vorbereitet werden, und erzeugt einen kompakten Hinweis-Text.
    """
    done_ids = set((trip or {}).get("completed_group_ids") or [])
    remaining = [(g, it) for (g, it) in active_jobs if g["id"] not in done_ids]
    if not remaining and active_jobs:
        remaining = list(active_jobs)

    alloc_map = job_allocations or {}
    skipped = [(g, it) for (g, it) in remaining if g["id"] not in alloc_map]
    if not skipped:
        return [], "", ""

    legs = (trip or {}).get("legs") or []
    n_full = sum(1 for l in legs if l.get("mode") == "regio_memo")
    n_rest = sum(1 for l in legs if l.get("mode") == "rest")

    if n_full > 0 and n_rest > 0:
        reason = f"{n_full}× voller Zug & {n_rest}× Pause"
    elif n_full >= 2:
        reason = f"{n_full} Züge voll – wenig Sitzplatz-Zeit"
    elif n_full == 1:
        reason = "1 Zug voll & Zeitbudget begrenzt"
    elif n_rest > 0:
        reason = f"{n_rest}× Zug-Pause aktiv"
    else:
        reason = "Fahrtzeit zu kurz für alle Module"

    skipped_names = [f"{g['icon']} {short_module_name(g['module'])} ({short_item_name(it['name'])})" for g, it in skipped]
    kept_count = max(0, len(remaining) - len(skipped))
    short_hint = (
        f"💡 Auto-Auswahl ({reason}): Nur {kept_count}/{len(remaining)} Module sinnvoll machbar — "
        f"nicht behandelt: {', '.join(skipped_names)}"
    )
    detail_tooltip = (
        f"Intelligente Zeit- & Zug-Optimierung:\n"
        f"Bedingung: {reason}.\n"
        f"Damit du pro Modul genug echte Lernzeit hast (statt alles in 15-Minuten-Happen zu quetschen),\n"
        f"bereitet die App automatisch nur {kept_count} von {len(remaining)} Modulen vor.\n\n"
        f"Auf dieser Fahrt ausgelassen:\n• " + "\n• ".join(f"{g['module']} – {it['name']}" for g, it in skipped)
    )
    return skipped, short_hint, detail_tooltip


def build_study_schedule(trip, active_jobs, ignore_completed=False):
    """
    Erstellt den minutengenauen Lern-Zeitplan:
    • Prüft automatisch anhand von Zug-Auslastung (voll/Pause) und Netto-Fahrtzeit, wie viele Module
      überhaupt sinnvoll gelernt werden können, und lässt überzählige Module automatisch weg!
    • Macht bei jeder Phase glasklar, welcher Zug es ist, genau von wo nach wo er fährt und die Uhrzeit!
    • Filtert Aufgaben heraus, die in der vergangenen Fahrtzeit bereits erledigt wurden.
    • Umstiegszeiten < 25 Min. = 100 % Lernpause ☕
    • Umstiegszeiten >= 25 Min. = 15 Min. Umstiegs-Pause ☕ + restliche Zeit als Lernblock 📖!
    • Volle / mittlere Regio-Verbindung ('regio_memo') = Priorisiert 1. Wifo, 2. Marketing, 3. FGdI fürs Auswendiglernen am Handy!
    """
    legs = trip.get("legs", [])
    if not legs:
        legs = DEFAULT_TRIP["legs"]

    done_ids = set() if ignore_completed else set(trip.get("completed_group_ids") or [])
    remaining_jobs = [(g, it) for (g, it) in active_jobs if g["id"] not in done_ids]
    if not remaining_jobs and active_jobs:
        remaining_jobs = list(active_jobs)
    else:
        remaining_jobs = list(remaining_jobs)

    schedule_blocks = []
    job_allocations = {}
    phase_counter = 1

    # --- FALL 1: Durchgehende 1-Zug-Fahrt (z.B. 1x ICE oder 1x Regio) ---
    if len(legs) == 1:
        leg = legs[0]
        tname = leg.get("train", "ICE")
        from_s = leg.get("from_station", "Start")
        to_s = leg.get("to_station", "Ziel")
        dep_s = leg.get("dep", "10:00")
        arr_s = leg.get("arr", "11:30")
        dur = int(leg.get("duration_min") or diff_minutes(dep_s, arr_s, 90))
        dep_min = parse_hhmm_to_min(dep_s) or 600
        mode = leg.get("mode", "focus")
        train_route_hdr = f"🚆 Zug 1/1 ({tname}): {from_s} (ab {dep_s} Uhr) ➔ {to_s} (an {arr_s} Uhr)"

        if mode in ("regio_memo", "rest"):
            tw = f"{min_to_hhmm(dep_min)} – {min_to_hhmm(dep_min + dur)}"
            is_memo = (mode == "regio_memo")
            memo_pair = _pick_memo_priority_job(remaining_jobs) if is_memo else None
            if is_memo and memo_pair:
                m_grp, m_itm = memo_pair
                s_mod = short_module_name(m_grp["module"])
                s_itm = short_item_name(m_itm["name"])
                job_allocations[m_grp["id"]] = {
                    "minutes": dur,
                    "leg_title": f"Zug 1/1 ({tname}: {from_s} → {to_s})",
                    "train_short": f"📱 {tname}",
                    "mode": "regio_memo",
                    "is_phone_memo": True,
                    "time_window": tw,
                    "train_type": leg.get("type", "REGIO"),
                    "leg_indices": [0],
                }
                chips_1 = [f"📱 {m_grp['icon']} {s_mod} ({s_itm}) · {dur}m (Handy / Auswendig)"]
                title_1 = f"Zug 1/1 ({tname}): {from_s} → {to_s} ({dur} Min. · 📱 {s_mod})"
                gid_1 = m_grp["id"]
                adv_1 = f"Auswendiglernen am Handy (OneDrive): {m_grp['module']} ({m_itm['name']})"
            else:
                chips_1 = ["🧠 Stehplatz / Voll · Nur Theorie (Kein Laptop)" if is_memo else "☕ Pause (Nichts lernen)"]
                title_1 = f"Zug 1/1 ({tname}): {from_s} → {to_s} ({dur} Min. {'Nur Theorie' if is_memo else 'Pause'})"
                gid_1 = None
                adv_1 = "Regio-Spickkarten zum Einprägen nutzen (kein Laptop)." if is_memo else "Komplett lernfreie Fahrt."

            schedule_blocks.append({
                "kind": "regio_memo" if is_memo else "rest",
                "phase_num": phase_counter,
                "leg_index": 0,
                "train_header": train_route_hdr,
                "start_min": dep_min,
                "end_min": dep_min + dur,
                "time": tw,
                "duration_min": dur,
                "title": title_1,
                "subtitle": f"{tw} Uhr · {LEG_MODE_LABELS.get(mode)}",
                "advice": adv_1,
                "chips": chips_1,
                "mode": mode,
                "group_id": gid_1,
            })
            return schedule_blocks, job_allocations

        buffer_start = 5 if dur > 25 else 2
        buffer_end = 5 if dur > 25 else 2
        usable = max(15, dur - buffer_start - buffer_end)

        cur_t = dep_min
        schedule_blocks.append({
            "kind": "boarding",
            "phase_num": phase_counter,
            "leg_index": 0,
            "train_header": train_route_hdr,
            "start_min": cur_t,
            "end_min": cur_t + buffer_start,
            "time": f"{min_to_hhmm(cur_t)} – {min_to_hhmm(cur_t + buffer_start)}",
            "duration_min": buffer_start,
            "title": f"Zug 1/1 ({tname}): Einsteigen in {from_s} ({buffer_start} Min.)",
            "subtitle": f"{from_s} ({dep_s}) → {to_s} ({arr_s})",
            "advice": "Sitzplatz einrichten & PDF öffnen.",
            "chips": [f"🚆 Einsteigen in {from_s} · {buffer_start}m"],
            "mode": "rest",
        })
        phase_counter += 1
        cur_t += buffer_start

        max_mods_1 = max(1, _slot_max_modules(usable, mode))
        selected_jobs_1 = _select_laptop_jobs(remaining_jobs, max_mods_1)

        num_jobs = max(1, len(selected_jobs_1))
        break_between = 10 if (num_jobs > 1 and usable >= num_jobs * 25) else 5 if num_jobs > 1 else 0
        total_breaks = break_between * max(0, num_jobs - 1)
        per_job_min = max(12, int((usable - total_breaks) / num_jobs))

        for idx, (grp, item) in enumerate(selected_jobs_1):
            end_t = cur_t + per_job_min
            tw = f"{min_to_hhmm(cur_t)} – {min_to_hhmm(end_t)}"
            s_mod = short_module_name(grp["module"])
            s_itm = short_item_name(item["name"])
            job_allocations[grp["id"]] = {
                "minutes": per_job_min,
                "leg_title": f"Zug 1/1 ({tname}: {from_s} → {to_s})",
                "train_short": tname,
                "mode": mode,
                "time_window": tw,
                "train_type": leg.get("type", "ICE"),
                "leg_indices": [0],
            }
            schedule_blocks.append({
                "kind": "study",
                "phase_num": phase_counter,
                "leg_index": 0,
                "train_header": train_route_hdr,
                "start_min": cur_t,
                "end_min": end_t,
                "time": tw,
                "duration_min": per_job_min,
                "title": f"Zug 1/1 ({tname}): {from_s} → {to_s} ({per_job_min} Min. Netto-Lernzeit)",
                "subtitle": f"{tw} Uhr · {grp['icon']} {s_mod} ({s_itm})",
                "advice": f"{grp['icon']} {s_mod} ({s_itm}) · {per_job_min}m",
                "chips": [f"{grp['icon']} {s_mod} ({s_itm}) · {per_job_min}m"],
                "mode": mode,
                "group_id": grp["id"],
            })
            phase_counter += 1
            cur_t = end_t
            if idx < num_jobs - 1 and break_between > 0:
                schedule_blocks.append({
                    "kind": "break",
                    "phase_num": phase_counter,
                    "leg_index": 0,
                    "train_header": train_route_hdr,
                    "start_min": cur_t,
                    "end_min": cur_t + break_between,
                    "time": f"{min_to_hhmm(cur_t)} – {min_to_hhmm(cur_t + break_between)}",
                    "duration_min": break_between,
                    "title": f"☕ Kurze Pause im {tname} ({break_between} Min.)",
                    "subtitle": f"{min_to_hhmm(cur_t)} – {min_to_hhmm(cur_t + break_between)} Uhr",
                    "advice": "Kurze Erholung vor dem nächsten Modul.",
                    "chips": [f"☕ Pause am Sitzplatz · {break_between}m"],
                    "mode": "rest",
                })
                phase_counter += 1
                cur_t += break_between

        if trip.get("extra_pause_min", 0) > 0:
            ep = int(trip["extra_pause_min"])
            schedule_blocks.append({
                "kind": "transfer_break",
                "phase_num": phase_counter,
                "leg_index": 0,
                "train_header": train_route_hdr,
                "start_min": cur_t,
                "end_min": cur_t + ep,
                "time": f"{min_to_hhmm(cur_t)} – {min_to_hhmm(cur_t + ep)}",
                "duration_min": ep,
                "title": f"⚠️ Verspätungs-Pause (+{ep} Min.)",
                "subtitle": "Automatisch hinzugerechnete Pausenzeit",
                "advice": "Entspannt bleiben – kein Lernstress.",
                "chips": [f"⚠️ Extra-Pause · +{ep}m"],
                "mode": "rest",
            })
            phase_counter += 1
            cur_t += ep

        end_final = max(cur_t + 2, dep_min + dur)
        schedule_blocks.append({
            "kind": "alighting",
            "phase_num": phase_counter,
            "leg_index": 0,
            "train_header": train_route_hdr,
            "start_min": cur_t,
            "end_min": end_final,
            "time": f"{min_to_hhmm(cur_t)} – {min_to_hhmm(end_final)}",
            "duration_min": end_final - cur_t,
            "title": f"🎒 Ankunft in {to_s} ({arr_s} Uhr)",
            "subtitle": f"Zug 1/1 ({tname}) · Zusammenpacken",
            "advice": "Laptop rechtzeitig einpacken.",
            "chips": [f"🎒 Aussteigen in {to_s} · {end_final - cur_t}m"],
            "mode": "rest",
        })
        return schedule_blocks, job_allocations

    # --- FALL 2: Mehrere Zugabschnitte (z.B. 2–3 Züge mit Umstiegen) ---
    # 1. Für 'regio_memo'-Züge (Stehplatz/Voll) genau 1 priorisiertes Auswendiglern-Modul reservieren (1. Wifo, 2. Marketing, 3. FGdI),
    #    damit aufs Handy genau 1 klares Auswendiglern-PDF geladen wird und kein Modul-Chaos im vollen Zug entsteht.
    memo_leg_assignments = {}
    laptop_candidates = list(remaining_jobs)
    has_regio_memo_leg = any(leg.get("mode", "focus") == "regio_memo" for leg in legs)
    chosen_memo = _pick_memo_priority_job(remaining_jobs) if has_regio_memo_leg else None

    if chosen_memo:
        for i, leg in enumerate(legs):
            if leg.get("mode", "focus") == "regio_memo":
                memo_leg_assignments[i] = chosen_memo
        if chosen_memo in laptop_candidates:
            laptop_candidates.remove(chosen_memo)

    # 2. Verfügbare Sitzplatz-/Laptop-Slots und deren realistische Modul-Kapazität ermitteln
    study_slots = []
    for i, leg in enumerate(legs):
        dur = int(leg.get("duration_min") or diff_minutes(leg.get("dep"), leg.get("arr"), 35))
        mode_i = leg.get("mode", "focus")
        if mode_i == "focus":
            net_i = max(10, dur - (5 if dur >= 25 else 3))
            cap_i = _slot_max_modules(net_i, mode_i)
            if cap_i > 0:
                study_slots.append(("leg", i, net_i, cap_i))

        if i < len(legs) - 1:
            tr_min = int(leg.get("transfer_after_min") or diff_minutes(leg.get("arr"), legs[i + 1].get("dep"), 12))
            is_penalty_pause = (trip.get("extra_pause_min", 0) > 0 and trip.get("extra_pause_after_leg") == i)
            if tr_min >= LONG_TRANSFER_THRESHOLD_MIN and not is_penalty_pause:
                tr_net = tr_min - LONG_TRANSFER_BREAK_MIN
                tr_cap = _slot_max_modules(tr_net, "focus")
                if tr_cap > 0:
                    study_slots.append(("transfer", i, tr_net, tr_cap))

    total_laptop_capacity = sum(s[3] for s in study_slots)
    selected_laptop_jobs = _select_laptop_jobs(laptop_candidates, total_laptop_capacity)

    slot_to_jobs = {idx: [] for idx in range(len(study_slots))}
    if study_slots and selected_laptop_jobs:
        job_cursor = 0
        # Erst jedem Slot 1 Modul geben, danach (falls ein langer ICE-Slot cap >= 2 hat) auffüllen
        for pass_num in range(max(s[3] for s in study_slots)):
            for s_idx, s_info in enumerate(study_slots):
                if job_cursor >= len(selected_laptop_jobs):
                    break
                if len(slot_to_jobs[s_idx]) < s_info[3]:
                    slot_to_jobs[s_idx].append(selected_laptop_jobs[job_cursor])
                    job_cursor += 1

    num_legs = len(legs)
    for i, leg in enumerate(legs):
        tname = leg.get("train", "Zug")
        from_s = leg.get("from_station", "Start")
        to_s = leg.get("to_station", "Ziel")
        dur = int(leg.get("duration_min") or diff_minutes(leg.get("dep"), leg.get("arr"), 35))
        dep_m = parse_hhmm_to_min(leg.get("dep", "09:00")) or (540 + i * 60)
        arr_m = dep_m + dur
        dep_hhmm = min_to_hhmm(dep_m)
        arr_hhmm = min_to_hhmm(arr_m)
        tw = f"{dep_hhmm} – {arr_hhmm}"
        mode = leg.get("mode", "focus")
        buffer_min = 5 if dur >= 25 else 3
        net_min = max(10, dur - buffer_min)
        train_route_hdr = f"Zug {i + 1}/{num_legs} ({tname}): {from_s} ({dep_hhmm}) → {to_s} ({arr_hhmm})"

        matching_slot = next((s_idx for s_idx, s in enumerate(study_slots) if s[0] == "leg" and s[1] == i), None)
        assigned = slot_to_jobs.get(matching_slot, []) if matching_slot is not None else []

        if mode == "regio_memo":
            memo_pair = memo_leg_assignments.get(i)
            if memo_pair:
                m_grp, m_itm = memo_pair
                s_mod = short_module_name(m_grp["module"])
                s_itm = short_item_name(m_itm["name"])
                if m_grp["id"] in job_allocations:
                    job_allocations[m_grp["id"]]["minutes"] += dur
                    job_allocations[m_grp["id"]]["leg_title"] += f" + Zug {i + 1}/{num_legs} ({tname})"
                    job_allocations[m_grp["id"]]["train_short"] += f"+{tname}"
                    job_allocations[m_grp["id"]]["time_window"] += f", {tw}"
                    job_allocations[m_grp["id"]]["leg_indices"].append(i)
                else:
                    job_allocations[m_grp["id"]] = {
                        "minutes": dur,
                        "leg_title": f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s}",
                        "train_short": f"📱 {tname}",
                        "mode": "regio_memo",
                        "is_phone_memo": True,
                        "time_window": tw,
                        "train_type": leg.get("type", "REGIO"),
                        "leg_indices": [i],
                    }
                memo_chips = [f"🧠 {m_grp['icon']} {s_mod} ({s_itm}) · {dur}m (📱 Handy / Auswendig)"]
                memo_title = f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s} ({dur} Min. · 📱 {s_mod})"
                memo_adv = f"Auswendiglernen am Handy (OneDrive): {m_grp['module']} ({m_itm['name']})"
                memo_gid = m_grp["id"]
            else:
                memo_chips = ["🧠 Stehplatz / Voll · Regio-Spickkarten (Kein Laptop)"]
                memo_title = f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s} ({dur} Min. · Nur Theorie)"
                memo_adv = "Regio-Spickkarten (Merksätze & Begriffe) anschauen oder Pause machen."
                memo_gid = None

            schedule_blocks.append({
                "kind": "regio_memo",
                "phase_num": phase_counter,
                "leg_index": i,
                "train_header": train_route_hdr,
                "start_min": dep_m,
                "end_min": arr_m,
                "time": tw,
                "duration_min": dur,
                "title": memo_title,
                "subtitle": f"{tw} Uhr · 🧠 Stehplatz / Voll (Kein Laptop)",
                "advice": memo_adv,
                "chips": memo_chips,
                "mode": "regio_memo",
                "group_id": memo_gid,
            })
            phase_counter += 1
        elif mode == "rest":
            schedule_blocks.append({
                "kind": "rest",
                "phase_num": phase_counter,
                "leg_index": i,
                "train_header": train_route_hdr,
                "start_min": dep_m,
                "end_min": arr_m,
                "time": tw,
                "duration_min": dur,
                "title": f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s} ({dur} Min. Pause)",
                "subtitle": f"{tw} Uhr · ☕ Lernfreie Fahrt",
                "advice": "Entspannen & Pause machen.",
                "chips": ["☕ Pause (Nichts lernen)"],
                "mode": "rest",
            })
            phase_counter += 1
        elif assigned:
            per_job = max(10, int(net_min / len(assigned)))
            chips_list = []
            first_gid = assigned[0][0]["id"]
            for grp, item in assigned:
                s_mod = short_module_name(grp["module"])
                s_itm = short_item_name(item["name"])
                job_allocations[grp["id"]] = {
                    "minutes": per_job,
                    "leg_title": f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s}",
                    "train_short": tname,
                    "mode": mode,
                    "time_window": tw,
                    "train_type": leg.get("type", "REGIO"),
                    "leg_indices": [i],
                }
                chips_list.append(f"{grp['icon']} {s_mod} ({s_itm}) · {per_job}m")
            schedule_blocks.append({
                "kind": "study",
                "phase_num": phase_counter,
                "leg_index": i,
                "train_header": train_route_hdr,
                "start_min": dep_m,
                "end_min": arr_m,
                "time": tw,
                "duration_min": dur,
                "title": f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s} ({net_min} Min. Netto-Lernzeit)",
                "subtitle": f"{tw} Uhr ({dur} Min. Fahrt) · {LEG_MODE_LABELS.get(mode)}",
                "advice": "  |  ".join(chips_list),
                "chips": chips_list,
                "mode": mode,
                "group_id": first_gid,
            })
            phase_counter += 1
        else:
            schedule_blocks.append({
                "kind": "study",
                "phase_num": phase_counter,
                "leg_index": i,
                "train_header": train_route_hdr,
                "start_min": dep_m,
                "end_min": arr_m,
                "time": tw,
                "duration_min": dur,
                "title": f"Zug {i + 1}/{num_legs} ({tname}): {from_s} → {to_s} ({net_min} Min. Wiederholung)",
                "subtitle": f"{tw} Uhr ({dur} Min. Fahrt) · {LEG_MODE_LABELS.get(mode)}",
                "advice": "Nachbereiten & Wiederholen",
                "chips": [f"📖 Wiederholung & Puffer · {net_min}m"],
                "mode": mode,
            })
            phase_counter += 1

        # --- Umstieg nach diesem Abschnitt ---
        if i < len(legs) - 1:
            nxt_leg = legs[i + 1]
            nxt_tname = nxt_leg.get("train", "Anschlusszug")
            nxt_to = nxt_leg.get("to_station", "Ziel")
            tr_min = int(leg.get("transfer_after_min") or diff_minutes(leg.get("arr"), nxt_leg.get("dep"), 12))
            tr_start = arr_m
            tr_end = arr_m + tr_min
            tr_tw = f"{min_to_hhmm(tr_start)} – {min_to_hhmm(tr_end)}"
            is_penalty_pause = (trip.get("extra_pause_min", 0) > 0 and trip.get("extra_pause_after_leg") == i)

            if is_penalty_pause:
                schedule_blocks.append({
                    "kind": "transfer_break",
                    "phase_num": phase_counter,
                    "leg_index": i,
                    "start_min": tr_start,
                    "end_min": tr_end,
                    "time": tr_tw,
                    "duration_min": tr_min,
                    "title": f"⚠️ Umstieg in {to_s} ({tr_min} Min. Pause inkl. +{MISSED_CONNECTION_PENALTY_MIN}m)",
                    "subtitle": f"{tr_tw} Uhr · {tname} → {nxt_tname}",
                    "advice": "In Ruhe zum neuen Gleis wechseln und warten.",
                    "chips": [f"⚠️ Anschluss verpasst · {tr_min}m Pause in {to_s}"],
                    "mode": "rest",
                })
                phase_counter += 1
            elif tr_min >= LONG_TRANSFER_THRESHOLD_MIN:
                p_end = tr_start + LONG_TRANSFER_BREAK_MIN
                study_tr_min = tr_min - LONG_TRANSFER_BREAK_MIN
                p_tw = f"{min_to_hhmm(tr_start)} – {min_to_hhmm(p_end)}"
                s_tw = f"{min_to_hhmm(p_end)} – {min_to_hhmm(tr_end)}"
                schedule_blocks.append({
                    "kind": "transfer_break",
                    "phase_num": phase_counter,
                    "leg_index": i,
                    "start_min": tr_start,
                    "end_min": p_end,
                    "time": p_tw,
                    "duration_min": LONG_TRANSFER_BREAK_MIN,
                    "title": f"☕ Umstieg in {to_s} ({LONG_TRANSFER_BREAK_MIN} Min. Pause)",
                    "subtitle": f"{p_tw} Uhr · Wechsel {tname} → {nxt_tname}",
                    "advice": "Gleiswechsel & kurze Pause.",
                    "chips": [f"☕ {LONG_TRANSFER_BREAK_MIN}m Umstiegs-Pause in {to_s}"],
                    "mode": "rest",
                })
                phase_counter += 1

                tr_slot = next((s_idx for s_idx, s in enumerate(study_slots) if s[0] == "transfer" and s[1] == i), None)
                tr_assigned = slot_to_jobs.get(tr_slot, []) if tr_slot is not None else []
                first_tr_gid = tr_assigned[0][0]["id"] if tr_assigned else None

                tr_chips = []
                if tr_assigned:
                    per_job = max(10, int(study_tr_min / len(tr_assigned)))
                    for grp, item in tr_assigned:
                        s_mod = short_module_name(grp["module"])
                        s_itm = short_item_name(item["name"])
                        job_allocations[grp["id"]] = {
                            "minutes": per_job,
                            "leg_title": f"Umstieg in {to_s} ({s_tw})",
                            "train_short": f"Umstieg {to_s}",
                            "mode": "light",
                            "time_window": s_tw,
                            "train_type": "TRANSFER",
                            "leg_indices": [i],
                        }
                        tr_chips.append(f"{grp['icon']} {s_mod} ({s_itm}) · {per_job}m")
                    tr_advice = "  |  ".join(tr_chips)
                else:
                    tr_chips = [f"📖 Wartezeit-Lernen · {study_tr_min}m"]
                    tr_advice = f"{study_tr_min} Min. Lernzeit am Bahnhof {to_s}."

                schedule_blocks.append({
                    "kind": "study",
                    "phase_num": phase_counter,
                    "leg_index": i,
                    "start_min": p_end,
                    "end_min": tr_end,
                    "time": s_tw,
                    "duration_min": study_tr_min,
                    "title": f"📖 Wartezeit-Lernen in {to_s} ({study_tr_min} Min. Netto-Lernzeit)",
                    "subtitle": f"{s_tw} Uhr · Warten auf {nxt_tname} nach {nxt_to}",
                    "advice": tr_advice,
                    "chips": tr_chips,
                    "mode": "light",
                    "group_id": first_tr_gid,
                })
                phase_counter += 1
            else:
                schedule_blocks.append({
                    "kind": "transfer_break",
                    "phase_num": phase_counter,
                    "leg_index": i,
                    "start_min": tr_start,
                    "end_min": tr_end,
                    "time": tr_tw,
                    "duration_min": tr_min,
                    "title": f"☕ {tr_min} Min. Umstieg & Pause in {to_s}",
                    "subtitle": f"{tr_tw} Uhr · {tname} → {nxt_tname} nach {nxt_to}",
                    "advice": "Feste Lernpause beim Umsteigen.",
                    "chips": [f"☕ {tr_min} Min. Umstieg & Pause in {to_s} ({tname} → {nxt_tname})"],
                    "mode": "rest",
                })
                phase_counter += 1

    return schedule_blocks, job_allocations


# --------------------------------------------------------------------------
# DB-Konto Login & Reise-Extraktion (Playwright + Microsoft Edge)
# --------------------------------------------------------------------------
FLOATING_BAHN_BANNER_JS = """
(() => {
    if (document.getElementById('er-floating-banner')) return;
    const box = document.createElement('div');
    box.id = 'er-floating-banner';
    box.style.cssText = 'position:fixed;bottom:20px;right:20px;z-index:999999;background:#0f172a;color:#fff;padding:16px 20px;border-radius:14px;box-shadow:0 10px 25px rgba(0,0,0,0.45);font-family:Segoe UI,sans-serif;max-width:380px;border:2px solid #0ea5e9;';
    box.innerHTML = `
        <div style="font-weight:bold;font-size:15px;margin-bottom:6px;color:#38bdf8;">🧳 Entspannt Reisen – DB-Verbindung</div>
        <div style="font-size:12.5px;color:#cbd5e1;margin-bottom:12px;line-height:1.45;">
            1. Einmal anmelden (dein Login bleibt dauerhaft gespeichert).<br>
            2. Öffne „Meine Reisen“, „Gemerkte Verbindungen“ oder suche deine neue Verbindung und klappe <b>Reisedetails</b> auf.<br>
            3. Klicke auf den blauen Button (oder schließe das Fenster).
        </div>
        <button id="er-capture-btn" style="width:100%;background:#0ea5e9;color:#fff;border:none;padding:10px 14px;border-radius:10px;font-weight:bold;font-size:13.5px;cursor:pointer;">
            ✅ Angezeigte Reise(n) übernehmen & schließen
        </button>
    `;
    document.body.appendChild(box);
    document.getElementById('er-capture-btn').addEventListener('click', () => {
        window.__ER_CAPTURE_NOW = true;
        document.getElementById('er-capture-btn').innerText = '⏳ Wird übernommen...';
    });
})();
"""


def _extract_time_and_date_from_halt_obj(halt_or_time_obj):
    """Liest Sollzeit, Istzeit und Datum aus DB-API-Feldern (dict mit sollzeit/istzeit oder String)."""
    soll_raw = ""
    ist_raw = ""
    if isinstance(halt_or_time_obj, dict):
        if "abfahrt" in halt_or_time_obj or "ankunft" in halt_or_time_obj:
            inner = halt_or_time_obj.get("abfahrt") or halt_or_time_obj.get("ankunft") or {}
            if isinstance(inner, dict):
                soll_raw = str(inner.get("sollzeit") or inner.get("zeit") or "")
                ist_raw = str(inner.get("istzeit") or inner.get("ezZeit") or soll_raw)
            else:
                soll_raw = str(inner)
                ist_raw = soll_raw
        else:
            soll_raw = str(halt_or_time_obj.get("sollzeit") or halt_or_time_obj.get("local") or halt_or_time_obj.get("zeit") or "")
            ist_raw = str(halt_or_time_obj.get("istzeit") or halt_or_time_obj.get("ezZeit") or soll_raw)
    else:
        soll_raw = str(halt_or_time_obj or "")
        ist_raw = soll_raw

    p_m = re.search(r"(\d{2}:\d{2})", soll_raw)
    e_m = re.search(r"(\d{2}:\d{2})", ist_raw)
    d_m = re.search(r"(\d{4})-(\d{2})-(\d{2})", soll_raw or ist_raw)
    date_str = f"{d_m.group(3)}.{d_m.group(2)}.{d_m.group(1)}" if d_m else None
    p_hhmm = p_m.group(1) if p_m else (e_m.group(1) if e_m else None)
    e_hhmm = e_m.group(1) if e_m else p_hhmm
    return p_hhmm, e_hhmm, date_str


def _build_trip_dict_from_legs(parsed_legs, trip_date, source_label="Aus DB-Konto (bahn.de) geladen"):
    if not parsed_legs:
        return None
    for i in range(len(parsed_legs) - 1):
        parsed_legs[i]["transfer_after_min"] = diff_minutes(parsed_legs[i]["arr"], parsed_legs[i + 1]["dep"], 12)
    parsed_legs[-1]["transfer_after_min"] = 0
    assign_smart_leg_modes(parsed_legs)
    first_st = parsed_legs[0].get("from_station", "Start")
    last_st = parsed_legs[-1].get("to_station", "Ziel")
    trip_title = (
        f"{parsed_legs[0]['train']}: {first_st} → {last_st} (Direktfahrt)"
        if len(parsed_legs) == 1
        else f"{first_st} → {last_st} ({len(parsed_legs) - 1}× Umsteigen)"
    )
    return {
        "title": trip_title,
        "date": trip_date or datetime.date.today().strftime("%d.%m.%Y"),
        "source": source_label,
        "extra_pause_min": 0,
        "extra_pause_after_leg": 0,
        "completed_group_ids": [],
        "legs": parsed_legs,
    }


def parse_all_bahn_trips(api_payloads, page_text):
    """
    Extrahiert ALLE im DB-Konto gefundenen Reisen (Gemerkte Reisen, gebuchte Aufträge, Verbindungsdetails)
    inklusive aller einzelnen Zugabschnitte, korrektem Reisedatum (z.B. Samstag 24.10.2026) und Zeiten.
    """
    found_trips = []
    seen_keys = set()

    for url, data in api_payloads:
        if not isinstance(data, dict):
            continue

        # 1. Detaillierte Verbindungen: 'trips' (aus /reisebegleitung/reiseketten/{uuid}), 'verbindungen', 'reisen', 'auftraege'
        candidates = []
        for list_key in ("trips", "verbindungen", "reisen", "auftraege"):
            val = data.get(list_key)
            if isinstance(val, list):
                candidates.extend(val)
        if isinstance(data.get("verbindung"), dict):
            candidates.append(data["verbindung"])
        if isinstance(data.get("verbindungsAbschnitte"), list):
            candidates.append(data)

        for verb in candidates:
            if not isinstance(verb, dict):
                continue
            abschnitte = verb.get("verbindungsAbschnitte") or verb.get("abschnitte") or []
            if not abschnitte and isinstance(verb.get("hinfahrt"), dict):
                abschnitte = verb["hinfahrt"].get("verbindungsAbschnitte") or verb["hinfahrt"].get("abschnitte") or []
            parsed_legs = []
            trip_date = None

            for ab in abschnitte:
                if not isinstance(ab, dict):
                    continue
                vm = ab.get("verkehrsmittel") or {}
                v_type = (vm.get("typ") or ab.get("typ") or vm.get("produktGattung") or "").upper()
                if v_type in ("WALK", "FUSSWEG", "TRAM", "BUS") and len(abschnitte) > 1:
                    continue

                t_name = (
                    vm.get("langText")
                    or vm.get("mittelText")
                    or vm.get("mitteltext")
                    or vm.get("linienNummer")
                    or vm.get("name")
                    or vm.get("kurzText")
                    or vm.get("kurztext")
                    or ab.get("zugname")
                    or "Zug"
                ).strip()

                p_dep, dep_str, d1 = _extract_time_and_date_from_halt_obj(
                    ab.get("abfahrt") or ab.get("startHalt") or ab.get("abfahrtsZeitpunkt")
                )
                p_arr, arr_str, d2 = _extract_time_and_date_from_halt_obj(
                    ab.get("ankunft") or ab.get("zielHalt") or ab.get("ankunftsZeitpunkt")
                )
                if ab.get("ezAbfahrtsZeitpunkt"):
                    _, ez_d, _ = _extract_time_and_date_from_halt_obj(ab.get("ezAbfahrtsZeitpunkt"))
                    if ez_d:
                        dep_str = ez_d
                if ab.get("ezAnkunftsZeitpunkt"):
                    _, ez_a, _ = _extract_time_and_date_from_halt_obj(ab.get("ezAnkunftsZeitpunkt"))
                    if ez_a:
                        arr_str = ez_a

                if d1 and not trip_date:
                    trip_date = d1
                elif d2 and not trip_date:
                    trip_date = d2

                planned_dep = p_dep or dep_str or "09:00"
                planned_arr = p_arr or arr_str or "09:45"
                dep_str = dep_str or planned_dep
                arr_str = arr_str or planned_arr

                delay_min = max(
                    0,
                    (parse_hhmm_to_min(dep_str) or 0) - (parse_hhmm_to_min(planned_dep) or 0),
                    (parse_hhmm_to_min(arr_str) or 0) - (parse_hhmm_to_min(planned_arr) or 0),
                )
                start_halt = ab.get("startHalt") if isinstance(ab.get("startHalt"), dict) else {}
                ziel_halt = ab.get("zielHalt") if isinstance(ab.get("zielHalt"), dict) else {}
                from_st = ab.get("abfahrtsOrt") or start_halt.get("name") or ab.get("startOrt") or "Start"
                to_st = ab.get("ankunftsOrt") or ziel_halt.get("name") or ab.get("zielOrt") or "Ziel"
                dur = int(ab.get("ezAbschnittsDauerInSekunden", 0) or ab.get("abschnittsDauer", 0)) // 60
                if dur <= 0:
                    dur = diff_minutes(dep_str, arr_str, 35)

                occ_detected = detect_db_auslastung(ab, "")
                leg_mode = "regio_memo" if occ_detected == "Hohe Auslastung" else "focus"
                parsed_legs.append({
                    "train": t_name,
                    "type": classify_train_type(t_name),
                    "from_station": from_st,
                    "to_station": to_st,
                    "planned_dep": planned_dep,
                    "planned_arr": planned_arr,
                    "dep": dep_str,
                    "arr": arr_str,
                    "duration_min": dur,
                    "transfer_after_min": 0,
                    "delay_min": delay_min,
                    "mode": leg_mode,
                    "db_occupancy": occ_detected,
                })

            if parsed_legs:
                rk_typ = str(data.get("typ") or verb.get("typ") or "").upper()
                if rk_typ == "AUFTRAG" or "auftraege" in data:
                    src_lbl = "Aus DB-Konto (bahn.de) – Gebuchtes Ticket"
                elif rk_typ == "FREI":
                    src_lbl = "Aus DB-Konto (bahn.de) – Gemerkte Reise"
                else:
                    src_lbl = "Aus DB-Konto (bahn.de) geladen"
                t_obj = _build_trip_dict_from_legs(parsed_legs, trip_date, source_label=src_lbl)
                k = trip_identity_key(t_obj)
                if t_obj and k not in seen_keys and not is_corrupted_trip(t_obj):
                    seen_keys.add(k)
                    found_trips.append(t_obj)

        # 2. Falls /reisebegleitung/reiseketten eine Liste von Reiseketten liefert, deren Details noch nicht geladen wurden:
        if isinstance(data.get("reiseketten"), list) and not found_trips:
            for rk in data["reiseketten"]:
                if not isinstance(rk, dict):
                    continue
                orig = rk.get("origin") or {}
                dest = rk.get("destination") or {}
                einstiege = rk.get("einstiegsInformationen") or []
                p_dep, dep_s, d_str = _extract_time_and_date_from_halt_obj((orig.get("dateTime") or {}).get("local"))
                p_arr, arr_s, _ = _extract_time_and_date_from_halt_obj((dest.get("dateTime") or {}).get("local"))
                if orig.get("name") and dest.get("name") and dep_s and arr_s:
                    total_dur = diff_minutes(dep_s, arr_s, 60)
                    n_trains = max(1, len(einstiege))
                    if n_trains == 1:
                        tname = (einstiege[0].get("name") if einstiege else "Zug") or "Zug"
                        legs_rk = [{
                            "train": tname,
                            "type": classify_train_type(tname),
                            "from_station": orig.get("name"),
                            "to_station": dest.get("name"),
                            "planned_dep": dep_s,
                            "planned_arr": arr_s,
                            "dep": dep_s,
                            "arr": arr_s,
                            "duration_min": total_dur,
                            "transfer_after_min": 0,
                            "delay_min": 0,
                            "mode": "focus",
                        }]
                        t_obj = _build_trip_dict_from_legs(legs_rk, d_str)
                        k = trip_identity_key(t_obj)
                        if t_obj and k not in seen_keys and not is_corrupted_trip(t_obj):
                            seen_keys.add(k)
                            found_trips.append(t_obj)

    # 3. Fallback auf Seitentext nur, wenn keine JSON-Reise gefunden wurde (mit strengem Zug-Regex: S erfordert Ziffern!)
    if not found_trips and page_text:
        MONTH_MAP = {
            "jan": "01", "feb": "02", "mär": "03", "mar": "03", "apr": "04", "mai": "05", "jun": "06",
            "jul": "07", "aug": "08", "sep": "09", "okt": "10", "nov": "11", "dez": "12",
        }
        trip_date = datetime.date.today().strftime("%d.%m.%Y")
        dm = re.search(r"\b(\d{1,2})\.\s*(\d{1,2})\.\s*(202\d)\b", page_text)
        if dm:
            trip_date = f"{int(dm.group(1)):02d}.{int(dm.group(2)):02d}.{dm.group(3)}"
        else:
            dm_txt = re.search(r"\b(\d{1,2})\.\s*([A-Za-zÄÖÜäöü]{3,9})\.?\s*(202\d)\b", page_text)
            if dm_txt:
                m_num = MONTH_MAP.get(dm_txt.group(2)[:3].lower(), "10")
                trip_date = f"{int(dm_txt.group(1)):02d}.{m_num}.{dm_txt.group(3)}"

        # Wichtig: \d+ ist Pflicht, damit Wochentage wie 'Sa' niemals als S-Bahn gematcht werden!
        train_pattern = re.compile(r"\b((?:ICE|IC|EC|RE|RB|IRE|S|TGV|RJ|FLX|MEX)\s*\d+[a-zA-Z]?)\b")
        lines = [ln.strip() for ln in page_text.splitlines() if ln.strip()]
        found_segments = []
        for idx, ln in enumerate(lines):
            tm = train_pattern.search(ln)
            if tm and len(ln) <= 35:
                tname = tm.group(1).strip()
                window = lines[max(0, idx - 6): min(len(lines), idx + 8)]
                times = []
                stations = []
                for w in window:
                    for hm in re.findall(r"\b([0-2]\d:[0-5]\d)\b", w):
                        if hm not in times:
                            times.append(hm)
                    if (
                        len(w) > 3
                        and not re.search(r"\b([0-2]\d:[0-5]\d)\b", w)
                        and not train_pattern.search(w)
                        and not any(x in w.lower() for x in (
                            "gleis", "min.", "umstieg", "dauer", "details", "klasse", "ticket",
                            "buchen", "preis", "richtung", "gemerkte reise", "reisedetails", "abfahrt", "ankunft"
                        ))
                    ):
                        stations.append(w)
                if len(times) >= 2 and len(stations) >= 2:
                    dep_s, arr_s = times[0], times[1]
                    st_from, st_to = stations[0], stations[1]
                    dur = diff_minutes(dep_s, arr_s, 35)
                    if 3 <= dur <= 480:
                        found_segments.append({
                            "train": tname,
                            "type": classify_train_type(tname),
                            "from_station": st_from[:40],
                            "to_station": st_to[:40],
                            "planned_dep": dep_s,
                            "planned_arr": arr_s,
                            "dep": dep_s,
                            "arr": arr_s,
                            "duration_min": dur,
                            "transfer_after_min": 0,
                            "delay_min": 0,
                            "mode": "focus",
                        })
        dedup = []
        seen = set()
        for seg in found_segments:
            key = (seg["train"], seg["dep"], seg["arr"])
            if key not in seen:
                seen.add(key)
                dedup.append(seg)
        if dedup:
            t_obj = _build_trip_dict_from_legs(dedup[:5], trip_date)
            if t_obj and not is_corrupted_trip(t_obj):
                found_trips.append(t_obj)

    # Sortiere so, dass bevorstehende Reisen (heute oder in der Zukunft) zuerst stehen
    today = datetime.date.today()
    found_trips.sort(key=lambda t: (parse_trip_date(t.get("date")) < today, parse_trip_date(t.get("date"))))
    return found_trips


def parse_bahn_json_or_text(api_payloads, page_text):
    trips = parse_all_bahn_trips(api_payloads, page_text)
    return trips[0] if trips else None


def fetch_db_trip_via_browser(cfg, interactive=False, log=print):
    os.makedirs(DB_PROFILE_DIR, exist_ok=True)
    from playwright.sync_api import sync_playwright

    api_payloads = []
    page_texts = []
    logged_in = False

    with sync_playwright() as p:
        ctx = p.chromium.launch_persistent_context(
            DB_PROFILE_DIR,
            channel="msedge",
            headless=not interactive,
            viewport=None if interactive else {"width": 1280, "height": 900},
            args=["--disable-blink-features=AutomationControlled"],
        )
        page = ctx.pages[0] if ctx.pages else ctx.new_page()

        def on_response(resp):
            try:
                if "bahn.de/web/api" in resp.url and "json" in resp.headers.get("content-type", ""):
                    data = resp.json()
                    api_payloads.append((resp.url, data))
                    if "user-context-data" in resp.url and isinstance(data, dict):
                        if data.get("profil") or data.get("hashedKundenkontoId"):
                            nonlocal logged_in
                            logged_in = True
            except Exception:
                pass

        page.on("response", on_response)
        target_url = "https://www.bahn.de/buchung/reiseuebersicht"
        log("   → Öffne bahn.de (Meine Reisen & Gemerkte Verbindungen) …")
        try:
            page.goto(target_url, wait_until="domcontentloaded", timeout=25000)
        except Exception:
            pass
        page.wait_for_timeout(3000)

        if "accounts.bahn.de" in page.url or "Anmelden" in page.title():
            user = (cfg.get("db_username") or "").strip()
            pw = (cfg.get("db_password") or "").strip()
            if user and pw:
                log("   → Fülle gespeicherte DB-Zugangsdaten automatisch aus …")
                try:
                    if page.locator("input#username, input[name='username']").count() > 0:
                        page.fill("input#username, input[name='username']", user)
                        if page.locator("input#password, input[name='password']").count() == 0:
                            page.click("button[type='submit'], input[type='submit']")
                            page.wait_for_timeout(1500)
                    if page.locator("input#password, input[name='password']").count() > 0:
                        page.fill("input#password, input[name='password']", pw)
                        page.click("button[type='submit'], input[type='submit']")
                        page.wait_for_timeout(3500)
                except Exception:
                    pass

        def _fetch_all_reiseketten_details(target_page):
            """Lädt für alle im DB-Konto gespeicherten/gemerkten Reiseketten die kompletten Zugabschnitte."""
            uuids = []
            for _wait_step in range(12):
                for _, d in list(api_payloads):
                    if isinstance(d, dict) and isinstance(d.get("reiseketten"), list):
                        for rk in d["reiseketten"]:
                            u = rk.get("reisekettenUuid") if isinstance(rk, dict) else None
                            if u and u not in uuids:
                                uuids.append(u)
                if uuids:
                    break
                target_page.wait_for_timeout(500)
            if not uuids:
                try:
                    rk_list = target_page.evaluate(
                        """async () => {
                            try {
                                const r = await fetch('/web/api/reisebegleitung/reiseketten?pagesize=100&types%5B%5D=AUFTRAG&types%5B%5D=FREI', {credentials: 'include'});
                                if (r.ok) return await r.json();
                            } catch (e) {}
                            return null;
                        }"""
                    )
                    if isinstance(rk_list, dict) and isinstance(rk_list.get("reiseketten"), list):
                        api_payloads.append(("https://www.bahn.de/web/api/reisebegleitung/reiseketten", rk_list))
                        for rk in rk_list["reiseketten"]:
                            u = rk.get("reisekettenUuid") if isinstance(rk, dict) else None
                            if u and u not in uuids:
                                uuids.append(u)
                except Exception:
                    pass
            if uuids:
                try:
                    fetched = target_page.evaluate(
                        """async (uuids) => {
                            const out = [];
                            for (const u of uuids) {
                                try {
                                    const r = await fetch('/web/api/reisebegleitung/reiseketten/' + u, {credentials: 'include'});
                                    if (r.ok) {
                                        out.push(['https://www.bahn.de/web/api/reisebegleitung/reiseketten/' + u, await r.json()]);
                                    }
                                } catch (e) {}
                            }
                            return out;
                        }""",
                        uuids,
                    )
                    if isinstance(fetched, list):
                        for item in fetched:
                            if isinstance(item, list) and len(item) == 2:
                                api_payloads.append((item[0], item[1]))
                except Exception:
                    pass

        if not interactive:
            if "accounts.bahn.de" in page.url:
                ctx.close()
                return None, False
            logged_in = True
            try:
                _fetch_all_reiseketten_details(page)
                for sel in ["text=Reisedetails", "button:has-text('Details')", "button:has-text('Verbindungsdetails')", "a:has-text('Details')"]:
                    btns = page.locator(sel)
                    for b_idx in range(min(3, btns.count())):
                        try:
                            btns.nth(b_idx).click(timeout=1500)
                            page.wait_for_timeout(1200)
                        except Exception:
                            pass
                page_texts.append(page.inner_text("body"))
            except Exception:
                pass
            ctx.close()
        else:
            log("   → Browser geöffnet. Bitte bei Bedarf anmelden / Verbindung wählen …")
            fetched_once = False
            while True:
                try:
                    if not ctx.pages:
                        break
                    active_page = ctx.pages[-1]
                    if "bahn.de" in active_page.url and "accounts.bahn.de" not in active_page.url:
                        logged_in = True
                        if not fetched_once:
                            fetched_once = True
                            _fetch_all_reiseketten_details(active_page)
                    try:
                        active_page.evaluate(FLOATING_BAHN_BANNER_JS)
                        capture_now = active_page.evaluate("() => window.__ER_CAPTURE_NOW === true")
                    except Exception:
                        capture_now = False

                    if capture_now:
                        try:
                            _fetch_all_reiseketten_details(active_page)
                            page_texts.append(active_page.inner_text("body"))
                        except Exception:
                            pass
                        break
                    try:
                        txt = active_page.inner_text("body")
                        if txt and len(txt) > 200:
                            if not page_texts:
                                page_texts.append(txt)
                            else:
                                page_texts[-1] = txt
                    except Exception:
                        pass
                    time.sleep(0.6)
                except Exception:
                    break
            try:
                ctx.close()
            except Exception:
                pass

    combined_text = "\n\n".join(page_texts)
    all_trips = parse_all_bahn_trips(api_payloads, combined_text)
    if all_trips:
        cfg["saved_trips"] = [json.loads(json.dumps(t)) for t in all_trips]

    trip = all_trips[0] if all_trips else None

    if not trip and len(combined_text) > 300 and any(k in combined_text for k in ("ICE", "RE", "RB", "IC", "Uhr", "Gleis", "Umstieg")):
        try:
            log("   → Analysiere Reise-Details von bahn.de mit KI …")
            trip = extract_trip_with_ai(cfg, combined_text)
            if trip:
                register_trip_in_saved_list(cfg, trip)
        except Exception:
            pass

    return trip, logged_in


def extract_trip_with_ai(cfg, raw_page_text):
    snippet = raw_page_text[:12000]
    prompt = f"""Extrahiere aus diesem Seitentext von bahn.de die nächste bevorstehende Zugreise (für heute oder morgen bzw. die erste angezeigte Verbindung).
Antworte AUSSCHLIESSLICH mit gültigem JSON im folgenden Format (keine Markdown-Blöcke, kein Text davor/danach):
{{
  "title": "Start -> Ziel",
  "date": "TT.MM.JJJJ",
  "legs": [
    {{
      "train": "z.B. RE 10 oder ICE 612",
      "from_station": "Abfahrtsbahnhof",
      "to_station": "Ankunftsbahnhof",
      "dep": "HH:MM",
      "arr": "HH:MM",
      "duration_min": 45,
      "transfer_after_min": 15
    }}
  ]
}}

Seitentext:
{snippet}"""
    workdir = tempfile.mkdtemp(prefix="er_trip_")
    try:
        provs = detect_providers(cfg)
        avail = [p[0] for p in provs if p[2]]
        if not avail:
            return None
        pid = avail[0]
        if pid == "agy_cli":
            out = summarize_agy_cli(cfg, prompt, workdir, lambda _: None, min_len=20)
        elif pid == "gemini_cli":
            out = summarize_gemini_cli(cfg, prompt, workdir, lambda _: None, min_len=20)
        elif pid == "gemini_api":
            out = summarize_gemini_api(cfg, prompt, workdir, [], lambda _: None)
        elif pid == "claude_cli":
            out = summarize_claude_cli(cfg, prompt, workdir, lambda _: None, min_len=20)
        elif pid == "claude_api":
            out = summarize_claude_api(cfg, prompt, workdir, [], lambda _: None)
        else:
            return None
        m = re.search(r"\{.*\}", out, re.S)
        if not m:
            return None
        data = json.loads(m.group(0))
        if not data.get("legs"):
            return None
        assign_smart_leg_modes(data["legs"])
        ensure_planned_times(data)
        data["source"] = "Aus DB-Konto (bahn.de) geladen"
        data["extra_pause_min"] = 0
        data["extra_pause_after_leg"] = 0
        data["completed_group_ids"] = []
        return data
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


# --------------------------------------------------------------------------
# Übungen finden
# --------------------------------------------------------------------------
def natural_key(s):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]


def scan_group(grp):
    items = []
    pdir = grp["parent_dir"]
    if not os.path.isdir(pdir):
        return items
    for entry in os.listdir(pdir):
        done = next((p for p in DONE_PREFIXES if entry.startswith(p)), None)
        if done:
            items.append({"name": entry[len(done):].strip(), "path": os.path.join(pdir, entry), "done": True})
        elif entry.startswith(OPEN_PREFIX):
            items.append({"name": entry[len(OPEN_PREFIX):].strip(), "path": os.path.join(pdir, entry), "done": False})
    items.sort(key=lambda it: natural_key(it["name"]))
    return items


def next_open(grp):
    for it in scan_group(grp):
        if not it["done"]:
            return it
    return None


def safe_name(s):
    s = re.sub(r'[<>:"/\\|?*]', "_", s)
    return s.strip().rstrip(".")


def group_output_dir(grp):
    return os.path.join(OUTPUT_ROOT, safe_name(f"{grp['module']} - {grp['category']}"))


def summary_pdf_path(grp, item):
    base = os.path.splitext(item["name"])[0] if os.path.isfile(item["path"]) else item["name"]
    return os.path.join(group_output_dir(grp), safe_name(base) + " - Zusammenfassung.pdf")


def clean_endstation_for_phone(trip):
    legs = (trip or {}).get("legs") or []
    raw = ""
    if legs:
        raw = (legs[-1].get("to_station") or "").strip()
    if not raw:
        title = (trip or {}).get("title") or ""
        for sep in ("→", "->"):
            if sep in title:
                raw = title.split(sep)[-1].strip()
                break
    if not raw:
        raw = "Ziel"
    raw = re.sub(r"\s*\(.*?\)", "", raw)
    raw = re.sub(r"\s+(Hauptbahnhof|Hbf\.?)\b", "", raw, flags=re.IGNORECASE).strip()
    return raw or "Ziel"


def clean_module_name_for_phone(grp):
    gid = (grp or {}).get("id", "")
    if gid == "wifo":
        return "Wirtschaftsinformatik"
    if gid == "marketing":
        return "Marketing"
    if gid == "fgdi":
        return "Formale Grundlagen der Informatik"
    mod = (grp or {}).get("module", "Modul")
    return re.sub(r"\s*\(.*?\)", "", mod).strip() or mod


def weekday_full_for_trip(trip):
    dt = parse_trip_date((trip or {}).get("date")) or datetime.date.today()
    return WEEKDAY_FULL_DE[dt.weekday()]


def phone_memo_pdf_path(trip, grp):
    endstation = clean_endstation_for_phone(trip)
    weekday = weekday_full_for_trip(trip)
    mod_name = clean_module_name_for_phone(grp)
    fname = safe_name(f"Entspannt Reisen nach {endstation} am {weekday}, {mod_name}") + ".pdf"
    target_dir = ONEDRIVE_PHONE_DIR if os.path.isdir(ONEDRIVE_PHONE_DIR) else ROOT
    return os.path.join(target_dir, fname)


def current_reise_mappe_path(trip):
    date_slug = safe_name((trip or {}).get("date") or datetime.date.today().strftime("%Y-%m-%d"))
    return os.path.join(OUTPUT_ROOT, f"Reise-Mappe ({date_slug}).pdf")


def calendar_ics_path(trip):
    endstation = clean_endstation_for_phone(trip)
    weekday = weekday_full_for_trip(trip)
    dt = parse_trip_date((trip or {}).get("date")) or datetime.date.today()
    date_str = dt.strftime("%d.%m.%Y")
    fname = safe_name(f"Entspannt Reisen nach {endstation} am {weekday}, {date_str}") + ".ics"
    target_dir = ONEDRIVE_PHONE_DIR if os.path.isdir(ONEDRIVE_PHONE_DIR) else ROOT
    return os.path.join(target_dir, fname)


def write_trip_calendar_ics(trip, schedule_blocks, allocations, active_jobs, out_ics_path):
    """
    Erstellt eine standardkonforme .ics-Kalenderdatei (RFC 5545) für Apple Calendar / iOS:
    - Verwendet das exakte Reisedatum (z.B. Sa, 24.10.2026).
    - Erzeugt für jeden Zugabschnitt einen eigenen Termin mit minutengenauen Abfahrts- & Ankunftszeiten.
    - Trägt die genauen Lernmodule, Übungsblätter und den Zug-Modus (Sitzplatz, Stehplatz, Pause) als Beschreibung ein.
    - Setzt eine 15-Minuten-Abfahrts-Erinnerung (VALARM) für Apple Calendar.
    """
    dt_date = parse_trip_date((trip or {}).get("date")) or datetime.date.today()
    now_stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    legs = (trip or {}).get("legs") or []
    events = []

    def escape_ics(text):
        if not text:
            return ""
        return (
            str(text)
            .replace("\\", "\\\\")
            .replace(";", "\\;")
            .replace(",", "\\,")
            .replace("\r\n", "\n")
            .replace("\n", "\\n")
        )

    for idx, leg in enumerate(legs):
        tname = leg.get("train", f"Zug {idx + 1}")
        from_st = leg.get("from_station", "Start")
        to_st = leg.get("to_station", "Ziel")
        dep_s = leg.get("dep", "09:00")
        arr_s = leg.get("arr", "10:00")
        mode = leg.get("mode", "focus")
        dur = int(leg.get("duration_min") or diff_minutes(dep_s, arr_s, 45))

        dep_m = re.match(r"^(\d{1,2}):(\d{2})$", dep_s.strip())
        arr_m = re.match(r"^(\d{1,2}):(\d{2})$", arr_s.strip())
        dep_h = int(dep_m.group(1)) if dep_m else 9
        dep_min = int(dep_m.group(2)) if dep_m else 0
        arr_h = int(arr_m.group(1)) if arr_m else 10
        arr_min = int(arr_m.group(2)) if arr_m else 0

        dt_start = datetime.datetime(dt_date.year, dt_date.month, dt_date.day, dep_h, dep_min, 0)
        dt_end = datetime.datetime(dt_date.year, dt_date.month, dt_date.day, arr_h, arr_min, 0)
        if dt_end < dt_start:
            dt_end += datetime.timedelta(days=1)

        assigned_jobs = []
        for grp, item in (active_jobs or []):
            al = (allocations or {}).get(grp["id"])
            if al and idx in (al.get("leg_indices") or []):
                assigned_jobs.append(f"• {grp['icon']} {grp['module']} ({item['name']}) · {al['minutes']} Min.")

        mode_label = {
            "focus": "💻 Sitzplatz (Aufgaben)",
            "regio_memo": "🧠 Stehplatz (Theorie)",
            "rest": "☕ Pause (Nichts lernen)",
        }.get(mode, "💻 Sitzplatz (Aufgaben)")

        desc_lines = [
            f"🚆 {tname}: {from_st} ➔ {to_st}",
            f"🕒 Fahrtzeit: {dep_s} – {arr_s} Uhr ({dur} Min.)",
            f"🎯 Modus: {mode_label}",
            "",
        ]

        if assigned_jobs:
            desc_lines.append("📚 LERNSTOFF IN DIESEM ZUG:")
            desc_lines.extend(assigned_jobs)
        elif mode == "rest":
            desc_lines.append("☕ In diesem Zug wird nichts gelernt (Erholung / Pause).")
        else:
            desc_lines.append("📖 Lernpuffer / Wiederholung.")

        if idx < len(legs) - 1:
            nxt_leg = legs[idx + 1]
            tr_min = int(leg.get("transfer_after_min") or 10)
            desc_lines.append("")
            desc_lines.append(
                f"☕ Danach: {tr_min} Min. Umstieg in {to_st} auf {nxt_leg.get('train', 'Anschlusszug')} "
                f"(Abfahrt {nxt_leg.get('dep', '')} Uhr)"
            )
        else:
            desc_lines.append("")
            desc_lines.append(f"🏁 Endstation erreicht: {to_st} ({arr_s} Uhr). Gute Ankunft!")

        summary_txt = escape_ics(f"🚆 {tname}: {from_st} ➔ {to_st}")
        location_txt = escape_ics(f"{from_st} ➔ {to_st}")
        desc_txt = escape_ics("\n".join(desc_lines))
        uid = f"er-{dt_date.strftime('%Y%m%d')}-leg{idx + 1}-{dep_h:02d}{dep_min:02d}@uni-mannheim.de"

        ev = [
            "BEGIN:VEVENT",
            f"UID:{uid}",
            f"DTSTAMP:{now_stamp}",
            f"DTSTART;TZID=Europe/Berlin:{dt_start.strftime('%Y%m%dT%H%M%S')}",
            f"DTEND;TZID=Europe/Berlin:{dt_end.strftime('%Y%m%dT%H%M%S')}",
            f"SUMMARY:{summary_txt}",
            f"LOCATION:{location_txt}",
            f"DESCRIPTION:{desc_txt}",
            "STATUS:CONFIRMED",
            "BEGIN:VALARM",
            "TRIGGER:-PT15M",
            "ACTION:DISPLAY",
            f"DESCRIPTION:Abfahrt {tname} in 15 Min.",
            "END:VALARM",
            "END:VEVENT",
        ]
        events.append("\n".join(ev))

    cal_name = escape_ics(f"Entspannt Reisen nach {clean_endstation_for_phone(trip)} ({dt_date.strftime('%d.%m.%Y')})")
    ics_lines = [
        "BEGIN:VCALENDAR",
        "VERSION:2.0",
        "PRODID:-//Entspannt Reisen//Bahn Lernplaner//DE",
        "CALSCALE:GREGORIAN",
        "METHOD:PUBLISH",
        f"X-WR-CALNAME:{cal_name}",
        "X-WR-TIMEZONE:Europe/Berlin",
        "BEGIN:VTIMEZONE",
        "TZID:Europe/Berlin",
        "X-LIC-LOCATION:Europe/Berlin",
        "BEGIN:DAYLIGHT",
        "TZOFFSETFROM:+0100",
        "TZOFFSETTO:+0200",
        "TZNAME:CEST",
        "DTSTART:19700329T020000",
        "RRULE:FREQ=YEARLY;BYMONTH=3;BYDAY=-1SU",
        "END:DAYLIGHT",
        "BEGIN:STANDARD",
        "TZOFFSETFROM:+0200",
        "TZOFFSETTO:+0100",
        "TZNAME:CET",
        "DTSTART:19701025T030000",
        "RRULE:FREQ=YEARLY;BYMONTH=10;BYDAY=-1SU",
        "END:STANDARD",
        "END:VTIMEZONE",
        "\n".join(events),
        "END:VCALENDAR\n",
    ]

    os.makedirs(os.path.dirname(out_ics_path), exist_ok=True)
    with open(out_ics_path, "w", encoding="utf-8", newline="\r\n") as f:
        f.write("\n".join(ics_lines))



def collect_files(item):
    p = item["path"]
    candidates = []
    if os.path.isfile(p):
        candidates = [p]
    else:
        for dp, _, fns in os.walk(p):
            for fn in fns:
                candidates.append(os.path.join(dp, fn))
    candidates.sort(key=lambda x: natural_key(os.path.relpath(x, p) if os.path.isdir(p) else x))
    files, total = [], 0
    for c in candidates:
        ext = os.path.splitext(c)[1].lower()
        if ext != ".pdf" and ext not in TEXT_EXT:
            continue
        try:
            size = os.path.getsize(c)
        except OSError:
            continue
        if ext in TEXT_EXT and size > 300 * 1024:
            continue
        if total + size > MAX_TOTAL_BYTES or len(files) >= MAX_FILES:
            break
        files.append(c)
        total += size
    return files


def stage_files(files, workdir):
    staged = []
    for i, f in enumerate(files, 1):
        base = os.path.basename(f)
        stem, ext = os.path.splitext(base)
        stem = stem.replace("ä", "ae").replace("ö", "oe").replace("ü", "ue").replace("Ä", "Ae") \
                   .replace("Ö", "Oe").replace("Ü", "Ue").replace("ß", "ss")
        stem = re.sub(r"[^A-Za-z0-9._-]+", "_", stem).strip("_") or "datei"
        name = f"{i:02d}_{stem[:60]}{ext.lower()}"
        shutil.copy2(f, os.path.join(workdir, name))
        staged.append(name)
    return staged


# --------------------------------------------------------------------------
# Zeitangepasster KI-Prompt
# --------------------------------------------------------------------------
def build_prompt(grp, item, file_names, use_at_refs, allocation=None):
    if use_at_refs:
        files_txt = "\n".join(f"@{n}" for n in file_names)
    else:
        files_txt = "\n".join(f"- {n}" for n in file_names)

    gid = grp.get("id", "")
    is_coding = gid in ("pi1", "pp1_grosse_uebung", "pp1_projekt")
    is_business = gid in ("marketing", "wifo")
    is_fgdi = gid == "fgdi"

    if allocation:
        mins = allocation.get("minutes", 40)
        leg_title = allocation.get("leg_title", "Zugabschnitt")
        tw = allocation.get("time_window", "")
        mode = allocation.get("mode", "focus")
        is_memo = (mode == "regio_memo") or bool(allocation.get("is_phone_memo"))
        t1 = max(5, int(mins * 0.25))
        t2 = max(10, int(mins * 0.45))
        t3 = max(5, mins - t1 - t2)
        if is_memo:
            mode_hint = (
                "WICHTIG (HANDY-AUSWENDIGLERN-MODUS FÜR VOLLE BAHN / STEHPLATZ): Dieser Abschnitt findet im vollen Zug statt "
                "(KEIN Laptop möglich!). Dieses PDF wird direkt auf das Smartphone geladen. Lege maximalen Fokus auf "
                "einprägsame Merksätze, griffige Merksprüche, Definitionen, Übersichten und Schnell-Check-Fragen zum Auswendiglernen!"
            )
        elif mode == "focus":
            mode_hint = "Dieser Abschnitt findet in einem ruhigen Zugabschnitt statt (Laptop möglich, aber Zeit ist begrenzt)."
        else:
            mode_hint = "In diesem Abschnitt ist WENIG PLATZ (kein intensives Tippen am Laptop möglich – gestalte alle Lösungen so, dass man sie rein durch Lesen & Mitdenken komplett versteht!)."
        time_instructions = f"""
WICHTIG – ZEITBUDGET FÜR DIESE BAHNFAHRT:
- Geplant für: **{leg_title}** ({tw})
- Exaktes Netto-Zeitbudget für dieses Lernblatt: **{mins} Minuten**
- {mode_hint}
- Schreibe hinter jede Hauptüberschrift den geplanten Zeitrichtwert (z. B. `⏱️ {t1} Min.`, `⏱️ {t2} Min.`, `⏱️ {t3} Min.`), sodass die Summe exakt **{mins} Minuten** ergibt.
"""
    else:
        mins = 45
        t1, t2, t3 = 12, 20, 13
        time_instructions = ""

    if is_coding:
        subject_guide = """
DIDAKTISCHER FOKUS (PROGRAMMIEREN: Praktische Informatik / Programmierpraktikum):
- Der Leser muss den Code VOLLSTÄNDIG VERSTEHEN, OHNE die Vorlesung dazu gehört oder gesehen zu haben!
- Erkläre komplexe Code-Passagen, Algorithmen, Datenstrukturen und Speicherzugriffe immer mit anschaulichen ALLTAGSBEISPIELEN (z. B. Postfiliale, Kochrezept, Bücherregal, Ticketautomat – greifbar, alltagsnah, aber nicht zu weit hergeholt).
- Nutze für Alltags-Analogien und Fallen farbige Callout-Boxen als Blockquote:
  - `> **🏠 Alltags-Beispiel:** ...` (wird im PDF als grüne Analogie-Box gerendert)
  - `> **⚠️ Typische Klausur- & Code-Falle:** ...` (wird im PDF als rote Warn-Box gerendert)
  - `> **💡 Merksatz:** ...` (wird im PDF als gelbe Merksatz-Box gerendert)
- Visualisiere Programmabläufe, Zeiger/Datenstrukturen oder Zustandsübergänge mindestens 1x als echtes Mermaid-Diagramm (````mermaid` mit `flowchart LR` oder `flowchart TD`, Knoten-Labels mit Sonderzeichen in Anführungszeichen setzen, z. B. `A["Start (init)"] --> B["Schleife"]`).
- Zeige den Code VOLLSTÄNDIG (keine faulen Auslassungen wie `// TODO: hier implementieren`).
- Kommentiere Code-Zeilen ausführlich und erkläre Zeile für Zeile, WAS dort geschieht und WARUM.
"""
    elif is_business:
        subject_guide = """
DIDAKTISCHER FOKUS (AUSWENDIGLERNEN: Wirtschaftsinformatik / Marketing):
- Bereite den gesamten Stoff optimal zum schnellen, nachhaltigen AUSWENDIGLERNEN auf!
- Nutze farbige Callout-Boxen als Blockquote für Definitionen und Merksprüche:
  - `> **📖 Definition:** ...` (wird im PDF als blaue Definitions-Box hervorgehoben)
  - `> **💡 Merksatz / Eselsbrücke:** ...` (wird im PDF als gelbe Spick-Box hervorgehoben)
  - `> **🏠 Praxis- & Alltags-Beispiel:** ...` (wird im PDF als grüne Praxis-Box hervorgehoben)
- Erstelle mindestens 1–2 visuelle MINDMAPS / ÜBERSICHTS-DIAGRAMME als echte Mermaid-Grafik (````mermaid` mit `flowchart LR` oder `flowchart TD`, Knoten-Labels in Anführungszeichen `A["Kernbegriff"] --> B["Teilbereich"]`) UND ergänze kompakte ASCII-/Baum-Übersichten.
- Verwende strukturierte TABELLEN (z. B. `| Konzept / Begriff | Definition | Praxis-Beispiel | Klausurtipp / Merksatz |`), damit alles sofort visuell erfassbar ist.
"""
    elif is_fgdi:
        subject_guide = """
DIDAKTISCHER FOKUS (VERSTÄNDNIS VOR FORMELN: Formale Grundlagen der Informatik):
- Bei FGdI steht VERSTÄNDLICHKEIT im Vordergrund, nicht nur das Abspulen formaler Aufgaben!
- Jedes mathematische Symbol (Mengenlehre, Relationen, Prädikatenlogik, Beweisoperatoren) in verständlicher Sprache erklären („Was bedeutet das auf Deutsch?“) – gerne als Übersetzungstabelle `| Mathematische Notation | Bedeutung auf Deutsch | Anschauliches Beispiel |`.
- Nutze farbige Callout-Boxen als Blockquote:
  - `> **🏠 Intuition & Alltags-Analogie:** ...` (z. B. Dominosteine bei vollständiger Induktion)
  - `> **📖 Formale Definition:** ...`
  - `> **⚠️ Typische Beweis-Falle:** ...`
- Visualisiere Beweisstrukturen, Relationseigenschaften oder Automaten/Logikbäume mit einem Mermaid-Diagramm (````mermaid` mit `flowchart LR` oder `flowchart TD`, Labels in Anführungszeichen).
- Gliedere Aufgaben/Beweise immer in:
  1. Intuition & Grundidee („Was wollen wir eigentlich zeigen und warum ist das logisch?“)
  2. Lückenloser, mathematischer Schritt-für-Schritt-Weg mit LaTeX ($...$, $$...$$)
  3. Fazit & Merksatz für die Klausur.
"""
    else:
        subject_guide = """
DIDAKTISCHER FOKUS:
- Maximale Verständlichkeit, klare Gliederung, Mermaid-Übersichten und alltagsnahe Beispiele.
"""

    return f"""Du bist ein exzellenter Universitätstutor und Didaktik-Experte. Erstelle eine perfekt auf eine Bahnfahrt abgestimmte,
sehr ausführliche, glasklar verständliche Lernzusammenfassung auf Deutsch für die Übung „{item['name']}“ aus dem Modul „{grp['module']}“ ({grp['category']}).
Die Zusammenfassung wird offline im Zug gelesen – sie muss komplett OHNE Vorlesungsfolien und OHNE Originaldateien aus sich selbst heraus verständlich sein.
Das PDF darf und soll AUSFÜHRLICH UND LANG sein – kürze nichts weg!

{time_instructions}
{subject_guide}

WICHTIGE ANTI-ABSCHNEIDE-REGELN (VOLLSTÄNDIGKEITS-GARANTIE):
- Beginne DIREKT mit der Hauptüberschrift `# {item['name']} – {grp['module']}` in der ALLERERSTEN Zeile (kein Vorgeplänkel wie „Hier ist...“, kein Begrüßungstext, keine Triple-Backticks am Anfang).
- Schließe am Ende NIEMALS mitten im Satz ab! Beende das Dokument IMMER mit dem Abschnitt `## 🏁 Zusammenfassung & Checkliste` und setze als allerletzte Zeile `---` gefolgt von `*Entspannt Reisen · Lernblatt vollständig abgeschlossen.*`.
- Wenn Code oder Tabellen gezeigt werden, schließe alle Codeblöcke (```) und Tabellenzeilen sauber ab.

Unterlagen (alle vollständig lesen, inkl. Lösungsdateien falls vorhanden):
{files_txt}

Gliederung (Markdown):
# {item['name']} – {grp['module']}

> **🚆 Reise-Fokus ({mins} Min. Lernzeit):** 3-Schritte-Fahrplan für diese Übung (Was zuerst lesen, worauf bei den Aufgaben achten, was für den Regio-Abschnitt merken).

## 🎯 Überblick & Kernthemen (⏱️ {t1} Min.)
Worum geht es, Lernziele, theoretische Grundlagen kompakt, anschaulich und mit alltagsnahen Analogien erklärt.

## 📝 Aufgaben mit komplettem Lösungsweg (⏱️ {t2} Min.)
Für JEDE Aufgabe aus den Unterlagen:
- Kurze, verständliche Aufgabenstellung.
- Schritt-für-Schritt-Lösungsweg mit ausführlicher Erklärung der Denkschritte.
- Bei Code: Vollständiger, lauffähiger Code mit erklärenden Kommentaren und Alltags-Analogie für komplexe Stellen.
- Bei Rechnungen/Beweisen: Jeder Zwischenschritt mit LaTeX ($...$, $$...$$).

## 🧮 Wichtige Formeln, Definitionen & Schemata (⏱️ {t3} Min.)
- Alle Kernformeln oder Definitionen sauber aufgeführt und symbolgenau erklärt.
- Strukturierte Übersicht / Mindmap-Baum oder Vergleichstabelle.

## 📱 Regio-Spickkarten (Für Smartphone & volle Bahnen – OHNE Laptop zum Auswendiglernen!)
*(Speziell für das Handy im vollen Zug: Merksätze, Begriffe & Blitz-Check!)*
- **💡 Top-8 Merksätze & Merksprüche** (fettgedruckt, eingängig, ideal zum Auswendiglernen)
- **📖 Wichtige Begriffe & Definitionen** als Tabelle `| Begriff / Konzept | Definition & Alltags-Merksatz |`
- **🧠 6 Schnell-Check-Fragen (mit kurzer Antwort direkt darunter)** zum stillen Selbsttest im Kopf.

## 🏁 Zusammenfassung & Checkliste
- Die 3 wichtigsten Takeaways für die Klausur auf den Punkt gebracht.
- Kurze Checkliste („Das kann ich jetzt“).

---
*Entspannt Reisen · Lernblatt vollständig abgeschlossen.*

Regeln: Gib AUSSCHLIESSLICH das fertige Markdown aus – keine Einleitung, keine Rückfragen, keine Metakommentare über dich.
"""


def clean_markdown(text):
    text = (text or "").strip()
    m = re.search(r"^# ", text, re.M)
    if m and m.start() > 0:
        text = text[m.start():]
    if text.startswith("```markdown"):
        text = text[len("```markdown"):].strip()
    elif text.startswith("```"):
        text = re.sub(r"^```[a-zA-Z0-9_-]*\n", "", text).strip()
    if text.endswith("```"):
        text = text[:-3].strip()

    # Schutz vor unvollstaendigen Code-Bloecken am Textende
    fence_count = len(re.findall(r"^```", text, flags=re.M))
    if fence_count % 2 != 0:
        text += "\n```\n"

    # Falls das Dokument am Ende unvollstaendig ist (kein Footer), sauberen Abschluss anfuegen
    footer = "*Entspannt Reisen · Lernblatt vollständig abgeschlossen.*"
    if footer not in text:
        text = text.rstrip() + "\n\n---\n" + footer + "\n"

    return text


# --------------------------------------------------------------------------
# KI-Anbieter
# --------------------------------------------------------------------------
def agy_cli_entry():
    exe = shutil.which("agy")
    return [exe] if exe else None


def gemini_cli_entry():
    exe = shutil.which("gemini")
    if not exe:
        return None
    d = os.path.dirname(exe)
    js = os.path.join(d, "node_modules", "@google", "gemini-cli", "bundle", "gemini.js")
    node = shutil.which("node")
    if os.path.isfile(js) and node:
        return [node, js]
    return [exe]


def gemini_cli_logged_in():
    home = os.path.expanduser("~")
    return (os.path.isfile(os.path.join(home, ".gemini", "oauth_creds.json"))
            or bool(os.environ.get("GEMINI_API_KEY")) or bool(os.environ.get("GOOGLE_API_KEY")))


def claude_cli_entry():
    exe = shutil.which("claude")
    return [exe] if exe else None


def detect_providers(cfg):
    res = []
    # 1. Antigravity CLI mit Gemini 4 Argon (Höchste Priorität & beste Qualität)
    agy = agy_cli_entry()
    argon_model = cfg.get("gemini_cli_model") or "gemini-4-argon-medium"
    if "argon" not in argon_model and argon_model in ("pro", "auto"):
        argon_model = "gemini-4-argon-medium"
    if agy:
        res.append(("agy_cli", f"Gemini 4 Argon (Antigravity · {argon_model})", True, ""))
    else:
        res.append(("agy_cli", "Gemini 4 Argon (Antigravity CLI)", False, "nicht im PATH"))

    # 2. Bestehende Fallbacks
    g = gemini_cli_entry()
    if g and gemini_cli_logged_in():
        res.append(("gemini_cli", f"Gemini CLI (Modell: {cfg['gemini_cli_model']})", True, ""))
    elif g:
        res.append(("gemini_cli", "Gemini CLI", False, "installiert, aber noch nicht angemeldet"))
    else:
        res.append(("gemini_cli", "Gemini CLI", False, "nicht installiert"))
    gkey = cfg.get("gemini_api_key") or os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    res.append(("gemini_api", "Gemini API (bestes Pro-Modell)", bool(gkey), "" if gkey else "kein Schlüssel"))
    c = claude_cli_entry()
    res.append(("claude_cli", f"Claude CLI (Modell: {cfg['claude_cli_model']})", bool(c), "" if c else "nicht installiert"))
    akey = cfg.get("anthropic_api_key") or os.environ.get("ANTHROPIC_API_KEY")
    res.append(("claude_api", "Claude API (bestes Opus-Modell)", bool(akey), "" if akey else "kein Schlüssel"))
    return res


def run_cli(cmd, prompt, workdir, timeout=1200, min_len=200):
    p = subprocess.run(cmd, input=prompt, cwd=workdir, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", timeout=timeout, creationflags=NO_WINDOW)
    out = (p.stdout or "").strip()
    if p.returncode != 0 or len(out) < min_len:
        err = (p.stderr or "").strip()[-1500:]
        raise RuntimeError(f"Exit-Code {p.returncode}. {err or out[-800:]}")
    return out


def summarize_agy_cli(cfg, prompt, workdir, log, min_len=200):
    model = cfg.get("gemini_cli_model") or "gemini-4-argon-medium"
    if "argon" not in model and model in ("pro", "auto"):
        model = "gemini-4-argon-medium"
    cmd = [
        "agy",
        "--add-dir", workdir,
        "--model", model,
        "--dangerously-skip-permissions",
        "--print", prompt,
    ]
    log(f"   🤖 Antigravity CLI, Modell {model} (Gemini 4 Argon) läuft …")
    return run_cli(cmd, "", workdir, timeout=1200, min_len=min_len)


def summarize_gemini_cli(cfg, prompt, workdir, log, min_len=200):
    base = gemini_cli_entry()
    models = [cfg.get("gemini_cli_model") or "pro"]
    if models[0] != "pro":
        models.append("pro")
    models.append(None)
    last = None
    for m in models:
        cmd = base + ["-p", "Erstelle jetzt die angeforderte Ausgabe.", "--approval-mode", "plan"]
        if m:
            cmd += ["-m", m]
        try:
            log(f"   → Gemini CLI, Modell {m or 'Standard'} …")
            return run_cli(cmd, prompt, workdir, min_len=min_len)
        except Exception as e:
            last = e
            try:
                cmd2 = [c for c in cmd if c not in ("--approval-mode", "plan")]
                return run_cli(cmd2, prompt, workdir, min_len=min_len)
            except Exception as e2:
                last = e2
                log(f"   ⚠ fehlgeschlagen: {str(e2)[:200]}")
    raise RuntimeError(f"Gemini CLI fehlgeschlagen: {last}")


def summarize_claude_cli(cfg, prompt, workdir, log, min_len=200):
    cmd = claude_cli_entry() + ["-p", "--model", cfg.get("claude_cli_model") or "opus",
                                "--allowedTools", "Read", "--output-format", "text"]
    log(f"   → Claude CLI, Modell {cfg.get('claude_cli_model') or 'opus'} …")
    return run_cli(cmd, prompt, workdir, min_len=min_len)


def http_json(url, payload=None, headers=None, timeout=900):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json", **(headers or {})})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP {e.code}: {e.read().decode('utf-8', 'replace')[:600]}")


def version_score(name):
    nums = re.findall(r"\d+(?:\.\d+)?", name)
    v = float(nums[0]) if nums else 0.0
    penalty = 0.01 if ("preview" in name or "exp" in name) else 0.0
    return v - penalty


def best_gemini_model(key):
    data = http_json(f"https://generativelanguage.googleapis.com/v1beta/models?key={key}&pageSize=200")
    cands = []
    for m in data.get("models", []):
        n = m.get("name", "").replace("models/", "")
        if "generateContent" not in m.get("supportedGenerationMethods", []):
            continue
        if "pro" in n and not any(x in n for x in ("tts", "image", "vision", "embedding", "audio", "computer")):
            cands.append(n)
    if not cands:
        return "gemini-2.5-pro"
    return max(cands, key=version_score)


def summarize_gemini_api(cfg, prompt, workdir, file_names, log):
    key = cfg.get("gemini_api_key") or os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    model = best_gemini_model(key)
    log(f"   → Gemini API, Modell {model} …")
    parts = [{"text": prompt}]
    for n in file_names:
        fp = os.path.join(workdir, n)
        if n.lower().endswith(".pdf"):
            with open(fp, "rb") as f:
                parts.append({"inline_data": {"mime_type": "application/pdf", "data": base64.b64encode(f.read()).decode()}})
        else:
            with open(fp, "r", encoding="utf-8", errors="replace") as f:
                parts.append({"text": f"--- Datei {n} ---\n{f.read()}"})
    data = http_json(f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={key}",
                     {"contents": [{"role": "user", "parts": parts}]})
    try:
        return "".join(p.get("text", "") for p in data["candidates"][0]["content"]["parts"])
    except Exception:
        raise RuntimeError(f"Unerwartete Antwort: {str(data)[:500]}")


def summarize_claude_api(cfg, prompt, workdir, file_names, log):
    key = cfg.get("anthropic_api_key") or os.environ.get("ANTHROPIC_API_KEY")
    hdr = {"x-api-key": key, "anthropic-version": "2023-06-01"}
    try:
        models = [m["id"] for m in http_json("https://api.anthropic.com/v1/models?limit=100", headers=hdr).get("data", [])]
        opus = [m for m in models if "opus" in m]
        model = opus[0] if opus else (models[0] if models else "claude-opus-4-1")
    except Exception:
        model = "claude-opus-4-1"
    log(f"   → Claude API, Modell {model} …")
    content = []
    for n in file_names:
        fp = os.path.join(workdir, n)
        if n.lower().endswith(".pdf"):
            with open(fp, "rb") as f:
                content.append({"type": "document", "source": {"type": "base64", "media_type": "application/pdf",
                                                               "data": base64.b64encode(f.read()).decode()}})
        else:
            with open(fp, "r", encoding="utf-8", errors="replace") as f:
                content.append({"type": "text", "text": f"--- Datei {n} ---\n{f.read()}"})
    content.append({"type": "text", "text": prompt})
    data = http_json("https://api.anthropic.com/v1/messages",
                     {"model": model, "max_tokens": 16000, "messages": [{"role": "user", "content": content}]},
                     headers=hdr)
    return "".join(b.get("text", "") for b in data.get("content", []) if b.get("type") == "text")


def summarize(cfg, grp, item, log, allocation=None):
    files = collect_files(item)
    if not files:
        raise RuntimeError("Keine PDFs/Textdateien in dieser Übung gefunden.")
    log(f"   {len(files)} Datei(en): " + ", ".join(os.path.basename(f) for f in files))
    providers = detect_providers(cfg)
    avail = [p[0] for p in providers if p[2]]
    order = avail if cfg["provider"] == "auto" else [cfg["provider"]]
    if not order:
        raise RuntimeError("Keine KI verfügbar. Bitte in den Einstellungen Gemini anmelden oder einen Schlüssel eintragen.")
    workdir = tempfile.mkdtemp(prefix="entspannt_reisen_")
    try:
        names = stage_files(files, workdir)
        errors = []
        for pid in order:
            try:
                if pid == "agy_cli":
                    md = summarize_agy_cli(cfg, build_prompt(grp, item, names, True, allocation), workdir, log)
                elif pid == "gemini_cli":
                    md = summarize_gemini_cli(cfg, build_prompt(grp, item, names, True, allocation), workdir, log)
                elif pid == "claude_cli":
                    md = summarize_claude_cli(cfg, build_prompt(grp, item, names, False, allocation), workdir, log)
                elif pid == "gemini_api":
                    md = summarize_gemini_api(cfg, build_prompt(grp, item, names, False, allocation), workdir, names, log)
                elif pid == "claude_api":
                    md = summarize_claude_api(cfg, build_prompt(grp, item, names, False, allocation), workdir, names, log)
                else:
                    continue
                md = clean_markdown(md)
                if len(md) < 200:
                    raise RuntimeError("Antwort zu kurz.")
                return md, pid
            except Exception as e:
                errors.append(f"{pid}: {e}")
                log(f"   ⚠ {pid} fehlgeschlagen – versuche nächste KI …")
        raise RuntimeError("Alle KIs fehlgeschlagen:\n" + "\n".join(errors))
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


# --------------------------------------------------------------------------
# Markdown & Reise-Zeitplan → PDF
# --------------------------------------------------------------------------
HTML_TEMPLATE = """<!DOCTYPE html><html lang="de"><head><meta charset="utf-8">
<title>{title}</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/gh/highlightjs/cdn-release@11.9.0/build/styles/github-dark.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"
 onload="renderMathInElement(document.body,{{delimiters:[{{left:'$$',right:'$$',display:true}},{{left:'\\[',right:'\\]',display:true}},{{left:'$',right:'$',display:false}},{{left:'\\(',right:'\\)',display:false}}],throwOnError:false}});"></script>
<script defer src="https://cdn.jsdelivr.net/gh/highlightjs/cdn-release@11.9.0/build/highlight.min.js"
 onload="if(window.hljs){{hljs.highlightAll();}}"></script>
<script src="https://cdn.jsdelivr.net/npm/mermaid@10.9.1/dist/mermaid.min.js"></script>
<script>
document.addEventListener("DOMContentLoaded", function() {{
  if (window.mermaid) {{
    mermaid.initialize({{
      startOnLoad: true,
      theme: "neutral",
      securityLevel: "loose",
      flowchart: {{ useMaxWidth: true, htmlLabels: true, curve: "basis" }}
    }});
  }}
}});
</script>
<style>
* {{ -webkit-print-color-adjust: exact !important; print-color-adjust: exact !important; box-sizing: border-box; }}
@page {{
  size: A4 portrait;
  margin: 14mm 14mm 16mm 14mm;
  @bottom-right {{
    content: "Seite " counter(page) " von " counter(pages);
    font-family: FONT_BODY, Calibri, Arial, sans-serif;
    font-size: 8.5pt;
    color: #64748b;
  }}
  @bottom-left {{
    content: "🧳 Entspannt Reisen · Offline-Lernblatt";
    font-family: FONT_BODY, Calibri, Arial, sans-serif;
    font-size: 8.5pt;
    color: #94a3b8;
  }}
}}
body {{ font-family: FONT_BODY, Calibri, Arial, sans-serif; font-size: 10pt; line-height: 1.56; color: #262b36; }}
h1 {{ font-size: 18.5pt; color: #0f172a; border-bottom: 3px solid #0ea5e9; padding-bottom: 6px; margin-top: 0; margin-bottom: 12px; page-break-after: avoid; break-after: avoid; }}
h2 {{ font-size: 13.5pt; color: #0369a1; margin-top: 22px; margin-bottom: 8px; border-bottom: 1.5px solid #bae6fd; padding-bottom: 4px; page-break-after: avoid; break-after: avoid; background: linear-gradient(90deg, #f0f9ff 0%, #ffffff 100%); padding-left: 8px; border-left: 4px solid #0284c7; border-radius: 4px; }}
h3 {{ font-size: 11.2pt; color: #0f172a; margin-top: 15px; margin-bottom: 6px; page-break-after: avoid; break-after: avoid; }}
h4 {{ font-size: 10.2pt; color: #343b4a; margin-top: 10px; margin-bottom: 4px; page-break-after: avoid; break-after: avoid; }}
p, li {{ orphans: 3; widows: 3; }}
ul, ol {{ margin-top: 4px; margin-bottom: 8px; padding-left: 20px; }}
li {{ margin-bottom: 3px; }}
code {{ font-family: Consolas, "Cascadia Code", monospace; background: #f1f5f9; color: #0f172a; padding: 1.5px 5px; border-radius: 4px; font-size: 9pt; border: 1px solid #e2e8f0; }}
pre {{ background: #0f172a !important; color: #f8fafc !important; padding: 12px 14px; border-radius: 8px; font-size: 8.8pt; line-height: 1.45; white-space: pre-wrap !important; word-wrap: break-word !important; overflow-wrap: anywhere; page-break-inside: avoid; break-inside: avoid; border-left: 4px solid #38bdf8; margin: 10px 0; box-shadow: 0 1px 3px rgba(0,0,0,0.12); }}
pre code, pre code.hljs {{ background: transparent !important; color: inherit !important; padding: 0 !important; border: none !important; font-size: inherit !important; white-space: pre-wrap !important; }}
table {{ border-collapse: collapse; width: 100%; margin: 12px 0; page-break-inside: auto; font-size: 9.3pt; border-radius: 6px; overflow: hidden; }}
thead {{ display: table-header-group; }}
tfoot {{ display: table-footer-group; }}
tr {{ page-break-inside: avoid; break-inside: avoid; }}
th, td {{ border: 1px solid #cbd5e1; padding: 6.5px 10px; vertical-align: top; text-align: left; }}
th {{ background: #e0f2fe !important; color: #0369a1 !important; font-weight: bold; }}
tr:nth-child(even) td {{ background: #f8fafc; }}
blockquote {{ border-left: 4px solid #0ea5e9; background: #f0f9ff; margin: 11px 0; padding: 9px 14px; border-radius: 0 8px 8px 0; font-size: 9.6pt; page-break-inside: avoid; break-inside: avoid; }}
blockquote p {{ margin: 4px 0; }}
blockquote.callout-memo {{ border-left: 5px solid #f59e0b; background: #fffbeb; color: #78350f; }}
blockquote.callout-analogy {{ border-left: 5px solid #10b981; background: #ecfdf5; color: #064e3b; }}
blockquote.callout-warn {{ border-left: 5px solid #f43f5e; background: #fff1f2; color: #881337; }}
blockquote.callout-def {{ border-left: 5px solid #0284c7; background: #f0f9ff; color: #0c4a6e; }}
.mermaid-box {{ background: #ffffff; border: 1.5px solid #cbd5e1; border-radius: 10px; padding: 12px 14px; margin: 12px 0; text-align: center; page-break-inside: avoid; break-inside: avoid; }}
.mermaid {{ display: flex; justify-content: center; max-width: 100% !important; page-break-inside: avoid; break-inside: avoid; }}
.mermaid svg {{ max-width: 100% !important; height: auto !important; }}
.meta {{ color: #64748b; font-size: 8.5pt; margin-bottom: 14px; padding-bottom: 6px; border-bottom: 1px solid #e2e8f0; }}
.katex {{ font-size: 1.04em; }}
.katex-display {{ overflow-x: hidden; overflow-y: hidden; margin: 10px 0; padding: 6px 10px; background: #f8fafc; border-left: 3px solid #94a3b8; border-radius: 4px; page-break-inside: avoid; break-inside: avoid; }}
.schedule-box {{ background: #f8fafc; border: 2px solid #0ea5e9; border-radius: 10px; padding: 14px 16px; margin-bottom: 18px; page-break-inside: avoid; break-inside: avoid; }}
.timeline-item {{ border-left: 4px solid #0ea5e9; padding: 8px 12px; margin: 10px 0; background: #ffffff; border-radius: 0 8px 8px 0; box-shadow: 0 1px 3px rgba(0,0,0,0.06); page-break-inside: avoid; break-inside: avoid; }}
.timeline-break {{ border-left-color: #16a34a; background: #f0fdf4; }}
.timeline-regio {{ border-left-color: #f59e0b; background: #fffbeb; }}
.page-break {{ page-break-before: always; break-before: page; }}
.section-banner {{ background: #0f172a; color: #ffffff; padding: 12px 18px; border-radius: 8px; margin-bottom: 14px; page-break-inside: avoid; break-inside: avoid; }}
.section-banner .sub {{ color: #38bdf8; font-size: 9.5pt; margin-top: 3px; }}
</style></head><body>
{body}
</body></html>"""

MATH_RE = re.compile(r"(\$\$.+?\$\$|\\\[.+?\\\]|\\\(.+?\\\)|(?<![\\$])\$(?!\s)[^$\n]+?(?<!\s)\$)", re.S)
MERMAID_BLOCK_RE = re.compile(r"```mermaid\s*\n(.*?)```", re.S | re.I)


def markdown_to_html(md_text):
    mermaids = []

    def protect_mermaid(m):
        code = m.group(1).strip()
        mermaids.append(code)
        return f"\n\nMERMAIDPLACEHOLDER{len(mermaids) - 1}X\n\n"

    md_no_mermaid = MERMAID_BLOCK_RE.sub(protect_mermaid, md_text or "")

    maths = []

    def protect(m):
        maths.append(m.group(0))
        return f"MATHPLACEHOLDER{len(maths) - 1}X"

    chunks = re.split(r"(```.*?```|`[^`\n]+`)", md_no_mermaid, flags=re.S)
    for i in range(0, len(chunks), 2):
        chunks[i] = MATH_RE.sub(protect, chunks[i])
    protected = "".join(chunks)
    try:
        import markdown
        body = markdown.markdown(protected, extensions=["tables", "fenced_code", "sane_lists", "nl2br"])
    except ImportError:
        body = "<pre>" + html.escape(protected) + "</pre>"

    for i, m in enumerate(maths):
        body = body.replace(f"MATHPLACEHOLDER{i}X", html.escape(m))

    for i, m_code in enumerate(mermaids):
        mermaid_html = f'<div class="mermaid-box"><div class="mermaid">{html.escape(m_code)}</div></div>'
        body = re.sub(rf"<p>\s*MERMAIDPLACEHOLDER{i}X\s*</p>", lambda _: mermaid_html, body)
        body = body.replace(f"MERMAIDPLACEHOLDER{i}X", mermaid_html)

    def _classify_callout(html_fragment):
        plain = re.sub(r"<[^>]+>", "", html_fragment).strip()
        if any(plain.startswith(x) for x in ("💡", "Merksatz", "Merkspruch", "Eselsbrücke", "Tipp")):
            return ' class="callout-memo"'
        if any(plain.startswith(x) for x in ("🏠", "🌍", "Alltags", "Analogie", "Praxis", "Vorstellung")):
            return ' class="callout-analogy"'
        if any(plain.startswith(x) for x in ("⚠️", "⚠", "Achtung", "Klausur-Falle", "Typische", "Falle", "Vorsicht")):
            return ' class="callout-warn"'
        if any(plain.startswith(x) for x in ("📖", "📌", "Definition", "Formale Definition")):
            return ' class="callout-def"'
        return ""

    def style_blockquote(m):
        inner = m.group(1).strip()
        paras = re.findall(r"<p>.*?</p>", inner, flags=re.S)
        if len(paras) > 1 and any(_classify_callout(p) for p in paras):
            out_boxes = []
            for p in paras:
                c = _classify_callout(p)
                out_boxes.append(f"<blockquote{c}>{p}</blockquote>")
            return "\n".join(out_boxes)
        cls = _classify_callout(inner)
        return f"<blockquote{cls}>{inner}</blockquote>"

    body = re.sub(r"<blockquote>(.*?)</blockquote>", style_blockquote, body, flags=re.S)
    return body


def extract_regio_pocket_markdown(md_text):
    m = re.search(r"(##\s*📱.*)", md_text, re.S)
    if m:
        return m.group(1).strip()
    m2 = re.search(r"(##\s*💡.*)", md_text, re.S)
    return m2.group(1).strip() if m2 else ""


def render_schedule_html(trip, schedule_blocks):
    rows = []
    for b in schedule_blocks:
        kind = b.get("kind", "study")
        cls = "timeline-item"
        if kind in ("transfer_break", "break"):
            cls += " timeline-break"
        elif kind == "regio_memo":
            cls += " timeline-regio"
        rows.append(f"""
        <div class="{cls}">
            <div style="display:flex;justify-content:space-between;font-weight:bold;color:#0f172a;font-size:11pt;">
                <span>{html.escape(b.get('title', ''))}</span>
                <span style="color:#0284c7;">⏱️ {html.escape(b.get('time', ''))} ({b.get('duration_min', 0)} Min.)</span>
            </div>
            <div style="font-size:9.5pt;color:#475569;margin-top:2px;">{html.escape(b.get('subtitle', ''))}</div>
            <div style="font-size:9.5pt;color:#0f172a;margin-top:4px;">👉 <b>Empfehlung:</b> {html.escape(b.get('advice', ''))}</div>
        </div>
        """)
    return f"""
    <h1>🧳 Entspannt Reisen – Dein Bahn-Zeitplan & Lernmappe</h1>
    <div class="schedule-box">
        <div style="font-size:12pt;font-weight:bold;color:#0f172a;">🚆 {html.escape(trip.get('title', 'Bevorstehende Fahrt'))}</div>
        <div style="font-size:9.5pt;color:#475569;margin-top:2px;">
            Datum: <b>{html.escape(trip.get('date', ''))}</b> · Quelle: {html.escape(trip.get('source', 'DB-Konto'))}
        </div>
        <div style="font-size:9.5pt;color:#0369a1;margin-top:8px;">
            <b>Goldene Regeln für diese Fahrt:</b>
            Normale Umstiege sind feste Lernpausen ☕. Lange Umstiege (ab 25 Min.) geben dir 15 Min. Pause + einen Wartezeit-Lernblock 📖.
            In der mittleren Regio-Verbindung bleibt der Laptop eingepackt 📱 (nur Regio-Spickkarten oder Pause!).
        </div>
    </div>
    <h2>📅 Dein Ablaufplan von Start bis Ziel</h2>
    {''.join(rows)}
    """


def find_browser():
    cands = [
        os.path.join(os.environ.get("ProgramFiles(x86)", ""), "Microsoft", "Edge", "Application", "msedge.exe"),
        os.path.join(os.environ.get("ProgramFiles", ""), "Microsoft", "Edge", "Application", "msedge.exe"),
        os.path.join(os.environ.get("ProgramFiles", ""), "Google", "Chrome", "Application", "chrome.exe"),
        os.path.join(os.environ.get("LOCALAPPDATA", ""), "Google", "Chrome", "Application", "chrome.exe"),
    ]
    return next((c for c in cands if os.path.isfile(c)), None)


def html_to_pdf(full_html_doc, out_pdf):
    os.makedirs(os.path.dirname(out_pdf), exist_ok=True)
    browser = find_browser()
    if not browser:
        html_out = os.path.splitext(out_pdf)[0] + ".html"
        with open(html_out, "w", encoding="utf-8") as f:
            f.write(full_html_doc)
        raise RuntimeError("Kein Edge/Chrome gefunden – HTML gespeichert statt PDF.")
    tmp = tempfile.mkdtemp(prefix="er_pdf_")
    try:
        h = os.path.join(tmp, "doc.html")
        p = os.path.join(tmp, "doc.pdf")
        with open(h, "w", encoding="utf-8") as f:
            f.write(full_html_doc)
        cmd = [browser, "--headless=new", "--disable-gpu", "--no-first-run", "--no-pdf-header-footer",
               f"--user-data-dir={os.path.join(tmp, 'profile')}", "--virtual-time-budget=25000",
               "--run-all-compositor-stages-before-draw", f"--print-to-pdf={p}", "file:///" + h.replace("\\", "/")]
        subprocess.run(cmd, capture_output=True, timeout=180, creationflags=NO_WINDOW)
        if not os.path.isfile(p) or os.path.getsize(p) < 1000:
            raise RuntimeError("PDF-Erstellung mit dem Browser fehlgeschlagen.")
        shutil.copyfile(p, out_pdf)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def write_pdf(md_text, out_pdf, grp, provider, allocation=None):
    os.makedirs(os.path.dirname(out_pdf), exist_ok=True)
    title = md_text.splitlines()[0].lstrip("# ").strip() if md_text else "Zusammenfassung"
    alloc_info = ""
    if allocation:
        alloc_info = (
            f" · 🚆 Geplant für: <b>{html.escape(allocation.get('leg_title', ''))}</b> "
            f"({html.escape(allocation.get('time_window', ''))}, Budget: <b>{allocation.get('minutes', 40)} Min.</b>)"
        )
    header_html = f'<div class="meta">🧳 Entspannt Reisen · {html.escape(grp["module"])} · erstellt am {time.strftime("%d.%m.%Y %H:%M")} mit {html.escape(provider)}{alloc_info}</div>'
    doc = HTML_TEMPLATE.format(title=html.escape(title), body=header_html + markdown_to_html(md_text))
    md_path = os.path.splitext(out_pdf)[0] + ".md"
    with open(md_path, "w", encoding="utf-8") as f:
        f.write(md_text)
    html_to_pdf(doc, out_pdf)


def write_phone_memo_pdf(md_text, out_pdf, trip, grp, item, provider, allocation=None):
    os.makedirs(os.path.dirname(out_pdf), exist_ok=True)
    endstation = clean_endstation_for_phone(trip)
    weekday = weekday_full_for_trip(trip)
    mod_name = clean_module_name_for_phone(grp)
    doc_title = f"Entspannt Reisen nach {endstation} am {weekday}, {mod_name}"

    leg_info = ""
    if allocation:
        leg_info = (
            f"🚆 Abschnitt: <b>{html.escape(allocation.get('leg_title', 'Volle Bahn'))}</b> "
            f"({html.escape(allocation.get('time_window', ''))} · ⏱️ {allocation.get('minutes', 35)} Min. Auswendiglernen)"
        )

    banner_html = f"""
    <div class="section-banner" style="background:#b45309;margin-bottom:14px;">
        <div style="font-size:14pt;font-weight:bold;">📱 {html.escape(doc_title)}</div>
        <div class="sub" style="color:#fde68a;">
            {grp['icon']} {html.escape(grp['module'])} – {html.escape(item['name'])} · Handy-Lernblatt (Merksätze &amp; Theorie zum Auswendiglernen ohne Laptop)<br>
            {leg_info}
        </div>
    </div>
    """

    pocket_md = extract_regio_pocket_markdown(md_text)
    body_parts = [banner_html]
    if pocket_md:
        body_parts.append(
            '<div style="background:#fffbeb;border:2px solid #f59e0b;border-radius:10px;padding:12px 16px;margin-bottom:16px;">'
            + markdown_to_html(pocket_md)
            + "</div>"
        )
    body_parts.append(markdown_to_html(md_text))
    doc = HTML_TEMPLATE.format(title=html.escape(doc_title), body="\n".join(body_parts))
    html_to_pdf(doc, out_pdf)


def write_reise_mappe_pdf(trip, schedule_blocks, module_results, out_pdf):
    parts = [render_schedule_html(trip, schedule_blocks)]
    has_regio_memo = any(b.get("kind") == "regio_memo" for b in schedule_blocks)
    if has_regio_memo and module_results:
        regio_cards = []
        for grp, item, md_text, alloc in module_results:
            pocket_md = extract_regio_pocket_markdown(md_text)
            if pocket_md:
                regio_cards.append(f"<h3>{grp['icon']} {html.escape(grp['module'])} – {html.escape(item['name'])}</h3>\n" + markdown_to_html(pocket_md))
        if regio_cards:
            parts.append(f"""
            <div class="page-break"></div>
            <div class="section-banner" style="background:#b45309;">
                <div style="font-size:14pt;font-weight:bold;">📱 Kompakt-Blatt für die mittlere Regio-Verbindung (OHNE Laptop!)</div>
                <div class="sub" style="color:#fde68a;">
                    Speziell für volle/enge Regionalbahnen: Laptop bleibt in der Tasche! Nur Merksätze, Begriffe & Kurz-Checks zum lockeren Einprägen (oder komplett Pause machen).
                </div>
            </div>
            {''.join(regio_cards)}
            """)

    for grp, item, md_text, alloc in module_results:
        leg_banner = ""
        if alloc:
            leg_banner = f"""
            <div class="section-banner">
                <div style="font-size:13pt;font-weight:bold;">{grp['icon']} {html.escape(grp['module'])} – {html.escape(item['name'])}</div>
                <div class="sub">
                    🚆 Geplant für: {html.escape(alloc.get('leg_title', ''))} · Uhrzeit: {html.escape(alloc.get('time_window', ''))} ·
                    ⏱️ Angepasst auf {alloc.get('minutes', 40)} Minuten Netto-Lernzeit
                </div>
            </div>
            """
        parts.append('<div class="page-break"></div>\n' + leg_banner + markdown_to_html(md_text))

    doc = HTML_TEMPLATE.format(title="Entspannt Reisen – Reise-Mappe", body="\n".join(parts))
    html_to_pdf(doc, out_pdf)


# --------------------------------------------------------------------------
# Dezenter Hover-Tooltip für kompakte UI-Elemente
# --------------------------------------------------------------------------
class HoverTooltip:
    def __init__(self, widget, text_or_fn):
        self.widget = widget
        self.text_or_fn = text_or_fn
        self.tip_win = None
        widget.bind("<Enter>", self.on_enter, add="+")
        widget.bind("<Leave>", self.on_leave, add="+")

    def on_enter(self, event=None):
        txt = self.text_or_fn() if callable(self.text_or_fn) else str(self.text_or_fn or "")
        if not txt.strip():
            return
        self.on_leave()
        try:
            x = self.widget.winfo_rootx() + 12
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 6
            tw = tk.Toplevel(self.widget)
            tw.wm_overrideredirect(True)
            tw.wm_geometry(f"+{x}+{y}")
            tw.configure(bg="#3a4350")
            inner = tk.Label(
                tw,
                text=txt,
                justify="left",
                bg="#1c222b",
                fg="#eef1f5",
                font=(FONT_BODY, 11),
                padx=14,
                pady=9,
                wraplength=460,
            )
            inner.pack(padx=1, pady=1)
            self.tip_win = tw
        except Exception:
            self.tip_win = None

    def on_leave(self, event=None):
        if self.tip_win is not None:
            try:
                self.tip_win.destroy()
            except Exception:
                pass
            self.tip_win = None


# --------------------------------------------------------------------------
# Moderne, entschlackte Oberfläche mit klarer visueller Hierarchie
# --------------------------------------------------------------------------
class App:
    def __init__(self, root: ctk.CTk):
        self.root = root
        self.cfg = load_config()
        self.busy = False
        root.title("Entspannt Reisen")
        try:
            root.iconbitmap(default=os.path.join(ROOT, "EntspanntReisen_v9.ico"))
        except Exception:
            pass
        root.geometry("1120x860")
        root.minsize(960, 700)
        root.configure(fg_color="#151a21")

        self.vars = {}
        self.current_phase = 1
        self.schedule_blocks = []
        self.job_allocations = {}

        # Live-Sync & Timer-Zustand
        self.is_online = True
        self.offline_async_mode = False
        self.user_forced_manual = False
        self.timer_sync_clock = True
        self.timer_running = True
        self.manual_block_idx = 0
        self.manual_remaining_sec = 0
        self.last_rendered_active_idx = None
        self.last_rendered_chips_sig = None

        # Tooltip-Detailtexte
        self.ai_tooltip_text = "Prüfe KI-Anbieter …"
        self.db_tooltip_text = "Prüfe DB-Konto …"
        self.state_tooltip_text = ""

        # Minutentakt-Polling für DB-Echtzeit-Verspätungen
        self.poll_in_flight = False
        self.seconds_until_next_poll = 2
        self.last_live_summary = "🌐 Prüfe Live-Zugverbindung …"

        self.build_ui()
        self.refresh()

        initial_state = detect_trip_live_state(self.cfg.get("current_trip") or DEFAULT_TRIP)
        if initial_state.get("is_in_train"):
            self.auto_mark_elapsed_groups()
            self.switch_phase(2)

        self.tick_timer()

    # ---------- Aufbau ----------
    def build_ui(self):
        # 1. Kompakte einzeilige Top-Bar (Titel links, dezente Status-Badges & Einstellungen rechts)
        head = ctk.CTkFrame(self.root, fg_color="#10141a", corner_radius=0)
        head.pack(fill="x")
        ctk.CTkFrame(head, fg_color="#EC0016", height=3, corner_radius=0).pack(fill="x", side="bottom")
        top_row = ctk.CTkFrame(head, fg_color="transparent")
        top_row.pack(fill="x", padx=28, pady=14)

        db_logo_badge = ctk.CTkLabel(
            top_row,
            text="DB",
            font=ctk.CTkFont(FONT_HEAD, 16, "bold"),
            text_color="#ffffff",
            fg_color="#EC0016",
            corner_radius=6,
            width=38,
            height=28,
        )
        db_logo_badge.pack(side="left", padx=(0, 10))

        ctk.CTkLabel(
            top_row,
            text="Entspannt Reisen",
            font=ctk.CTkFont(FONT_HEAD, 22, "bold"),
            text_color="#eef1f5",
        ).pack(side="left")

        ctk.CTkButton(
            top_row,
            text="⚙️ Einstellungen",
            command=self.open_settings,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="transparent",
            hover_color="#262e39",
            text_color="#c3cad4",
            corner_radius=16,
            height=32,
            width=135,
        ).pack(side="right", padx=(8, 0))

        self.lbl_live_poll_status = ctk.CTkButton(
            top_row,
            text="🟢 Live-Sync (60s)",
            command=self.trigger_immediate_live_poll,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#1c222b",
            hover_color="#262e39",
            text_color="#86d4a4",
            border_width=0,
            corner_radius=16,
            height=32,
            width=145,
        )
        self.lbl_live_poll_status.pack(side="right", padx=4)
        HoverTooltip(
            self.lbl_live_poll_status,
            lambda: f"{self.last_live_summary}\n(Klick prüft sofort die DB-Echtzeitdaten)",
        )

        # Dezentes Status-Badge (Gemini Pro | DB Sync)
        status_pill = ctk.CTkFrame(top_row, fg_color="#1c222b", corner_radius=16, border_width=0)
        status_pill.pack(side="right", padx=4)

        self.ai_label = ctk.CTkLabel(
            status_pill,
            text="🟢 Gemini 4 Argon",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#86d4a4",
        )
        self.ai_label.pack(side="left", padx=(14, 6), pady=4)
        HoverTooltip(self.ai_label, lambda: self.ai_tooltip_text)

        ctk.CTkLabel(status_pill, text="·", font=ctk.CTkFont(FONT_BODY, 14, "bold"), text_color="#4a5462").pack(side="left")

        self.db_status_label = ctk.CTkLabel(
            status_pill,
            text="🟢 DB Sync",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#86d4a4",
        )
        self.db_status_label.pack(side="left", padx=(6, 14), pady=4)
        HoverTooltip(self.db_status_label, lambda: self.db_tooltip_text)

        # 2. Einzeilige blaue Status-Leiste (Halbiert: nur 1 kompakte Zeile + "⚡ Fahrt jetzt starten" rechts)
        self.live_state_banner = ctk.CTkFrame(
            self.root, fg_color="#1c222b", corner_radius=18, border_width=0
        )
        self.live_state_banner.pack(fill="x", padx=28, pady=(18, 6))

        b_top = ctk.CTkFrame(self.live_state_banner, fg_color="transparent")
        b_top.pack(fill="x", padx=18, pady=12)

        self.state_accent = ctk.CTkFrame(b_top, fg_color="#ff7a85", width=4, height=24, corner_radius=2)
        self.state_accent.pack(side="left", padx=(0, 12))

        self.lbl_state_headline = ctk.CTkLabel(
            b_top,
            text="📅 Nächste Fahrt wird geladen …",
            font=ctk.CTkFont(FONT_BODY, 14, "bold"),
            text_color="#dde2e9",
        )
        self.lbl_state_headline.pack(side="left")
        HoverTooltip(self.lbl_state_headline, lambda: self.state_tooltip_text)

        self.btn_start_now = ctk.CTkButton(
            b_top,
            text="⚡ Fahrt jetzt starten",
            command=self.on_set_trip_start_now,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#EC0016",
            hover_color="#c50014",
            corner_radius=16,
            height=34,
            width=180,
        )
        self.btn_start_now.pack(side="right")
        HoverTooltip(
            self.btn_start_now,
            "Setzt die Abfahrtszeit deiner aktuellen Verbindung auf JETZT und startet den synchronen Live-Timer.",
        )

        # 3. Kompakte Phasen-Tabs (1. Planung & PDFs | 2. Live-Fahrt & Timer)
        nav_bar = ctk.CTkFrame(self.root, fg_color="#1c222b", corner_radius=20, border_width=0)
        nav_bar.pack(fill="x", padx=28, pady=(6, 14))

        self.btn_phase1 = ctk.CTkButton(
            nav_bar,
            text="1. Planung & PDFs",
            command=lambda: self.switch_phase(1),
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            corner_radius=16,
            height=40,
            fg_color="#2c3440",
            hover_color="#313a47",
        )
        self.btn_phase1.pack(side="left", fill="x", expand=True, padx=(6, 3), pady=6)

        self.btn_phase2 = ctk.CTkButton(
            nav_bar,
            text="2. Live-Fahrt & Timer",
            command=lambda: self.switch_phase(2),
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            corner_radius=16,
            height=40,
            fg_color="transparent",
            text_color="#9aa4b2",
            hover_color="#262e39",
        )
        self.btn_phase2.pack(side="left", fill="x", expand=True, padx=(3, 6), pady=6)

        # Container für beide Tabs
        self.main_container = ctk.CTkFrame(self.root, fg_color="transparent")
        self.main_container.pack(fill="both", expand=True, padx=28, pady=(0, 18))

        self.phase1_frame = ctk.CTkFrame(self.main_container, fg_color="transparent")
        self.phase2_frame = ctk.CTkFrame(self.main_container, fg_color="transparent")

        self.build_phase1()
        self.build_phase2()
        self.switch_phase(1)

    # ---------- TAB 1: Planung & PDFs ----------
    def build_phase1(self):
        self.p1_scroll = ctk.CTkScrollableFrame(self.phase1_frame, fg_color="transparent", corner_radius=0)
        self.p1_scroll.pack(fill="both", expand=True)

        # Karte 1: Reise-Auswahl & 1-zeilige Zug-Karten (Ohne redundante Überschriften!)
        trip_box = ctk.CTkFrame(self.p1_scroll, fg_color="#1c222b", corner_radius=20, border_width=0)
        trip_box.pack(fill="x", pady=(2, 16))

        trip_sel_row = ctk.CTkFrame(trip_box, fg_color="transparent")
        trip_sel_row.pack(fill="x", padx=20, pady=(18, 12))

        ctk.CTkLabel(
            trip_sel_row,
            text="Deine Reise",
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            text_color="#eef1f5",
        ).pack(side="left", padx=(0, 8))

        self.trip_select_var = tk.StringVar(value="")
        self.trip_select_menu = ctk.CTkOptionMenu(
            trip_sel_row,
            variable=self.trip_select_var,
            values=["Reise wird geladen …"],
            command=self.on_select_trip_from_dropdown,
            font=ctk.CTkFont(FONT_BODY, 13, "bold"),
            dropdown_font=ctk.CTkFont(FONT_BODY, 13),
            fg_color="#262e39",
            button_color="#262e39",
            button_hover_color="#313a47",
            text_color="#eef1f5",
            corner_radius=12,
            height=36,
            width=200,
            dynamic_resizing=False,
        )
        self.trip_select_menu.pack(side="left", fill="x", expand=True, padx=(0, 10))

        btn_edit = ctk.CTkButton(
            trip_sel_row,
            text="✏️ Bearbeiten",
            command=self.open_trip_editor,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            text_color="#dde2e9",
            hover_color="#313a47",
            corner_radius=12,
            height=36,
            width=118,
        )
        btn_edit.pack(side="right", padx=(6, 0))
        HoverTooltip(btn_edit, "Zugabschnitte, Zeiten oder Vorlagen manuell anpassen")

        btn_login = ctk.CTkButton(
            trip_sel_row,
            text="🌐 DB-Browser",
            command=lambda: self.sync_db_trip(interactive=True),
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            text_color="#dde2e9",
            hover_color="#313a47",
            corner_radius=12,
            height=36,
            width=122,
        )
        btn_login.pack(side="right", padx=(6, 0))
        HoverTooltip(btn_login, "bahn.de im Browser öffnen, anmelden oder gemerkte Reise auswählen")

        btn_sync = ctk.CTkButton(
            trip_sel_row,
            text="🔄 DB-Sync",
            command=lambda: self.sync_db_trip(interactive=False),
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#EC0016",
            hover_color="#c50014",
            corner_radius=12,
            height=36,
            width=124,
        )
        btn_sync.pack(side="right")
        HoverTooltip(btn_sync, "Gespeicherte Reisen automatisch im Hintergrund aus deinem DB-Konto abrufen")

        self.trip_card_inner = ctk.CTkFrame(trip_box, fg_color="transparent")
        self.trip_card_inner.pack(fill="x", padx=20, pady=(0, 18))

        # Karte 2: Module kompakt als Dropdown + visuelle Chips
        mod_box = ctk.CTkFrame(self.p1_scroll, fg_color="#1c222b", corner_radius=20, border_width=0)
        mod_box.pack(fill="x", pady=(0, 16))

        m_head = ctk.CTkFrame(mod_box, fg_color="transparent")
        m_head.pack(fill="x", padx=20, pady=(18, 10))
        ctk.CTkLabel(
            m_head,
            text="Module & Lernstoff",
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            text_color="#eef1f5",
        ).pack(side="left")

        self.lbl_mod_count_badge = ctk.CTkLabel(
            m_head,
            text="",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#86d4a4",
        )
        self.lbl_mod_count_badge.pack(side="right")
        self.mod_count_tooltip_text = ""
        HoverTooltip(self.lbl_mod_count_badge, lambda: self.mod_count_tooltip_text)

        self.list_frame = ctk.CTkFrame(mod_box, fg_color="transparent")
        self.list_frame.pack(fill="x", padx=20, pady=(0, 18))

        # Karte 3: Kompaktes Status-Protokoll
        log_card = ctk.CTkFrame(self.p1_scroll, fg_color="#181d25", corner_radius=18, border_width=0)
        log_card.pack(fill="x", pady=(0, 10))
        ctk.CTkLabel(
            log_card,
            text="Protokoll",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#6f7a8a",
        ).pack(anchor="w", padx=20, pady=(12, 2))
        self.log_box = ctk.CTkTextbox(
            log_card,
            height=90,
            font=ctk.CTkFont(FONT_BODY, 11),
            fg_color="#181d25",
            text_color="#9aa4b2",
            corner_radius=8,
        )
        self.log_box.pack(fill="x", padx=14, pady=(0, 12))
        self.log_box.configure(state="disabled")

        # Feste Aktionsleiste unten in Tab 1
        footer = ctk.CTkFrame(self.phase1_frame, fg_color="#1c222b", corner_radius=20, border_width=0)
        footer.pack(fill="x", pady=(10, 0))

        self.progress = ctk.CTkProgressBar(footer, mode="determinate", height=3, corner_radius=2, fg_color="#1c222b", progress_color="#EC0016")
        self.progress.pack(fill="x", padx=24, pady=(8, 0))
        self.progress.set(0)

        f_row = ctk.CTkFrame(footer, fg_color="transparent")
        f_row.pack(fill="x", padx=18, pady=(8, 14))

        # Angenehmer orangener Hauptbutton mit kurzem Text "📄 Reise-PDFs generieren"
        self.go_btn = ctk.CTkButton(
            f_row,
            text="📄 Reise-PDFs generieren",
            command=self.start,
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            fg_color="#EC0016",
            hover_color="#c50014",
            text_color="#ffffff",
            corner_radius=22,
            height=44,
            width=260,
        )
        self.go_btn.pack(side="left")
        HoverTooltip(
            self.go_btn,
            "Erstellt die zeitangepassten Lernblätter für alle gewählten Module sowie die gemeinsame Reise-Mappe.pdf",
        )

        self.overwrite_var = tk.BooleanVar(value=self.cfg.get("overwrite", False))
        ctk.CTkCheckBox(
            f_row,
            text="Vorhandene neu erstellen",
            variable=self.overwrite_var,
            command=self.save_toggles,
            font=ctk.CTkFont(FONT_BODY, 12),
            text_color="#c3cad4",
            fg_color="#EC0016",
            hover_color="#c50014",
            border_color="#4a5462",
            border_width=2,
            corner_radius=6,
        ).pack(side="left", padx=18)

        ctk.CTkButton(
            f_row,
            text="📂 PDF-Ordner",
            command=self.open_output,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            text_color="#dde2e9",
            hover_color="#313a47",
            corner_radius=22,
            height=44,
            width=140,
        ).pack(side="right")

    # ---------- TAB 2: Live-Fahrt & Timer (Fokus auf den Countdown) ----------
    def build_phase2(self):
        self.p2_scroll = ctk.CTkScrollableFrame(self.phase2_frame, fg_color="transparent", corner_radius=0)
        self.p2_scroll.pack(fill="both", expand=True)

        # 1. FOKUSSIERTE TIMER-CARD OBEN
        timer_card = ctk.CTkFrame(self.p2_scroll, fg_color="#1c222b", corner_radius=24, border_width=0)
        timer_card.pack(fill="x", pady=(2, 16))
        ctk.CTkFrame(timer_card, fg_color="#EC0016", height=4, corner_radius=2).pack(fill="x", padx=140)

        tc_top = ctk.CTkFrame(timer_card, fg_color="transparent")
        tc_top.pack(fill="x", padx=24, pady=(16, 4))

        # Kleines Badge über dem Timer ("⏳ Automatischer Start bei Abfahrt" / "🟢 Synchron mit Zugverbindung")
        self.lbl_timer_mode_badge = ctk.CTkLabel(
            tc_top,
            text="⏳ Automatischer Start bei Abfahrt",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#ff7a85",
            fg_color="#232a34",
            corner_radius=14,
            padx=12,
            pady=4,
        )
        self.lbl_timer_mode_badge.pack(side="left")

        self.btn_toggle_sync = ctk.CTkButton(
            tc_top,
            text="🔄 Manuell / Synchron",
            command=self.toggle_timer_sync_mode,
            font=ctk.CTkFont(FONT_BODY, 11, "bold"),
            fg_color="transparent",
            hover_color="#262e39",
            text_color="#9aa4b2",
            corner_radius=14,
            height=28,
            width=150,
        )
        self.btn_toggle_sync.pack(side="right")
        HoverTooltip(self.btn_toggle_sync, "Zwischen synchronem Zug-Timer und manuellem Countdown umschalten")

        # Gekürzte, prägnante Hauptüberschrift ("Zug 1/3 (S3): Mannheim Hbf → Karlsruhe-Durlach (55 Min. Netto-Lernzeit)")
        self.lbl_current_block_title = ctk.CTkLabel(
            timer_card,
            text="Zug 1/3 (S3): Mannheim Hbf → Karlsruhe-Durlach (55 Min. Netto-Lernzeit)",
            font=ctk.CTkFont(FONT_HEAD, 18, "bold"),
            text_color="#dde2e9",
            wraplength=900,
        )
        self.lbl_current_block_title.pack(pady=(14, 0), padx=28)

        # RIESIGE ZEITANZEIGE
        self.lbl_big_countdown = ctk.CTkLabel(
            timer_card,
            text="40:00",
            font=ctk.CTkFont(FONT_HEAD, 76, "bold"),
            text_color="#ffffff",
        )
        self.lbl_big_countdown.pack(pady=(4, 6))

        self.timer_progressbar = ctk.CTkProgressBar(
            timer_card,
            height=8,
            corner_radius=4,
            fg_color="#262e39",
            progress_color="#EC0016",
        )
        self.timer_progressbar.pack(fill="x", padx=72, pady=(2, 14))
        self.timer_progressbar.set(0.0)

        # Visuelle Lernstoff-Pills (Chips) nebeneinander unter der Progress-Bar!
        self.timer_pills_frame = ctk.CTkFrame(timer_card, fg_color="transparent")
        self.timer_pills_frame.pack(pady=(0, 14), padx=24)

        # Steuer-Buttons für den Timer
        t_btns = ctk.CTkFrame(timer_card, fg_color="transparent")
        t_btns.pack(pady=(0, 22))

        ctk.CTkButton(
            t_btns,
            text="⏮️ Zurück",
            command=lambda: self.step_manual_block(-1),
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            hover_color="#313a47",
            text_color="#dde2e9",
            corner_radius=20,
            height=40,
            width=120,
        ).pack(side="left", padx=5)

        self.btn_pause_resume = ctk.CTkButton(
            t_btns,
            text="⏸️ Pausieren",
            command=self.toggle_timer_pause,
            font=ctk.CTkFont(FONT_BODY, 13, "bold"),
            fg_color="#EC0016",
            hover_color="#c50014",
            corner_radius=20,
            height=40,
            width=150,
        )
        self.btn_pause_resume.pack(side="left", padx=5)

        ctk.CTkButton(
            t_btns,
            text="⏭️ Phase erledigt",
            command=lambda: self.step_manual_block(1),
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            hover_color="#313a47",
            text_color="#dde2e9",
            corner_radius=20,
            height=40,
            width=150,
        ).pack(side="left", padx=5)

        ctk.CTkButton(
            t_btns,
            text="📘 Reise-Mappe.pdf",
            command=self.open_reise_mappe,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="transparent",
            hover_color="#262e39",
            text_color="#dde2e9",
            border_width=1,
            border_color="#3a4350",
            corner_radius=20,
            height=40,
            width=175,
        ).pack(side="left", padx=(14, 5))

        # 2. ABLAUFPLAN DER FAHRT (Kompakt & übersichtlich)
        sched_card = ctk.CTkFrame(self.p2_scroll, fg_color="#1c222b", corner_radius=20, border_width=0)
        sched_card.pack(fill="x", pady=(0, 10))

        s_head = ctk.CTkFrame(sched_card, fg_color="transparent")
        s_head.pack(fill="x", padx=20, pady=(18, 10))
        ctk.CTkLabel(
            s_head,
            text="Phasen deiner Fahrt",
            font=ctk.CTkFont(FONT_HEAD, 15, "bold"),
            text_color="#eef1f5",
        ).pack(side="left")

        ctk.CTkButton(
            s_head,
            text="↺ Zurücksetzen",
            command=self.reset_trip_progress,
            font=ctk.CTkFont(FONT_BODY, 11),
            fg_color="transparent",
            text_color="#9aa4b2",
            hover_color="#262e39",
            corner_radius=13,
            height=26,
            width=110,
        ).pack(side="right")

        self.live_schedule_frame = ctk.CTkFrame(sched_card, fg_color="transparent")
        self.live_schedule_frame.pack(fill="x", padx=20, pady=(0, 18))

        # 3. KOMPAKTE EINZEILIGE VERSPÄTUNGS-TOOLBAR AM UNTEREN RAND VON TAB 2
        self.delay_card = ctk.CTkFrame(self.phase2_frame, fg_color="#1c222b", corner_radius=20, border_width=0, border_color="#1c222b")
        self.delay_card.pack(fill="x", pady=(10, 0))

        # Warn-Banner: Standardmäßig ausgeblendet, poppt erst bei Konflikt / Klick auf!
        self.lbl_delay_feedback = ctk.CTkLabel(
            self.delay_card,
            text="",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#fef2f2",
            fg_color="#3a1f24",
            corner_radius=12,
            padx=14,
            pady=6,
        )

        d_bar = ctk.CTkFrame(self.delay_card, fg_color="transparent")
        d_bar.pack(fill="x", padx=18, pady=12)

        ctk.CTkLabel(
            d_bar,
            text="Verspätung",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            text_color="#9aa4b2",
        ).pack(side="left", padx=(0, 6))

        self.delay_leg_var = tk.StringVar(value="1")
        self.delay_leg_menu = ctk.CTkOptionMenu(
            d_bar,
            variable=self.delay_leg_var,
            values=["1"],
            width=175,
            height=32,
            corner_radius=16,
            fg_color="#262e39",
            button_color="#262e39",
            button_hover_color="#313a47",
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
        )
        self.delay_leg_menu.pack(side="left", padx=(0, 6))

        for mins in (5, 10, 15, 25):
            ctk.CTkButton(
                d_bar,
                text=f"+{mins}m",
                command=lambda m=mins: self.on_add_delay(m),
                font=ctk.CTkFont(FONT_BODY, 12, "bold"),
                fg_color="#262e39",
                text_color="#dde2e9",
                hover_color="#313a47",
                corner_radius=16,
                height=32,
                width=52,
            ).pack(side="left", padx=2)

        btn_recalc = ctk.CTkButton(
            d_bar,
            text="🔄 Route neu berechnen",
            command=self.on_replace_connection,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#262e39",
            hover_color="#313a47",
            text_color="#dde2e9",
            corner_radius=16,
            height=32,
            width=170,
        )
        btn_recalc.pack(side="right", padx=(6, 0))
        HoverTooltip(
            btn_recalc,
            "Alte Verbindung verwerfen & neue wählen (Vergangene Lernphasen bleiben im Hintergrund als erledigt gespeichert)",
        )

        btn_missed = ctk.CTkButton(
            d_bar,
            text="⚠️ Anschluss verpasst (+30m Pause)",
            command=self.on_missed_connection,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            fg_color="#2a1a1f",
            hover_color="#3a1f24",
            text_color="#ff8a94",
            corner_radius=16,
            height=32,
            width=225,
        )
        btn_missed.pack(side="right")
        HoverTooltip(
            btn_missed,
            "Rechnet sofort +30 Min. Extra-Pause für den verpassten Anschluss hinzu und verschiebt die Folge-Phasen",
        )

    def show_delay_alert(self, msg, is_conflict=True):
        if not msg:
            self.lbl_delay_feedback.pack_forget()
            return
        self.lbl_delay_feedback.configure(
            text=msg,
            fg_color="#3a1f24" if is_conflict else "#2a1a1f",
            text_color="#ffc2c7" if is_conflict else "#c3cad4",
        )
        self.lbl_delay_feedback.pack(fill="x", padx=18, pady=(12, 0), before=self.delay_card.winfo_children()[-1])

    def _render_pills_into(self, parent_frame, chips):
        for w in parent_frame.winfo_children():
            w.destroy()
        for chip_txt in (chips or []):
            is_warn = chip_txt.startswith("⚠️")
            is_pause = chip_txt.startswith("☕")
            is_theory = chip_txt.startswith("🧠")
            bg = "#2e2618" if is_theory else ("#1b2a24" if is_pause else ("#3a1f24" if is_warn else "#262e39"))
            fg = "#f0d58f" if is_theory else ("#86d4a4" if is_pause else ("#ffa3ab" if is_warn else "#dde2e9"))
            pill = ctk.CTkFrame(parent_frame, fg_color=bg, corner_radius=14, border_width=0)
            pill.pack(side="left", padx=4, pady=3)
            ctk.CTkLabel(
                pill,
                text=chip_txt,
                font=ctk.CTkFont(FONT_BODY, 12),
                text_color=fg,
            ).pack(padx=12, pady=4)

    # ---------- Phasen-Wechsel ----------
    def switch_phase(self, phase_num):
        self.current_phase = phase_num
        if phase_num == 1:
            self.phase2_frame.pack_forget()
            self.phase1_frame.pack(fill="both", expand=True)
            self.btn_phase1.configure(fg_color="#2c3440", text_color="#ffffff")
            self.btn_phase2.configure(fg_color="transparent", text_color="#9aa4b2")
        else:
            self.phase1_frame.pack_forget()
            self.phase2_frame.pack(fill="both", expand=True)
            self.btn_phase2.configure(fg_color="#2c3440", text_color="#ffffff")
            self.btn_phase1.configure(fg_color="transparent", text_color="#9aa4b2")
            self.refresh()

    # ---------- Live-State & Automatische Erledigt-Erkennung ----------
    def auto_mark_elapsed_groups(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        state_info = detect_trip_live_state(trip)
        if state_info.get("is_in_train"):
            active_jobs = self.get_active_jobs()
            done_ids = get_elapsed_completed_groups(trip, active_jobs)
            progress = sorted(set(done_ids) - set(trip.get("completed_group_ids") or []))
            if progress != sorted(trip.get("progress_done_ids") or []):
                trip["progress_done_ids"] = progress
                save_config(self.cfg)

    def on_set_trip_start_now(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        shift_trip_to_start_now(trip)
        self.offline_async_mode = False
        self.user_forced_manual = False
        self.timer_sync_clock = True
        save_config(self.cfg)
        self.log("\n⚡ Fahrtzeiten auf JETZT gesetzt – Live-Timer gestartet!")
        self.refresh()
        self.switch_phase(2)
        self.trigger_immediate_live_poll()

    # ---------- Minutentakt Live-DB-Polling & Offline-Fallback ----------
    def trigger_immediate_live_poll(self):
        self.seconds_until_next_poll = 0
        self.run_background_live_poll()

    def run_background_live_poll(self):
        if self.poll_in_flight:
            return
        self.poll_in_flight = True
        self.seconds_until_next_poll = LIVE_POLL_INTERVAL_SEC

        def _worker():
            try:
                trip = self.cfg.get("current_trip") or DEFAULT_TRIP
                res = poll_live_trip_delays(trip)
                self.root.after(0, lambda: self._on_live_poll_result(res))
            except Exception:
                self.root.after(
                    0,
                    lambda: self._on_live_poll_result({
                        "online": False,
                        "updated": False,
                        "matched_count": 0,
                        "messages": [],
                        "summary": "📡 Offline (Kein Internet) – Timer läuft asynchron weiter",
                    }),
                )
            finally:
                self.poll_in_flight = False

        threading.Thread(target=_worker, daemon=True).start()

    def _on_live_poll_result(self, res):
        was_online = self.is_online
        self.is_online = bool(res.get("online", True))
        self.last_live_summary = res.get("summary", "")

        if not self.is_online:
            if not self.offline_async_mode:
                self.offline_async_mode = True
                self.timer_sync_clock = False
                self.timer_running = True
                self.log("\n📡 Offline – Timer läuft asynchron weiter.")
            self.delay_card.configure(border_color="#c99a45", border_width=1)
        else:
            if self.offline_async_mode or not was_online:
                self.offline_async_mode = False
                if not self.user_forced_manual:
                    self.timer_sync_clock = True
                self.log("\n🌐 Wieder online – Live-Sync aktiv.")
            self.delay_card.configure(border_color="#1c222b", border_width=0)

        if res.get("updated"):
            save_config(self.cfg)
            for m in res.get("messages", []):
                self.log(f"\n{m}")
                self.show_delay_alert(m, is_conflict=("⚠️" in m or "🚨" in m))
            self.refresh()

        self.update_top_state_banner()

    def update_top_state_banner(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        st = detect_trip_live_state(trip)

        calm = {"#4ade80": "#86d4a4", "#fbbf24": "#f0c36b", "#ff4d5e": "#ff7a85", "#9ca3af": "#6f7a8a"}
        self.lbl_state_headline.configure(text=st["badge"], text_color="#dde2e9")
        self.state_tooltip_text = st.get("sub", "")
        self.state_accent.configure(fg_color=calm.get(st["color"], st["color"]))

        if st.get("is_in_train"):
            self.btn_start_now.configure(text="⚡ Start neu setzen")
        else:
            self.btn_start_now.configure(text="⚡ Fahrt jetzt starten")

        rem_s = max(0, int(self.seconds_until_next_poll))
        if self.is_online:
            self.lbl_live_poll_status.configure(text=f"🟢 Live-Sync ({rem_s}s)", text_color="#86d4a4")
        else:
            self.lbl_live_poll_status.configure(text=f"📡 Offline ({rem_s}s)", text_color="#f0c36b")

        if self.offline_async_mode:
            self.lbl_timer_mode_badge.configure(
                text="📡 Offline-Timer (Asynchron)",
                text_color="#f0c36b",
            )
            self.btn_toggle_sync.configure(text="🌐 Live-Sync prüfen")
        elif self.timer_sync_clock:
            if st.get("is_in_train"):
                self.lbl_timer_mode_badge.configure(
                    text="🟢 Synchron mit Zugverbindung",
                    text_color="#86d4a4",
                )
            else:
                self.lbl_timer_mode_badge.configure(
                    text="⏳ Automatischer Start bei Abfahrt",
                    text_color="#ff7a85",
                )
            self.btn_toggle_sync.configure(text="🔄 Manueller Timer")
        else:
            self.lbl_timer_mode_badge.configure(
                text="⏱️ Manueller Timer (Asynchron)",
                text_color="#f0d58f",
            )
            self.btn_toggle_sync.configure(text="🕒 Synchronisieren")

    # ---------- Reise-Auswahl-Dropdown & Modul-Dropdown Logik ----------
    def _build_available_trips_list(self):
        all_candidates = []
        seen = set()
        cur = self.cfg.get("current_trip") or DEFAULT_TRIP
        raw_list = [cur] + (self.cfg.get("saved_trips") or [])
        today_s = datetime.date.today().strftime("%d.%m.%Y")
        for t in raw_list:
            if isinstance(t, dict) and not is_corrupted_trip(t):
                title = str(t.get("title") or "")
                src = str(t.get("source") or "")
                # Ungewollte Dummy-Verbindungen von heute herausfiltern
                if "Vorlage:" in src or ("Direktfahrt" in title and "ICE 613" in title and t.get("date") == today_s):
                    continue
                k = trip_identity_key(t)
                if k not in seen:
                    seen.add(k)
                    all_candidates.append(t)
        if not all_candidates:
            all_candidates = [DEFAULT_TRIP]
        return all_candidates

    def on_select_trip_from_dropdown(self, choice):
        if "DB-Browser" in choice:
            self.sync_db_trip(interactive=True)
            return
        if "im Editor eingeben" in choice:
            self.open_trip_editor()
            return
        candidates = self._build_available_trips_list()
        for idx, t in enumerate(candidates, start=1):
            lbl = format_trip_dropdown_label(t, idx=idx)
            if lbl == choice:
                self.cfg["current_trip"] = json.loads(json.dumps(t))
                ensure_planned_times(self.cfg["current_trip"])
                save_config(self.cfg)
                self.show_delay_alert("")
                self.log(f"\n🔀 Reise gewechselt: {format_trip_dropdown_label(t)}")
                self.refresh()
                self.trigger_immediate_live_poll()
                return

    def on_set_leg_mode_from_dropdown(self, leg_idx, selected_label):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        legs = trip.get("legs", [])
        if 0 <= leg_idx < len(legs):
            code = LEG_LABEL_TO_MODE.get(selected_label, "focus")
            legs[leg_idx]["mode"] = code
            changed = apply_consecutive_full_train_rule(legs)
            if changed:
                for c_idx in changed:
                    tname = legs[c_idx].get("train", f"Zug {c_idx + 1}")
                    nxt_name = legs[c_idx + 1].get("train", f"Zug {c_idx + 2}")
                    self.log(f"\n☕ Automatische Pause in {tname}: Da danach {nxt_name} ebenfalls voll ist, pausierst du im ersten Zug.")
            save_config(self.cfg)
            self.refresh()

    def on_module_dropdown_select(self, choice):
        if choice.startswith("📚 ") or choice.startswith("───"):
            self.refresh()
            return
        if choice.startswith("✅ Alle"):
            for g in GROUPS:
                self.cfg["enabled"][g["id"]] = True
        elif choice.startswith("❌ Keine"):
            for g in GROUPS:
                self.cfg["enabled"][g["id"]] = False
        elif choice.startswith("🎯 Nur:"):
            target_name = choice.split("🎯 Nur:", 1)[1].strip()
            for g in GROUPS:
                label_short = f"{g['icon']} {g['module']} ({g['category']})"
                self.cfg["enabled"][g["id"]] = (label_short == target_name)
        else:
            for g in GROUPS:
                tag = f"{g['icon']} {g['module']} — {g['category']}"
                if tag in choice:
                    cur_val = bool(self.cfg["enabled"].get(g["id"], True))
                    self.cfg["enabled"][g["id"]] = not cur_val
                    break
        save_config(self.cfg)
        self.refresh()

    def on_pdf_dropdown_select(self, choice):
        if not choice or choice == "📄 Fertiges PDF öffnen …":
            return
        if choice.startswith("📘 Gemeinsame Reise-Mappe"):
            self.open_reise_mappe()
            self.pdf_dropdown_var.set("📄 Fertiges PDF öffnen …")
            return
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        if choice.startswith("📱 OneDrive-Handy-PDF:"):
            for grp in GROUPS:
                p_pdf = phone_memo_pdf_path(trip, grp)
                if clean_module_name_for_phone(grp) in choice and os.path.isfile(p_pdf):
                    os.startfile(p_pdf)
                    break
            self.pdf_dropdown_var.set("📄 Fertiges PDF öffnen …")
            return
        if choice.startswith("📅 Apple-Kalender"):
            ics_p = calendar_ics_path(trip)
            if os.path.isfile(ics_p):
                os.startfile(ics_p)
            self.pdf_dropdown_var.set("📄 Fertiges PDF öffnen …")
            return
        for grp in GROUPS:
            nxt = next_open(grp)
            if nxt:
                pdf = summary_pdf_path(grp, nxt)
                if choice == f"📄 {grp['icon']} {grp['module']} ({nxt['name']})" and os.path.isfile(pdf):
                    os.startfile(pdf)
                    break
        self.pdf_dropdown_var.set("📄 Fertiges PDF öffnen …")

    # ---------- Aktualisierung der Oberfläche ----------
    def get_active_jobs(self):
        jobs = []
        for grp in GROUPS:
            if self.cfg["enabled"].get(grp["id"], True):
                nxt = next_open(grp)
                if nxt:
                    jobs.append((grp, nxt))
        return jobs

    def refresh(self):
        # 1. Dezente Top-Bar Badges + ausführlicher Hover-Tooltip
        provs = detect_providers(self.cfg)
        avail = [p for p in provs if p[2]]
        if avail:
            first_id = avail[0][0]
            if "agy" in first_id or "argon" in first_id:
                short_ai = "Gemini 4 Argon"
            elif "gemini" in first_id:
                short_ai = "Gemini Pro"
            else:
                short_ai = "Claude Opus"
            self.ai_label.configure(text=f"🟢 {short_ai}", text_color="#86d4a4")
            self.ai_tooltip_text = "Aktive KI: " + avail[0][1] + (f" (+{len(avail)-1} Ersatz)" if len(avail) > 1 else "")
        else:
            self.ai_label.configure(text="⚠️ Keine KI", text_color="#f0c36b")
            self.ai_tooltip_text = "Keine KI verfügbar – bitte in den Einstellungen anmelden."

        has_profile = os.path.isdir(DB_PROFILE_DIR) and bool(os.listdir(DB_PROFILE_DIR))
        db_ok = self.cfg.get("db_logged_in") or has_profile or bool(self.cfg.get("db_username"))
        self.db_status_label.configure(
            text="🟢 DB Sync" if db_ok else "⚪ DB Login",
            text_color="#86d4a4" if db_ok else "#f0c36b",
        )
        self.db_tooltip_text = (
            "DB-Konto dauerhaft verbunden (Browser-Profil aktiv)"
            if db_ok else "Noch nicht mit bahn.de verbunden – klicke auf „🌐 DB-Browser“."
        )

        active_jobs = self.get_active_jobs()
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        ensure_planned_times(trip)
        self.schedule_blocks, self.job_allocations = build_study_schedule(trip, active_jobs)
        self.update_top_state_banner()

        # 2. Reise-Auswahl-Dropdown in Tab 1 aktualisieren
        candidates = self._build_available_trips_list()
        dropdown_trip_values = [format_trip_dropdown_label(t, idx=i + 1) for i, t in enumerate(candidates)]
        dropdown_trip_values.append("🌐 Andere Reise im DB-Browser (bahn.de) wählen …")
        dropdown_trip_values.append("✏️ Eigene Verbindung im Editor eingeben …")
        current_trip_label = format_trip_dropdown_label(trip, idx=1)
        for i, t in enumerate(candidates):
            if trip_identity_key(t) == trip_identity_key(trip):
                current_trip_label = format_trip_dropdown_label(t, idx=i + 1)
                break
        self.trip_select_menu.configure(values=dropdown_trip_values)
        self.trip_select_var.set(current_trip_label)

        # 3. Tab 1: 1-zeilige Zug-Karten + schmale Umstiegs-Trenner rendern
        for w in self.trip_card_inner.winfo_children():
            w.destroy()

        legs = trip.get("legs", [])
        leg_menu_vals = []
        mode_label_list = [m[1] for m in LEG_MODES]

        for idx, leg in enumerate(legs):
            tname = leg.get("train", "Zug")
            from_s = leg.get("from_station", "Start")
            to_s = leg.get("to_station", "Ziel")
            dep_s = leg.get("dep", "")
            arr_s = leg.get("arr", "")
            leg_menu_vals.append(f"Zug {idx + 1}: {tname} ({dep_s})")

            row = ctk.CTkFrame(
                self.trip_card_inner,
                fg_color="#232a34",
                corner_radius=14,
                border_width=0,
            )
            row.pack(fill="x", pady=4)

            dur = int(leg.get("duration_min") or diff_minutes(dep_s, arr_s, 35))
            delay_m = int(leg.get("delay_min", 0))
            status_txt = f"🔴 +{delay_m} Min." if delay_m > 0 else "🟢 pünktlich"
            status_col = "#ff8a94" if delay_m > 0 else "#86d4a4"

            mode = leg.get("mode", "focus")
            mode_colors = {
                "focus": ("#2a1a1f", "#3a1f24", "#ff9aa3"),
                "light": ("#2a1a1f", "#3a1f24", "#ff9aa3"),
                "regio_memo": ("#2e2618", "#3a3020", "#f0d58f"),
                "rest": ("#262e39", "#313a47", "#c3cad4"),
            }.get(mode, ("#2a1a1f", "#3a1f24", "#ff9aa3"))

            # Links: Badge [S3] + "12:30 Mannheim Hbf → 13:30 Karlsruhe-Durlach (60 Min.) · 🟢 pünktlich" in 1 Zeile!
            ctk.CTkLabel(
                row,
                text=tname,
                font=ctk.CTkFont(FONT_BODY, 12, "bold"),
                text_color="#ffffff",
                fg_color="#EC0016" if leg.get("type") == "ICE" else "#3a4350",
                corner_radius=8,
                padx=9,
                pady=3,
            ).pack(side="left", padx=(14, 12), pady=10)

            ctk.CTkLabel(
                row,
                text=f"{dep_s} {from_s}  →  {arr_s} {to_s}  ({dur} Min.)",
                font=ctk.CTkFont(FONT_BODY, 13, "bold"),
                text_color="#eef1f5",
            ).pack(side="left")

            ctk.CTkLabel(
                row,
                text=f"  ·  {status_txt}",
                font=ctk.CTkFont(FONT_BODY, 12),
                text_color=status_col,
            ).pack(side="left")

            # Rechts: DB-Auslastungs-Badge + kompaktes 3-Optionen-Dropdown
            leg_mode_var = tk.StringVar(value=LEG_MODE_LABELS.get(mode, mode_label_list[0]))
            ctk.CTkOptionMenu(
                row,
                variable=leg_mode_var,
                values=mode_label_list,
                command=lambda val, i=idx: self.on_set_leg_mode_from_dropdown(i, val),
                font=ctk.CTkFont(FONT_BODY, 12, "bold"),
                dropdown_font=ctk.CTkFont(FONT_BODY, 12),
                fg_color=mode_colors[0],
                button_color=mode_colors[0],
                button_hover_color=mode_colors[1],
                text_color=mode_colors[2],
                corner_radius=15,
                height=30,
                width=215,
            ).pack(side="right", padx=12, pady=8)

            db_occ = leg.get("db_occupancy", "")
            if db_occ:
                is_full = ("hohe" in db_occ.lower() or "voll" in db_occ.lower())
                badge_bg = "#2e2618" if is_full else "#1b2a24"
                badge_fg = "#f0d58f" if is_full else "#a8dcbb"
                badge_txt = "👥 DB: Voll" if is_full else "👥 DB: Frei"
                occ_badge = ctk.CTkLabel(
                    row,
                    text=badge_txt,
                    font=ctk.CTkFont(FONT_BODY, 11, "bold"),
                    text_color=badge_fg,
                    fg_color=badge_bg,
                    corner_radius=10,
                    padx=9,
                    pady=3,
                )
                occ_badge.pack(side="right", padx=4)
                HoverTooltip(occ_badge, f"Offizielle DB-Auslastung: {db_occ}")

            # Schmaler, dezenter Trenner für den Umstieg zwischen zwei Zügen
            if idx < len(legs) - 1:
                nxt_leg = legs[idx + 1]
                tr_min = int(leg.get("transfer_after_min") or diff_minutes(arr_s, nxt_leg.get("dep"), 12))
                if tr_min >= LONG_TRANSFER_THRESHOLD_MIN:
                    tr_desc = f"☕ {LONG_TRANSFER_BREAK_MIN} Min. Pause + 📖 {tr_min - LONG_TRANSFER_BREAK_MIN} Min. Lernen in {to_s}"
                else:
                    tr_desc = f"☕ {tr_min} Min. Umstieg & Pause in {to_s}"
                ctk.CTkLabel(
                    self.trip_card_inner,
                    text=tr_desc,
                    font=ctk.CTkFont(FONT_BODY, 11),
                    text_color="#7d9a8a",
                ).pack(anchor="w", padx=28, pady=2)

        if leg_menu_vals:
            self.delay_leg_menu.configure(values=leg_menu_vals)
            if self.delay_leg_var.get() not in leg_menu_vals:
                self.delay_leg_var.set(leg_menu_vals[0])

        # 4. Tab 1: Modul-Dropdown + kompakte Chips
        for w in self.list_frame.winfo_children():
            w.destroy()

        enabled_groups = [g for g in GROUPS if self.cfg["enabled"].get(g["id"], True)]
        self.lbl_mod_count_badge.configure(
            text=f"✅ {len(enabled_groups)}/{len(GROUPS)} aktiv",
            text_color="#86d4a4" if enabled_groups else "#f0c36b",
        )

        short_names = [short_module_name(g["module"]) for g in enabled_groups]
        summary_header = (
            f"📚 Aktive Module ({len(enabled_groups)}/{len(GROUPS)}): " + ", ".join(short_names)
            if short_names
            else "📚 Keine Module ausgewählt"
        )

        mod_dropdown_values = [
            "✅ Alle 6 Module aktivieren",
            "❌ Keine Module (alle abwählen)",
            "─── Einzelnes Modul an-/abhaken (Klick schaltet um) ───",
        ]
        for grp in GROUPS:
            is_on = bool(self.cfg["enabled"].get(grp["id"], True))
            nxt = next_open(grp)
            nxt_txt = f" [{short_item_name(nxt['name'])}]" if nxt else " [Erledigt]"
            box_icon = "☑️" if is_on else "⬜"
            mod_dropdown_values.append(f"{box_icon} {grp['icon']} {grp['module']} — {grp['category']}{nxt_txt}")

        mod_dropdown_values.append("─── Nur 1 einzelnes Modul wählen ───")
        for grp in GROUPS:
            mod_dropdown_values.append(f"🎯 Nur: {grp['icon']} {grp['module']} ({grp['category']})")

        drop_bar = ctk.CTkFrame(self.list_frame, fg_color="transparent")
        drop_bar.pack(fill="x", pady=(0, 10))

        self.mod_dropdown_var = tk.StringVar(value=summary_header)
        ctk.CTkOptionMenu(
            drop_bar,
            variable=self.mod_dropdown_var,
            values=mod_dropdown_values,
            command=self.on_module_dropdown_select,
            font=ctk.CTkFont(FONT_BODY, 13, "bold"),
            dropdown_font=ctk.CTkFont(FONT_BODY, 12),
            fg_color="#262e39",
            button_color="#262e39",
            button_hover_color="#313a47",
            text_color="#eef1f5",
            corner_radius=12,
            height=36,
        ).pack(side="left", fill="x", expand=True, padx=(0, 8))

        pdf_choices = ["📄 Fertiges PDF öffnen …"]
        mappe_p = current_reise_mappe_path(trip)
        if os.path.isfile(mappe_p):
            pdf_choices.append("📘 Gemeinsame Reise-Mappe.pdf öffnen")
        for grp in GROUPS:
            p_pdf = phone_memo_pdf_path(trip, grp)
            if os.path.isfile(p_pdf):
                pdf_choices.append(f"📱 OneDrive-Handy-PDF: {os.path.basename(p_pdf)}")
        ics_p = calendar_ics_path(trip)
        if os.path.isfile(ics_p):
            pdf_choices.append(f"📅 Apple-Kalender (.ics): {os.path.basename(ics_p)}")
        for grp in GROUPS:
            nxt = next_open(grp)
            if nxt and os.path.isfile(summary_pdf_path(grp, nxt)):
                pdf_choices.append(f"📄 {grp['icon']} {grp['module']} ({nxt['name']})")

        self.pdf_dropdown_var = tk.StringVar(value="📄 Fertiges PDF öffnen …")
        ctk.CTkOptionMenu(
            drop_bar,
            variable=self.pdf_dropdown_var,
            values=pdf_choices,
            command=self.on_pdf_dropdown_select,
            font=ctk.CTkFont(FONT_BODY, 12, "bold"),
            dropdown_font=ctk.CTkFont(FONT_BODY, 12),
            fg_color="#262e39",
            button_color="#262e39",
            button_hover_color="#313a47",
            text_color="#eef1f5" if len(pdf_choices) > 1 else "#9aa4b2",
            corner_radius=12,
            height=36,
            width=220,
        ).pack(side="right")

        # Kompakte UI-Chips für die Modul-Aufteilung in Tab 1 + automatischer Hinweis bei ausgelassenen Modulen
        chips_bar = ctk.CTkFrame(self.list_frame, fg_color="transparent")
        chips_bar.pack(fill="x")
        p1_chips = []
        for grp, nxt in active_jobs:
            al = self.job_allocations.get(grp["id"])
            if al:
                is_memo = al.get("is_phone_memo") or al.get("mode") == "regio_memo"
                tag_suffix = f"📱 {al.get('train_short', 'Zug')} · Handy" if is_memo else al.get("train_short", "Zug")
                p1_chips.append(
                    f"{grp['icon']} {short_module_name(grp['module'])} ({short_item_name(nxt['name'])}) · {al['minutes']}m [{tag_suffix}]"
                )
        self._render_pills_into(chips_bar, p1_chips)

        skipped_list, short_hint, detail_tooltip = get_skipped_jobs_info(trip, active_jobs, self.job_allocations)
        self.mod_count_tooltip_text = detail_tooltip if skipped_list else ""
        if skipped_list:
            kept_n = len(self.job_allocations)
            self.lbl_mod_count_badge.configure(
                text=f"⚡ {kept_n}/{len(enabled_groups)} eingeplant",
                text_color="#f0c36b",
            )

        # 5. Tab 2: Live-Zeitplan rendern
        self.render_live_schedule()

    def render_live_schedule(self):
        for w in self.live_schedule_frame.winfo_children():
            w.destroy()

        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        legs = trip.get("legs", [])
        st = detect_trip_live_state(trip)
        is_in_train = st.get("is_in_train", False)
        now_m = now_minutes_of_day()
        mode_label_list = [m[1] for m in LEG_MODES]

        for idx, b in enumerate(self.schedule_blocks):
            kind = b.get("kind", "study")
            start_m = b.get("start_min", 0)
            end_m = b.get("end_min", 0)
            leg_idx = b.get("leg_index")
            if self.timer_sync_clock:
                is_past = is_in_train and (now_m >= end_m)
                is_active = is_in_train and (start_m <= now_m < end_m)
            else:
                is_past = idx < self.manual_block_idx
                is_active = idx == self.manual_block_idx

            # Schmaler Trenner für normale Umstiegs-Pausen im Zeitplan
            if kind == "transfer_break" and not is_active:
                tr_line = ctk.CTkFrame(self.live_schedule_frame, fg_color="transparent")
                tr_line.pack(fill="x", padx=12, pady=3)
                ctk.CTkLabel(
                    tr_line,
                    text=f"{b.get('title', '')}  ·  {b.get('time', '')} Uhr",
                    font=ctk.CTkFont(FONT_BODY, 12),
                    text_color="#7d9a8a",
                ).pack(side="left", padx=(8, 0))
                ctk.CTkButton(
                    tr_line,
                    text="⏱️ Timer",
                    command=lambda i=idx: self.select_block_in_timer(i),
                    font=ctk.CTkFont(FONT_BODY, 11),
                    fg_color="transparent",
                    hover_color="#262e39",
                    text_color="#9aa4b2",
                    corner_radius=11,
                    height=22,
                    width=75,
                ).pack(side="right")
                continue

            if is_active:
                bg_col, border_col = "#2a1a1f", "#EC0016"
            elif is_past:
                bg_col, border_col = "#1f252e", "#1f252e"
            elif kind == "regio_memo":
                bg_col, border_col = "#2a2519", "#2a2519"
            else:
                bg_col, border_col = "#232a34", "#232a34"

            card = ctk.CTkFrame(
                self.live_schedule_frame,
                fg_color=bg_col,
                corner_radius=14,
                border_width=1 if is_active else 0,
                border_color=border_col,
            )
            card.pack(fill="x", pady=4)

            top = ctk.CTkFrame(card, fg_color="transparent")
            top.pack(fill="x", padx=16, pady=(10, 8))

            state_tag = "▶️ " if is_active else ("✅ " if is_past else "")
            ctk.CTkLabel(
                top,
                text=f"{state_tag}{b.get('title', '')}",
                font=ctk.CTkFont(FONT_BODY, 14, "bold"),
                text_color="#7a8494" if is_past else "#eef1f5",
            ).pack(side="left")

            ctk.CTkButton(
                top,
                text="⏱️ Timer",
                command=lambda i=idx: self.select_block_in_timer(i),
                font=ctk.CTkFont(FONT_BODY, 11, "bold"),
                fg_color="#EC0016" if is_active else "#2c3440",
                text_color="#ffffff" if is_active else "#c3cad4",
                hover_color="#c50014" if is_active else "#3a4350",
                corner_radius=13,
                height=26,
                width=85,
            ).pack(side="right", padx=(6, 0))

            if kind in ("study", "regio_memo", "rest") and leg_idx is not None and 0 <= leg_idx < len(legs) and "Wartezeit" not in b.get("title", ""):
                cur_leg_mode = legs[leg_idx].get("mode", "focus")
                p2_mode_var = tk.StringVar(value=LEG_MODE_LABELS.get(cur_leg_mode, mode_label_list[0]))
                ctk.CTkOptionMenu(
                    top,
                    variable=p2_mode_var,
                    values=mode_label_list,
                    command=lambda val, li=leg_idx: self.on_set_leg_mode_from_dropdown(li, val),
                    font=ctk.CTkFont(FONT_BODY, 11, "bold"),
                    dropdown_font=ctk.CTkFont(FONT_BODY, 11),
                    fg_color="#262e39",
                    button_color="#262e39",
                    button_hover_color="#313a47",
                    text_color="#c3cad4",
                    corner_radius=13,
                    height=26,
                    width=215,
                ).pack(side="right", padx=(6, 0))

            ctk.CTkLabel(
                top,
                text=f"🕒 {b.get('time', '')}",
                font=ctk.CTkFont(FONT_BODY, 13),
                text_color="#9aa4b2",
            ).pack(side="right", padx=8)

            # Chips-Zeile in der Karte
            if b.get("chips"):
                c_row = ctk.CTkFrame(card, fg_color="transparent")
                c_row.pack(fill="x", padx=12, pady=(0, 10))
                self._render_pills_into(c_row, b.get("chips"))

    # ---------- Großer Live-Timer ----------
    def select_block_in_timer(self, idx):
        if 0 <= idx < len(self.schedule_blocks):
            self.user_forced_manual = True
            self.timer_sync_clock = False
            self.manual_block_idx = idx
            self.manual_remaining_sec = int(self.schedule_blocks[idx].get("duration_min", 25)) * 60
            self.timer_running = True
            self.btn_pause_resume.configure(text="⏸️ Pausieren")
            self.update_top_state_banner()
            self.render_live_schedule()

    def toggle_timer_sync_mode(self):
        if self.offline_async_mode:
            self.trigger_immediate_live_poll()
            return

        self.timer_sync_clock = not self.timer_sync_clock
        self.user_forced_manual = not self.timer_sync_clock
        if not self.timer_sync_clock:
            if 0 <= self.manual_block_idx < len(self.schedule_blocks):
                if self.manual_remaining_sec <= 0:
                    self.manual_remaining_sec = int(self.schedule_blocks[self.manual_block_idx].get("duration_min", 25)) * 60
            self.timer_running = True
            self.btn_pause_resume.configure(text="⏸️ Pausieren")
        else:
            self.btn_pause_resume.configure(text="⏸️ Pausieren")
        self.update_top_state_banner()
        self.render_live_schedule()

    def toggle_timer_pause(self):
        if self.timer_sync_clock:
            self.user_forced_manual = True
            self.timer_sync_clock = False
            self.timer_running = False
            self.btn_pause_resume.configure(text="▶️ Fortsetzen")
            self.update_top_state_banner()
            return

        self.timer_running = not self.timer_running
        self.btn_pause_resume.configure(text="⏸️ Pausieren" if self.timer_running else "▶️ Fortsetzen")

    def step_manual_block(self, delta):
        if not self.schedule_blocks:
            return
        if delta > 0 and 0 <= self.manual_block_idx < len(self.schedule_blocks):
            gid = self.schedule_blocks[self.manual_block_idx].get("group_id")
            if gid:
                trip = self.cfg.get("current_trip") or DEFAULT_TRIP
                done_list = trip.setdefault("progress_done_ids", [])
                if gid not in done_list:
                    done_list.append(gid)
                    save_config(self.cfg)
        new_idx = max(0, min(len(self.schedule_blocks) - 1, self.manual_block_idx + delta))
        self.select_block_in_timer(new_idx)

    def tick_timer(self):
        try:
            self.seconds_until_next_poll -= 1
            if self.seconds_until_next_poll <= 0:
                self.run_background_live_poll()

            self.update_top_state_banner()

            if self.schedule_blocks:
                trip = self.cfg.get("current_trip") or DEFAULT_TRIP
                st = detect_trip_live_state(trip)

                if self.timer_sync_clock and not self.offline_async_mode:
                    now_m = now_minutes_of_day()
                    if st["state"] in ("im_zug", "umstieg"):
                        active_idx = None
                        for i, b in enumerate(self.schedule_blocks):
                            if b.get("start_min", 0) <= now_m < b.get("end_min", 0):
                                active_idx = i
                                break
                        if active_idx is None:
                            upcoming = [i for i, b in enumerate(self.schedule_blocks) if b.get("start_min", 0) > now_m]
                            active_idx = upcoming[0] if upcoming else len(self.schedule_blocks) - 1
                        self.manual_block_idx = active_idx
                        b = self.schedule_blocks[active_idx]
                        rem_sec = max(0, int(round((b["end_min"] - now_m) * 60)))
                        total_sec = max(1, int(b.get("duration_min", 1) * 60))
                        self.manual_remaining_sec = rem_sec
                        prog = 1.0 - (rem_sec / total_sec)
                        self.update_timer_display(b, rem_sec, prog)

                        if self.last_rendered_active_idx != active_idx:
                            self.last_rendered_active_idx = active_idx
                            self.auto_mark_elapsed_groups()
                            self.render_live_schedule()

                    elif st["state"] == "vorbereitung":
                        first_b = self.schedule_blocks[0]
                        wait_sec = st.get("wait_sec", 0)
                        self.manual_block_idx = 0
                        self.manual_remaining_sec = int(first_b.get("duration_min", 25) * 60)
                        self.update_timer_display(first_b, wait_sec, 0.0)
                    else:
                        first_b = self.schedule_blocks[0]
                        self.manual_remaining_sec = int(first_b.get("duration_min", 25) * 60)
                        self.update_timer_display(first_b, self.manual_remaining_sec, 0.0)
                else:
                    idx = max(0, min(len(self.schedule_blocks) - 1, self.manual_block_idx))
                    b = self.schedule_blocks[idx]
                    total_sec = max(1, int(b.get("duration_min", 1) * 60))
                    if self.manual_remaining_sec <= 0:
                        self.manual_remaining_sec = total_sec
                    if self.timer_running and self.manual_remaining_sec > 0:
                        self.manual_remaining_sec -= 1
                        if self.manual_remaining_sec <= 0 and idx < len(self.schedule_blocks) - 1:
                            self.manual_block_idx = idx + 1
                            nxt_b = self.schedule_blocks[self.manual_block_idx]
                            self.manual_remaining_sec = max(1, int(nxt_b.get("duration_min", 25) * 60))
                            self.render_live_schedule()
                    prog = 1.0 - (self.manual_remaining_sec / total_sec)
                    self.update_timer_display(b, self.manual_remaining_sec, prog)
        except Exception:
            pass
        self.root.after(1000, self.tick_timer)

    def update_timer_display(self, block, rem_sec, progress):
        rem_sec = max(0, int(rem_sec))
        if rem_sec >= 86400:
            days, rem_d = divmod(rem_sec, 86400)
            h, rem = divmod(rem_d, 3600)
            mins, secs = divmod(rem, 60)
            time_txt = f"{days}T {h:02d}:{mins:02d}:{secs:02d}"
        elif rem_sec >= 3600:
            h, rem = divmod(rem_sec, 3600)
            mins, secs = divmod(rem, 60)
            time_txt = f"{h:02d}:{mins:02d}:{secs:02d}"
        else:
            mins, secs = divmod(rem_sec, 60)
            time_txt = f"{mins:02d}:{secs:02d}"

        self.lbl_big_countdown.configure(text=time_txt)
        self.timer_progressbar.set(max(0.0, min(1.0, progress)))
        self.lbl_current_block_title.configure(text=block.get("title", ""))

        chips = block.get("chips") or []
        sig = "|".join(chips)
        if sig != self.last_rendered_chips_sig:
            self.last_rendered_chips_sig = sig
            self._render_pills_into(self.timer_pills_frame, chips)

    def open_reise_mappe(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        p = current_reise_mappe_path(trip)
        if os.path.isfile(p):
            os.startfile(p)
        else:
            messagebox.showinfo(
                "Reise-Mappe noch nicht erstellt",
                "Bitte klicke in Tab 1 („1. Planung & PDFs“) unten auf „📄 Reise-PDFs generieren“.",
            )

    # ---------- Verspätungs- & Verbindungs-Aktionen ----------
    def on_add_delay(self, minutes):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        sel = self.delay_leg_var.get()
        m = re.search(r"Zug\s+(\d+)", sel) or re.match(r"^(\d+)\.", sel)
        leg_idx = (int(m.group(1)) - 1) if m else 0
        missed, msg = apply_delay_to_trip(trip, leg_idx, minutes)

        if not self.timer_sync_clock or self.offline_async_mode:
            if 0 <= self.manual_block_idx < len(self.schedule_blocks):
                cur_b = self.schedule_blocks[self.manual_block_idx]
                if cur_b.get("leg_index") == leg_idx:
                    self.manual_remaining_sec += int(minutes) * 60

        save_config(self.cfg)
        self.show_delay_alert(msg, is_conflict=missed)
        self.log(f"\n{msg}")
        self.refresh()

    def on_missed_connection(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        sel = self.delay_leg_var.get()
        m = re.search(r"Zug\s+(\d+)", sel) or re.match(r"^(\d+)\.", sel)
        leg_idx = (int(m.group(1)) - 1) if m else None
        msg = trigger_missed_connection_plus_30(trip, leg_idx)
        save_config(self.cfg)
        self.show_delay_alert(msg, is_conflict=True)
        self.log(f"\n{msg}")
        self.refresh()

    def on_replace_connection(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        active_jobs = self.get_active_jobs()
        done_ids = get_elapsed_completed_groups(trip, active_jobs)
        for idx in range(min(self.manual_block_idx, len(self.schedule_blocks))):
            gid = self.schedule_blocks[idx].get("group_id")
            if gid and gid not in done_ids:
                done_ids.append(gid)

        trip["completed_group_ids"] = done_ids
        trip["progress_done_ids"] = []
        trip["extra_pause_min"] = 0
        trip["extra_pause_after_leg"] = 0
        save_config(self.cfg)
        self.show_delay_alert("")

        done_names = [g["module"] for g in GROUPS if g["id"] in done_ids]
        done_info = (
            f"Als erledigt gespeichert:\n• " + "\n• ".join(done_names)
            if done_names
            else "Alle offenen Module werden auf die neue Route verteilt."
        )

        ans = messagebox.askyesnocancel(
            "Route neu berechnen",
            f"Alte Verbindung verwerfen und Zeitplan neu berechnen.\n\n"
            f"{done_info}\n\n"
            f"Neue Verbindung im DB-Browser (bahn.de) wählen?\n"
            f"• JA = DB-Browser öffnen\n"
            f"• NEIN = Im Verbindungs-Editor eingeben",
        )
        if ans is True:
            self.sync_db_trip(interactive=True, preserve_completed=done_ids)
        elif ans is False:
            self.open_trip_editor(preserve_completed=done_ids, clear_old=True)

    def reset_trip_progress(self):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        trip["completed_group_ids"] = []
        trip["progress_done_ids"] = []
        trip["extra_pause_min"] = 0
        trip["extra_pause_after_leg"] = 0
        legs = trip.get("legs", [])
        for leg in legs:
            leg["delay_min"] = 0
            leg.pop("live_cancelled", None)
            if leg.get("planned_dep"):
                leg["dep"] = leg["planned_dep"]
            if leg.get("planned_arr"):
                leg["arr"] = leg["planned_arr"]
        for i in range(len(legs) - 1):
            legs[i]["transfer_after_min"] = diff_minutes(legs[i].get("arr"), legs[i + 1].get("dep"), 12)
        save_config(self.cfg)
        self.show_delay_alert("")
        self.refresh()

    # ---------- Reise-Konfiguration & DB-Sync ----------
    def on_module_toggle(self):
        self.save_toggles()
        self.refresh()

    def cycle_leg_mode(self, leg_idx):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        legs = trip.get("legs", [])
        if 0 <= leg_idx < len(legs):
            keys = [m[0] for m in LEG_MODES]
            cur = legs[leg_idx].get("mode", "focus")
            nxt_mode = keys[(keys.index(cur) + 1) % len(keys)] if cur in keys else "focus"
            legs[leg_idx]["mode"] = nxt_mode
            save_config(self.cfg)
            self.refresh()

    def sync_db_trip(self, interactive=False, preserve_completed=None):
        if self.busy:
            return
        self.busy = True
        self.progress.start()
        mode_txt = "Interaktiver DB-Browser" if interactive else "Hintergrund-Abfrage"
        self.log(f"\n🚆 Starte DB-Konto Synchronisation ({mode_txt}) …")

        def _run():
            try:
                trip, logged_in = fetch_db_trip_via_browser(self.cfg, interactive=interactive, log=self.log)
                if logged_in:
                    self.cfg["db_logged_in"] = True
                if trip and trip.get("legs"):
                    if preserve_completed:
                        trip["completed_group_ids"] = list(preserve_completed)
                    ensure_planned_times(trip)
                    self.cfg["current_trip"] = trip
                    save_config(self.cfg)
                    n_saved = len(self.cfg.get("saved_trips") or [])
                    self.log(
                        f"   ✅ Reise geladen: {format_date_with_weekday(trip['date'])} · {trip['title']} "
                        f"({len(trip['legs'])} Züge: {', '.join(l.get('train', '') for l in trip['legs'])}) "
                        f"[{n_saved} Reise(n) im Auswahl-Dropdown verfügbar]"
                    )
                    self.root.after(200, self.trigger_immediate_live_poll)
                else:
                    save_config(self.cfg)
                    if not logged_in and not interactive:
                        self.log("   ℹ️ Noch nicht bei bahn.de eingeloggt – öffne jetzt das Login-Fenster …")
                        trip2, logged_in2 = fetch_db_trip_via_browser(self.cfg, interactive=True, log=self.log)
                        if logged_in2:
                            self.cfg["db_logged_in"] = True
                        if trip2 and trip2.get("legs"):
                            if preserve_completed:
                                trip2["completed_group_ids"] = list(preserve_completed)
                            ensure_planned_times(trip2)
                            self.cfg["current_trip"] = trip2
                            self.log(f"   ✅ Reise übernommen: {format_date_with_weekday(trip2['date'])} · {trip2['title']} ({len(trip2['legs'])} Züge)")
                            self.root.after(200, self.trigger_immediate_live_poll)
                        save_config(self.cfg)
                    else:
                        self.log("   ℹ️ Keine neue Reise erkannt. Du kannst oben im Reise-Dropdown zwischen deinen gespeicherten Fahrten wechseln.")
            except Exception as e:
                self.log(f"   ⚠ DB-Abruf Hinweis: {e}")
            finally:
                self.root.after(0, self.finish)

        threading.Thread(target=_run, daemon=True).start()

    def open_trip_editor(self, preserve_completed=None, clear_old=False):
        w = ctk.CTkToplevel(self.root)
        w.title("Fahrt & Zugabschnitte anpassen – Entspannt Reisen")
        w.geometry("1040x650")
        w.configure(fg_color="#151a21")
        w.transient(self.root)
        w.grab_set()

        trip = json.loads(json.dumps(self.cfg.get("current_trip") or DEFAULT_TRIP))
        if clear_old:
            trip["extra_pause_min"] = 0
            trip["extra_pause_after_leg"] = 0
            for l in trip.get("legs", []):
                l["delay_min"] = 0
        if preserve_completed is not None:
            trip["completed_group_ids"] = list(preserve_completed)

        preset_frame = ctk.CTkFrame(w, fg_color="transparent")
        preset_frame.pack(fill="x", padx=20, pady=(16, 10))
        ctk.CTkLabel(preset_frame, text="Schnell-Vorlagen:", font=ctk.CTkFont(FONT_BODY, 14, "bold"), text_color="#eef1f5").pack(side="left")

        def apply_preset(kind):
            today = datetime.date.today().strftime("%d.%m.%Y")
            now_h = datetime.datetime.now().hour
            base_h = max(8, min(20, now_h))
            if kind == "ice1":
                trip["title"] = "Durchgehende ICE-Direktfahrt"
                trip["date"] = today
                trip["source"] = "Vorlage: 1× ICE Direktfahrt"
                dep_s = f"{base_h:02d}:00"
                arr_s = f"{(base_h + 2) % 24:02d}:15"
                trip["legs"] = [{
                    "train": "ICE 613", "type": "ICE", "from_station": "Mannheim Hbf", "to_station": "Stuttgart Hbf",
                    "planned_dep": dep_s, "planned_arr": arr_s,
                    "dep": dep_s, "arr": arr_s, "duration_min": 135, "transfer_after_min": 0, "delay_min": 0, "mode": "focus"
                }]
            elif kind == "regio3":
                trip["title"] = DEFAULT_TRIP["title"]
                trip["date"] = DEFAULT_TRIP["date"]
                trip["source"] = DEFAULT_TRIP["source"]
                trip["legs"] = json.loads(json.dumps(DEFAULT_TRIP["legs"]))
            elif kind == "regio_long_transfer":
                trip["title"] = "Fahrt mit langem Umstieg (35 Min. = 15m Pause + 20m Lernen)"
                trip["date"] = today
                trip["source"] = "Vorlage: Langer Umstieg + mittlerer Regio"
                trip["legs"] = [
                    {"train": "RE 1", "type": "REGIO", "from_station": "Mannheim Hbf", "to_station": "Heidelberg Hbf",
                     "planned_dep": "09:00", "planned_arr": "09:40", "dep": "09:00", "arr": "09:40",
                     "duration_min": 40, "transfer_after_min": 35, "delay_min": 0, "mode": "focus"},
                    {"train": "RB 68", "type": "REGIO", "from_station": "Heidelberg Hbf", "to_station": "Karlsruhe Hbf",
                     "planned_dep": "10:15", "planned_arr": "10:55", "dep": "10:15", "arr": "10:55",
                     "duration_min": 40, "transfer_after_min": 15, "delay_min": 0, "mode": "regio_memo"},
                    {"train": "IC 2013", "type": "ICE", "from_station": "Karlsruhe Hbf", "to_station": "Stuttgart Hbf",
                     "planned_dep": "11:10", "planned_arr": "11:55", "dep": "11:10", "arr": "11:55",
                     "duration_min": 45, "transfer_after_min": 0, "delay_min": 0, "mode": "focus"},
                ]
            title_var.set(trip["title"])
            date_var.set(trip["date"])
            render_leg_rows()

        ctk.CTkButton(
            preset_frame, text="🚄 1× Durchgehender ICE", command=lambda: apply_preset("ice1"),
            fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=17, height=34
        ).pack(side="left", padx=6)
        ctk.CTkButton(
            preset_frame, text="🚆 Fr. 06.11. Mannheim ➔ Ulm (3 Züge)", command=lambda: apply_preset("regio3"),
            fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=17, height=34
        ).pack(side="left", padx=6)
        ctk.CTkButton(
            preset_frame, text="⏳ Langer Umstieg (35m = Pause + Lernen)", command=lambda: apply_preset("regio_long_transfer"),
            fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=17, height=34
        ).pack(side="left", padx=6)

        meta_f = ctk.CTkFrame(w, fg_color="transparent")
        meta_f.pack(fill="x", padx=20, pady=6)
        ctk.CTkLabel(meta_f, text="Bezeichnung:", font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#eef1f5").pack(side="left")
        title_var = tk.StringVar(value=trip.get("title", ""))
        ctk.CTkEntry(meta_f, textvariable=title_var, width=420, height=34, corner_radius=10).pack(side="left", padx=8)
        ctk.CTkLabel(meta_f, text="Datum (TT.MM.JJJJ):", font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#eef1f5").pack(side="left", padx=(12, 0))
        date_var = tk.StringVar(value=trip.get("date", ""))
        ctk.CTkEntry(meta_f, textvariable=date_var, width=120, height=34, corner_radius=10).pack(side="left", padx=8)

        rows_container = ctk.CTkScrollableFrame(w, fg_color="#1c222b", corner_radius=20, border_width=0)
        rows_container.pack(fill="both", expand=True, padx=20, pady=10)

        leg_vars = []
        mode_labels = [m[1] for m in LEG_MODES]

        def sync_vars_to_trip():
            new_legs = []
            for lv in leg_vars:
                dep_s = lv["dep"].get().strip()
                arr_s = lv["arr"].get().strip()
                try:
                    dur_i = int(lv["dur"].get().strip())
                except ValueError:
                    dur_i = diff_minutes(dep_s, arr_s, 35)
                try:
                    tr_i = int(lv["transfer"].get().strip())
                except ValueError:
                    tr_i = 12
                tname = lv["train"].get().strip() or "Zug"
                sel_lbl = lv["mode_label"].get()
                mode_code = LEG_LABEL_TO_MODE.get(sel_lbl, sel_lbl if sel_lbl in LEG_MODE_LABELS else "focus")
                new_legs.append({
                    "train": tname,
                    "type": classify_train_type(tname),
                    "from_station": lv["from"].get().strip() or "Start",
                    "to_station": lv["to"].get().strip() or "Ziel",
                    "planned_dep": dep_s,
                    "planned_arr": arr_s,
                    "dep": dep_s,
                    "arr": arr_s,
                    "duration_min": dur_i,
                    "transfer_after_min": tr_i,
                    "delay_min": 0,
                    "mode": mode_code,
                })
            trip["legs"] = new_legs

        def render_leg_rows():
            for child in rows_container.winfo_children():
                child.destroy()
            leg_vars.clear()
            headers = ["Zug #", "Zugname", "Von (Startbahnhof)", "Nach (Zielbahnhof)", "Abfahrt", "Ankunft", "Dauer (m)", "Umstieg (m)", "Zug voll / frei? (Dropdown)", ""]
            for col, htxt in enumerate(headers):
                ctk.CTkLabel(rows_container, text=htxt, font=ctk.CTkFont(FONT_BODY, 12, "bold"), text_color="#9aa4b2").grid(row=0, column=col, padx=4, pady=4, sticky="w")

            for i, leg in enumerate(trip.get("legs", [])):
                cur_m = leg.get("mode", "focus")
                lv = {
                    "train": tk.StringVar(value=leg.get("train", "")),
                    "from": tk.StringVar(value=leg.get("from_station", "")),
                    "to": tk.StringVar(value=leg.get("to_station", "")),
                    "dep": tk.StringVar(value=leg.get("dep", "09:00")),
                    "arr": tk.StringVar(value=leg.get("arr", "09:45")),
                    "dur": tk.StringVar(value=str(leg.get("duration_min", 45))),
                    "transfer": tk.StringVar(value=str(leg.get("transfer_after_min", 15 if i < len(trip["legs"]) - 1 else 0))),
                    "mode_label": tk.StringVar(value=LEG_MODE_LABELS.get(cur_m, mode_labels[0])),
                }
                leg_vars.append(lv)
                r = i + 1
                ctk.CTkLabel(rows_container, text=f"Zug {r}", font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#dde2e9").grid(row=r, column=0, padx=4)
                ctk.CTkEntry(rows_container, textvariable=lv["train"], width=115, height=32, corner_radius=8).grid(row=r, column=1, padx=3, pady=4)
                ctk.CTkEntry(rows_container, textvariable=lv["from"], width=130, height=32, corner_radius=8).grid(row=r, column=2, padx=3)
                ctk.CTkEntry(rows_container, textvariable=lv["to"], width=130, height=32, corner_radius=8).grid(row=r, column=3, padx=3)
                ctk.CTkEntry(rows_container, textvariable=lv["dep"], width=65, height=32, corner_radius=8).grid(row=r, column=4, padx=3)
                ctk.CTkEntry(rows_container, textvariable=lv["arr"], width=65, height=32, corner_radius=8).grid(row=r, column=5, padx=3)
                ctk.CTkEntry(rows_container, textvariable=lv["dur"], width=60, height=32, corner_radius=8).grid(row=r, column=6, padx=3)
                ctk.CTkEntry(rows_container, textvariable=lv["transfer"], width=60, height=32, corner_radius=8).grid(row=r, column=7, padx=3)
                ctk.CTkOptionMenu(rows_container, variable=lv["mode_label"], values=mode_labels, width=250, height=32, corner_radius=8, fg_color="#262e39", button_color="#262e39", button_hover_color="#313a47").grid(row=r, column=8, padx=3)
                if len(trip["legs"]) > 1:
                    ctk.CTkButton(rows_container, text="✖", fg_color="transparent", text_color="#9aa4b2", hover_color="#3a1f24", width=34, height=32, corner_radius=8,
                                  command=lambda idx=i: remove_leg(idx)).grid(row=r, column=9, padx=3)

        def add_leg():
            sync_vars_to_trip()
            trip["legs"].append({
                "train": "RE 10", "type": "REGIO", "from_station": "Heidelberg Hbf", "to_station": "Mannheim Hbf",
                "planned_dep": "12:00", "planned_arr": "12:45",
                "dep": "12:00", "arr": "12:45", "duration_min": 45, "transfer_after_min": 0, "delay_min": 0, "mode": "focus"
            })
            assign_smart_leg_modes(trip["legs"])
            render_leg_rows()

        def remove_leg(idx):
            sync_vars_to_trip()
            if len(trip["legs"]) > 1:
                trip["legs"].pop(idx)
                assign_smart_leg_modes(trip["legs"])
                render_leg_rows()

        def auto_modes():
            sync_vars_to_trip()
            for leg in trip["legs"]:
                leg["duration_min"] = diff_minutes(leg["dep"], leg["arr"], leg["duration_min"])
            for i in range(len(trip["legs"]) - 1):
                trip["legs"][i]["transfer_after_min"] = diff_minutes(trip["legs"][i]["arr"], trip["legs"][i + 1]["dep"], 12)
            assign_smart_leg_modes(trip["legs"])
            render_leg_rows()

        def save_and_close():
            sync_vars_to_trip()
            trip["title"] = title_var.get().strip() or "Geplante Fahrt"
            trip["date"] = date_var.get().strip() or datetime.date.today().strftime("%d.%m.%Y")
            trip["extra_pause_min"] = 0
            ensure_planned_times(trip)
            self.cfg["current_trip"] = trip
            save_config(self.cfg)
            w.destroy()
            self.refresh()
            self.trigger_immediate_live_poll()

        render_leg_rows()

        bot = ctk.CTkFrame(w, fg_color="transparent")
        bot.pack(fill="x", padx=20, pady=(4, 16))
        ctk.CTkButton(bot, text="➕ Weiteren Zug hinzufügen", command=add_leg, fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=20, height=40).pack(side="left")
        ctk.CTkButton(bot, text="🪄 Zeiten & Regio-Modus automatisch berechnen", command=auto_modes, fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=20, height=40).pack(side="left", padx=10)
        ctk.CTkButton(bot, text="💾 Verbindung speichern & übernehmen", command=save_and_close, fg_color="#EC0016", hover_color="#c50014", font=ctk.CTkFont(FONT_BODY, 14, "bold"), corner_radius=20, height=40).pack(side="right")

    # ---------- Haupt-Lauf (Lernblätter & Reise-Mappe erstellen) ----------
    def save_toggles(self):
        self.cfg["overwrite"] = bool(self.overwrite_var.get())
        save_config(self.cfg)

    def log(self, msg):
        def _w():
            self.log_box.configure(state="normal")
            self.log_box.insert("end", msg + "\n")
            self.log_box.see("end")
            self.log_box.configure(state="disabled")
        self.root.after(0, _w)

    def open_output(self):
        os.makedirs(OUTPUT_ROOT, exist_ok=True)
        os.startfile(OUTPUT_ROOT)

    def start(self):
        if self.busy:
            return
        self.save_toggles()
        active_jobs = self.get_active_jobs()
        if not active_jobs:
            self.log("Keine offenen Übungen in den aktivierten Modulen gefunden.")
            return

        self.busy = True
        self.go_btn.configure(state="disabled", text="⏳ PDFs werden generiert …")
        self.progress.start()
        threading.Thread(target=self.worker, args=(active_jobs,), daemon=True).start()

    def worker(self, active_jobs):
        trip = self.cfg.get("current_trip") or DEFAULT_TRIP
        schedule_blocks, allocations = build_study_schedule(trip, active_jobs)

        self.log(f"\n🚆 Reise: {trip.get('title', '')} ({format_date_with_weekday(trip.get('date', ''))})")
        for b in schedule_blocks:
            self.log(f"   • [{b['time']} | {b['duration_min']}m] {b['title']}")

        names = {"agy_cli": "Gemini 4 Argon", "gemini_cli": "Gemini CLI", "gemini_api": "Gemini API", "claude_cli": "Claude CLI", "claude_api": "Claude API"}
        module_results = []
        ok = 0

        done_ids = set(trip.get("completed_group_ids") or [])
        remaining = [(g, it) for (g, it) in active_jobs if g["id"] not in done_ids] or list(active_jobs)
        skipped_list, short_hint, _ = get_skipped_jobs_info(trip, active_jobs, allocations)
        if skipped_list:
            self.log(f"\n{short_hint}")
        jobs_to_process = [(g, it) for (g, it) in remaining if g["id"] in allocations]
        if not jobs_to_process:
            self.log("\n☕ Alle Züge stehen auf Pause (keine Lernblätter für diese Fahrt nötig).")
            self.root.after(0, self.finish)
            return

        for grp, item in jobs_to_process:
            alloc = allocations.get(grp["id"])
            is_phone_memo = bool(alloc and (alloc.get("is_phone_memo") or alloc.get("mode") == "regio_memo"))
            out = summary_pdf_path(grp, item)
            md_path = os.path.splitext(out)[0] + ".md"
            mins_txt = f" (angepasst auf {alloc['minutes']} Min. in {alloc['leg_title']})" if alloc else ""

            if os.path.isfile(out) and os.path.isfile(md_path) and not self.cfg["overwrite"]:
                self.log(f"\n✓ {grp['icon']} {grp['module']}: „{item['name']}“ bereits vorhanden – binde in Reise-Mappe ein.")
                try:
                    with open(md_path, "r", encoding="utf-8") as f:
                        md = f.read()
                    module_results.append((grp, item, md, alloc))
                    if is_phone_memo:
                        phone_pdf = phone_memo_pdf_path(trip, grp)
                        write_phone_memo_pdf(md, phone_pdf, trip, grp, item, "Gespeichertes Lernblatt", allocation=alloc)
                        self.log(f"   📱 Handy-PDF (OneDrive) gespeichert: {phone_pdf}")
                    ok += 1
                    continue
                except Exception:
                    pass

            self.log(f"\n▶ {grp['icon']} {grp['module']}: „{item['name']}“{mins_txt}")
            try:
                md, pid = summarize(self.cfg, grp, item, self.log, allocation=alloc)
                prov_name = names.get(pid, pid)
                write_pdf(md, out, grp, prov_name, allocation=alloc)
                if is_phone_memo:
                    phone_pdf = phone_memo_pdf_path(trip, grp)
                    write_phone_memo_pdf(md, phone_pdf, trip, grp, item, prov_name, allocation=alloc)
                    self.log(f"   📱 Handy-PDF (OneDrive) gespeichert: {phone_pdf}")
                module_results.append((grp, item, md, alloc))
                self.log(f"   ✅ Einzel-PDF gespeichert: {os.path.relpath(out, ROOT)}")
                ok += 1
            except Exception as e:
                self.log(f"   ❌ Fehler: {e}")
                with open(os.path.join(tempfile.gettempdir(), "entspannt_reisen_error.log"), "a", encoding="utf-8") as f:
                    f.write(traceback.format_exc() + "\n")

        try:
            mappe_pdf = current_reise_mappe_path(trip)
            self.log("\n📘 Erstelle gemeinsame „Reise-Mappe.pdf“ (inkl. Zeitplan & Regio-Spickkarten) …")
            write_reise_mappe_pdf(trip, schedule_blocks, module_results, mappe_pdf)
            self.log(f"   ✅ Reise-Mappe fertig: {os.path.relpath(mappe_pdf, ROOT)}")
        except Exception as e:
            self.log(f"   ⚠ Fehler bei Reise-Mappe.pdf: {e}")

        try:
            ics_path = calendar_ics_path(trip)
            self.log("\n📅 Erstelle Apple-Kalenderdatei (.ics) für dein Handy …")
            write_trip_calendar_ics(trip, schedule_blocks, allocations, active_jobs, ics_path)
            self.log(f"   ✅ Kalenderdatei (OneDrive) gespeichert: {os.path.basename(ics_path)}")
            local_ics = os.path.join(OUTPUT_ROOT, f"Reise-Kalender ({safe_name((trip or {}).get('date', ''))}).ics")
            shutil.copy2(ics_path, local_ics)
        except Exception as e:
            self.log(f"   ⚠ Fehler bei Apple-Kalenderdatei (.ics): {e}")

        self.log(f"\nFertig: {ok} von {len(jobs_to_process)} Modul(en) bereit für die Fahrt. Gute & entspannte Reise! 🚆")
        self.root.after(0, self.finish)

    def finish(self):
        self.busy = False
        self.progress.stop()
        self.progress.set(0)
        self.go_btn.configure(state="normal", text="📄 Reise-PDFs generieren")
        self.refresh()

    # ---------- Einstellungen ----------
    def open_settings(self):
        w = ctk.CTkToplevel(self.root)
        w.title("Einstellungen & DB-Konto – Entspannt Reisen")
        w.geometry("760x600")
        w.configure(fg_color="#151a21")
        w.transient(self.root)
        w.grab_set()

        frame = ctk.CTkScrollableFrame(w, fg_color="transparent")
        frame.pack(fill="both", expand=True, padx=24, pady=20)

        ctk.CTkLabel(frame, text="1. Erkannte KIs auf diesem Laptop", font=ctk.CTkFont(FONT_HEAD, 16, "bold"), text_color="#eef1f5").pack(anchor="w", pady=(0, 6))
        for pid, desc, ok, hint in detect_providers(self.cfg):
            ctk.CTkLabel(
                frame,
                text=("✅ " if ok else "❌ ") + desc + (f"  – {hint}" if hint else ""),
                font=ctk.CTkFont(FONT_BODY, 13),
                text_color="#86d4a4" if ok else "#ff8a94",
            ).pack(anchor="w", pady=1)

        ctk.CTkButton(
            frame, text="🔑 Bei Gemini anmelden (öffnet Konsole)", command=self.gemini_login,
            fg_color="#262e39", text_color="#dde2e9", hover_color="#313a47", corner_radius=18, height=36
        ).pack(anchor="w", pady=(8, 14))

        prov_row = ctk.CTkFrame(frame, fg_color="transparent")
        prov_row.pack(fill="x", pady=4)
        ctk.CTkLabel(prov_row, text="Bevorzugte KI:", font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#dde2e9", width=200, anchor="w").pack(side="left")
        prov = tk.StringVar(value=self.cfg["provider"])
        ctk.CTkOptionMenu(prov_row, variable=prov, values=["auto", "agy_cli", "gemini_cli", "gemini_api", "claude_cli", "claude_api"], width=260, height=34, corner_radius=10, fg_color="#262e39", button_color="#262e39", button_hover_color="#313a47").pack(side="left")

        fields = [
            ("Argon / Gemini-Modell:", "gemini_cli_model", "gemini-4-argon-medium (oder gemini-4-argon-high)"),
            ("Claude-CLI-Modell:", "claude_cli_model", "opus = bestes Claude-Modell"),
            ("Gemini-API-Schlüssel:", "gemini_api_key", "optional, aistudio.google.com"),
            ("Anthropic-API-Schlüssel:", "anthropic_api_key", "optional"),
        ]
        evars = {}
        for label, key, hint in fields:
            row = ctk.CTkFrame(frame, fg_color="transparent")
            row.pack(fill="x", pady=4)
            ctk.CTkLabel(row, text=label, font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#dde2e9", width=200, anchor="w").pack(side="left")
            v = tk.StringVar(value=self.cfg.get(key, ""))
            ctk.CTkEntry(row, textvariable=v, width=260, height=34, corner_radius=10, show="•" if "key" in key else "").pack(side="left")
            ctk.CTkLabel(row, text=hint, font=ctk.CTkFont(FONT_BODY, 12), text_color="#9aa4b2").pack(side="left", padx=10)
            evars[key] = v

        ctk.CTkLabel(frame, text="2. DB-Konto (bahn.de) – Dauerhafter Login", font=ctk.CTkFont(FONT_HEAD, 16, "bold"), text_color="#eef1f5").pack(anchor="w", pady=(18, 4))
        ctk.CTkLabel(
            frame,
            text="Deine Browser-Sitzung wird dauerhaft lokal gespeichert. Optional kannst du hier deine DB-Zugangsdaten hinterlegen:",
            font=ctk.CTkFont(FONT_BODY, 12),
            text_color="#9aa4b2",
        ).pack(anchor="w", pady=(0, 8))

        for label, key, show_c in [("DB E-Mail / Benutzername:", "db_username", ""), ("DB Passwort (optional):", "db_password", "•")]:
            row = ctk.CTkFrame(frame, fg_color="transparent")
            row.pack(fill="x", pady=4)
            ctk.CTkLabel(row, text=label, font=ctk.CTkFont(FONT_BODY, 13, "bold"), text_color="#dde2e9", width=200, anchor="w").pack(side="left")
            v = tk.StringVar(value=self.cfg.get(key, ""))
            ctk.CTkEntry(row, textvariable=v, width=260, height=34, corner_radius=10, show=show_c).pack(side="left")
            evars[key] = v

        ctk.CTkButton(
            frame,
            text="🌐 Jetzt im DB-Browser anmelden (Sitzung dauerhaft speichern)",
            command=lambda: (w.destroy(), self.sync_db_trip(interactive=True)),
            fg_color="#262e39",
            text_color="#dde2e9",
            hover_color="#313a47",
            corner_radius=19,
            height=38,
        ).pack(anchor="w", pady=(10, 14))

        def save():
            self.cfg["provider"] = prov.get()
            for k, v in evars.items():
                self.cfg[k] = v.get().strip()
            save_config(self.cfg)
            w.destroy()
            self.refresh()

        ctk.CTkButton(
            frame, text="💾 Einstellungen speichern", command=save,
            fg_color="#EC0016", hover_color="#c50014", font=ctk.CTkFont(FONT_HEAD, 15, "bold"), corner_radius=22, height=44
        ).pack(fill="x", pady=(12, 0))

    def gemini_login(self):
        if not shutil.which("gemini"):
            if messagebox.askyesno("Gemini CLI fehlt", "Die Gemini CLI ist nicht installiert. Jetzt installieren (npm)?"):
                subprocess.Popen('start "Gemini CLI installieren" cmd /k "npm install -g @google/gemini-cli && echo Fertig! Fenster schliessen."', shell=True)
            return
        messagebox.showinfo("Gemini anmelden",
                            "Es öffnet sich ein Konsolenfenster.\n\n"
                            "1. Wähle „Login with Google“ und melde dich im Browser an.\n"
                            "2. Sobald du die Eingabezeile siehst, tippe /quit.\n"
                            "3. Danach hier auf „Aktualisieren“ klicken.")
        subprocess.Popen('start "Gemini Login" cmd /k gemini', shell=True, cwd=tempfile.gettempdir())


if __name__ == "__main__":
    root = ctk.CTk()
    App(root)
    root.mainloop()
