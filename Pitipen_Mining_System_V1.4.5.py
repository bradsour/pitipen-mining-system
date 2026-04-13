
"""
Pitipen Mining System
- OCR de firmas radar
- Selección múltiple de modos
- Overlay inspirado en Star Citizen
- Integración UEX para precios RAW y REFINADOS
- Caché SQLite local de 12 horas
- Soporte multiidioma: ES / EN / FR / DE / RU
- Configuración de token UEX desde interfaz
- Ayuda / guía de uso / botón de donación
"""

import csv
import json
import base64
import os
import re
import sqlite3
import threading
import time
import webbrowser
from pathlib import Path

import cv2
import mss
import numpy as np
import pytesseract
import requests
import tkinter as tk
from tkinter import messagebox

try:
    import keyboard
except Exception:
    keyboard = None

INTERVAL = 0.02
HISTORY_SIZE = 6
VOTE_THRESHOLD = 1
MAX_MULT = 50
DETECTION_TTL = 30
HOLD_LAST_DETECTION = 2.0

UEX_API_BASE = "https://api.uexcorp.space/2.0"
UEX_CACHE_TTL = 12 * 60 * 60
UEX_HTTP_TIMEOUT = 15
SUPPORT_PROMPT_INTERVAL = 5

PAYPAL_URL = ""
DISCORD_URL = ""

BG = "#0b0f14"
PANEL = "#121820"
PANEL_2 = "#0f141b"
BORDER = "#1f2a35"
TEXT = "#d7e1ea"
MUTED = "#6f889c"
ACCENT = "#00ffc3"
GREEN = "#6cff9a"
RED = "#ff5c5c"
GOLD = "#ffd166"
REFINED_COLOR = "#ffd166"
STAR_FULL = "◆"
STAR_EMPTY = "◆"
STAR_EMPTY_COLOR = "#2a3a4a"

FONT_UI = "Orbitron"
FONT_ALT = "Segoe UI"
FONT_MONO = "Consolas"

DEFAULT_MODES = {"asteroid"}
ROOT_NAME = "Pitipen Mining System"
APP_VERSION = "1.4.5"
APP_VERSION_LABEL = f"V {APP_VERSION}"
VERSION_JSON_URL = "https://raw.githubusercontent.com/bradsour/pitipen-mining-system/main/version.json"

import sys as _sys, os as _os
if getattr(_sys, "_MEIPASS", None):
    _BASE_DIR = Path(_sys.executable).parent
else:
    _BASE_DIR = Path(_os.path.dirname(_os.path.abspath(__file__)))

CONFIG_FILE = _BASE_DIR / "config.json"
CSV_FILE = _BASE_DIR / "Minerales.csv"
PREFS_FILE = _BASE_DIR / "preferences.json"
UEX_DB_FILE = _BASE_DIR / "uex_cache.sqlite3"

# Archivo de log OCR junto al exe para diagnóstico en producción
OCR_LOG_FILE = _BASE_DIR / "ocr_debug.log"

SUPPORTED_LANGS = ["es", "en", "fr", "de", "ru"]
LANG = "en"

OCR_SENSITIVITY_PROFILES = {
    "low": {
        "label": {"es": "Baja", "en": "Low", "fr": "Faible", "de": "Niedrig", "ru": "Низкая"},
        "vote_threshold": 3,
        "upscale": 3,
        "crop_pad_x": 10,
        "crop_pad_y": 6,
        "min_confident_repeats": 3,
    },
    "normal": {
        "label": {"es": "Normal", "en": "Normal", "fr": "Normale", "de": "Normal", "ru": "Обычная"},
        "vote_threshold": 2,
        "upscale": 4,
        "crop_pad_x": 12,
        "crop_pad_y": 7,
        "min_confident_repeats": 2,
    },
    "high": {
        "label": {"es": "Alta", "en": "High", "fr": "Élevée", "de": "Hoch", "ru": "Высокая"},
        "vote_threshold": 1,
        "upscale": 5,
        "crop_pad_x": 14,
        "crop_pad_y": 8,
        "min_confident_repeats": 2,
    },
}
DEFAULT_OCR_SENSITIVITY = "normal"
DEFAULT_CALIBRATION_HOTKEY = "F8"
DEFAULT_SHOW_OVERLAY_HOTKEY = "F7"
HOTKEY_OPTIONS = ["F6", "F7", "F8", "F9", "F10"]
PREVIEW_MODES = ["none", "raw", "processed"]


TEXTS = {
    "app_title": {"es":"Pitipen Mining System","en":"Pitipen Mining System","fr":"Pitipen Mining System","de":"Pitipen Mining System","ru":"Pitipen Mining System"},
    "app_subtitle": {
        "es":"Interfaz táctica de firmas radar y mercado",
        "en":"Tactical radar signature and market interface",
        "fr":"Interface tactique de signatures radar et marché",
        "de":"Taktische Radar-Signatur- und Marktoberfläche",
        "ru":"Тактический интерфейс радарных сигнатур и рынка",
    },
    "search_modules":{"es":"Módulos de búsqueda","en":"Search modules","fr":"Modules de recherche","de":"Suchmodule","ru":"Модули поиска"},
    "calibrate_zone":{"es":"⊙ CALIBRAR ZONA","en":"⊙ CALIBRATE AREA","fr":"⊙ CALIBRER LA ZONE","de":"⊙ BEREICH KALIBRIEREN","ru":"⊙ КАЛИБРОВАТЬ ОБЛАСТЬ"},
    "start_system":{"es":"▶ INICIAR SISTEMA","en":"▶ START SYSTEM","fr":"▶ DÉMARRER LE SYSTÈME","de":"▶ SYSTEM STARTEN","ru":"▶ ЗАПУСТИТЬ СИСТЕМУ"},
    "csv_loaded":{"es":"✔ CSV cargado","en":"✔ CSV loaded","fr":"✔ CSV chargé","de":"✔ CSV geladen","ru":"✔ CSV загружен"},
    "csv_error":{"es":"⚠ No se pudo cargar Minerales.csv","en":"⚠ Could not load Minerales.csv","fr":"⚠ Impossible de charger Minerales.csv","de":"⚠ Minerales.csv konnte nicht geladen werden","ru":"⚠ Не удалось загрузить Minerales.csv"},
    "calibration_hint":{
        "es":"Consejo: calibra solo los dígitos, sin iconos ni bordes del HUD.",
        "en":"Tip: calibrate only the digits, without HUD icons or borders.",
        "fr":"Conseil : calibrez uniquement les chiffres, sans icônes ni bordures du HUD.",
        "de":"Tipp: Kalibriere nur die Ziffern, ohne HUD-Symbole oder Ränder.",
        "ru":"Совет: калибруйте только цифры, без значков и границ HUD.",
    },
    "market_uex":{"es":"MERCADO UEX","en":"UEX MARKET","fr":"MARCHÉ UEX","de":"UEX-MARKT","ru":"РЫНОК UEX"},
    "no_material_selected":{"es":"Sin material seleccionado","en":"No material selected","fr":"Aucun matériau sélectionné","de":"Kein Material ausgewählt","ru":"Материал не выбран"},
    "scanning":{"es":"Escaneando firmas...","en":"Scanning signatures...","fr":"Analyse des signatures...","de":"Signaturen werden gescannt...","ru":"Сканирование сигнатур..."},
    "value":{"es":"VALOR","en":"VALUE","fr":"VALEUR","de":"WERT","ru":"ЗНАЧЕНИЕ"},
    "apply":{"es":"CONSULTAR","en":"QUERY","fr":"RECHERCHER","de":"ABFRAGEN","ru":"ЗАПРОСИТЬ"},
    "manual_entry_hint":{"es":"Entrada de datos manual","en":"Manual data entry","fr":"Saisie manuelle","de":"Manuelle Eingabe","ru":"Ручной ввод"},
    "raw":{"es":"RAW","en":"RAW","fr":"BRUT","de":"ROH","ru":"СЫРЬЁ"},
    "refined":{"es":"REFINADO por SCU","en":"REFINED per SCU","fr":"RAFFINÉ par SCU","de":"RAFFINIERT pro SCU","ru":"ПЕРЕРАБОТАННОЕ за SCU"},
    "surface_mining_prices":{"es":"MINERÍA EN SUPERFICIE","en":"SURFACE MINING","fr":"MINAGE DE SURFACE","de":"OBERFLÄCHENABBAU","ru":"ДОБЫЧА НА ПОВЕРХНОСТИ"},
    "salvage_prices":{"es":"CHATARRERÍA","en":"SALVAGE","fr":"RÉCUPÉRATION","de":"BERGUNG","ru":"САЛЬВАЖ"},
    "sell_prices":{"es":"Precios de venta","en":"Sell prices","fr":"Prix de vente","de":"Verkaufspreise","ru":"Цены продажи"},
    "cache":{"es":"caché","en":"cache","fr":"cache","de":"Cache","ru":"кэш"},
    "live":{"es":"live","en":"live","fr":"live","de":"live","ru":"live"},
    "old_cache":{"es":"antigua","en":"old","fr":"ancien","de":"alt","ru":"старый"},
    "no_data":{"es":"Sin dato","en":"No data","fr":"Pas de donnée","de":"Keine Daten","ru":"Нет данных"},
    "invalid_manual":{"es":"Entrada manual no válida.","en":"Invalid manual input.","fr":"Entrée manuelle invalide.","de":"Ungültige manuelle Eingabe.","ru":"Недопустимый ручной ввод."},
    "manual_not_match":{"es":"Ese valor no encaja con los modos activos.","en":"That value does not match the active modes.","fr":"Cette valeur ne correspond pas aux modes actifs.","de":"Dieser Wert passt nicht zu den aktiven Modi.","ru":"Это значение не соответствует активным режимам."},
    "active_modes":{"es":"Modos activos:","en":"Active modes:","fr":"Modes actifs :","de":"Aktive Modi:","ru":"Активные режимы:"},
    "invalid_fast_read":{"es":"Lectura rápida no validada:","en":"Fast unvalidated read:","fr":"Lecture rapide non validée :","de":"Schnelle ungültige Lesung:","ru":"Быстрое неподтверждённое чтение:"},
    "ocr_error":{"es":"Error OCR:","en":"OCR error:","fr":"Erreur OCR :","de":"OCR-Fehler:","ru":"Ошибка OCR:"},
    "no_new_detection_30s":{"es":"Sin nuevas detecciones en 30 s.","en":"No new detections in 30 s.","fr":"Aucune nouvelle détection en 30 s.","de":"Keine neuen Erkennungen seit 30 s.","ru":"Нет новых обнаружений за 30 с."},
    "consulting_market":{"es":"Consultando mercado:","en":"Checking market:","fr":"Consultation du marché :","de":"Markt wird geprüft:","ru":"Проверка рынка:"},
    "market_cache_sqlite":{"es":"caché SQLite 12h","en":"SQLite cache 12h","fr":"cache SQLite 12h","de":"SQLite-Cache 12h","ru":"кэш SQLite 12ч"},
    "language":{"es":"Idioma","en":"Language","fr":"Langue","de":"Sprache","ru":"Язык"},
    "uex_settings":{"es":"UEX Market","en":"UEX Market","fr":"Marché UEX","de":"UEX-Markt","ru":"Рынок UEX"},
    "enable_market":{"es":"Activar precios de mercado","en":"Enable market prices","fr":"Activer les prix du marché","de":"Marktpreise aktivieren","ru":"Включить рыночные цены"},
    "token":{"es":"Token UEX","en":"UEX token","fr":"Jeton UEX","de":"UEX-Token","ru":"Токен UEX"},
    "save":{"es":"Guardar","en":"Save","fr":"Enregistrer","de":"Speichern","ru":"Сохранить"},
    "test":{"es":"Probar","en":"Test","fr":"Tester","de":"Testen","ru":"Проверить"},
    "show":{"es":"Mostrar","en":"Show","fr":"Afficher","de":"Anzeigen","ru":"Показать"},
    "hide":{"es":"Ocultar","en":"Hide","fr":"Masquer","de":"Verbergen","ru":"Скрыть"},
    "token_not_set":{"es":"Token no configurado","en":"Token not set","fr":"Jeton non configuré","de":"Token nicht konfiguriert","ru":"Токен не настроен"},
    "token_saved":{"es":"Token guardado","en":"Token saved","fr":"Jeton enregistré","de":"Token gespeichert","ru":"Токен сохранён"},
    "token_valid":{"es":"Token válido","en":"Valid token","fr":"Jeton valide","de":"Gültiger Token","ru":"Токен действителен"},
    "token_test_error":{"es":"Error al probar token:","en":"Error testing token:","fr":"Erreur lors du test du jeton :","de":"Fehler beim Testen des Tokens:","ru":"Ошибка проверки токена:"},
    "help":{"es":"Ayuda","en":"Help","fr":"Aide","de":"Hilfe","ru":"Помощь"},
    "guide":{"es":"Guía de uso","en":"Usage guide","fr":"Guide d'utilisation","de":"Anleitung","ru":"Руководство"},
    "donate":{"es":"Apoya este proyecto","en":"Support this project","fr":"Soutenez ce projet","de":"Unterstütze dieses Projekt","ru":"Поддержите этот проект"},
    "support_popup_title":{"es":"Apoya este proyecto","en":"Support this project","fr":"Soutenez ce projet","de":"Unterstütze dieses Projekt","ru":"Поддержите этот проект"},
    "support_popup_body":{
        "es":"Desarrollado por un jugador apasionado del juego, este proyecto es totalmente gratuito y requiere tiempo para mantenerse.\n\nSi realmente te está ayudando, considera apoyar el proyecto para poder seguir mejorándolo.\n\nEste mensaje dejará de mostrarse si decides apoyar el proyecto.",
        "en":"Built by a player passionate about the game, this project is completely free and takes time to maintain.\n\nIf it is genuinely helping you, please consider supporting the project so it can keep improving.\n\nThis message will stop appearing if you choose to support the project.",
        "fr":"Créé par un joueur passionné par le jeu, ce projet est entièrement gratuit et demande du temps pour être maintenu.\n\nS'il vous aide vraiment, pensez à soutenir le projet pour qu'il puisse continuer à s'améliorer.\n\nCe message ne s'affichera plus si vous décidez de soutenir le projet.",
        "de":"Dieses Projekt wurde von einem leidenschaftlichen Spieler entwickelt, ist völlig kostenlos und benötigt Zeit für die Pflege.\n\nWenn es dir wirklich hilft, unterstütze das Projekt, damit es weiter verbessert werden kann.\n\nDiese Nachricht wird nicht mehr angezeigt, wenn du dich entscheidest, das Projekt zu unterstützen.",
        "ru":"Этот проект создан увлечённым игроком, полностью бесплатен и требует времени на поддержку.\n\nЕсли он действительно помогает вам, подумайте о поддержке проекта, чтобы его можно было и дальше улучшать.\n\nЭто сообщение больше не будет появляться, если вы решите поддержать проект.",
    },
    "support_popup_continue":{"es":"Continuar","en":"Continue","fr":"Continuer","de":"Weiter","ru":"Продолжить"},
    "help_title":{"es":"Cómo conseguir tu token UEX","en":"How to get your UEX token","fr":"Comment obtenir votre jeton UEX","de":"So erhalten Sie Ihren UEX-Token","ru":"Как получить токен UEX"},
    "help_body":{
        "es":"1. Entra en UEX\n2. Inicia sesión\n3. Ve a My Apps\n4. Crea una app nueva\n5. Copia el token\n6. Pégalo aquí\n7. Guarda y prueba conexión\n\nConsejo: no actives bloqueos raros si no los necesitas.",
        "en":"1. Go to UEX\n2. Sign in\n3. Open My Apps\n4. Create a new app\n5. Copy the token\n6. Paste it here\n7. Save and test connection\n\nTip: do not enable unusual locks unless you need them.",
        "fr":"1. Allez sur UEX\n2. Connectez-vous\n3. Ouvrez My Apps\n4. Créez une nouvelle app\n5. Copiez le jeton\n6. Collez-le ici\n7. Enregistrez et testez la connexion\n\nConseil : n'activez pas de verrous inutiles.",
        "de":"1. Gehen Sie zu UEX\n2. Melden Sie sich an\n3. Öffnen Sie My Apps\n4. Erstellen Sie eine neue App\n5. Kopieren Sie den Token\n6. Fügen Sie ihn hier ein\n7. Speichern und Verbindung testen\n\nTipp: Aktivieren Sie keine unnötigen Sperren.",
        "ru":"1. Перейдите в UEX\n2. Войдите в систему\n3. Откройте My Apps\n4. Создайте новое приложение\n5. Скопируйте токен\n6. Вставьте его сюда\n7. Сохраните и проверьте соединение\n\nСовет: не включайте лишние блокировки без необходимости.",
    },
    "guide_title":{"es":"Guía rápida de uso","en":"Quick usage guide","fr":"Guide d'utilisation rapide","de":"Kurzanleitung","ru":"Краткое руководство"},
    "guide_body":{
        "es":"1. Calibra solo los números.\n2. Marca los modos de búsqueda.\n3. Inicia el sistema.\n4. Si quieres precios, añade tu token UEX.\n5. Los datos de mercado se guardan 12 horas en caché.\n6. Si la API falla, el programa mostrará el fallo y usará caché antigua si existe.",
        "en":"1. Calibrate only the digits.\n2. Select the search modes.\n3. Start the system.\n4. If you want prices, add your UEX token.\n5. Market data is cached for 12 hours.\n6. If the API fails, the program shows the error and uses old cache if available.",
        "fr":"1. Calibrez uniquement les chiffres.\n2. Sélectionnez les modes de recherche.\n3. Démarrez le système.\n4. Si vous voulez les prix, ajoutez votre jeton UEX.\n5. Les données du marché sont mises en cache pendant 12 heures.\n6. Si l'API échoue, le programme affiche l'erreur et utilise l'ancien cache si disponible.",
        "de":"1. Kalibrieren Sie nur die Ziffern.\n2. Wählen Sie die Suchmodi.\n3. Starten Sie das System.\n4. Wenn Sie Preise möchten, fügen Sie Ihren UEX-Token hinzu.\n5. Marktdaten werden 12 Stunden zwischengespeichert.\n6. Wenn die API fehlschlägt, zeigt das Programm den Fehler und verwendet alten Cache, falls vorhanden.",
        "ru":"1. Калибруйте только цифры.\n2. Выберите режимы поиска.\n3. Запустите систему.\n4. Если нужны цены, добавьте токен UEX.\n5. Рыночные данные кэшируются на 12 часов.\n6. Если API недоступен, программа покажет ошибку и использует старый кэш, если он есть.",
    },
    "donate_not_configured":{
        "es":"Configura tu enlace de PayPal en la constante PAYPAL_URL del script.",
        "en":"Set your PayPal link in the PAYPAL_URL constant in the script.",
        "fr":"Configurez votre lien PayPal dans la constante PAYPAL_URL du script.",
        "de":"Konfigurieren Sie Ihren PayPal-Link in der Konstante PAYPAL_URL im Skript.",
        "ru":"Укажите ссылку PayPal в константе PAYPAL_URL в скрипте.",
    },
    "market_disabled":{"es":"Mercado desactivado","en":"Market disabled","fr":"Marché désactivé","de":"Markt deaktiviert","ru":"Рынок отключён"},
    "asteroids":{"es":"Asteroides","en":"Asteroids","fr":"Astéroïdes","de":"Asteroiden","ru":"Астероиды"},
    "ship_mining":{"es":"Minería con nave","en":"Ship mining","fr":"Minage en vaisseau","de":"Schiffsbergbau","ru":"Корабельная добыча"},
    "hand_mining":{"es":"Minería en Superficie","en":"Surface mining","fr":"Minage de surface","de":"Oberflächenbergbau","ru":"Добыча на поверхности"},
    "salvage":{"es":"Chatarrería","en":"Salvage","fr":"Récupération","de":"Bergung","ru":"Сальваж"},
    "possible_materials":{"es":"Materiales posibles:","en":"Possible materials:","fr":"Matériaux possibles :","de":"Mögliche Materialien:","ru":"Возможные материалы:"},
    "contains":{"es":"Contiene:","en":"Contains:","fr":"Contient :","de":"Enthält:","ru":"Содержит:"},
    "history_duration":{"es":"Duración mensajes (s)","en":"Message duration (s)","fr":"Durée des messages (s)","de":"Nachrichtendauer (s)","ru":"Длительность сообщений (с)"},
    "ocr_sensitivity":{"es":"Sensibilidad OCR","en":"OCR sensitivity","fr":"Sensibilité OCR","de":"OCR-Empfindlichkeit","ru":"Чувствительность OCR"},
    "preview_mode":{"es":"Vista previa","en":"Preview","fr":"Aper?u","de":"Vorschau","ru":"Preview"},
    "preview_none":{"es":"Ninguna","en":"None","fr":"Aucun","de":"Keine","ru":"None"},
    "preview_raw":{"es":"OCR Preview","en":"OCR Preview","fr":"OCR Preview","de":"OCR Preview","ru":"OCR Preview"},
    "preview_processed":{"es":"Imagen procesada","en":"Processed Image","fr":"Image trait?e","de":"Verarbeitetes Bild","ru":"Processed Image"},
    "verify_candidates": {"es":"Verificar candidatos","en":"Verify candidates","fr":"V?rifier candidats","de":"Kandidaten pr?fen","ru":"Verify candidates"},
    "calibration_hotkey":{"es":"Atajo calibración","en":"Calibration hotkey","fr":"Raccourci calibration","de":"Kalibrierungs-Hotkey","ru":"Горячая клавиша калибровки"},
    "hotkey_saved":{"es":"Atajo guardado","en":"Hotkey saved","fr":"Raccourci enregistré","de":"Hotkey gespeichert","ru":"Горячая клавиша сохранена"},
    "hotkeys_unavailable":{"es":"Hotkeys no disponibles","en":"Hotkeys unavailable","fr":"Raccourcis indisponibles","de":"Hotkeys nicht verfügbar","ru":"Горячие клавиши недоступны"},
    "settings_saved":{"es":"Configuración guardada","en":"Settings saved","fr":"Configuration enregistrée","de":"Einstellungen gespeichert","ru":"Настройки сохранены"},
    "loading_market":{"es":"Cargando mercado:","en":"Loading market:","fr":"Chargement du marché :","de":"Markt wird geladen:","ru":"Загрузка рынка:"},
    "click_history_hint":{"es":"Haz clic en el historial para recargar precios","en":"Click history to reload prices","fr":"Cliquez sur l'historique pour recharger les prix","de":"Klicken Sie auf den Verlauf, um Preise neu zu laden","ru":"Нажмите на историю, чтобы перезагрузить цены"},
}

MANUAL_CONTENTS = {
    "3000": ["Hadanite", "Aphorite", "Dolivine", "Janalite"],
    "4000": ["Hadanite", "Aphorite", "Dolivine", "Janalite"],
}

ASTEROID_CONTENTS = {
    "Asteroide Tipo C": {"common": ["Quartz", "Copper", "Tungsten", "Iron"], "rare": ["Quantainium", "Stileron"]},
    "Asteroide Tipo E": {"common": ["Silicon", "Iron", "Tungsten", "Corundum"], "rare": ["Quantainium", "Laranite"]},
    "Asteroide Tipo M": {"common": ["Quartz", "Copper", "Silicon", "Titanium"], "rare": ["Quantainium", "Riccite", "Stileron"]},
    "Asteroide Tipo P": {"common": ["Quartz", "Copper", "Iron", "Titanium"], "rare": ["Quantainium", "Riccite", "Stileron"]},
    "Asteroide Tipo Q": {"common": ["Quartz", "Copper", "Iron", "Titanium"], "rare": ["Quantainium", "Stileron"]},
    "Asteroide Tipo S": {"common": ["Titanium", "Quartz", "Iron", "Tungsten"], "rare": ["Quantainium", "Riccite"]},
}

SURFACE_MINING_MATERIALS = [
    "Janalite", "Hadanite", "Feynmaline", "Beradom", "Dolivine",
    "Glacosite", "Aphorite", "Carinite", "Jaclium", "Saldynium",
]

SALVAGE_MARKET_ITEMS = [
    "Construction Materials",
    "Recycled Material Composite",
]

COMMODITY_ALIASES = {
    "Aluminium": ["Aluminum"],
    "Aslarite": ["Aslarite", "Astatine"],
    "Agricium": ["Agricium"],
    "Beryl": ["Beryl"],
    "Bexalite": ["Bexalite"],
    "Borase": ["Borase"],
    "Copper": ["Copper"],
    "Corundum": ["Corundum"],
    "Gold": ["Gold"],
    "Hephestanite": ["Hephestanite"],
    "Ice": ["Ice"],
    "Iron": ["Iron"],
    "Laranite": ["Laranite"],
    "Quartz": ["Quartz"],
    "Silicon": ["Silicon"],
    "Taranite": ["Taranite"],
    "Titanium": ["Titanium"],
    "Tin": ["Tin"],
    "Torite": ["Torite"],
    "Tungsten": ["Tungsten"],
    "Quantainium": ["Quantainium"],
    "Riccite": ["Riccite"],
    "Lindinium": ["Lindinium"],
    "Ouratite": ["Ouratite"],
    "Savrilum": ["Savrilum"],
    "Stileron": ["Stileron"],
}

def T(key):
    return TEXTS.get(key, {}).get(LANG, TEXTS.get(key, {}).get("en", key))

def ocr_sensitivity_label(key):
    profile = OCR_SENSITIVITY_PROFILES.get(key, OCR_SENSITIVITY_PROFILES[DEFAULT_OCR_SENSITIVITY])
    labels = profile.get("label", {})
    return labels.get(LANG, labels.get("en", key))

def load_ocr_sensitivity():
    val = load_prefs().get("__ocr_sensitivity__", DEFAULT_OCR_SENSITIVITY) if 'load_prefs' in globals() else DEFAULT_OCR_SENSITIVITY
    return val if val in OCR_SENSITIVITY_PROFILES else DEFAULT_OCR_SENSITIVITY

def save_ocr_sensitivity(value):
    prefs = load_prefs()
    prefs["__ocr_sensitivity__"] = value if value in OCR_SENSITIVITY_PROFILES else DEFAULT_OCR_SENSITIVITY
    save_prefs(prefs)

def get_ocr_profile():
    return OCR_SENSITIVITY_PROFILES.get(load_ocr_sensitivity(), OCR_SENSITIVITY_PROFILES[DEFAULT_OCR_SENSITIVITY])


def _parse_version_tuple(version_str):
    cleaned = str(version_str).strip().lower().lstrip('v').replace(' ', '')
    parts = []
    for chunk in cleaned.split('.'):
        digits = ''.join(ch for ch in chunk if ch.isdigit())
        parts.append(int(digits) if digits else 0)
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts[:3])


def is_remote_version_newer(remote_version, local_version=APP_VERSION):
    return _parse_version_tuple(remote_version) > _parse_version_tuple(local_version)


def fetch_version_info(timeout=5):
    try:
        response = requests.get(VERSION_JSON_URL, timeout=timeout)
        response.raise_for_status()
        payload = response.json()
        version = str(payload.get('version', '')).strip()
        changes = payload.get('changes', []) or []
        url = str(payload.get('url', '')).strip()
        if not version:
            return None
        return {'version': version, 'changes': changes, 'url': url}
    except Exception as e:
        _ocr_log(f"[update_check] {e}")
        return None



# ---------------------------------------------------------------------------
# Logging OCR para diagnóstico en producción (escribe en ocr_debug.log)
# ---------------------------------------------------------------------------
def _ocr_log(msg):
    """Escribe una línea de log OCR en ocr_debug.log junto al exe."""
    try:
        with open(OCR_LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{time.strftime('%H:%M:%S')}] {msg}\n")
    except Exception:
        pass

def _reset_ocr_log():
    try:
        OCR_LOG_FILE.write_text("", encoding="utf-8")
    except Exception:
        pass

_reset_ocr_log()



# ---------------------------------------------------------------------------
# CORRECCIÓN 1: _find_tesseract — lógica robusta para exe + carpeta integrada
#
# Estructura esperada junto al .exe:
#   MiApp/
#   ├── Pitipen_Mining_System.exe
#   └── tesseract/
#       ├── tesseract.exe
#       └── tessdata/
#           └── eng.traineddata   ← debe ser la versión COMPLETA, no "fast"
# ---------------------------------------------------------------------------
def _find_tesseract():
    import sys, os, shutil

    def _configure_tesseract_dir(tess_dir):
        """
        Configura TESSDATA_PREFIX y PATH para una carpeta de Tesseract.
        tess_dir debe contener tesseract.exe y la subcarpeta tessdata/.
        Devuelve (ruta_exe, ruta_tessdata) si todo está correcto.
        """
        exe_path = os.path.join(tess_dir, "tesseract.exe")
        tessdata_dir = os.path.join(tess_dir, "tessdata")
        traineddata = os.path.join(tessdata_dir, "eng.traineddata")

        if not os.path.exists(exe_path):
            _ocr_log(f"[tesseract] tesseract.exe not found at: {tess_dir}")
            return None, None
        if not os.path.isdir(tessdata_dir):
            _ocr_log(f"[tesseract] tessdata/ folder not found at: {tess_dir}")
            return None, None
        if not os.path.exists(traineddata):
            _ocr_log(f"[tesseract] eng.traineddata not found at: {tessdata_dir}")

        # Forzamos la carpeta tessdata real y además la pasaremos por config.
        os.environ["TESSDATA_PREFIX"] = tessdata_dir

        current_path = os.environ.get("PATH", "")
        if tess_dir not in current_path:
            os.environ["PATH"] = tess_dir + os.pathsep + current_path

        _ocr_log(f"[tesseract] configurado OK → {exe_path}")
        _ocr_log(f"[tesseract] TESSDATA_PREFIX → {tessdata_dir}")
        return exe_path, tessdata_dir

    # 1) Caso PyInstaller --onedir: la carpeta tesseract/ está junto al .exe
    app_dir = os.path.dirname(sys.executable) if getattr(sys, "frozen", False)               else os.path.dirname(os.path.abspath(__file__))

    exe, tessdata = _configure_tesseract_dir(os.path.join(app_dir, "tesseract"))
    if exe:
        return exe, tessdata

    # 2) Caso PyInstaller --onefile: recursos en _MEIPASS
    meipass_base = getattr(sys, "_MEIPASS", None)
    if meipass_base:
        exe, tessdata = _configure_tesseract_dir(os.path.join(meipass_base, "tesseract"))
        if exe:
            return exe, tessdata

    # 3) Carpeta del script cuando se ejecuta sin empaquetar (.py directo)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    if script_dir != app_dir:
        exe, tessdata = _configure_tesseract_dir(os.path.join(script_dir, "tesseract"))
        if exe:
            return exe, tessdata

    # 4) Tesseract instalado en el sistema / PATH
    t = shutil.which("tesseract")
    if t:
        t_dir = os.path.dirname(t)
        tessdata_dir = os.path.join(t_dir, "tessdata")
        if os.path.isdir(tessdata_dir):
            os.environ["TESSDATA_PREFIX"] = tessdata_dir
            current_path = os.environ.get("PATH", "")
            if t_dir not in current_path:
                os.environ["PATH"] = t_dir + os.pathsep + current_path
            _ocr_log(f"[tesseract] TESSDATA_PREFIX → {tessdata_dir}")
        _ocr_log(f"[tesseract] encontrado en PATH → {t}")
        return t, tessdata_dir if os.path.isdir(tessdata_dir) else None

    # 5) Rutas típicas de instalación de Windows
    for c in [
        r"C:\Program Files\Tesseract-OCR\tesseract.exe",
        r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
        r"D:\Tesseract-OCR\tesseract.exe",
    ]:
        if Path(c).exists():
            t_dir = str(Path(c).parent)
            tessdata_dir = os.path.join(t_dir, "tessdata")
            if os.path.isdir(tessdata_dir):
                os.environ["TESSDATA_PREFIX"] = tessdata_dir
                current_path = os.environ.get("PATH", "")
                if t_dir not in current_path:
                    os.environ["PATH"] = t_dir + os.pathsep + current_path
                _ocr_log(f"[tesseract] TESSDATA_PREFIX → {tessdata_dir}")
            _ocr_log(f"[tesseract] encontrado en ruta fija → {c}")
            return c, tessdata_dir if os.path.isdir(tessdata_dir) else None

    _ocr_log("[tesseract] ERROR: no se encontró tesseract en ninguna ruta conocida")
    return "tesseract", None  # último recurso


TESSERACT_CMD, TESSDATA_DIR = _find_tesseract()
pytesseract.pytesseract.tesseract_cmd = TESSERACT_CMD

def _build_tess_config(oem=1):
    parts = []
    if TESSDATA_DIR:
        # Sin comillas aquí para evitar rutas rotas del tipo:
        # "D:/Pitipen/tesseract/tessdata"/eng.traineddata
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append("--psm 7")
    parts.append(f"--oem {oem}")
    parts.append("-c tessedit_char_whitelist=0123456789")
    return " ".join(parts)

# CORRECCIÓN 2: usar solo LSTM (--oem 1).
# El fallback legacy (--oem 0) se desactiva porque suele fallar
# cuando el paquete de idiomas no incluye los datos del motor clásico.
TESS_CONFIG      = _build_tess_config(1)
TESS_CONFIG_FALL = TESS_CONFIG

try:
    v = pytesseract.get_tesseract_version()
    _ocr_log(f"[tesseract] versión detectada: {v}")
    _ocr_log(f"[tesseract] command used: {TESSERACT_CMD}")
    _ocr_log(f"[tesseract] tessdata used: {TESSDATA_DIR}")
except Exception as e:
    _ocr_log(f"[tesseract] ERROR REAL al validar instalación: {e}")


def f_ui(size, weight="normal"): return (FONT_UI, size, weight)
def f_alt(size, weight="normal"): return (FONT_ALT, size, weight)
def f_mono(size, weight="normal"): return (FONT_MONO, size, weight)

def format_price(value):
    try:
        v = float(value)
        if v >= 1_000_000: return f"{v/1_000_000:.1f} M"
        if v >= 1_000: return f"{v/1_000:.0f} k"
        return f"{v:.0f}"
    except Exception: return "—"

def load_prefs():
    if PREFS_FILE.exists():
        try: return json.loads(PREFS_FILE.read_text(encoding="utf-8"))
        except Exception: return {}
    return {}

def save_prefs(prefs):
    try: PREFS_FILE.write_text(json.dumps(prefs, indent=2, ensure_ascii=False), encoding="utf-8")
    except Exception: pass

def load_selected_modes():
    prefs = load_prefs()
    modes = set(prefs.get("__selected_modes__", []))
    return modes if modes else set(DEFAULT_MODES)

def save_selected_modes(modes):
    prefs = load_prefs(); prefs["__selected_modes__"] = sorted(list(modes)); save_prefs(prefs)

def load_overlay_geometry(): return load_prefs().get("__overlay_geometry__", "720x900+30+30")
def save_overlay_geometry(geometry):
    prefs = load_prefs(); prefs["__overlay_geometry__"] = geometry; save_prefs(prefs)

def load_lang():
    prefs = load_prefs(); lang = prefs.get("__lang__", "en")
    return lang if lang in SUPPORTED_LANGS else "en"

def save_lang(lang):
    prefs = load_prefs(); prefs["__lang__"] = lang; save_prefs(prefs)

def load_uex_token(): return load_prefs().get("__uex_token__", "")
def save_uex_token(token):
    prefs = load_prefs(); prefs["__uex_token__"] = token; save_prefs(prefs)

def load_market_enabled(): return bool(load_prefs().get("__market_enabled__", False))
def save_market_enabled(enabled):
    prefs = load_prefs(); prefs["__market_enabled__"] = bool(enabled); save_prefs(prefs)

def load_preview_mode():
    val = str(load_prefs().get("__preview_mode__", "none")).lower()
    return val if val in PREVIEW_MODES else "none"
def save_preview_mode(mode):
    mode = str(mode).lower()
    prefs = load_prefs(); prefs["__preview_mode__"] = mode if mode in PREVIEW_MODES else "none"; save_prefs(prefs)

def load_verify_enabled(): return bool(load_prefs().get("__verify_enabled__", False))
def save_verify_enabled(enabled):
    prefs = load_prefs(); prefs["__verify_enabled__"] = bool(enabled); save_prefs(prefs)

def load_history_duration():
    try:
        val = int(load_prefs().get("__history_duration__", DETECTION_TTL))
    except Exception:
        val = DETECTION_TTL
    return max(5, min(300, val))

def save_history_duration(seconds):
    prefs = load_prefs()
    prefs["__history_duration__"] = int(max(5, min(300, seconds)))
    save_prefs(prefs)

def load_calibration_hotkey():
    val = str(load_prefs().get("__calibration_hotkey__", DEFAULT_CALIBRATION_HOTKEY)).upper()
    return val if val in HOTKEY_OPTIONS else DEFAULT_CALIBRATION_HOTKEY

def save_calibration_hotkey(value):
    prefs = load_prefs()
    value = str(value).upper()
    prefs["__calibration_hotkey__"] = value if value in HOTKEY_OPTIONS else DEFAULT_CALIBRATION_HOTKEY
    save_prefs(prefs)

def save_ocr_sensitivity_setting(value):
    save_ocr_sensitivity(value)

def _support_connect():
    return sqlite3.connect(UEX_DB_FILE)

def _support_init_db():
    con = _support_connect()
    try:
        cur = con.cursor()
        cur.execute(
            "CREATE TABLE IF NOT EXISTS app_support_state ("
            "id INTEGER PRIMARY KEY CHECK (id = 1), "
            "launch_count INTEGER NOT NULL DEFAULT 0, "
            "support_clicked INTEGER NOT NULL DEFAULT 0, "
            "prompt_disabled INTEGER NOT NULL DEFAULT 0, "
            "last_prompt_launch INTEGER NOT NULL DEFAULT 0)"
        )
        cur.execute(
            "INSERT OR IGNORE INTO app_support_state (id, launch_count, support_clicked, prompt_disabled, last_prompt_launch) "
            "VALUES (1, 0, 0, 0, 0)"
        )
        con.commit()
    finally:
        con.close()

def get_support_state():
    _support_init_db()
    con = _support_connect()
    try:
        con.row_factory = sqlite3.Row
        row = con.execute(
            "SELECT launch_count, support_clicked, prompt_disabled, last_prompt_launch "
            "FROM app_support_state WHERE id = 1"
        ).fetchone()
        if not row:
            return {"launch_count": 0, "support_clicked": 0, "prompt_disabled": 0, "last_prompt_launch": 0}
        return {k: int(row[k] or 0) for k in row.keys()}
    finally:
        con.close()

def increment_support_launch():
    _support_init_db()
    con = _support_connect()
    try:
        cur = con.cursor()
        cur.execute("UPDATE app_support_state SET launch_count = launch_count + 1 WHERE id = 1")
        con.commit()
    finally:
        con.close()
    return get_support_state()

def record_support_prompt_shown(launch_count):
    _support_init_db()
    con = _support_connect()
    try:
        con.execute("UPDATE app_support_state SET last_prompt_launch = ? WHERE id = 1", (int(launch_count),))
        con.commit()
    finally:
        con.close()

def mark_support_clicked():
    _support_init_db()
    con = _support_connect()
    try:
        con.execute("UPDATE app_support_state SET support_clicked = 1, prompt_disabled = 1 WHERE id = 1")
        con.commit()
    finally:
        con.close()

class GlobalHotkeyManager:
    def __init__(self):
        self._handles = []

    @property
    def available(self):
        return keyboard is not None

    def clear(self):
        if keyboard is None:
            self._handles.clear()
            return
        for handle in self._handles:
            try:
                keyboard.remove_hotkey(handle)
            except Exception:
                pass
        self._handles.clear()

    def add(self, hotkey, callback):
        if keyboard is None:
            return False
        try:
            handle = keyboard.add_hotkey(str(hotkey).lower(), callback, suppress=False, trigger_on_release=False)
            self._handles.append(handle)
            return True
        except Exception as e:
            _ocr_log(f"[hotkey] error registering {hotkey}: {e}")
            return False

    def stop(self):
        self.clear()

def _load_icon(root):
    import sys, os
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    ico_path = os.path.join(base, "star_detection.ico")
    try: root.iconbitmap(ico_path)
    except Exception: pass

def stars(rarete):
    try:
        n = int(rarete)
        if 0 <= n <= 3: return n, 3-n
    except Exception: pass
    return None

MODE_INFO = {
    "asteroid":{"label_key":"asteroids","fallback":"Asteroides","color":ACCENT},
    "material":{"label_key":"ship_mining","fallback":"Minería con nave","color":GREEN},
    "hand":{"label_key":"hand_mining","fallback":"Minería en Superficie","color":GOLD},
    "salvage":{"label_key":"salvage","fallback":"Chatarrería","color":RED},
}
BASE_SIGNATURES = {"asteroid":{1700,1720,1750,1850,1870,1900},"hand":{3000,4000},"salvage":{2000}}

def mode_label(mode_key):
    info = MODE_INFO.get(mode_key, {})
    return T(info.get("label_key","")) if info.get("label_key") else info.get("fallback", mode_key)

def _infer_subrol(sig):
    if sig in BASE_SIGNATURES["asteroid"]: return "asteroid"
    if sig in (3000, 4000): return "hand"
    if sig in (2000,1450): return "salvage"
    return "material"

def load_csv(path: Path):
    if not path.exists(): raise FileNotFoundError(f"Archivo no encontrado: {path}")
    mapping = {}
    with open(path, newline="", encoding="utf-8-sig") as f:
        sample = f.read(1024); f.seek(0)
        sep = ";" if sample.count(";") > sample.count(",") else ","
        reader = csv.DictReader(f, delimiter=sep)
        for row in reader:
            code = (row.get("signature_radar") or row.get("firma_radar") or "").strip()
            nom = (row.get("nom") or row.get("nombre") or "").strip()
            contenu = (row.get("contenu") or row.get("contenido") or "").strip()
            rarete = (row.get("rarete") or row.get("rareza") or "").strip()
            rol = (row.get("rol") or "").strip() or "ship"
            subrol = (row.get("subrol") or "").strip()
            if not code.isdigit(): continue
            sig = int(code)
            if not subrol: subrol = _infer_subrol(sig)
            mapping[sig] = {"signature":sig,"nom":nom or f"Firma {sig}","contenu":contenu,"rarete":rarete,"rol":rol,"subrol":subrol}
    return mapping

def build_lookup(mapping, max_mult=MAX_MULT):
    lookup = {}
    for sig, item in mapping.items():
        for mult in range(1, max_mult + 1):
            val = str(sig * mult)
            entry = {"signature":sig,"nom":item["nom"],"contenu":item["contenu"],"rarete":item["rarete"],"rol":item["rol"],"subrol":item["subrol"],"mult":mult}
            lookup.setdefault(val, []).append(entry)
    return lookup

def filter_matches_for_modes(matches, active_modes): return [m for m in matches if m["subrol"] in active_modes]

def find_matches(value, lookup, active_modes):
    matches = filter_matches_for_modes(lookup.get(str(value), []), active_modes)
    def _sort_key(m):
        try: r = int(m["rarete"]); has_rarete = 1
        except Exception: r = 0; has_rarete = 0
        return (has_rarete, r, m["mult"], m["nom"])
    return sorted(matches, key=_sort_key)

def allowed_by_modes(value, lookup, active_modes): return bool(find_matches(value, lookup, active_modes))

def capture_region(region):
    with mss.mss() as sct:
        raw = sct.grab(region)
        img = np.frombuffer(raw.bgra, dtype=np.uint8).reshape(raw.height, raw.width, 4)
        return cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)

def crop_to_number(img):
    """
    Recorte conservador: prioriza no cortar el número aunque deje algo de margen.
    """
    try:
        profile = get_ocr_profile()
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        h, w = gray.shape
        row_max = np.max(gray, axis=1)
        bright_threshold = max(120, int(np.percentile(row_max, 65)))
        active_rows = np.where(row_max >= bright_threshold)[0]
        if len(active_rows) == 0:
            return img
        pad_y = int(profile.get("crop_pad_y", 7))
        y_min = max(0, active_rows[0] - pad_y)
        y_max = min(h, active_rows[-1] + pad_y + 1)

        region = gray[y_min:y_max, :]
        col_max = np.max(region, axis=0)
        bright_threshold_x = max(120, int(np.percentile(col_max, 60)))
        active_cols = np.where(col_max >= bright_threshold_x)[0]
        if len(active_cols) == 0:
            return img

        pad_x = int(profile.get("crop_pad_x", 12))
        x_min = max(0, active_cols[0] - pad_x)
        x_max = min(w, active_cols[-1] + pad_x + 1)
        cropped = img[y_min:y_max, x_min:x_max]
        if cropped.shape[0] >= 5 and cropped.shape[1] >= 10:
            return cropped
    except Exception as e:
        _ocr_log(f"[crop_to_number] excepción: {e}")
    return img

def _upscale_for_ocr(img):
    h, w = img.shape[:2]
    scale = max(2, int(get_ocr_profile().get("upscale", 4)))
    return cv2.resize(img, (w * scale, h * scale), interpolation=cv2.INTER_CUBIC)

def preprocess_bright(img):
    img = _upscale_for_ocr(img)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    gray = cv2.GaussianBlur(gray, (3, 3), 0)
    gray = cv2.convertScaleAbs(gray, alpha=1.6, beta=18)
    _, binary = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    return cv2.morphologyEx(binary, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))

def preprocess_adaptive(img):
    img = _upscale_for_ocr(img)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    gray = cv2.bilateralFilter(gray, 5, 35, 35)
    binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                   cv2.THRESH_BINARY, 31, -2)
    return cv2.morphologyEx(binary, cv2.MORPH_CLOSE, np.ones((2, 2), np.uint8))

def preprocess_support_color(img):
    img = _upscale_for_ocr(img)
    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
    mask_low_sat = cv2.inRange(hsv, np.array([0, 0, 125]), np.array([180, 120, 255]))
    v = hsv[:, :, 2]
    _, mask_bright = cv2.threshold(v, 150, 255, cv2.THRESH_BINARY)
    mask = cv2.bitwise_or(mask_low_sat, mask_bright)
    return cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))

def preprocess_gray(img):
    img = _upscale_for_ocr(img)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    return cv2.convertScaleAbs(gray, alpha=1.4, beta=12)

OCR_CONFUSIONS = {"8":["6","3","0"],"6":["8"],"3":["8"],"0":["8"],"5":["6","8"]}

def candidate_corrections(val):
    yielded = set()
    if val not in yielded: yielded.add(val); yield val
    if len(val) >= 4:
        trimmed = val[1:]
        if trimmed not in yielded: yielded.add(trimmed); yield trimmed
    for i, c in enumerate(val):
        for repl in OCR_CONFUSIONS.get(c, []):
            cand = val[:i] + repl + val[i+1:]
            if cand not in yielded: yielded.add(cand); yield cand


def _run_tesseract(proc, config):
    """
    Ejecuta pytesseract con el config dado.
    Devuelve lista de candidatos num?ricos (3-6 d?gitos), aceptando comas.
    Registra cualquier error en el log.
    """
    try:
        text = pytesseract.image_to_string(proc, config=config).strip()
        raw = re.findall(r"\d[\d,]{2,8}", text)
        cleaned = []
        for val in raw:
            norm = val.replace(",", "")
            if norm.isdigit() and 3 <= len(norm) <= 6:
                cleaned.append(norm)
        return cleaned
    except Exception as e:
        _ocr_log(f"[tesseract] error con config '{config}': {e}")
        return []


# ---------------------------------------------------------------------------
# CORRECCIÓN 3: read_number reescrita
#
# Cambios respecto al original:
#  - El fallback con imagen invertida se ejecuta UNA SOLA VEZ al final,
#    cuando ninguna de las tres versiones produjo candidatos. Ya no está
#    dentro del bucle for (bug del original).
#  - Se añade un segundo intento con TESS_CONFIG_FALL (--oem 0) si --oem 1
#    no devuelve nada, como seguro ante instalaciones sin modelo LSTM completo.
#  - Los errores de Tesseract se registran en ocr_debug.log en lugar de
#    silenciarse con "except: pass".
# ---------------------------------------------------------------------------
def _read_number_internal(img, lookup, active_modes):
    img = crop_to_number(img)
    processed_versions = [
        preprocess_bright(img),
        preprocess_adaptive(img),
        preprocess_gray(img),
        preprocess_support_color(img),
    ]

    raw_candidates = []
    for proc in processed_versions:
        raw_candidates.extend(_run_tesseract(proc, TESS_CONFIG))

    if not raw_candidates:
        for proc in processed_versions[:3]:
            inv = cv2.bitwise_not(proc)
            raw_candidates.extend(_run_tesseract(inv, TESS_CONFIG))

    if not raw_candidates:
        _ocr_log("[read_number] no candidates after all attempts")
        return None, raw_candidates, []

    validated = []
    numeric_fallback = []
    for raw in raw_candidates:
        for cand in candidate_corrections(raw):
            if cand.isdigit():
                numeric_fallback.append(str(int(cand)))
            if cand in lookup and allowed_by_modes(int(cand), lookup, active_modes):
                validated.append(str(int(cand)))

    if validated:
        counts = {}
        for cand in validated:
            counts[cand] = counts.get(cand, 0) + 1
        return max(counts, key=counts.get), raw_candidates, validated

    _ocr_log(f"[read_number] discarded unvalidated candidates: {raw_candidates}")
    return None, raw_candidates, validated


def read_number(img, lookup, active_modes):
    value, _, _ = _read_number_internal(img, lookup, active_modes)
    return value


class UEXMarketError(Exception): pass

class UEXMarketClient:
    def __init__(self, token="", db_path=UEX_DB_FILE):
        self.token = token.strip()
        self.db_path = Path(db_path)
        self.session = requests.Session()
        self._init_db()

    def set_token(self, token): self.token = token.strip()
    def _connect(self): return sqlite3.connect(self.db_path)

    def _init_db(self):
        con = self._connect()
        try:
            cur = con.cursor()
            cur.execute("CREATE TABLE IF NOT EXISTS commodity_map (detected_name TEXT PRIMARY KEY, commodity_id INTEGER, commodity_name TEXT, updated_at INTEGER)")
            cur.execute("CREATE TABLE IF NOT EXISTS market_prices (detected_name TEXT, price_type TEXT, system_name TEXT, price_sell REAL, terminal_name TEXT, commodity_id INTEGER, commodity_name TEXT, updated_at INTEGER, PRIMARY KEY (detected_name, price_type, system_name))")
            con.commit()
        finally: con.close()

    def _headers(self):
        headers = {"Accept":"application/json"}
        if self.token: headers["Authorization"] = f"Bearer {self.token}"
        return headers

    def _get(self, endpoint, params=None):
        url = f"{UEX_API_BASE}/{endpoint}"
        r = self.session.get(url, params=params or {}, headers=self._headers(), timeout=UEX_HTTP_TIMEOUT)
        r.raise_for_status()
        payload = r.json()
        status = payload.get("status")
        if status not in ("ok", None): raise UEXMarketError(f"API status: {status}")
        return payload

    def test_connection(self):
        if not self.token: raise UEXMarketError(T("token_not_set"))
        self._get("commodities", {})
        return True

    def _normalize(self, s): return str(s).strip().lower().replace(" ","").replace("-","").replace("_","")
    def _catalog(self): return self._get("commodities").get("data", [])

    def resolve_commodity(self, detected_name):
        now = int(time.time())
        con = self._connect()
        try:
            cur = con.cursor()
            row = cur.execute("SELECT commodity_id, commodity_name, updated_at FROM commodity_map WHERE detected_name=?", (detected_name,)).fetchone()
            if row and now - int(row[2]) < UEX_CACHE_TTL:
                return {"id": row[0], "name": row[1]}

            commodities = self._catalog()
            alias_candidates = [detected_name] + COMMODITY_ALIASES.get(detected_name, [])
            chosen = None

            for alias in alias_candidates:
                alias_lower = str(alias).strip().lower()
                for c in commodities:
                    if str(c.get("name", "")).strip().lower() == alias_lower:
                        chosen = c; break
                if chosen: break

            if chosen is None:
                for alias in alias_candidates:
                    alias_norm = self._normalize(alias)
                    for c in commodities:
                        if self._normalize(c.get("name", "")) == alias_norm:
                            chosen = c; break
                    if chosen: break

            if chosen is None:
                for alias in alias_candidates:
                    alias_norm = self._normalize(alias)
                    contains = [c for c in commodities if alias_norm and alias_norm in self._normalize(c.get("name", ""))]
                    if contains: chosen = contains[0]; break

            if chosen is None:
                raise UEXMarketError(f"No se pudo resolver commodity: {detected_name}")

            cur.execute(
                "INSERT INTO commodity_map (detected_name, commodity_id, commodity_name, updated_at) VALUES (?, ?, ?, ?) "
                "ON CONFLICT(detected_name) DO UPDATE SET commodity_id=excluded.commodity_id, commodity_name=excluded.commodity_name, updated_at=excluded.updated_at",
                (detected_name, int(chosen["id"]), str(chosen.get("name", detected_name)), now)
            )
            con.commit()
            return {"id": int(chosen["id"]), "name": str(chosen.get("name", detected_name))}
        finally:
            con.close()

    def _fetch_raw_prices(self, commodity_id): return self._get("commodities_raw_prices", {"id_commodity": commodity_id}).get("data", [])
    def _fetch_refined_prices(self, commodity_id): return self._get("commodities_prices", {"id_commodity": commodity_id}).get("data", [])

    def get_best_system_lines(self, detected_name, price_type="refined"):
        commodity = self.resolve_commodity(detected_name)
        cid = commodity["id"]; cname = commodity["name"]

        cached = self._read_cached_block(detected_name, price_type)
        if cached:
            return {"detected_name":detected_name,"commodity_name":cname,"price_type":price_type,
                    "systems":cached.get("systems",[]),"updated_at":cached.get("updated_at"),
                    "cached":True,"stale":cached.get("stale",False),"error":None}

        try:
            rows = self._fetch_raw_prices(cid) if price_type == "raw" else self._fetch_refined_prices(cid)
            systems = self._aggregate_best_by_system(rows)
            self._write_cached_block(detected_name, price_type, cid, cname, systems)
            refreshed = self._read_cached_block(detected_name, price_type, allow_stale=True)
            if refreshed:
                return {"detected_name":detected_name,"commodity_name":cname,"price_type":price_type,
                        "systems":refreshed.get("systems",[]),"updated_at":refreshed.get("updated_at"),
                        "cached":refreshed.get("cached",False),"stale":refreshed.get("stale",False),"error":None}
            return {"detected_name":detected_name,"commodity_name":cname,"price_type":price_type,
                    "systems":systems,"updated_at":int(time.time()),"cached":False,"stale":False,"error":None}
        except Exception as e:
            stale = self._read_cached_block(detected_name, price_type, allow_stale=True)
            if stale:
                return {"detected_name":detected_name,"commodity_name":cname,"price_type":price_type,
                        "systems":stale.get("systems",[]),"updated_at":stale.get("updated_at"),
                        "cached":stale.get("cached",False),"stale":True,"error":str(e)}
            return {"detected_name":detected_name,"commodity_name":cname,"price_type":price_type,
                    "systems":[],"updated_at":None,"cached":False,"stale":False,"error":str(e)}


    def get_top_terminals_by_system(self, detected_name, price_type="refined", top_n=3):
        commodity = self.resolve_commodity(detected_name)
        cid = commodity["id"]; cname = commodity["name"]
        try:
            rows = self._fetch_raw_prices(cid) if price_type == "raw" else self._fetch_refined_prices(cid)
            systems = self._aggregate_top_terminals_by_system(rows, top_n=top_n)
            return {
                "detected_name": detected_name,
                "commodity_name": cname,
                "price_type": price_type,
                "systems": systems,
                "updated_at": int(time.time()),
                "cached": False,
                "stale": False,
                "error": None,
            }
        except Exception as e:
            return {
                "detected_name": detected_name,
                "commodity_name": cname,
                "price_type": price_type,
                "systems": [],
                "updated_at": None,
                "cached": False,
                "stale": False,
                "error": str(e),
            }

    def _aggregate_top_terminals_by_system(self, rows, top_n=3):
        grouped = {}
        for row in rows:
            system_name = (row.get("star_system_name") or "").strip()
            terminal_name = (row.get("terminal_name") or "").strip()
            price_sell = row.get("price_sell")
            if not system_name or not terminal_name or price_sell in (None, "", 0):
                continue
            try:
                price_sell = float(price_sell)
            except Exception:
                continue
            system_map = grouped.setdefault(system_name, {})
            current = system_map.get(terminal_name)
            if current is None or price_sell > current["price_sell"]:
                system_map[terminal_name] = {"terminal_name": terminal_name, "price_sell": price_sell}

        order = {"Stanton": 0, "Pyro": 1, "Nyx": 2}
        result = []
        for system_name, terminals_map in grouped.items():
            terminals = sorted(
                terminals_map.values(),
                key=lambda x: (-x["price_sell"], x["terminal_name"])
            )[:max(1, int(top_n))]
            best_price = terminals[0]["price_sell"] if terminals else 0
            result.append({
                "system_name": system_name,
                "best_price": best_price,
                "terminals": terminals,
            })
        return sorted(result, key=lambda x: (order.get(x["system_name"], 99), -x["best_price"], x["system_name"]))

    def get_multi_market_lines(self, names, price_type="refined"):
        items = []; errors = []
        for name in names:
            res = self.get_best_system_lines(name, price_type=price_type)
            items.append(res)
            if res.get("error"): errors.append(f"{name}: {res['error']}")
        return {"items":items,"error":" | ".join(errors) if errors else None}

    def _aggregate_best_by_system(self, rows):
        best = {}
        for row in rows:
            system_name  = (row.get("star_system_name") or "").strip()
            terminal_name = (row.get("terminal_name") or "").strip()
            price_sell   = row.get("price_sell")
            if not system_name or price_sell in (None,"",0): continue
            try: price_sell = float(price_sell)
            except Exception: continue
            cur = best.get(system_name)
            if cur is None or price_sell > cur["price_sell"]:
                best[system_name] = {"system_name":system_name,"price_sell":price_sell,"terminal_name":terminal_name}
        order = {"Stanton":0,"Pyro":1,"Nyx":2}
        return sorted(best.values(), key=lambda x: (order.get(x["system_name"],99), -x["price_sell"], x["system_name"]))

    def _read_cached_block(self, detected_name, price_type, allow_stale=False):
        now = int(time.time())
        con = self._connect()
        try:
            cur = con.cursor()
            rows = cur.execute("SELECT system_name, price_sell, terminal_name, commodity_id, commodity_name, updated_at FROM market_prices WHERE detected_name=? AND price_type=?", (detected_name, price_type)).fetchall()
            if not rows: return None
            updated_at = max(int(r[5]) for r in rows)
            if not allow_stale and now - updated_at >= UEX_CACHE_TTL: return None
            systems = [{"system_name":r[0],"price_sell":float(r[1]),"terminal_name":r[2] or ""} for r in rows]
            order = {"Stanton":0,"Pyro":1,"Nyx":2}
            systems = sorted(systems, key=lambda x: (order.get(x["system_name"],99), -x["price_sell"], x["system_name"]))
            return {"systems":systems,"updated_at":updated_at,"cached":True,"stale":(now - updated_at >= UEX_CACHE_TTL)}
        finally: con.close()

    def _write_cached_block(self, detected_name, price_type, commodity_id, commodity_name, systems):
        now = int(time.time())
        con = self._connect()
        try:
            cur = con.cursor()
            cur.execute("DELETE FROM market_prices WHERE detected_name=? AND price_type=?", (detected_name, price_type))
            for row in systems:
                cur.execute("INSERT OR REPLACE INTO market_prices (detected_name, price_type, system_name, price_sell, terminal_name, commodity_id, commodity_name, updated_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (detected_name, price_type, row["system_name"], float(row["price_sell"]), row.get("terminal_name",""), int(commodity_id), commodity_name, now))
            con.commit()
        finally: con.close()

    def get_market_summary(self, detected_name):
        commodity = self.resolve_commodity(detected_name)
        cid = commodity["id"]; cname = commodity["name"]
        raw_cached = self._read_cached_block(detected_name, "raw")
        refined_cached = self._read_cached_block(detected_name, "refined")
        if raw_cached and refined_cached:
            return {"detected_name":detected_name,"commodity_name":cname,"raw":raw_cached,"refined":refined_cached,"error":None}

        errors = []; raw_block = raw_cached; refined_block = refined_cached
        try:
            raw_rows = self._fetch_raw_prices(cid)
            raw_systems = self._aggregate_best_by_system(raw_rows)
            self._write_cached_block(detected_name, "raw", cid, cname, raw_systems)
            raw_block = self._read_cached_block(detected_name, "raw", allow_stale=True) or {"systems":raw_systems,"updated_at":int(time.time()),"cached":False,"stale":False}
        except Exception as e:
            errors.append(f"RAW: {e}")
            raw_block = self._read_cached_block(detected_name, "raw", allow_stale=True) or {"systems":[],"updated_at":None,"cached":False,"stale":False}
        try:
            refined_rows = self._fetch_refined_prices(cid)
            refined_systems = self._aggregate_best_by_system(refined_rows)
            self._write_cached_block(detected_name, "refined", cid, cname, refined_systems)
            refined_block = self._read_cached_block(detected_name, "refined", allow_stale=True) or {"systems":refined_systems,"updated_at":int(time.time()),"cached":False,"stale":False}
        except Exception as e:
            errors.append(f"REFINADO: {e}")
            refined_block = self._read_cached_block(detected_name, "refined", allow_stale=True) or {"systems":[],"updated_at":None,"cached":False,"stale":False}
        return {"detected_name":detected_name,"commodity_name":cname,"raw":raw_block,"refined":refined_block,"error":" | ".join(errors) if errors else None}


class RegionSelector:
    def __init__(self, parent):
        self.result = None; self._start_x = self._start_y = 0; self._rect = None
        with mss.mss() as sct:
            monitor = sct.monitors[0]
            self._offset_x = monitor["left"]; self._offset_y = monitor["top"]; self._total_w = monitor["width"]; self._total_h = monitor["height"]
        self.win = tk.Toplevel(parent)
        self.win.overrideredirect(True); self.win.attributes("-topmost", True); self.win.attributes("-alpha", 0.25)
        self.win.configure(bg="#000010")
        self.win.geometry(f"{self._total_w}x{self._total_h}+{self._offset_x}+{self._offset_y}")
        self.canvas = tk.Canvas(self.win, width=self._total_w, height=self._total_h, bg="#000010", highlightthickness=0, cursor="crosshair")
        self.canvas.pack()
        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.win.bind("<Escape>", lambda e: self.win.destroy())
        parent.wait_window(self.win)

    def _on_press(self, e):
        self._start_x, self._start_y = e.x, e.y
        if self._rect: self.canvas.delete(self._rect)

    def _on_drag(self, e):
        if self._rect: self.canvas.delete(self._rect)
        self._rect = self.canvas.create_rectangle(self._start_x, self._start_y, e.x, e.y, outline=ACCENT, width=2, fill="", dash=(6,3))

    def _on_release(self, e):
        x1 = min(self._start_x, e.x) + self._offset_x; y1 = min(self._start_y, e.y) + self._offset_y
        x2 = max(self._start_x, e.x) + self._offset_x; y2 = max(self._start_y, e.y) + self._offset_y
        if (x2 - x1) > 10 and (y2 - y1) > 10:
            self.result = {"left":x1, "top":y1, "width":x2-x1, "height":y2-y1}
        self.win.destroy()


def _safe_widget_call(widget, fn):
    try:
        if widget is not None and int(widget.winfo_exists()) == 1: fn()
    except Exception: pass


class Menu:
    def __init__(self):
        global LANG
        LANG = load_lang()
        try: self.mapping = load_csv(CSV_FILE)
        except Exception: self.mapping = None

        self.token_hidden = True
        self.root = tk.Tk()
        self.market_enabled_var = tk.BooleanVar(master=self.root, value=load_market_enabled())
        self.history_duration_var = tk.StringVar(master=self.root, value=str(load_history_duration()))
        self.ocr_sensitivity_var = tk.StringVar(master=self.root, value=load_ocr_sensitivity())
        self.calibration_hotkey_var = tk.StringVar(master=self.root, value=load_calibration_hotkey())
        self.hotkeys = GlobalHotkeyManager()
        self.support_popup_shown_this_session = False
        self.support_state = increment_support_launch()
        self.root.title(f"{T('app_title')} {APP_VERSION_LABEL}")
        self.root.configure(bg=BG)
        self.root.resizable(False, False)
        self.root.geometry("620x770")
        self.root.attributes("-topmost", True)
        _load_icon(self.root)

        header = tk.Frame(self.root, bg=BG); header.pack(fill="x", padx=16, pady=(16,8))
        left = tk.Frame(header, bg=BG); left.pack(side="left", fill="x", expand=True)
        self.lbl_title = tk.Label(left, text=T("app_title"), bg=BG, fg=ACCENT, font=f_ui(18, "bold")); self.lbl_title.pack(anchor="w")
        self.lbl_subtitle = tk.Label(left, text=T("app_subtitle"), bg=BG, fg=MUTED, font=f_alt(10)); self.lbl_subtitle.pack(anchor="w", pady=(2,0))
        self.lbl_version = tk.Label(left, text=APP_VERSION_LABEL, bg=BG, fg=GOLD, font=f_alt(9, "bold")); self.lbl_version.pack(anchor="w", pady=(2,0))
        lang_box = tk.Frame(header, bg=BG); lang_box.pack(side="right")
        self.lbl_language = tk.Label(lang_box, text=T("language"), bg=BG, fg=TEXT, font=f_alt(9, "bold")); self.lbl_language.pack(anchor="e")
        self.lang_var = tk.StringVar(master=self.root, value=LANG)
        lang_menu = tk.OptionMenu(lang_box, self.lang_var, *SUPPORTED_LANGS, command=self.set_language)
        lang_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        lang_menu["menu"].config(bg=PANEL, fg=TEXT)
        lang_menu.pack(anchor="e", pady=(2,0))

        self.mode_frame = tk.LabelFrame(self.root, text=T("search_modules"), bg=BG, fg=TEXT, bd=1, font=f_ui(10, "bold"), relief="groove", highlightbackground=BORDER)
        self.mode_frame.pack(fill="x", padx=16, pady=(0,10))
        self.mode_vars = {}; self.mode_checkbuttons = {}
        selected_modes = load_selected_modes()
        for key in ["asteroid","material","hand","salvage"]:
            var = tk.BooleanVar(value=(key in selected_modes)); self.mode_vars[key] = var
            cb = tk.Checkbutton(self.mode_frame, text=mode_label(key), variable=var, bg=BG, fg=MODE_INFO[key]["color"], activebackground=BG, activeforeground=MODE_INFO[key]["color"], selectcolor=PANEL, font=f_alt(10), anchor="w")
            cb.pack(fill="x", padx=10, pady=2); self.mode_checkbuttons[key] = cb

        self.uex_frame = tk.LabelFrame(self.root, text=T("uex_settings"), bg=BG, fg=TEXT, bd=1, font=f_ui(10, "bold"), relief="groove", highlightbackground=BORDER)
        self.uex_frame.pack(fill="x", padx=16, pady=(0,10))
        top_uex = tk.Frame(self.uex_frame, bg=BG); top_uex.pack(fill="x", padx=10, pady=(8,4))
        self.chk_market = tk.Checkbutton(top_uex, text=T("enable_market"), variable=self.market_enabled_var, command=self._toggle_market_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(10))
        self.chk_market.pack(side="left")
        self.btn_help = tk.Button(top_uex, text="?", bg=PANEL, fg=ACCENT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.show_help, width=3)
        self.btn_help.pack(side="right", padx=(6,0))

        token_row = tk.Frame(self.uex_frame, bg=BG); token_row.pack(fill="x", padx=10, pady=(4,4))
        self.lbl_token = tk.Label(token_row, text=T("token"), bg=BG, fg=TEXT, font=f_alt(10, "bold")); self.lbl_token.pack(side="left")
        self.token_var = tk.StringVar(master=self.root, value=load_uex_token())
        self.entry_token = tk.Entry(token_row, textvariable=self.token_var, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="solid", bd=1, font=f_mono(10), show="*")
        self.entry_token.pack(side="left", fill="x", expand=True, padx=8)
        self.btn_show = tk.Button(token_row, text=T("show"), bg=PANEL, fg=TEXT, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(9), command=self.toggle_token_visibility)
        self.btn_show.pack(side="left")

        token_buttons = tk.Frame(self.uex_frame, bg=BG); token_buttons.pack(fill="x", padx=10, pady=(2,8))
        self.btn_save = tk.Button(token_buttons, text=T("save"), bg=PANEL, fg=ACCENT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.save_token)
        self.btn_save.pack(side="left")
        self.btn_test = tk.Button(token_buttons, text=T("test"), bg=ACCENT, fg=BG, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.test_token)
        self.btn_test.pack(side="left", padx=(8,0))
        self.lbl_token_status = tk.Label(token_buttons, text="", bg=BG, fg=MUTED, font=f_alt(9))
        self.lbl_token_status.pack(side="left", padx=(12,0))

        history_row = tk.Frame(self.root, bg=BG)
        history_row.pack(fill="x", padx=16, pady=(0, 8))
        self.lbl_history_duration = tk.Label(history_row, text=T("history_duration"), bg=BG, fg=TEXT, font=f_alt(10, "bold"))
        self.lbl_history_duration.pack(side="left")
        self.entry_history_duration = tk.Entry(history_row, textvariable=self.history_duration_var, width=6, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="solid", bd=1, font=f_mono(10))
        self.entry_history_duration.pack(side="left", padx=8)
        self.btn_history_save = tk.Button(history_row, text=T("save"), bg=PANEL, fg=ACCENT, relief="solid", bd=1,
                                  highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.save_history_setting)
        self.btn_history_save.pack(side="left")
        ocr_row = tk.Frame(self.root, bg=BG)
        ocr_row.pack(fill="x", padx=16, pady=(0, 8))
        self.lbl_ocr_sensitivity = tk.Label(ocr_row, text=T("ocr_sensitivity"), bg=BG, fg=TEXT, font=f_alt(10, "bold"))
        self.lbl_ocr_sensitivity.pack(side="left")
        self.ocr_options = list(OCR_SENSITIVITY_PROFILES.keys())
        self.ocr_menu = tk.OptionMenu(ocr_row, self.ocr_sensitivity_var, *self.ocr_options)
        self.ocr_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        self.ocr_menu["menu"].config(bg=PANEL, fg=TEXT)
        self.ocr_menu.pack(side="left", padx=8)
        self.btn_ocr_save = tk.Button(ocr_row, text=T("save"), bg=PANEL, fg=ACCENT, relief="solid", bd=1,
                                  highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.save_ocr_sensitivity_setting)
        self.btn_ocr_save.pack(side="left")
        self.lbl_ocr_status = tk.Label(ocr_row, text=ocr_sensitivity_label(self.ocr_sensitivity_var.get()), bg=BG, fg=MUTED, font=f_alt(9))
        self.lbl_ocr_status.pack(side="left", padx=(12, 0))

        preview_row = tk.Frame(self.root, bg=BG)
        preview_row.pack(fill="x", padx=16, pady=(0, 8))
        self.lbl_preview_mode = tk.Label(preview_row, text=T("preview_mode"), bg=BG, fg=TEXT, font=f_alt(10, "bold"))
        self.lbl_preview_mode.pack(side="left")
        self.preview_mode_var = tk.StringVar(master=self.root, value=load_preview_mode())
        self.preview_menu = tk.OptionMenu(preview_row, self.preview_mode_var, *PREVIEW_MODES)
        self.preview_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        self.preview_menu["menu"].config(bg=PANEL, fg=TEXT)
        self.preview_menu.pack(side="left", padx=8)
        self._refresh_preview_menu()
        self.preview_mode_var.trace_add("write", lambda *args: self._set_preview_mode(self.preview_mode_var.get()))

        hotkey_row = tk.Frame(self.root, bg=BG)
        hotkey_row.pack(fill="x", padx=16, pady=(0, 8))
        self.lbl_calibration_hotkey = tk.Label(hotkey_row, text=T("calibration_hotkey"), bg=BG, fg=TEXT, font=f_alt(10, "bold"))
        self.lbl_calibration_hotkey.pack(side="left")
        self.hotkey_menu = tk.OptionMenu(hotkey_row, self.calibration_hotkey_var, *HOTKEY_OPTIONS)
        self.hotkey_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        self.hotkey_menu["menu"].config(bg=PANEL, fg=TEXT)
        self.hotkey_menu.pack(side="left", padx=8)
        self.btn_hotkey_save = tk.Button(hotkey_row, text=T("save"), bg=PANEL, fg=ACCENT, relief="solid", bd=1,
                                  highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.save_hotkey_setting)
        self.btn_hotkey_save.pack(side="left")
        self.lbl_hotkey_status = tk.Label(hotkey_row, text="", bg=BG, fg=MUTED, font=f_alt(9))
        self.lbl_hotkey_status.pack(side="left", padx=(12, 0))

        btn_frame = tk.Frame(self.root, bg=BG); btn_frame.pack(fill="x", padx=16, pady=6)
        self.btn_calibrate = tk.Button(btn_frame, text=T("calibrate_zone"), bg=PANEL, fg=ACCENT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(11, "bold"), padx=12, pady=8, command=self.calibrate)
        self.btn_calibrate.pack(fill="x", pady=4)
        self.btn_start = tk.Button(btn_frame, text=T("start_system"), bg=ACCENT, fg=BG, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(11, "bold"), padx=12, pady=10, command=self.start)
        self.btn_start.pack(fill="x", pady=4)

        extra_frame = tk.Frame(self.root, bg=BG); extra_frame.pack(fill="x", padx=16, pady=(6,6))
        self.btn_guide = tk.Button(extra_frame, text=T("guide"), bg=PANEL, fg=TEXT, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(10), command=self.show_guide)
        self.btn_guide.pack(side="left")
        self.btn_donate = tk.Button(extra_frame, text=T("donate"), bg=PANEL, fg=GOLD, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(10, "bold"), command=self.open_donate)
        self.btn_donate.pack(side="right")

        status_text = T("csv_loaded") if self.mapping else T("csv_error")
        status_fg = GREEN if self.mapping else RED
        self.status = tk.Label(self.root, text=status_text, bg=BG, fg=status_fg, font=f_alt(9)); self.status.pack(pady=(8,6))
        self.lbl_hint = tk.Label(self.root, text=T("calibration_hint"), bg=BG, fg=MUTED, font=f_alt(9), wraplength=560, justify="left"); self.lbl_hint.pack(padx=16, pady=(0,10))

        self.refresh_token_status(); self._toggle_market_enabled()
        footer = tk.Frame(self.root, bg=BG); footer.pack(fill="x", pady=(4, 8), padx=16)
        tk.Label(footer, text=APP_VERSION_LABEL, bg=BG, fg=GOLD, font=f_alt(9, "bold")).pack(side="left", anchor="w")
        center_footer = tk.Frame(footer, bg=BG)
        center_footer.pack(side="left", expand=True)
        tk.Label(center_footer, text="Creado por ", bg=BG, fg=MUTED, font=f_alt(9)).pack(side="left")
        lbl_discord = tk.Label(center_footer, text="danypolo", bg=BG, fg=ACCENT, font=f_alt(9, "bold"), cursor="hand2")
        lbl_discord.pack(side="left")
        lbl_discord.bind("<Button-1>", lambda e: webbrowser.open(DISCORD_URL))

        self._register_menu_hotkey()
        self.root.protocol("WM_DELETE_WINDOW", self.close_menu)
        self._start_update_check()
        self.root.after(700, self.maybe_show_support_popup)
        self.root.mainloop()

    def close_menu(self):
        try:
            self.hotkeys.stop()
        except Exception:
            pass
        self.root.destroy()

    def _start_update_check(self):
        threading.Thread(target=self._check_for_updates_worker, daemon=True).start()

    def _check_for_updates_worker(self):
        info = fetch_version_info()
        if not info:
            return
        if is_remote_version_newer(info.get('version', ''), APP_VERSION):
            try:
                self.root.after(600, lambda i=info: self._show_update_available(i))
            except Exception:
                pass

    def _show_update_available(self, info):
        try:
            version = info.get('version', '').strip()
            changes = info.get('changes', []) or []
            url = info.get('url', '').strip()
            body = f"Hay una nueva versión disponible: V {version}\n\nVersión actual: {APP_VERSION_LABEL}\n\nCambios:\n"
            if changes:
                body += "\n".join(f"• {c}" for c in changes)
            else:
                body += "• Correcciones y mejoras"
            body += "\n\n¿Quieres abrir la descarga?"
            if messagebox.askyesno("Actualización disponible", body):
                if url:
                    webbrowser.open(url)
        except Exception as e:
            _ocr_log(f"[update_popup] {e}")

    def set_language(self, lang):
        global LANG
        if lang not in SUPPORTED_LANGS: return
        LANG = lang; save_lang(lang); self.refresh_ui()

    def refresh_ui(self):
        self.root.title(f"{T('app_title')} {APP_VERSION_LABEL}"); self.lbl_title.config(text=T("app_title")); self.lbl_subtitle.config(text=T("app_subtitle")); self.lbl_version.config(text=APP_VERSION_LABEL); self.lbl_language.config(text=T("language"))
        self.mode_frame.config(text=T("search_modules"))
        for key, cb in self.mode_checkbuttons.items(): cb.config(text=mode_label(key))
        self.uex_frame.config(text=T("uex_settings")); self.chk_market.config(text=T("enable_market")); self.lbl_token.config(text=T("token"))
        self.btn_show.config(text=T("hide") if not self.token_hidden else T("show")); self.btn_save.config(text=T("save")); self.btn_test.config(text=T("test"))
        self.lbl_history_duration.config(text=T("history_duration")); self.btn_history_save.config(text=T("save"))
        self.lbl_ocr_sensitivity.config(text=T("ocr_sensitivity")); self.btn_ocr_save.config(text=T("save")); self.lbl_ocr_status.config(text=ocr_sensitivity_label(self.ocr_sensitivity_var.get()))
        self.lbl_preview_mode.config(text=T("preview_mode")); self._refresh_preview_menu()
        self.chk_verify.config(text=T("verify_candidates"))
        self.lbl_calibration_hotkey.config(text=T("calibration_hotkey")); self.btn_hotkey_save.config(text=T("save"))
        self.btn_calibrate.config(text=T("calibrate_zone")); self.btn_start.config(text=T("start_system")); self.btn_guide.config(text=T("guide")); self.btn_donate.config(text=T("donate"))
        status_text = T("csv_loaded") if self.mapping else T("csv_error"); status_fg = GREEN if self.mapping else RED
        self.status.config(text=status_text, fg=status_fg); self.lbl_hint.config(text=T("calibration_hint")); self.refresh_token_status()

    def _toggle_market_enabled(self):
        enabled = self.market_enabled_var.get(); save_market_enabled(enabled)
        state = "normal" if enabled else "disabled"
        self.entry_token.config(state=state); self.btn_show.config(state=state); self.btn_save.config(state=state); self.btn_test.config(state=state); self.btn_help.config(state=state)
        self.refresh_token_status()

    def _preview_label(self, mode):
        if mode == "raw": return T("preview_raw")
        if mode == "processed": return T("preview_processed")
        return T("preview_none")

    def _refresh_preview_menu(self):
        menu = self.preview_menu["menu"]
        menu.delete(0, "end")
        for mode in PREVIEW_MODES:
            menu.add_command(label=self._preview_label(mode), command=lambda m=mode: self.preview_mode_var.set(m))

    def _set_preview_mode(self, mode):
        save_preview_mode(mode)

    def refresh_token_status(self):
        if not self.market_enabled_var.get(): self.lbl_token_status.config(text=T("market_disabled"), fg=MUTED); return
        token = self.token_var.get().strip()
        if token: self.lbl_token_status.config(text=T("token_saved"), fg=GREEN)
        else: self.lbl_token_status.config(text=T("token_not_set"), fg=MUTED)

    def toggle_token_visibility(self):
        self.token_hidden = not self.token_hidden
        self.entry_token.config(show="*" if self.token_hidden else "")
        self.btn_show.config(text=T("hide") if not self.token_hidden else T("show"))

    def save_token(self):
        save_uex_token(self.token_var.get().strip()); self.refresh_token_status()

    def test_token(self):
        token = self.token_var.get().strip()
        if not token: self.lbl_token_status.config(text=T("token_not_set"), fg=MUTED); return
        client = UEXMarketClient(token=token)
        try:
            client.test_connection(); self.lbl_token_status.config(text=T("token_valid"), fg=GREEN); save_uex_token(token)
        except Exception as e:
            self.lbl_token_status.config(text=f"{T('token_test_error')} {e}", fg=RED)

    def save_history_setting(self):
        try:
            seconds = int(self.history_duration_var.get().strip())
        except Exception:
            seconds = DETECTION_TTL
        seconds = max(5, min(300, seconds))
        self.history_duration_var.set(str(seconds))
        save_history_duration(seconds)
        self.lbl_history_status.config(text=f"{T('settings_saved')}: {seconds}s", fg=GREEN)

    def save_ocr_sensitivity_setting(self):
        value = self.ocr_sensitivity_var.get().strip()
        if value not in OCR_SENSITIVITY_PROFILES:
            value = DEFAULT_OCR_SENSITIVITY
            self.ocr_sensitivity_var.set(value)
        save_ocr_sensitivity(value)
        self.lbl_ocr_status.config(text=f"{T('settings_saved')}: {ocr_sensitivity_label(value)}", fg=GREEN)

    def save_hotkey_setting(self):
        value = self.calibration_hotkey_var.get().strip().upper()
        if value not in HOTKEY_OPTIONS:
            value = DEFAULT_CALIBRATION_HOTKEY
            self.calibration_hotkey_var.set(value)
        save_calibration_hotkey(value)
        self._register_menu_hotkey()
        status = f"{T('hotkey_saved')}: {value}"
        if keyboard is None:
            status = T('hotkeys_unavailable')
        self.lbl_hotkey_status.config(text=status, fg=GREEN if keyboard is not None else RED)

    def _register_menu_hotkey(self):
        self.hotkeys.clear()
        if keyboard is None:
            self.lbl_hotkey_status.config(text=T('hotkeys_unavailable'), fg=RED)
            return
        hotkey = load_calibration_hotkey()
        ok = self.hotkeys.add(hotkey, lambda: self.root.after(0, self.calibrate))
        self.lbl_hotkey_status.config(text=(f"{hotkey}" if ok else T('hotkeys_unavailable')), fg=GREEN if ok else RED)

    def show_help(self): messagebox.showinfo(T("help_title"), T("help_body"))
    def show_guide(self): messagebox.showinfo(T("guide_title"), T("guide_body"))

    def maybe_show_support_popup(self):
        if self.support_popup_shown_this_session:
            return
        state = get_support_state()
        launch_count = int(state.get("launch_count", 0))
        if int(state.get("support_clicked", 0)) or int(state.get("prompt_disabled", 0)):
            return
        if launch_count <= 0 or launch_count % SUPPORT_PROMPT_INTERVAL != 0:
            return
        if int(state.get("last_prompt_launch", 0)) == launch_count:
            return
        self.support_popup_shown_this_session = True
        record_support_prompt_shown(launch_count)
        if self._show_support_popup_dialog():
            self.open_donate()

    def _show_support_popup_dialog(self):
        result = {"support": False}
        win = tk.Toplevel(self.root)
        win.title(T("support_popup_title"))
        win.configure(bg=BG)
        win.resizable(False, False)
        win.attributes("-topmost", True)
        win.transient(self.root)
        win.grab_set()
        _load_icon(win)

        body = tk.Frame(win, bg=BG)
        body.pack(fill="both", expand=True, padx=18, pady=18)

        tk.Label(body, text=T("support_popup_title"), bg=BG, fg=ACCENT, font=f_ui(12, "bold")).pack(anchor="w")
        tk.Label(
            body,
            text=T("support_popup_body"),
            bg=BG,
            fg=TEXT,
            font=f_alt(10),
            justify="left",
            wraplength=420,
        ).pack(anchor="w", pady=(10, 14))

        buttons = tk.Frame(body, bg=BG)
        buttons.pack(fill="x")

        def _support():
            result["support"] = True
            win.destroy()

        def _continue():
            win.destroy()

        tk.Button(
            buttons,
            text=T("donate"),
            bg=ACCENT,
            fg=BG,
            relief="solid",
            bd=1,
            highlightbackground=BORDER,
            font=f_ui(9, "bold"),
            command=_support,
        ).pack(side="right")
        tk.Button(
            buttons,
            text=T("support_popup_continue"),
            bg=PANEL,
            fg=TEXT,
            relief="solid",
            bd=1,
            highlightbackground=BORDER,
            font=f_alt(9),
            command=_continue,
        ).pack(side="right", padx=(0, 8))

        win.update_idletasks()
        x = self.root.winfo_x() + max(20, (self.root.winfo_width() - win.winfo_width()) // 2)
        y = self.root.winfo_y() + max(20, (self.root.winfo_height() - win.winfo_height()) // 2)
        win.geometry(f"+{x}+{y}")
        self.root.wait_window(win)
        return result["support"]

    def open_donate(self):
        if PAYPAL_URL.strip():
            mark_support_clicked()
            self.support_state = get_support_state()
            webbrowser.open(PAYPAL_URL.strip())
        else:
            messagebox.showinfo(T("donate"), T("donate_not_configured"))

    def get_selected_modes(self):
        modes = {k for k,v in self.mode_vars.items() if v.get()}
        if not modes:
            modes = set(DEFAULT_MODES); self.mode_vars[next(iter(modes))].set(True)
        return modes

    def calibrate(self):
        self.root.withdraw()
        try:
            selector = RegionSelector(self.root)
            if selector.result:
                CONFIG_FILE.write_text(json.dumps(selector.result, indent=2), encoding="utf-8")
                self.status.config(text=T("csv_loaded") if self.mapping else T("csv_error"), fg=GREEN if self.mapping else RED)
        except Exception as e:
            messagebox.showerror(T("calibrate_zone"), str(e))
        finally:
            self.root.deiconify()
            self.root.lift()
            try:
                self.root.attributes("-topmost", True)
                self.root.focus_force()
            except Exception:
                pass

    def start(self):
        if not self.mapping: messagebox.showerror("Error", T("csv_error")); return
        if not CONFIG_FILE.exists(): messagebox.showwarning(T("calibrate_zone"), T("calibration_hint")); return
        modes = self.get_selected_modes(); save_selected_modes(modes)
        region = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        self.hotkeys.stop()
        self.root.destroy()
        try:
            App(region, self.mapping, modes)
        except Exception as e:
            _ocr_log(f"[overlay] failed to start: {e}")
            messagebox.showerror("Overlay error", str(e))


class App:
    def _ui_after(self, delay_ms, fn):
        try:
            if self.running and self.root is not None and int(self.root.winfo_exists()) == 1:
                self.root.after(delay_ms, fn)
        except Exception:
            pass

    def _ensure_overlay_height(self):
        try:
            if not self.running or self.root is None or int(self.root.winfo_exists()) != 1:
                return
            self.root.update_idletasks()
            sw = self.root.winfo_screenwidth()
            geom = self.root.geometry()
            m = re.match(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)", geom)
            if m:
                cur_w = int(m.group(1)); cur_h = int(m.group(2)); pos_x = int(m.group(3)); pos_y = int(m.group(4))
            else:
                cur_w, cur_h, pos_x, pos_y = 720, 900, 30, 30
            min_w = 600; max_w = min(int(sw * 0.55), 900)
            new_w = max(min_w, min(max_w, cur_w))
            if abs(new_w - cur_w) > 8:
                self.root.geometry(f"{new_w}x{cur_h}+{max(0, pos_x)}+{max(0, pos_y)}")
        except Exception:
            pass

    def _ui_call(self, fn):
        self._ui_after(0, fn)

    def _show_overlay(self):
        try:
            self._ensure_overlay_visible()
            self.root.deiconify()
            self.root.lift()
            self.root.attributes("-topmost", True)
            self.root.focus_force()
        except Exception:
            pass

    def _keep_window_alive(self):
        try:
            if not self.running or self.root is None or int(self.root.winfo_exists()) != 1:
                return
            self.root.attributes("-topmost", False)
            self.root.attributes("-topmost", True)
            self.root.lift()
        except Exception:
            pass
        self._ui_after(1200, self._keep_window_alive)

    def _ensure_overlay_visible(self):
        try:
            if not self.running or self.root is None or int(self.root.winfo_exists()) != 1:
                return
            self.root.update_idletasks()
            sw = self.root.winfo_screenwidth()
            sh = self.root.winfo_screenheight()
            geom = self.root.geometry()
            m = re.match(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)", geom)
            if not m:
                self.root.geometry("720x900+30+30")
                return
            cur_w = int(m.group(1)); cur_h = int(m.group(2)); pos_x = int(m.group(3)); pos_y = int(m.group(4))
            if cur_w < 200 or cur_h < 200:
                cur_w, cur_h = 720, 900
            max_x = max(0, sw - 60)
            max_y = max(0, sh - 60)
            new_x = min(max(0, pos_x), max_x)
            new_y = min(max(0, pos_y), max_y)
            if new_x != pos_x or new_y != pos_y:
                self.root.geometry(f"{cur_w}x{cur_h}+{new_x}+{new_y}")
        except Exception:
            pass

    def _force_debug_overlay(self):
        try:
            if not self.running or self.root is None or int(self.root.winfo_exists()) != 1:
                return
            self.root.update_idletasks()
            if int(self.root.winfo_viewable()) == 1:
                return
            # Fallback: disable overrideredirect and force a visible window
            try: self.root.overrideredirect(False)
            except Exception: pass
            try: self.root.attributes("-alpha", 1.0)
            except Exception: pass
            self.root.geometry("720x900+50+50")
            self.root.deiconify()
            self.root.lift()
            self.root.attributes("-topmost", True)
            if not getattr(self, "_debug_overlay_label", None):
                self._debug_overlay_label = tk.Label(self.root, text="DEBUG OVERLAY MODE", bg=RED, fg=BG, font=f_ui(12, "bold"))
                self._debug_overlay_label.pack(fill="x", padx=6, pady=6)
        except Exception as e:
            _ocr_log(f"[overlay] debug fallback failed: {e}")

    def _calibrate_from_overlay(self):
        try:
            self.root.withdraw()
            selector = RegionSelector(self.root)
            if selector.result:
                self.region = selector.result
                CONFIG_FILE.write_text(json.dumps(selector.result, indent=2), encoding="utf-8")
                self._show_overlay()
        except Exception as e:
            self._ui_call(lambda err=str(e): _safe_widget_call(self.info_label, lambda: self.info_label.config(text=f"{T('ocr_error')} {err}", fg=RED)))
            self._show_overlay()

    def _register_app_hotkeys(self):
        self.hotkeys.clear()
        if keyboard is None:
            return
        self.hotkeys.add(DEFAULT_SHOW_OVERLAY_HOTKEY, lambda: self.root.after(0, self._show_overlay))
        self.hotkeys.add(load_calibration_hotkey(), lambda: self.root.after(0, self._calibrate_from_overlay))

    def _preview_label(self, mode):
        if mode == "raw": return T("preview_raw")
        if mode == "processed": return T("preview_processed")
        return T("preview_none")

    def _clear_preview_widget(self):
        try:
            self.preview_label.config(image="", text="")
            self._preview_photo = None
        except Exception:
            pass

    def _render_preview(self, img):
        try:
            if self.preview_mode == "none":
                self._clear_preview_widget()
                return
            h, w = img.shape[:2]
            max_w = self.preview_label.winfo_width()
            max_h = self.preview_label.winfo_height()
            if max_w <= 1: max_w = 320
            if max_h <= 1: max_h = 120
            scale = min(max_w / float(w), max_h / float(h), 1.0)
            if scale < 1.0:
                img = cv2.resize(img, (max(1, int(w * scale)), max(1, int(h * scale))), interpolation=cv2.INTER_AREA)
            # Encode as PNG for Tk (more reliable than raw PPM)
            ok, buf = cv2.imencode(".png", img)
            if not ok:
                raise RuntimeError("png_encode_failed")
            data = base64.b64encode(buf).decode("ascii")
            photo = tk.PhotoImage(data=data, format="PNG")
            self._preview_photo = photo
            self.preview_label.config(image=photo)
        except Exception as e:
            _ocr_log(f"[preview_render] {e}")
            try:
                h, w = img.shape[:2]
                self.preview_label.config(image="", text=f"Preview error ({w}x{h})")
            except Exception:
                pass

    def _refresh_preview_menu(self):
        menu = self.preview_menu["menu"]
        menu.delete(0, "end")
        for mode in PREVIEW_MODES:
            menu.add_command(label=self._preview_label(mode), command=lambda m=mode: self.preview_mode_var.set(m))

    def _set_preview_mode(self, mode):
        self.preview_mode = mode if mode in PREVIEW_MODES else "none"
        save_preview_mode(self.preview_mode)
        if self.preview_mode == "none":
            self._clear_preview_widget()

    def _toggle_verify_enabled(self):
        self.verify_enabled = bool(self.verify_var.get())
        save_verify_enabled(self.verify_enabled)
        if not self.verify_enabled:
            try: self.verify_label.config(text="")
            except Exception: pass

    def _get_preview_image(self, img):
        if self.preview_mode == "processed":
            proc = preprocess_bright(img)
            if len(proc.shape) == 2:
                proc = cv2.cvtColor(proc, cv2.COLOR_GRAY2BGR)
            return proc
        return img

    def _show_preview(self, img):
        if self.preview_mode == "none":
            return
        try:
            now = time.time()
            if now - self._preview_last_ts < 0.12:
                return
            self._preview_last_ts = now
            preview_img = self._get_preview_image(img)
            self._ui_call(lambda im=preview_img.copy(): self._render_preview(im))
        except Exception as e:
            _ocr_log(f"[preview] {e}")

    def __init__(self, region, mapping, active_modes):
        global LANG
        LANG = load_lang()
        self.region = region; self.mapping = mapping; self.lookup = build_lookup(mapping); self.active_modes = set(active_modes)
        self.running = True; self.confirmed_value = None; self.history = []; self.last_seen_time = 0; self.recent_detections = []
        self.history_duration = load_history_duration()
        self.ocr_profile = get_ocr_profile()
        self.preview_mode = load_preview_mode()
        self._preview_last_ts = 0.0
        self._preview_photo = None
        self.verify_enabled = load_verify_enabled()
        self.market_enabled = load_market_enabled(); self.market_client = UEXMarketClient(token=load_uex_token()); self.market_request_id = 0; self.current_market_material = None; self.current_market_kind = None
        self.hotkeys = GlobalHotkeyManager()

        self.root = tk.Tk(); self.root.title(T("app_title")); self.root.configure(bg=BG); self.root.attributes("-topmost", True); self.root.geometry(load_overlay_geometry()); self.root.overrideredirect(True); _load_icon(self.root)
        try: self.root.attributes("-alpha", 0.85)
        except Exception: pass
        self._drag_x = 0; self._drag_y = 0
        self._resize_start_x = 0; self._resize_start_y = 0; self._resize_start_w = 0; self._resize_start_h = 0

        top = tk.Frame(self.root, bg=PANEL_2, height=34, highlightthickness=1, highlightbackground=BORDER); top.pack(fill="x")
        top.bind("<ButtonPress-1>", self._start_drag); top.bind("<B1-Motion>", self._do_drag)
        self.lbl_overlay_title = tk.Label(top, text=f"{T('app_title').upper()} · {APP_VERSION_LABEL}", bg=PANEL_2, fg=ACCENT, font=f_ui(10, "bold")); self.lbl_overlay_title.pack(side="left", padx=8)
        tk.Button(top, text="↻", bg=PANEL_2, fg=TEXT, relief="flat", command=self.reset_detection, font=f_ui(10, "bold")).pack(side="right", padx=2)
        tk.Button(top, text="×", bg=PANEL_2, fg=RED, relief="flat", command=self.close, font=f_ui(11, "bold")).pack(side="right", padx=2)
        tk.Button(top, text="≡", bg=PANEL_2, fg=TEXT, relief="flat", command=self.back_to_menu, font=f_ui(10, "bold")).pack(side="right", padx=2)

        mode_frame = tk.Frame(self.root, bg=BG); mode_frame.pack(fill="x", padx=8, pady=(6,3))
        self.mode_vars = {}; self.mode_checkbuttons = {}
        for key in ["asteroid","material","hand","salvage"]:
            var = tk.BooleanVar(value=(key in self.active_modes)); self.mode_vars[key] = var
            cb = tk.Checkbutton(mode_frame, text=mode_label(key), variable=var, command=self.apply_mode_selection, bg=BG, fg=MODE_INFO[key]["color"], activebackground=BG, activeforeground=MODE_INFO[key]["color"], selectcolor=PANEL, font=f_alt(9))
            cb.pack(side="left", padx=3); self.mode_checkbuttons[key] = cb

        preview_row = tk.Frame(self.root, bg=BG); preview_row.pack(fill="x", padx=8, pady=(0,2))
        self.lbl_preview_mode = tk.Label(preview_row, text=T("preview_mode"), bg=BG, fg=TEXT, font=f_alt(9, "bold"))
        self.lbl_preview_mode.pack(side="left")
        self.preview_mode_var = tk.StringVar(value=self.preview_mode)
        self.preview_menu = tk.OptionMenu(preview_row, self.preview_mode_var, *PREVIEW_MODES)
        self.preview_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        self.preview_menu["menu"].config(bg=PANEL, fg=TEXT)
        self.preview_menu.pack(side="left", padx=6)
        self._refresh_preview_menu()
        self.preview_mode_var.trace_add("write", lambda *args: self._set_preview_mode(self.preview_mode_var.get()))

        verify_row = tk.Frame(self.root, bg=BG); verify_row.pack(fill="x", padx=8, pady=(0,2))
        self.verify_var = tk.BooleanVar(value=self.verify_enabled)
        self.chk_verify = tk.Checkbutton(verify_row, text=T("verify_candidates"), variable=self.verify_var, command=self._toggle_verify_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(9))
        self.chk_verify.pack(side="left")

        self.preview_frame = tk.Frame(self.root, bg=BG, height=140)
        self.preview_frame.pack(fill="x", padx=8, pady=(0,4))
        self.preview_frame.pack_propagate(False)
        self.preview_label = tk.Label(self.preview_frame, text="", bg=PANEL, fg=MUTED, font=f_mono(8), anchor="center")
        self.preview_label.pack(fill="both", expand=True)
        if self.preview_mode == "none":
            self._clear_preview_widget()

        val_frame = tk.Frame(self.root, bg=BG); val_frame.pack(fill="x", padx=8, pady=(2,0))
        self.lbl_value = tk.Label(val_frame, text=T("value"), bg=BG, fg=MUTED, font=f_ui(8)); self.lbl_value.pack(anchor="w")
        self.val_label = tk.Label(val_frame, text="—", bg=BG, fg=ACCENT, font=f_mono(22, "bold"), anchor="w"); self.val_label.pack(fill="x")

        manual = tk.Frame(self.root, bg=BG); manual.pack(fill="x", padx=8, pady=4)
        self.manual_var = tk.StringVar()
        entry = tk.Entry(manual, textvariable=self.manual_var, bg=PANEL, fg=MUTED, insertbackground=TEXT, relief="solid", bd=1, font=f_mono(11))
        entry.pack(side="left", fill="x", expand=True, padx=(0,6))
        entry.bind("<Return>", lambda e: self.apply_manual())
        _placeholder = T("manual_entry_hint")
        def _on_focus_in(e):
            if entry.get() == _placeholder:
                entry.delete(0, "end"); entry.config(fg=TEXT)
        def _on_focus_out(e):
            if not entry.get().strip():
                entry.insert(0, _placeholder); entry.config(fg=MUTED)
        entry.insert(0, _placeholder)
        entry.bind("<FocusIn>", _on_focus_in)
        entry.bind("<FocusOut>", _on_focus_out)
        self.btn_apply = tk.Button(manual, text=T("apply"), bg=ACCENT, fg=BG, relief="solid", bd=1, highlightbackground=BORDER, command=self.apply_manual, font=f_ui(9, "bold")); self.btn_apply.pack(side="left")

        self.info_label = tk.Label(self.root, text=T("scanning"), bg=BG, fg=MUTED, font=f_alt(9), anchor="w", justify="left"); self.info_label.pack(fill="x", padx=8, pady=(0,2))
        self.verify_label = tk.Label(self.root, text="", bg=BG, fg=MUTED, font=f_mono(8), anchor="w", justify="left", wraplength=680)
        self.verify_label.pack(fill="x", padx=8, pady=(0,2))
        self.history_hint_label = tk.Label(self.root, text=T("click_history_hint"), bg=BG, fg=MUTED, font=f_alt(8), anchor="w", justify="left")
        self.history_hint_label.pack(fill="x", padx=8, pady=(0,4))
        self.result_frame = tk.Frame(self.root, bg=BG); self.result_frame.pack(fill="x", padx=8, pady=(0,8))
        self.market_frame = tk.Frame(self.root, bg=BG); self.market_frame.pack(fill="both", expand=True, padx=8, pady=(0,8))
        market_header = tk.Frame(self.market_frame, bg=BG); market_header.pack(fill="x", pady=(0,4))
        self.lbl_market_title = tk.Label(market_header, text=T("market_uex"), bg=BG, fg=ACCENT, font=f_ui(10, "bold")); self.lbl_market_title.pack(side="left")
        self.market_status = tk.Label(market_header, text=T("market_disabled") if not self.market_enabled else T("no_material_selected"), bg=BG, fg=MUTED, font=f_alt(8)); self.market_status.pack(side="right")
        self.market_error = tk.Label(self.market_frame, text="", bg=BG, fg=RED, font=f_alt(8), anchor="w", justify="left", wraplength=680); self.market_error.pack(fill="x", pady=(0,4))
        self.market_cards = tk.Frame(self.market_frame, bg=BG); self.market_cards.pack(fill="both", expand=True)

        grip = tk.Label(self.root, text="◢", bg=BG, fg=BORDER, font=f_mono(10), cursor="size_nw_se")
        grip.pack(side="bottom", anchor="se", padx=2, pady=1)
        grip.bind("<ButtonPress-1>", self._start_resize)
        grip.bind("<B1-Motion>", self._do_resize)

        self.monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True); self.monitor_thread.start()
        self._register_app_hotkeys()
        self._ui_after(100, self._ensure_overlay_visible)
        self._ui_after(150, self._show_overlay)
        self._ui_after(800, self._force_debug_overlay)
        self._ui_after(200, self._ensure_overlay_height)
        self._ui_after(500, self._cleanup_old_detections)
        self._ui_after(1200, self._keep_window_alive)
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.mainloop()

    def _start_drag(self, event): self._drag_x = event.x; self._drag_y = event.y
    def _do_drag(self, event):
        x = self.root.winfo_x() + event.x - self._drag_x; y = self.root.winfo_y() + event.y - self._drag_y
        self.root.geometry(f"+{x}+{y}")

    def _start_resize(self, event):
        self._resize_start_x = event.x_root; self._resize_start_y = event.y_root
        self._resize_start_w = self.root.winfo_width(); self._resize_start_h = self.root.winfo_height()

    def _do_resize(self, event):
        dx = event.x_root - self._resize_start_x; dy = event.y_root - self._resize_start_y
        new_w = max(600, self._resize_start_w + dx); new_h = max(400, self._resize_start_h + dy)
        self.root.geometry(f"{new_w}x{new_h}+{self.root.winfo_x()}+{self.root.winfo_y()}")

    def apply_mode_selection(self):
        modes = {k for k,v in self.mode_vars.items() if v.get()}
        if not modes:
            modes = set(DEFAULT_MODES); self.mode_vars[next(iter(modes))].set(True)
        self.active_modes = modes; save_selected_modes(modes); self.reset_detection()

    def apply_manual(self):
        text = self.manual_var.get().strip()
        if not text or text == T("manual_entry_hint"):
            self.info_label.config(text=T("invalid_manual"), fg=RED)
            return

        if text.isdigit():
            value = int(text)
            matches = find_matches(value, self.lookup, self.active_modes)
            if not matches:
                self.info_label.config(text=T("manual_not_match"), fg=RED)
                return
            self._accept_detection(str(value), matches)
            self.manual_var.set("")
            return

        matches = self._find_manual_material_matches(text)
        if not matches:
            self.info_label.config(text=T("manual_not_match"), fg=RED)
            return

        material_name = matches[0].get("nom") or text.strip()
        self._accept_manual_material(material_name, matches)
        self.manual_var.set("")


    def _find_manual_material_matches(self, text):
        query = " ".join(str(text).strip().lower().split())
        if not query:
            return []

        exact = []
        partial = []
        for item in self.mapping.values():
            if item.get("subrol") != "material":
                continue
            name = str(item.get("nom", "")).strip()
            normalized_name = " ".join(name.lower().split())
            if normalized_name == query:
                exact.append(item)
            elif query in normalized_name:
                partial.append(item)

        candidates = exact or partial
        filtered = [item for item in candidates if item.get("subrol") in self.active_modes]

        unique = []
        seen = set()
        for item in filtered:
            key = (item.get("signature"), str(item.get("nom", "")).lower())
            if key in seen:
                continue
            seen.add(key)
            unique.append(item)
        return unique

    def _accept_manual_material(self, material_name, matches):
        self.confirmed_value = material_name
        self.last_seen_time = time.time()
        self.val_label.config(text=material_name, fg=GREEN)
        active_text = ", ".join(mode_label(m) for m in sorted(self.active_modes))
        self.info_label.config(text=f"{T('active_modes')} {active_text}", fg=MUTED)

        for w in self.result_frame.winfo_children():
            w.destroy()

        if not self.market_enabled:
            self.market_status.config(text=T("market_disabled"), fg=MUTED)
            self.market_error.config(text="")
            return

        self.market_request_id += 1
        current_id = self.market_request_id
        self.market_client.set_token(load_uex_token())
        self.current_market_kind = "manual_material"
        self.current_market_material = material_name
        self.market_status.config(text=f"{T('consulting_market')} {material_name}", fg=MUTED)
        self.market_error.config(text="")
        threading.Thread(target=self._fetch_market_data, args=(material_name, current_id), daemon=True).start()

    def reset_detection(self):
        self.confirmed_value = None; self.history = []; self.last_seen_time = 0; self.recent_detections = []; self.current_market_material = None; self.market_request_id += 1
        self.val_label.config(text="—", fg=ACCENT); self.info_label.config(text=T("scanning"), fg=MUTED)
        self.market_status.config(text=T("market_disabled") if not self.market_enabled else T("no_material_selected"), fg=MUTED)
        self.market_error.config(text="")
        for w in self.result_frame.winfo_children(): w.destroy()
        for w in self.market_cards.winfo_children(): w.destroy()
        self._ui_after(10, self._ensure_overlay_height)

    def close(self):
        self.running = False
        try: self.hotkeys.stop()
        except Exception: pass
        try: save_overlay_geometry(self.root.geometry())
        except Exception: pass
        try: self.root.destroy()
        except Exception: pass
        self.root = None

    def back_to_menu(self):
        self.running = False
        try: self.hotkeys.stop()
        except Exception: pass
        try: save_overlay_geometry(self.root.geometry())
        except Exception: pass
        try: self.root.destroy()
        except Exception: pass
        self.root = None
        Menu()

    def _cleanup_old_detections(self):
        try:
            if not self.running or self.root is None or int(self.root.winfo_exists()) != 1: return
        except Exception: return
        now = time.time()
        if self.recent_detections and (now - self.recent_detections[-1]["ts"] > self.history_duration):
            self.recent_detections = []; self.confirmed_value = None
            self.val_label.config(text="—", fg=ACCENT)
            self.info_label.config(text=T("no_new_detection_30s"), fg=MUTED)
            for w in self.result_frame.winfo_children(): w.destroy()
            self._ui_after(10, self._ensure_overlay_height)
        self._ui_after(1000, self._cleanup_old_detections)

    def _render_asteroid_contents(self, parent, asteroid_name, row_bg):
        info = ASTEROID_CONTENTS.get(asteroid_name)
        if not info: return
        line1 = tk.Frame(parent, bg=row_bg); line1.pack(fill="x", padx=8, pady=(0,2))
        tk.Label(line1, text=T("contains"), bg=row_bg, fg=MUTED, font=f_alt(8, "bold"), anchor="w", width=14).pack(side="left")
        tk.Label(line1, text=", ".join(info["common"]), bg=row_bg, fg=TEXT, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)
        line2 = tk.Frame(parent, bg=row_bg); line2.pack(fill="x", padx=8, pady=(0,4))
        tk.Label(line2, text=T("rare"), bg=row_bg, fg=MUTED, font=f_alt(8, "bold"), anchor="w", width=14).pack(side="left")
        tk.Label(line2, text=", ".join(info["rare"]), bg=row_bg, fg=GOLD, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)

    def _render_possible_materials(self, parent, match, row_bg):
        mats = None
        subrol = match.get("subrol"); sig = str(match.get("signature",""))
        if subrol == "hand": mats = MANUAL_CONTENTS.get(sig)
        if not mats: return
        line = tk.Frame(parent, bg=row_bg); line.pack(fill="x", padx=8, pady=(0,4))
        tk.Label(line, text=T("possible_materials"), bg=row_bg, fg=MUTED, font=f_alt(8, "bold"), anchor="w", width=18).pack(side="left")
        tk.Label(line, text=", ".join(mats), bg=row_bg, fg=TEXT, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)

    def _reload_market_from_history(self, matches):
        if not self.market_enabled:
            self.market_status.config(text=T("market_disabled"), fg=MUTED); return
        primary = matches[0] if matches else None
        if not primary: return
        self.market_request_id += 1; current_id = self.market_request_id
        self.market_client.set_token(load_uex_token())
        if primary.get("subrol") == "material":
            material_name = primary.get("nom")
            if not material_name: return
            self.current_market_kind = "material"; self.current_market_material = material_name
            self.market_status.config(text=f"{T('loading_market')} {material_name}", fg=MUTED); self.market_error.config(text="")
            threading.Thread(target=self._fetch_market_data, args=(material_name, current_id), daemon=True).start()
        elif primary.get("subrol") == "hand":
            self.current_market_kind = "surface"; self.current_market_material = None
            self.market_status.config(text=T("surface_mining_prices"), fg=MUTED); self.market_error.config(text="")
            threading.Thread(target=self._fetch_market_data, args=("surface", current_id), daemon=True).start()
        elif primary.get("subrol") == "salvage":
            self.current_market_kind = "salvage"; self.current_market_material = None
            self.market_status.config(text=T("salvage_prices"), fg=MUTED); self.market_error.config(text="")
            threading.Thread(target=self._fetch_market_data, args=("salvage", current_id), daemon=True).start()
        else:
            self.market_status.config(text=T("click_history_hint"), fg=MUTED)

    def _render_results(self):
        for w in self.result_frame.winfo_children(): w.destroy()
        if not self.recent_detections: return
        show = list(reversed(self.recent_detections[-3:])); fades = [TEXT, "#bdd0dd", "#8ca2b4"]
        for idx, det in enumerate(show):
            row_bg = PANEL if idx == 0 else PANEL_2; fg = fades[min(idx, len(fades)-1)]
            card = tk.Frame(self.result_frame, bg=row_bg, bd=1, relief="flat", highlightthickness=1, highlightbackground=ACCENT if idx == 0 else BORDER); card.pack(fill="x", pady=3)
            header = tk.Frame(card, bg=row_bg, cursor="hand2"); header.pack(fill="x", padx=8, pady=(6,2))
            tk.Label(header, text=det["value"], bg=row_bg, fg=ACCENT if idx == 0 else fg, font=f_mono(16 if idx == 0 else 13, "bold"), cursor="hand2").pack(side="left")
            age = int(time.time() - det["ts"]); tk.Label(header, text=f"hace {age}s", bg=row_bg, fg=MUTED, font=f_alt(8), cursor="hand2").pack(side="right")
            header.bind("<Button-1>", lambda e, matches=det["matches"]: self._reload_market_from_history(matches))
            for m in det["matches"][:3]:
                line = tk.Frame(card, bg=row_bg, cursor="hand2"); line.pack(fill="x", padx=8, pady=(0,3))
                tk.Label(line, text=f"→ {m['mult']} × {m['nom']}  (sig. {m['signature']})", bg=row_bg, fg=fg, font=f_alt(9, "bold" if idx == 0 else "normal"), anchor="w", cursor="hand2").pack(side="left", fill="x", expand=True)
                line.bind("<Button-1>", lambda e, matches=det["matches"]: self._reload_market_from_history(matches))
                s = stars(m["rarete"])
                if s:
                    full, empty = s
                    if full: tk.Label(line, text=STAR_FULL * full, bg=row_bg, fg=GOLD, font=f_alt(8)).pack(side="right")
                    if empty: tk.Label(line, text=STAR_EMPTY * empty, bg=row_bg, fg=STAR_EMPTY_COLOR, font=f_alt(8)).pack(side="right")
                if m.get("subrol") == "asteroid":
                    self._render_asteroid_contents(card, m.get("nom",""), row_bg)
                elif m.get("subrol") == "hand":
                    self._render_possible_materials(card, m, row_bg)
        self._ui_after(10, self._ensure_overlay_height)

    def _create_market_card(self, parent, title, block, color):
        card = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        header = tk.Frame(card, bg=PANEL_2); header.pack(fill="x")
        tk.Label(header, text=title, bg=PANEL_2, fg=color, font=f_ui(10, "bold")).pack(side="left", padx=8, pady=6)
        systems = block.get("systems", []); updated_at = block.get("updated_at"); cached = block.get("cached", False); stale = block.get("stale", False)
        if updated_at:
            age_label = T("old_cache") if stale else (T("cache") if cached else T("live"))
            age_str = time.strftime("%H:%M", time.localtime(updated_at))
            tk.Label(header, text=f"{age_label} {age_str}", bg=PANEL_2, fg=MUTED, font=f_alt(8)).pack(side="right", padx=8)
        if not systems:
            tk.Label(card, text=T("no_data"), bg=PANEL, fg=MUTED, font=f_alt(9), anchor="w").pack(fill="x", padx=8, pady=6)
        else:
            for sys_row in systems:
                row = tk.Frame(card, bg=PANEL); row.pack(fill="x", padx=8, pady=2)
                sys_name = sys_row.get("system_name","—"); price = sys_row.get("price_sell",0); terminal = sys_row.get("terminal_name","") or "—"
                tk.Label(row, text=sys_name, bg=PANEL, fg=TEXT, font=f_alt(9,"bold"), width=10, anchor="w").pack(side="left")
                tk.Label(row, text=format_price(price), bg=PANEL, fg=color, font=f_mono(10,"bold"), width=10, anchor="e").pack(side="left", padx=(0,6))
                tk.Label(row, text=terminal[:26], bg=PANEL, fg=MUTED, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)
        return card

    def _render_market_panel(self, summary, request_id):
        if request_id != self.market_request_id: return
        for w in self.market_cards.winfo_children(): w.destroy()
        if not summary:
            self.market_status.config(text=T("no_data"), fg=MUTED); self.market_error.config(text=""); self._ui_after(10, self._ensure_overlay_height); return
        title_name = summary.get("commodity_name",""); cached = summary.get("cached",False); stale = summary.get("stale",False)
        cache_tag = T("old_cache") if stale else (T("cache") if cached else T("live"))
        self.market_status.config(text=f"{title_name} | {cache_tag}", fg=MUTED)
        err_text = summary.get("error") or ""; systems = summary.get("systems",[])
        if not systems:
            err_text = (err_text + " | " if err_text else "") + "Sin precios devueltos por UEX para este material"
        self.market_error.config(text=err_text)
        block = {"systems":systems,"updated_at":summary.get("updated_at"),"cached":cached,"stale":stale}
        card = self._create_market_card(self.market_cards, f"{T('refined')} — {title_name}", block, REFINED_COLOR)
        card.pack(fill="x", expand=True)
        self._ui_after(10, self._ensure_overlay_height)


    def _render_manual_material_market_panel(self, summary, request_id):
        if request_id != self.market_request_id:
            return
        for w in self.market_cards.winfo_children():
            w.destroy()
        if not summary:
            self.market_status.config(text=T("no_data"), fg=MUTED)
            self.market_error.config(text="")
            self._ui_after(10, self._ensure_overlay_height)
            return

        title_name = summary.get("commodity_name", "")
        cached = summary.get("cached", False)
        stale = summary.get("stale", False)
        cache_tag = T("old_cache") if stale else (T("cache") if cached else T("live"))
        self.market_status.config(text=f"{title_name} | {cache_tag}", fg=MUTED)

        systems = summary.get("systems", [])
        err_text = summary.get("error") or ""
        if not systems:
            err_text = (err_text + " | " if err_text else "") + "Sin precios devueltos por UEX para este material"
        self.market_error.config(text=err_text)

        container = tk.Frame(self.market_cards, bg=BG)
        container.pack(fill="both", expand=True)

        title_card = tk.Frame(container, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        title_card.pack(fill="x", pady=(0, 6))
        title_header = tk.Frame(title_card, bg=PANEL_2)
        title_header.pack(fill="x")
        tk.Label(
            title_header,
            text=f"{T('refined')} — {title_name}",
            bg=PANEL_2,
            fg=REFINED_COLOR,
            font=f_ui(10, "bold"),
        ).pack(side="left", padx=8, pady=6)
        tk.Label(
            title_header,
            text="TOP 3 / sistema",
            bg=PANEL_2,
            fg=MUTED,
            font=f_alt(8, "bold"),
        ).pack(side="right", padx=8, pady=6)

        if not systems:
            tk.Label(title_card, text=T("no_data"), bg=PANEL, fg=MUTED, font=f_alt(9), anchor="w").pack(fill="x", padx=8, pady=8)
            self._ui_after(10, self._ensure_overlay_height)
            return

        for system_block in systems:
            system_name = system_block.get("system_name", "—")
            terminals = system_block.get("terminals", [])
            best_price = terminals[0].get("price_sell", 0) if terminals else 0

            system_card = tk.Frame(container, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
            system_card.pack(fill="x", pady=(0, 6))

            sys_header = tk.Frame(system_card, bg=PANEL_2)
            sys_header.pack(fill="x")
            tk.Label(
                sys_header,
                text=system_name,
                bg=PANEL_2,
                fg=TEXT,
                font=f_alt(9, "bold"),
                anchor="w",
            ).pack(side="left", padx=8, pady=6)
            tk.Label(
                sys_header,
                text=f"Mejor: {format_price(best_price)}",
                bg=PANEL_2,
                fg=REFINED_COLOR,
                font=f_mono(9, "bold"),
                anchor="e",
            ).pack(side="right", padx=8, pady=6)

            for idx, terminal_row in enumerate(terminals[:3], start=1):
                row_bg = PANEL if idx % 2 else PANEL_2
                row = tk.Frame(system_card, bg=row_bg)
                row.pack(fill="x", padx=8, pady=1)

                terminal_name = terminal_row.get("terminal_name", "—")
                price = terminal_row.get("price_sell", 0)

                rank_box = tk.Label(
                    row,
                    text=f"#{idx}",
                    bg=row_bg,
                    fg=ACCENT if idx == 1 else MUTED,
                    font=f_alt(8, "bold"),
                    width=4,
                    anchor="w",
                )
                rank_box.pack(side="left")

                tk.Label(
                    row,
                    text=terminal_name[:40],
                    bg=row_bg,
                    fg=TEXT if idx == 1 else MUTED,
                    font=f_alt(8, "bold" if idx == 1 else "normal"),
                    anchor="w",
                ).pack(side="left", fill="x", expand=True)

                tk.Label(
                    row,
                    text=format_price(price),
                    bg=row_bg,
                    fg=REFINED_COLOR,
                    font=f_mono(9, "bold"),
                    width=10,
                    anchor="e",
                ).pack(side="right")

        self._ui_after(10, self._ensure_overlay_height)

    def _render_surface_market_panel(self, summary, request_id):
        if request_id != self.market_request_id: return
        for w in self.market_cards.winfo_children(): w.destroy()
        self.market_status.config(text=f"{T('surface_mining_prices')} | {T('sell_prices')}", fg=MUTED)
        self.market_error.config(text=summary.get("error") or "")
        card = tk.Frame(self.market_cards, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        card.pack(fill="both", expand=True)
        header = tk.Frame(card, bg=PANEL_2); header.pack(fill="x")
        tk.Label(header, text=T("surface_mining_prices"), bg=PANEL_2, fg=REFINED_COLOR, font=f_ui(10,"bold")).pack(side="left", padx=8, pady=6)
        for item in summary.get("items",[]):
            row = tk.Frame(card, bg=PANEL); row.pack(fill="x", padx=8, pady=2)
            systems = item.get("systems",[]); best = systems[0] if systems else None
            label = item.get("commodity_name") or item.get("detected_name")
            tk.Label(row, text=label[:18], bg=PANEL, fg=TEXT, font=f_alt(9,"bold"), width=18, anchor="w").pack(side="left")
            if best:
                price = best.get("price_sell",0); system = best.get("system_name","—"); terminal = best.get("terminal_name","") or "—"
                tk.Label(row, text=format_price(price), bg=PANEL, fg=REFINED_COLOR, font=f_mono(10,"bold"), width=10, anchor="e").pack(side="left", padx=(0,6))
                tk.Label(row, text=f"{system} · {terminal[:20]}", bg=PANEL, fg=MUTED, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)
            else:
                tk.Label(row, text="—", bg=PANEL, fg=MUTED, font=f_mono(10,"bold"), width=12, anchor="e").pack(side="left", padx=(0,6))
                tk.Label(row, text=T("no_data"), bg=PANEL, fg=MUTED, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)
        self._ui_after(10, self._ensure_overlay_height)

    def _render_salvage_market_panel(self, summary, request_id):
        if request_id != self.market_request_id: return
        for w in self.market_cards.winfo_children(): w.destroy()
        self.market_status.config(text=f"{T('salvage_prices')} | {T('sell_prices')}", fg=MUTED)
        self.market_error.config(text=summary.get("error") or "")
        container = tk.Frame(self.market_cards, bg=BG); container.pack(fill="both", expand=True)

        def add_card(title, items, color):
            card = tk.Frame(container, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
            card.pack(fill="x", expand=True, pady=4)
            header = tk.Frame(card, bg=PANEL_2); header.pack(fill="x")
            tk.Label(header, text=title, bg=PANEL_2, fg=color, font=f_ui(10,"bold")).pack(side="left", padx=8, pady=6)
            for item in items:
                row = tk.Frame(card, bg=PANEL); row.pack(fill="x", padx=8, pady=2)
                systems = item.get("systems",[]); best = systems[0] if systems else None
                label = item.get("commodity_name") or item.get("detected_name")
                tk.Label(row, text=label[:24], bg=PANEL, fg=TEXT, font=f_alt(9,"bold"), width=24, anchor="w").pack(side="left")
                if best:
                    price = best.get("price_sell",0); system = best.get("system_name","—"); terminal = best.get("terminal_name","") or "—"
                    tk.Label(row, text=format_price(price), bg=PANEL, fg=color, font=f_mono(10,"bold"), width=10, anchor="e").pack(side="left", padx=(0,6))
                    tk.Label(row, text=f"{system} · {terminal[:20]}", bg=PANEL, fg=MUTED, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)
                else:
                    tk.Label(row, text="—", bg=PANEL, fg=MUTED, font=f_mono(10,"bold"), width=12, anchor="e").pack(side="left", padx=(0,6))
                    tk.Label(row, text=T("no_data"), bg=PANEL, fg=MUTED, font=f_alt(8), anchor="w").pack(side="left", fill="x", expand=True)

        add_card("Construction Materials · RAW", summary.get("raw_items",[]), GOLD)
        add_card("Refinado / Venta", summary.get("refined_items",[]), REFINED_COLOR)
        self._ui_after(10, self._ensure_overlay_height)

    def _fetch_market_data(self, material_name, request_id):
        try:
            if self.current_market_kind == "surface":
                summary = self.market_client.get_multi_market_lines(SURFACE_MINING_MATERIALS, price_type="refined")
                self._ui_call(lambda s=summary, rid=request_id: self._render_surface_market_panel(s, rid))
            elif self.current_market_kind == "salvage":
                raw_summary = self.market_client.get_multi_market_lines(["Construction Materials"], price_type="raw")
                refined_summary = self.market_client.get_multi_market_lines(["Construction Materials","Recycled Material Composite"], price_type="refined")
                summary = {
                    "raw_items": raw_summary.get("items",[]),
                    "refined_items": refined_summary.get("items",[]),
                    "error": " | ".join([x for x in [raw_summary.get("error"), refined_summary.get("error")] if x]) or None,
                }
                self._ui_call(lambda s=summary, rid=request_id: self._render_salvage_market_panel(s, rid))
            elif self.current_market_kind == "manual_material":
                summary = self.market_client.get_top_terminals_by_system(material_name, price_type="refined", top_n=3)
                self._ui_call(lambda s=summary, rid=request_id: self._render_manual_material_market_panel(s, rid))
            else:
                summary = self.market_client.get_best_system_lines(material_name, price_type="refined")
                self._ui_call(lambda s=summary, rid=request_id: self._render_market_panel(s, rid))
        except Exception as e:
            err = str(e)
            self._ui_call(lambda err=err: _safe_widget_call(self.market_error, lambda: self.market_error.config(text=f"UEX: {err}")))

    def _accept_detection(self, value_str, matches):
        self.confirmed_value = value_str; self.last_seen_time = time.time()
        accent_live = "#00ffc3" if int(value_str) % 2 == 0 else "#00bfa5"
        self.val_label.config(text=value_str, fg=accent_live)
        active_text = ", ".join(mode_label(m) for m in sorted(self.active_modes))
        self.info_label.config(text=f"{T('active_modes')} {active_text}", fg=MUTED)
        item = {"ts":time.time(),"value":value_str,"matches":matches}
        if self.recent_detections and self.recent_detections[-1]["value"] == value_str: self.recent_detections[-1] = item
        else: self.recent_detections.append(item)
        self.recent_detections = self.recent_detections[-3:]; self._render_results()

        if not self.market_enabled or not matches: return
        primary = matches[0]
        self.market_request_id += 1; current_id = self.market_request_id
        self.market_client.set_token(load_uex_token())

        if primary.get("subrol") == "hand":
            self.current_market_kind = "surface"; self.current_market_material = None
            self.market_status.config(text=T("surface_mining_prices"), fg=MUTED); self.market_error.config(text="")
            threading.Thread(target=self._fetch_market_data, args=("surface", current_id), daemon=True).start()
        elif primary.get("subrol") == "salvage":
            self.current_market_kind = "salvage"; self.current_market_material = None
            self.market_status.config(text=T("salvage_prices"), fg=MUTED); self.market_error.config(text="")
            threading.Thread(target=self._fetch_market_data, args=("salvage", current_id), daemon=True).start()
        elif primary.get("subrol") == "material":
            material_name = primary.get("nom")
            if material_name:
                self.current_market_kind = "material"; self.current_market_material = material_name
                self.market_status.config(text=f"{T('consulting_market')} {material_name}", fg=MUTED); self.market_error.config(text="")
                threading.Thread(target=self._fetch_market_data, args=(material_name, current_id), daemon=True).start()

    def _monitor_loop(self):
        while self.running:
            try:
                img = capture_region(self.region)
                self._show_preview(img)
                raw, raw_candidates, validated = _read_number_internal(img, self.lookup, self.active_modes)
                if self.verify_enabled:
                    raw_set = ", ".join(sorted(set(raw_candidates))) if raw_candidates else "—"
                    val_set = ", ".join(sorted(set(validated))) if validated else "—"
                    self._ui_call(lambda r=raw_set, v=val_set: _safe_widget_call(self.verify_label, lambda: self.verify_label.config(text=f"OCR raw: {r}  |  valid: {v}")))
                else:
                    self._ui_call(lambda: _safe_widget_call(self.verify_label, lambda: self.verify_label.config(text="")))
                self.history.append(raw)
                if len(self.history) > HISTORY_SIZE: self.history.pop(0)
                valid = [v for v in self.history if v is not None]
                if not valid:
                    if self.confirmed_value and (time.time() - self.last_seen_time < HOLD_LAST_DETECTION):
                        time.sleep(INTERVAL); continue
                    time.sleep(INTERVAL); continue
                counts = {}
                for v in valid: counts[v] = counts.get(v,0) + 1
                candidate = max(counts, key=counts.get); best_count = counts[candidate]
                self.ocr_profile = get_ocr_profile()
                required_votes = int(self.ocr_profile.get("vote_threshold", 2))
                if best_count < required_votes: time.sleep(INTERVAL); continue
                matches = find_matches(int(candidate), self.lookup, self.active_modes)
                if not matches:
                    if self.confirmed_value and (time.time() - self.last_seen_time < HOLD_LAST_DETECTION):
                        time.sleep(INTERVAL); continue
                    self._ui_call(lambda c=candidate: _safe_widget_call(self.info_label, lambda: self.info_label.config(text=f"{T('invalid_fast_read')} {c}", fg=GOLD)))
                    time.sleep(INTERVAL); continue
                if candidate != self.confirmed_value:
                    self._ui_call(lambda c=candidate, m=matches: self._accept_detection(c, m))
                else:
                    self.last_seen_time = time.time()
                time.sleep(INTERVAL)
            except Exception as e:
                err = str(e)
                _ocr_log(f"[monitor_loop] excepción: {err}")
                self._ui_call(lambda err=err: _safe_widget_call(self.info_label, lambda: self.info_label.config(text=f"{T('ocr_error')} {err}", fg=RED)))
                time.sleep(0.2)


if __name__ == "__main__":
    Menu()
