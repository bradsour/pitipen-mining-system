
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
import difflib
import hashlib
import os
import re
import sqlite3
import logging
import shutil
import warnings
import threading
import time
import webbrowser
from pathlib import Path

import cv2
import mss
import numpy as np
import pytesseract
from pytesseract import Output as _TESS_OUTPUT
try:
    from paddleocr import PaddleOCR
    _PADDLE_IMPORT_ERROR = None
except Exception as _paddle_import_err:
    PaddleOCR = None
    _PADDLE_IMPORT_ERROR = _paddle_import_err
try:
    import keyring
except Exception:
    keyring = None
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

OPENAI_API_URL = "https://api.openai.com/v1/responses"
OPENAI_REQUEST_TIMEOUT = 20
OPENAI_DEFAULT_MODEL = "gpt-4.1-mini"
OPENAI_KEYRING_SERVICE = "pitipen-mining-system"
OPENAI_KEYRING_USER = "openai_api_key"

GEMINI_API_BASE = "https://generativelanguage.googleapis.com/v1beta/models"
GEMINI_REQUEST_TIMEOUT = 20
GEMINI_DEFAULT_MODEL = "gemini-2.5-flash"
GEMINI_KEYRING_SERVICE = "pitipen-mining-system"
GEMINI_KEYRING_USER = "gemini_api_key"

PPLX_API_URL = "https://api.perplexity.ai/v1/agent"
PPLX_REQUEST_TIMEOUT = 20
PPLX_DEFAULT_MODEL = "openai/gpt-5-mini"
PPLX_KEYRING_SERVICE = "pitipen-mining-system"
PPLX_KEYRING_USER = "perplexity_api_key"

AI_PROVIDERS = ["openai", "gemini", "perplexity"]
AI_PROVIDER_LABELS = {"openai": "OpenAI", "gemini": "Gemini", "perplexity": "Perplexity"}
DEFAULT_AI_PROVIDER = "openai"

AI_DEFAULT_PROMPT = (
    "You are reading the Star Citizen mining HUD contents list.\n"
    "Return JSON only in this exact shape:\n"
    "{\"rows\":[{\"pct\":\"5.42\",\"name\":\"IRON (ORE)\",\"quality\":\"543\"}]}\n"
    "Rules:\n"
    "- pct is numeric without %\n"
    "- name is the material name as seen\n"
    "- quality is the right-column number\n"
    "- keep top-to-bottom order\n"
    "- if nothing is found, return {\"rows\":[]}\n"
)

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
ROCK_CONFIG_FILE = _BASE_DIR / "rock_config.json"
CSV_FILE = _BASE_DIR / "Minerales.csv"
PREFS_FILE = _BASE_DIR / "preferences.json"
UEX_DB_FILE = _BASE_DIR / "uex_cache.sqlite3"

# Archivo de log OCR junto al exe para diagnóstico en producción
OCR_LOG_FILE = _BASE_DIR / "ocr_debug.log"
SAMPLE_TEMPLATE_FILE = _BASE_DIR / "ocr_sample_template.csv"

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
PADDLE_USE_PREDICT = False


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
    "ocr_mode_fast":{"es":"OCR: Fast","en":"OCR: Fast","fr":"OCR: Fast","de":"OCR: Fast","ru":"OCR: Fast"},
    "ocr_mode_high":{"es":"OCR: High Accuracy","en":"OCR: High Accuracy","fr":"OCR: High Accuracy","de":"OCR: High Accuracy","ru":"OCR: High Accuracy"},
    "no_new_detection_30s":{"es":"Sin nuevas detecciones en 30 s.","en":"No new detections in 30 s.","fr":"Aucune nouvelle détection en 30 s.","de":"Keine neuen Erkennungen seit 30 s.","ru":"Нет новых обнаружений за 30 с."},
    "consulting_market":{"es":"Consultando mercado:","en":"Checking market:","fr":"Consultation du marché :","de":"Markt wird geprüft:","ru":"Проверка рынка:"},
    "market_cache_sqlite":{"es":"caché SQLite 12h","en":"SQLite cache 12h","fr":"cache SQLite 12h","de":"SQLite-Cache 12h","ru":"кэш SQLite 12ч"},
    "language":{"es":"Idioma","en":"Language","fr":"Langue","de":"Sprache","ru":"Язык"},
    "uex_settings":{"es":"UEX Market","en":"UEX Market","fr":"Marché UEX","de":"UEX-Markt","ru":"Рынок UEX"},
    "enable_market":{"es":"Activar precios de mercado","en":"Enable market prices","fr":"Activer les prix du marché","de":"Marktpreise aktivieren","ru":"Включить рыночные цены"},
    "token":{"es":"Token UEX","en":"UEX token","fr":"Jeton UEX","de":"UEX-Token","ru":"Токен UEX"},
    "ai_settings":{"es":"OCR con IA","en":"AI OCR","fr":"OCR IA","de":"KI OCR","ru":"AI OCR"},
    "ai_enable":{"es":"Usar IA para contenidos","en":"Use AI for contents","fr":"Utiliser l'IA pour le contenu","de":"KI für Inhalte verwenden","ru":"Использовать ИИ для содержимого"},
    "ai_provider":{"es":"Proveedor IA","en":"AI provider","fr":"Fournisseur IA","de":"KI-Anbieter","ru":"Провайдер ИИ"},
    "ai_model":{"es":"Modelo IA","en":"AI model","fr":"Modèle IA","de":"KI-Modell","ru":"Модель ИИ"},
    "ai_key":{"es":"Clave IA","en":"AI key","fr":"Clé IA","de":"KI-Schlüssel","ru":"Ключ ИИ"},
    "ai_saved":{"es":"Clave guardada","en":"Key saved","fr":"Clé enregistrée","de":"Schlüssel gespeichert","ru":"Ключ сохранён"},
    "ai_not_set":{"es":"Clave no configurada","en":"Key not set","fr":"Clé non configurée","de":"Schlüssel nicht gesetzt","ru":"Ключ не задан"},
    "ai_keyring_missing":{"es":"Sin keyring: la clave no se guardará", "en":"No keyring: key will not be saved", "fr":"Pas de keyring : la clé ne sera pas enregistrée", "de":"Kein Keyring: Schlüssel wird nicht gespeichert", "ru":"Нет keyring: ключ не будет сохранён"},
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
    "rock":{"label_key":"rock_details","fallback":"Rock details","color":TEXT},
    "rock_details":{"es":"Detalles de roca","en":"Rock details","fr":"D?tails de roche","de":"Gesteinsdetails","ru":"Rock details"},
    "calibrate_rock":{"es":"? CALIBRAR ROCA","en":"? CALIBRATE ROCK","fr":"? CALIBRER ROCHER","de":"? GESTEIN KALIBRIEREN","ru":"? CALIBRATE ROCK"},
    "run_rock_calibration":{"es":"? EJECUTAR CALIBRACIÃ“N ROCA","en":"? RUN ROCK CALIBRATION","fr":"? LANCER CALIBRATION ROCHE","de":"? KALIBRIERUNG ROCHER AUSFÃœHREN","ru":"? RUN ROCK CALIBRATION"},
    "rock_panel":{"es":"ROCA","en":"ROCK","fr":"ROCHE","de":"GESTEIN","ru":"ROCK"},
    "rock_missing_calibration":{"es":"Calibra la zona de roca antes de iniciar este modo.","en":"Calibrate the rock panel area before starting this mode.","fr":"Calibrez la zone de roche avant de d?marrer ce mode.","de":"Kalibriere den Gesteinsbereich, bevor du diesen Modus startest.","ru":"Calibrate the rock panel area before starting this mode."},
    "rock_scanning":{"es":"Escaneando roca...","en":"Scanning rock...","fr":"Analyse de la roche...","de":"Gestein wird gescannt...","ru":"Scanning rock..."},
    "possible_materials":{"es":"Materiales posibles:","en":"Possible materials:","fr":"Matériaux possibles :","de":"Mögliche Materialien:","ru":"Возможные материалы:"},
    "contains":{"es":"Contiene:","en":"Contains:","fr":"Contient :","de":"Enthält:","ru":"Содержит:"},
    "history_duration":{"es":"Duración mensajes (s)","en":"Message duration (s)","fr":"Durée des messages (s)","de":"Nachrichtendauer (s)","ru":"Длительность сообщений (с)"},
    "ocr_sensitivity":{"es":"Sensibilidad OCR","en":"OCR sensitivity","fr":"Sensibilité OCR","de":"OCR-Empfindlichkeit","ru":"Чувствительность OCR"},
    "preview_mode":{"es":"Vista previa","en":"Preview","fr":"Aper?u","de":"Vorschau","ru":"Preview"},
    "preview_none":{"es":"Ninguna","en":"None","fr":"Aucun","de":"Keine","ru":"None"},
    "preview_raw":{"es":"OCR Preview","en":"OCR Preview","fr":"OCR Preview","de":"OCR Preview","ru":"OCR Preview"},
    "preview_processed":{"es":"Imagen procesada","en":"Processed Image","fr":"Image trait?e","de":"Verarbeitetes Bild","ru":"Processed Image"},
    "verify_candidates": {"es":"Verificar candidatos","en":"Verify candidates","fr":"V?rifier candidats","de":"Kandidaten pr?fen","ru":"Verify candidates"},
    "rock_preview":{"es":"Vista previa roca","en":"Rock OCR preview","fr":"Aper?u OCR roche","de":"Gestein OCR Vorschau","ru":"Rock OCR preview"},
    "rock_boxes":{"es":"Mostrar cajas","en":"Draw boxes","fr":"Afficher cadres","de":"Boxen anzeigen","ru":"Draw boxes"},
    "rock_ocr_mode":{"es":"Modo OCR roca","en":"Rock OCR mode","fr":"Mode OCR roche","de":"Rock OCR Modus","ru":"Rock OCR mode"},
    "rock_ocr_gray":{"es":"Gris","en":"Gray","fr":"Gris","de":"Grau","ru":"Gray"},
    "rock_ocr_bright":{"es":"Brillante","en":"Bright","fr":"Brillant","de":"Hell","ru":"Bright"},
    "rock_ocr_adaptive":{"es":"Adaptativo","en":"Adaptive","fr":"Adaptatif","de":"Adaptiv","ru":"Adaptive"},
    "rock_ocr_color":{"es":"Color","en":"Color","fr":"Couleur","de":"Farbe","ru":"Color"},
    "rock_preview_zoom":{"es":"Zoom vista roca","en":"Rock preview zoom","fr":"Zoom aper?u roche","de":"Gestein Vorschau Zoom","ru":"Rock preview zoom"},
    "rock_quality_crop":{"es":"Mostrar recorte calidad","en":"Show quality crop","fr":"Afficher recadrage qualit?","de":"Qualit?tsausschnitt zeigen","ru":"Show quality crop"},
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
_CURRENT_ROCK_MODE = None

def _ocr_log(msg):
    """Escribe una l??nea de log OCR en ocr_debug.log junto al exe."""
    try:
        if _CURRENT_ROCK_MODE and msg.startswith("[rock"):
            msg = f"{msg} [mode={_CURRENT_ROCK_MODE}]"
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

def _build_tess_config_hud(oem=1):
    parts = []
    if TESSDATA_DIR:
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append("--psm 7")
    parts.append(f"--oem {oem}")
    parts.append("-c tessedit_char_whitelist=0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ%.:")
    return " ".join(parts)

def _build_tess_config_text(oem=1):
    parts = []
    if TESSDATA_DIR:
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append("--psm 6")
    parts.append(f"--oem {oem}")
    parts.append("-c preserve_interword_spaces=1")
    parts.append("-c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.%():- ")
    return " ".join(parts)

def _build_tess_config_name(oem=1):
    parts = []
    if TESSDATA_DIR:
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append("--psm 7")
    parts.append(f"--oem {oem}")
    parts.append("-c preserve_interword_spaces=1")
    parts.append("-c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz() ")
    return " ".join(parts)

def _build_tess_config_numeric(oem=1):
    parts = []
    if TESSDATA_DIR:
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append("--psm 6")
    parts.append(f"--oem {oem}")
    parts.append("-c preserve_interword_spaces=1")
    parts.append("-c tessedit_char_whitelist=0123456789.%SCU,")
    return " ".join(parts)

def _build_tess_config_quality(oem=1, psm=6):
    parts = []
    if TESSDATA_DIR:
        safe_tessdata = Path(TESSDATA_DIR).as_posix()
        parts.append(f'--tessdata-dir {safe_tessdata}')
    parts.append(f"--psm {psm}")
    parts.append(f"--oem {oem}")
    parts.append("-c preserve_interword_spaces=1")
    parts.append("-c tessedit_char_whitelist=0123456789")
    return " ".join(parts)

# CORRECCIÓN 2: usar solo LSTM (--oem 1).
# El fallback legacy (--oem 0) se desactiva porque suele fallar
# cuando el paquete de idiomas no incluye los datos del motor clásico.
TESS_CONFIG      = _build_tess_config(1)
HUD_TESS_CONFIG  = _build_tess_config_hud(1)
TESS_CONFIG_FALL = TESS_CONFIG
ROCK_TESS_CONFIG = _build_tess_config_text(1)
ROCK_NAME_TESS_CONFIG = _build_tess_config_name(1)
ROCK_NUM_TESS_CONFIG = _build_tess_config_numeric(1)
ROCK_QUALITY_TESS_CONFIG = _build_tess_config_quality(1, 6)
ROCK_QUALITY_TESS_CONFIG_SPARSE = _build_tess_config_quality(1, 11)
ROCK_QUALITY_TESS_CONFIG_LINE = _build_tess_config_quality(1, 7)

try:
    v = pytesseract.get_tesseract_version()
    _ocr_log(f"[tesseract] versión detectada: {v}")
    _ocr_log(f"[tesseract] command used: {TESSERACT_CMD}")
    _ocr_log(f"[tesseract] tessdata used: {TESSDATA_DIR}")
except Exception as e:
    _ocr_log(f"[tesseract] ERROR REAL al validar instalación: {e}")


PADDLE_ENGINE = None
PADDLE_INIT_ERROR = None
LAST_OCR_ENGINE = "tesseract"
LAST_OCR_CONF = 0.0
SAMPLE_TEMPLATE = {}

def _purge_paddle_debug():
    try:
        out_dir = _BASE_DIR / "paddle_debug"
        if out_dir.exists() and out_dir.is_dir():
            shutil.rmtree(out_dir)
        out_dir.mkdir(exist_ok=True)
    except Exception as e:
        _ocr_log(f"[paddle] debug purge error: {e}")

def _sample_expected_for_label(label):
    if not label or not SAMPLE_TEMPLATE:
        return ""
    key = str(label).strip().lower()
    # Map known labels to sample keys
    if key in ("name", "panel_name"):
        return SAMPLE_TEMPLATE.get("name", "")
    if key == "stats":
        parts = [SAMPLE_TEMPLATE.get("mass",""), SAMPLE_TEMPLATE.get("res",""), SAMPLE_TEMPLATE.get("inst","")]
        return " ".join([p for p in parts if p]).strip()
    if key in ("mass", "res", "inst", "comp"):
        return SAMPLE_TEMPLATE.get(key, "")
    if key.startswith("row_name_"):
        idx = key.replace("row_name_", "")
        return SAMPLE_TEMPLATE.get(f"row{idx}_name", "")
    if key.startswith("percent_row_"):
        idx = key.replace("percent_row_", "")
        return SAMPLE_TEMPLATE.get(f"row{idx}_pct", "")
    if key.startswith("quality_row_"):
        idx = key.replace("quality_row_", "")
        return SAMPLE_TEMPLATE.get(f"row{idx}_quality", "")
    return SAMPLE_TEMPLATE.get(key, "")

def _score_text_against_sample(text, expected):
    if not expected:
        return 0.0
    if not text:
        return 0.0
    t = re.sub(r"\\s+", "", str(text).upper())
    e = re.sub(r"\\s+", "", str(expected).upper())
    if not e:
        return 0.0
    if not any(ch.isalnum() for ch in t):
        return 0.0
    if t == e:
        return 1.0
    return difflib.SequenceMatcher(None, t, e).ratio()

def _scale_img(img, scale):
    try:
        if scale is None or abs(scale - 1.0) < 0.01:
            return img
        h, w = img.shape[:2]
        new_w = max(1, int(w * scale))
        new_h = max(1, int(h * scale))
        # Respect Paddle's max_side_limit (default 4000)
        max_side = 4000
        max_dim = max(new_w, new_h)
        if max_dim > max_side:
            factor = max_side / float(max_dim)
            new_w = max(1, int(new_w * factor))
            new_h = max(1, int(new_h * factor))
        return cv2.resize(img, (new_w, new_h), interpolation=cv2.INTER_CUBIC)
    except Exception:
        return img

def _benchmark_field(field_key, crop, expected, tess_config, require_pattern=None, progress_cb=None):
    modes = ["gray", "adaptive", "bright", "color"]
    scales = [1.0, 1.5, 2.0]
    mode_rank = {m:i for i,m in enumerate(modes)}
    best = {"score": -1.0, "engine": None, "mode": None, "scale": None, "text": ""}
    # Tesseract first
    for mode in modes:
        for scale in scales:
            if progress_cb:
                progress_cb(field_key, "tesseract", mode, scale)
            img = _scale_img(crop, scale)
            proc = _rock_preprocess(img, mode)
            if len(proc.shape) == 3:
                proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
            text, _ = _tesseract_text_and_conf(proc, tess_config)
            if require_pattern and not re.search(require_pattern, text or "", re.IGNORECASE):
                pass
            score = _score_text_against_sample(text, expected)
            if score > best["score"]:
                best = {"score": score, "engine": "tesseract", "mode": mode, "scale": scale, "text": text}
            elif abs(score - best["score"]) < 1e-6:
                # Tie-break: prefer tesseract, then cheaper mode, then smaller scale
                if best["engine"] != "tesseract":
                    best = {"score": score, "engine": "tesseract", "mode": mode, "scale": scale, "text": text}
                elif mode_rank.get(mode, 99) < mode_rank.get(best["mode"], 99) or (mode == best["mode"] and scale < (best["scale"] or 99)):
                    best = {"score": score, "engine": "tesseract", "mode": mode, "scale": scale, "text": text}
    # Paddle
    for mode in modes:
        for scale in scales:
            if progress_cb:
                progress_cb(field_key, "paddle", mode, scale)
            img = _scale_img(crop, scale)
            text, _ = _paddle_extract_text_and_conf(img, label=field_key)
            if require_pattern and not re.search(require_pattern, text or "", re.IGNORECASE):
                pass
            score = _score_text_against_sample(text, expected)
            if score > best["score"]:
                best = {"score": score, "engine": "paddle", "mode": mode, "scale": scale, "text": text}
            elif abs(score - best["score"]) < 1e-6:
                # Tie-breaker: prefer tesseract over paddle
                if best["engine"] == "paddle" and score > 0:
                    best = {"score": score, "engine": "tesseract", "mode": mode, "scale": scale, "text": text}
                elif best["engine"] == "paddle":
                    if mode_rank.get(mode, 99) < mode_rank.get(best["mode"], 99) or (mode == best["mode"] and scale < (best["scale"] or 99)):
                        best = {"score": score, "engine": "paddle", "mode": mode, "scale": scale, "text": text}
    return best

def _run_rock_calibration(panel_img, boxes, sample, progress_cb=None):
    if panel_img is None or not boxes or not sample:
        return {}
    cal = {}
    try:
        h, w = panel_img.shape[:2]
        def _box_to_int(b):
            x1, y1, x2, y2 = b
            # normalize if floats in [0,1]
            if 0 <= x1 <= 1 and 0 <= x2 <= 1:
                x1 = int(x1 * w); x2 = int(x2 * w)
            if 0 <= y1 <= 1 and 0 <= y2 <= 1:
                y1 = int(y1 * h); y2 = int(y2 * h)
            return int(x1), int(y1), int(x2), int(y2)

        def _crop(key):
            x1, y1, x2, y2 = _box_to_int(boxes.get(key, (0, 0, w, h)))
            return panel_img[y1:y2, x1:x2]

        # Core fields
        stats_expected = " ".join([sample.get("mass",""), sample.get("res",""), sample.get("inst","")]).strip()
        cal["name"] = _benchmark_field("name", _crop("name"), sample.get("name",""), ROCK_NAME_TESS_CONFIG, r"[A-Z]", progress_cb)
        cal["stats"] = _benchmark_field("stats", _crop("stats"), stats_expected, ROCK_NUM_TESS_CONFIG, r"\\d", progress_cb)
        cal["comp"] = _benchmark_field("comp", _crop("comp"), sample.get("comp",""), ROCK_NUM_TESS_CONFIG, r"\\d", progress_cb)

        # Rows
        table = _crop("table")
        th, tw = table.shape[:2]
        row_box = boxes.get("row")
        row_h = None
        if row_box:
            _, ry1, _, ry2 = row_box
            row_h = max(6, int(ry2 - ry1))
        row_count = 0
        if str(sample.get("row_count","")).isdigit():
            row_count = int(sample.get("row_count"))
        if row_count == 0:
            for k in sample.keys():
                if k.startswith("row") and k.endswith("_pct"):
                    row_count = max(row_count, int(k.replace("row","").replace("_pct","") or 0))
        if row_count == 0 and row_h:
            row_count = max(1, int((th + row_h - 1) / row_h))
        if row_h is None:
            row_h = max(8, int(th / max(1, row_count)))

        # Percent/quality column bounds
        tbox = _box_to_int(boxes.get("table", (0, 0, w, h)))
        p1, py1, p2, py2 = _box_to_int(boxes.get("percent", (0, 0, int(tw * 0.30), th)))
        q1, qy1, q2, qy2 = _box_to_int(boxes.get("quality", (int(tw * 0.70), 0, tw, th)))
        p_left = max(0, p1 - tbox[0]); p_right = min(tw, p2 - tbox[0])
        q_left = max(0, q1 - tbox[0]); q_right = min(tw, q2 - tbox[0])

        for i in range(row_count):
            y0 = i * row_h
            y1 = min(th, (i + 1) * row_h)
            if y1 <= y0:
                continue
            row_img = table[y0:y1, :]
            pct_img = row_img[:, p_left:p_right]
            name_img = row_img[:, p_right:q_left] if q_left > p_right else row_img
            qual_img = row_img[:, q_left:q_right] if q_right > q_left else row_img[:, int(tw*0.7):tw]

            key = i + 1
            cal[f"row_name_{key}"] = _benchmark_field(
                f"row_name_{key}", name_img, sample.get(f"row{key}_name",""), ROCK_NAME_TESS_CONFIG, r"[A-Z]", progress_cb
            )
            cal[f"percent_row_{key}"] = _benchmark_field(
                f"percent_row_{key}", pct_img, sample.get(f"row{key}_pct",""), ROCK_NUM_TESS_CONFIG, r"\\d", progress_cb
            )
            cal[f"quality_row_{key}"] = _benchmark_field(
                f"quality_row_{key}", qual_img, sample.get(f"row{key}_quality",""), ROCK_QUALITY_TESS_CONFIG_LINE, r"\\d", progress_cb
            )
    except Exception as e:
        _ocr_log(f"[calibration] run error: {e}")
    try:
        for k, v in cal.items():
            if isinstance(v, dict):
                _ocr_log(f"[calibration] {k} -> {v.get('engine','')} {v.get('mode','')} scale={v.get('scale','')}")
    except Exception:
        pass
    return cal

def _ocr_with_calibration(field_key, crop, tess_config, require_pattern, default_mode, calib):
    try:
        mode = calib.get("mode", default_mode)
        scale = calib.get("scale", 1.0)
        engine = calib.get("engine", "tesseract")
        img = _scale_img(crop, scale)
        if engine == "paddle":
            text, _ = _paddle_extract_text_and_conf(img, label=field_key)
            return text or ""
        # Tesseract path
        proc = _rock_preprocess(img, mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        text, _ = _tesseract_text_and_conf(proc, tess_config)
        return text or ""
    except Exception:
        return ""

def _upscale_for_paddle(img, factor=None):
    try:
        h, w = img.shape[:2]
        if factor is None:
            base = int(get_ocr_profile().get("upscale", 4))
            factor = max(6, min(12, base * 2 + 2))
        new_w = w * factor
        new_h = h * factor
        max_side = 4000
        max_dim = max(new_w, new_h)
        if max_dim > max_side:
            factor2 = max_side / float(max_dim)
            new_w = max(1, int(new_w * factor2))
            new_h = max(1, int(new_h * factor2))
        return cv2.resize(img, (int(new_w), int(new_h)), interpolation=cv2.INTER_CUBIC)
    except Exception:
        return img


def _init_paddleocr():
    global PADDLE_ENGINE, PADDLE_INIT_ERROR
    if PaddleOCR is None:
        if _PADDLE_IMPORT_ERROR:
            _ocr_log(f"[paddle] import error: {_PADDLE_IMPORT_ERROR}")
        return None
    try:
        logging.getLogger("ppocr").setLevel(logging.ERROR)
        warnings.filterwarnings("ignore", category=DeprecationWarning, message=".*predict.*")
        PADDLE_ENGINE = PaddleOCR(lang="en", ocr_version="PP-OCRv4")
        _ocr_log("[paddle] initialized successfully (PP-OCRv4)")
        return PADDLE_ENGINE
    except Exception as e:
        PADDLE_INIT_ERROR = str(e)
        _ocr_log(f"[paddle] init error: {e}")
        PADDLE_ENGINE = None
        return None

def _paddle_self_test():
    try:
        if PADDLE_ENGINE is None:
            return
        img = np.zeros((180, 520, 3), dtype=np.uint8)
        cv2.putText(img, "PADDLE TEST 123", (8, 110),
                    cv2.FONT_HERSHEY_SIMPLEX, 1.6, (255, 255, 255), 3, cv2.LINE_AA)
        text, conf = _paddle_extract_text_and_conf(img, label="selftest")
        if text:
            _ocr_log(f"[paddle] selftest ok text='{text[:48]}' conf={conf:.1f}")
        else:
            _ocr_log("[paddle] selftest no_text")
    except Exception as e:
        _ocr_log(f"[paddle] selftest error: {e}")

def _bw_hash_image(img):
    try:
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if len(img.shape) == 3 else img
        _, bw = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        small = cv2.resize(bw, (64, 64), interpolation=cv2.INTER_AREA)
        return hashlib.md5(small.tobytes()).hexdigest()
    except Exception:
        return ""

def _has_any_text_fast(img):
    try:
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if len(img.shape) == 3 else img
        data = pytesseract.image_to_data(gray, config="--psm 6", output_type=_TESS_OUTPUT.DICT)
        n = len(data.get("text", []))
        for i in range(n):
            txt = (data["text"][i] or "").strip()
            conf = data["conf"][i]
            if not txt:
                continue
            try:
                if int(conf) >= 30:
                    return True
            except Exception:
                return True
        return False
    except Exception:
        return False

def _openai_extract_text(resp_json):
    try:
        if isinstance(resp_json, dict):
            if resp_json.get("output_text"):
                return str(resp_json.get("output_text"))
            out = resp_json.get("output")
            texts = []
            if isinstance(out, list):
                for item in out:
                    if not isinstance(item, dict):
                        continue
                    content = item.get("content", [])
                    if isinstance(content, list):
                        for c in content:
                            if isinstance(c, dict):
                                if c.get("text"):
                                    texts.append(str(c.get("text")))
                                elif c.get("output_text"):
                                    texts.append(str(c.get("output_text")))
            if texts:
                return "\n".join(texts)
    except Exception:
        pass
    return ""

def _openai_parse_rows_from_text(text, provider="openai"):
    if not text:
        return []
    raw = text.strip()
    payload = None
    try:
        payload = json.loads(raw)
    except Exception:
        try:
            start = raw.find("{")
            end = raw.rfind("}")
            if start >= 0 and end > start:
                payload = json.loads(raw[start:end + 1])
        except Exception:
            payload = None
    if not isinstance(payload, dict):
        return []
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return []
    cleaned = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        pct = str(row.get("pct", "")).replace("%", "").strip()
        name = str(row.get("name", "")).strip()
        quality = str(row.get("quality", "")).strip()
        if not (pct or name or quality):
            continue
        cleaned.append({"pct": pct, "name": name, "quality": quality, "engine": provider})
    return cleaned

def _get_ai_prompt_from_config():
    try:
        if ROCK_CONFIG_FILE.exists():
            payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
            if isinstance(payload, dict):
                prompt = payload.get("ai_prompt") or payload.get("openai_prompt")
                if isinstance(prompt, str) and prompt.strip():
                    return prompt.strip()
    except Exception:
        pass
    return AI_DEFAULT_PROMPT

def _openai_contents_rows(table_img, table_text):
    global AI_LAST_BW_HASH
    if not load_ai_enabled():
        return []
    provider = load_ai_provider()
    api_key = _get_ai_api_key(provider)
    if not api_key:
        _ocr_log(f"[ai-{provider}] skip: key not set")
        return []
    if table_img is None or table_img.size == 0:
        return []
    bw_hash = _bw_hash_image(table_img)
    if bw_hash and bw_hash == AI_LAST_BW_HASH:
        _ocr_log(f"[ai-{provider}] skip: table unchanged")
        return []
    AI_LAST_BW_HASH = bw_hash
    if not (table_text and re.search(r"[A-Z0-9]", table_text, re.IGNORECASE)):
        if not _has_any_text_fast(table_img):
            _ocr_log(f"[ai-{provider}] skip: no text detected")
            return []
    try:
        ok, buf = cv2.imencode(".png", table_img)
        if not ok:
            return []
        b64 = base64.b64encode(buf.tobytes()).decode("utf-8")
    except Exception as e:
        _ocr_log(f"[ai-{provider}] encode error: {e}")
        return []
    prompt = _get_ai_prompt_from_config()
    try:
        if provider == "gemini":
            model = load_ai_model(provider)
            url = f"{GEMINI_API_BASE}/{model}:generateContent"
            payload = {
                "contents": [{
                    "parts": [
                        {"text": prompt},
                        {"inline_data": {"mime_type": "image/png", "data": b64}},
                    ]
                }]
            }
            headers = {"x-goog-api-key": api_key, "Content-Type": "application/json"}
            resp = requests.post(url, headers=headers, json=payload, timeout=GEMINI_REQUEST_TIMEOUT)
            if resp.status_code >= 400:
                _ocr_log(f"[ai-{provider}] error status={resp.status_code} body={resp.text[:160]}")
                return []
            data = resp.json()
            text_parts = []
            for cand in data.get("candidates", []) or []:
                content = cand.get("content", {})
                for part in content.get("parts", []) or []:
                    if isinstance(part, dict) and part.get("text"):
                        text_parts.append(str(part.get("text")))
            text = "\n".join(text_parts).strip()
            rows = _openai_parse_rows_from_text(text, provider=provider)
        else:
            model = load_ai_model(provider)
            url = OPENAI_API_URL if provider == "openai" else PPLX_API_URL
            payload = {
                "model": model,
                "input": [{
                    "role": "system",
                    "content": [{"type": "input_text", "text": prompt}],
                }, {
                    "role": "user",
                    "content": [
                        {"type": "input_image", "image_url": f"data:image/png;base64,{b64}"},
                    ],
                }],
            }
            headers = {
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
            }
            timeout = OPENAI_REQUEST_TIMEOUT if provider == "openai" else PPLX_REQUEST_TIMEOUT
            resp = requests.post(url, headers=headers, json=payload, timeout=timeout)
            if resp.status_code >= 400:
                _ocr_log(f"[ai-{provider}] error status={resp.status_code} body={resp.text[:160]}")
                return []
            data = resp.json()
            text = _openai_extract_text(data)
            rows = _openai_parse_rows_from_text(text, provider=provider)
        if rows:
            _ocr_log(f"[ai-{provider}] rows={len(rows)}")
        else:
            _ocr_log(f"[ai-{provider}] empty rows")
        return rows
    except Exception as e:
        _ocr_log(f"[ai-{provider}] request error: {e}")
        return []

def _rock_table_hash(img):
    try:
        h, w = img.shape[:2]
        boxes = rock_boxes_for_shape(h, w)
        if not boxes or "table" not in boxes:
            return ""
        tx1, ty1, tx2, ty2 = boxes.get("table", (0, 0, w, h))
        table_img = img[ty1:ty2, tx1:tx2]
        if table_img is None or table_img.size == 0:
            return ""
        return _bw_hash_image(table_img)
    except Exception:
        return ""

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

AI_KEY_MEM = {"openai": "", "gemini": "", "perplexity": ""}
AI_LAST_BW_HASH = None

def _hash_key(value):
    if not value:
        return ""
    try:
        return hashlib.sha256(value.encode("utf-8")).hexdigest()
    except Exception:
        return ""

def load_ai_enabled():
    prefs = load_prefs()
    if "__ai_enabled__" in prefs:
        return bool(prefs.get("__ai_enabled__", False))
    return bool(prefs.get("__openai_enabled__", False))

def save_ai_enabled(enabled):
    prefs = load_prefs()
    prefs["__ai_enabled__"] = bool(enabled)
    save_prefs(prefs)

def load_ai_provider():
    prefs = load_prefs()
    provider = str(prefs.get("__ai_provider__", DEFAULT_AI_PROVIDER)).strip().lower()
    return provider if provider in AI_PROVIDERS else DEFAULT_AI_PROVIDER

def save_ai_provider(provider):
    prefs = load_prefs()
    provider = str(provider).strip().lower()
    prefs["__ai_provider__"] = provider if provider in AI_PROVIDERS else DEFAULT_AI_PROVIDER
    save_prefs(prefs)

def _model_pref_key(provider):
    return f"__ai_model_{provider}__"

def load_ai_model(provider):
    prefs = load_prefs()
    provider = str(provider).strip().lower()
    key = _model_pref_key(provider)
    if provider == "gemini":
        default = GEMINI_DEFAULT_MODEL
    elif provider == "perplexity":
        default = PPLX_DEFAULT_MODEL
    else:
        default = OPENAI_DEFAULT_MODEL
    return str(prefs.get(key, default)).strip() or default

def save_ai_model(provider, model):
    prefs = load_prefs()
    provider = str(provider).strip().lower()
    key = _model_pref_key(provider)
    prefs[key] = str(model).strip()
    save_prefs(prefs)

def _key_hash_pref_key(provider):
    return f"__ai_key_hash_{provider}__"

def load_ai_key_hash(provider):
    prefs = load_prefs()
    return str(prefs.get(_key_hash_pref_key(provider), "")).strip()

def save_ai_key_hash(provider, key):
    prefs = load_prefs()
    prefs[_key_hash_pref_key(provider)] = _hash_key(key)
    save_prefs(prefs)

def _get_ai_api_key(provider):
    provider = str(provider).strip().lower()
    cached = AI_KEY_MEM.get(provider, "")
    if cached:
        return cached
    if keyring is not None:
        try:
            if provider == "gemini":
                stored = keyring.get_password(GEMINI_KEYRING_SERVICE, GEMINI_KEYRING_USER)
            elif provider == "perplexity":
                stored = keyring.get_password(PPLX_KEYRING_SERVICE, PPLX_KEYRING_USER)
            else:
                stored = keyring.get_password(OPENAI_KEYRING_SERVICE, OPENAI_KEYRING_USER)
            if stored:
                return stored
        except Exception:
            pass
    if provider == "gemini":
        env_key = os.environ.get("GEMINI_API_KEY", "").strip() or os.environ.get("GOOGLE_API_KEY", "").strip()
    elif provider == "perplexity":
        env_key = os.environ.get("PERPLEXITY_API_KEY", "").strip() or os.environ.get("PPLX_API_KEY", "").strip()
    else:
        env_key = os.environ.get("OPENAI_API_KEY", "").strip()
    if env_key:
        return env_key
    return ""

def _save_ai_api_key(provider, value):
    provider = str(provider).strip().lower()
    key = (value or "").strip()
    AI_KEY_MEM[provider] = key
    if not key:
        return False
    saved = False
    if keyring is not None:
        try:
            if provider == "gemini":
                keyring.set_password(GEMINI_KEYRING_SERVICE, GEMINI_KEYRING_USER, key)
            elif provider == "perplexity":
                keyring.set_password(PPLX_KEYRING_SERVICE, PPLX_KEYRING_USER, key)
            else:
                keyring.set_password(OPENAI_KEYRING_SERVICE, OPENAI_KEYRING_USER, key)
            saved = True
        except Exception:
            saved = False
    save_ai_key_hash(provider, key)
    return saved

# Back-compat wrappers for renamed AI settings
def load_openai_enabled():
    return load_ai_enabled()

def save_openai_enabled(enabled):
    save_ai_enabled(enabled)

def load_openai_model():
    return load_ai_model(load_ai_provider())

def save_openai_model(model):
    save_ai_model(load_ai_provider(), model)

def _get_openai_api_key():
    return _get_ai_api_key(load_ai_provider())

def _save_openai_api_key(value):
    return _save_ai_api_key(load_ai_provider(), value)

def _ensure_sample_template():
    if SAMPLE_TEMPLATE_FILE.exists():
        return
    try:
        _save_sample_template({
            "name": "IRON (ORE)",
            "mass": "1132",
            "res": "0%",
            "inst": "1.32",
            "comp": "1.48",
            "row1_pct": "5.42%",
            "row1_name": "IRON (ORE)",
            "row1_quality": "543",
            "row2_pct": "62.89%",
            "row2_name": "IRON (ORE)",
            "row2_quality": "249",
            "row3_pct": "32.48%",
            "row3_name": "INERT MATERIALS",
            "row3_quality": "0",
        })
    except Exception as e:
        _ocr_log(f"[sample] template write error: {e}")

def _load_sample_template():
    data = {}
    try:
        if not SAMPLE_TEMPLATE_FILE.exists():
            return data
        with SAMPLE_TEMPLATE_FILE.open("r", encoding="utf-8", errors="ignore") as f:
            reader = csv.reader(f)
            rows = list(reader)
        for row in rows[1:]:
            if len(row) < 2:
                continue
            key = str(row[0]).strip().lower()
            val = str(row[1]).strip()
            if key:
                data[key] = val
    except Exception as e:
        _ocr_log(f"[sample] template read error: {e}")
    return data

def _save_sample_template(data):
    try:
        rows = ["key,value"]
        for k, v in data.items():
            rows.append(f"{k},{v}")
        SAMPLE_TEMPLATE_FILE.write_text("\n".join(rows) + "\n", encoding="utf-8")
    except Exception as e:
        _ocr_log(f"[sample] template write error: {e}")

def _get_sample_row_count():
    try:
        payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            sample = payload.get("sample") or {}
            if isinstance(sample, dict):
                if str(sample.get("row_count","")).isdigit():
                    return int(sample.get("row_count"))
                # fallback count from row*_pct keys
                count = 0
                for k in sample.keys():
                    if str(k).startswith("row") and str(k).endswith("_pct"):
                        try:
                            idx = int(str(k).replace("row","").replace("_pct",""))
                            count = max(count, idx)
                        except Exception:
                            pass
                if count:
                    return count
    except Exception:
        pass
    return 0

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

def load_rock_preview_enabled(): return bool(load_prefs().get("__rock_preview_enabled__", False))
def save_rock_preview_enabled(enabled):
    prefs = load_prefs(); prefs["__rock_preview_enabled__"] = bool(enabled); save_prefs(prefs)

def load_rock_boxes_enabled(): return bool(load_prefs().get("__rock_boxes_enabled__", False))
def save_rock_boxes_enabled(enabled):
    prefs = load_prefs(); prefs["__rock_boxes_enabled__"] = bool(enabled); save_prefs(prefs)

ROCK_OCR_MODES = ["adaptive"]
def load_rock_ocr_mode():
    val = str(load_prefs().get("__rock_ocr_mode__", "adaptive")).lower()
    return val if val in ROCK_OCR_MODES else "adaptive"
def save_rock_ocr_mode(mode):
    mode = str(mode).lower()
    prefs = load_prefs(); prefs["__rock_ocr_mode__"] = mode if mode in ROCK_OCR_MODES else "adaptive"; save_prefs(prefs)

def load_rock_preview_zoom():
    try:
        val = float(load_prefs().get("__rock_preview_zoom__", 1.0))
    except Exception:
        val = 1.0
    return max(1.0, min(10.0, val))
def save_rock_preview_zoom(value):
    try:
        v = float(value)
    except Exception:
        v = 1.0
    v = max(1.0, min(10.0, v))
    prefs = load_prefs(); prefs["__rock_preview_zoom__"] = v; save_prefs(prefs)

def load_rock_quality_crop_enabled(): return bool(load_prefs().get("__rock_quality_crop__", False))
def save_rock_quality_crop_enabled(enabled):
    prefs = load_prefs(); prefs["__rock_quality_crop__"] = bool(enabled); save_prefs(prefs)

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
    "rock":{"label_key":"rock_details","fallback":"Rock details","color":TEXT},
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

# Toggle to disable rock name matching against rock_names.txt
DISABLE_ROCK_NAME_MATCHING = True
# Prefer automatic row band detection for contents rows
AUTO_CONTENT_ROWS = True
# Disable whole-column OCR collection (kept for fallback if re-enabled)
ENABLE_COLUMN_WHOLE_OCR = False

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


PADDLE_CONF_THRESHOLD = 80

def _text_score(text, require_pattern=None):
    if not text:
        return 0
    score = sum(ch.isalnum() for ch in text)
    if require_pattern:
        try:
            if re.search(require_pattern, text or "", re.IGNORECASE):
                score += 5
        except Exception:
            pass
    return score

def _paddle_wins(tess_text, paddle_text, require_pattern=None):
    # Only let Paddle override when it clearly looks better
    if not paddle_text:
        return False
    if not tess_text:
        return True
    return _text_score(paddle_text, require_pattern) > _text_score(tess_text, require_pattern)

def _adaptive_threshold_hud(img):
    img = _upscale_for_ocr(img)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    return cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                 cv2.THRESH_BINARY_INV, 11, 2)

def _tesseract_text_and_conf(proc, config):
    try:
        data = pytesseract.image_to_data(proc, config=config, output_type=_TESS_OUTPUT.DICT)
        confs = [int(c) for c in data.get('conf', []) if c != '-1']
        avg_conf = sum(confs) / len(confs) if confs else 0
        text = " ".join([t for t in data.get('text', []) if t]).strip()
        return text, avg_conf
    except Exception as e:
        _ocr_log(f"[tesseract] data error: {e}")
        return "", 0

def _extract_numeric_candidates_from_text(text):
    raw = re.findall(r"\d[\d,]{2,8}", text or "")
    cleaned = []
    for val in raw:
        norm = val.replace(",", "")
        if norm.isdigit() and 3 <= len(norm) <= 6:
            cleaned.append(norm)
    return cleaned

def _collect_texts_scores(obj, texts, scores):
    if isinstance(obj, dict):
        for k, v in obj.items():
            lk = str(k).lower()
            if lk in ("text", "rec_text", "rec_texts", "texts"):
                if isinstance(v, str):
                    texts.append(v)
                elif isinstance(v, (list, tuple)):
                    for item in v:
                        if isinstance(item, str):
                            texts.append(item)
            elif lk in ("score", "rec_score", "text_rec_score", "rec_scores", "scores"):
                try:
                    scores.append(float(v))
                except Exception:
                    pass
            elif lk == "res":
                _collect_texts_scores(v, texts, scores)
            else:
                _collect_texts_scores(v, texts, scores)
    elif isinstance(obj, tuple):
        # Common pattern: (text, score)
        if len(obj) == 2 and isinstance(obj[0], str):
            texts.append(obj[0])
            try:
                scores.append(float(obj[1]))
            except Exception:
                pass
        else:
            for item in obj:
                _collect_texts_scores(item, texts, scores)
    elif isinstance(obj, list):
        for item in obj:
            _collect_texts_scores(item, texts, scores)

def _paddle_ocr_result(img):
    if PADDLE_ENGINE is None:
        return None
    try:
        # Ensure 3-channel BGR input for Paddle
        if img is not None:
            if len(img.shape) == 2:
                img = cv2.cvtColor(img, cv2.COLOR_GRAY2BGR)
            elif len(img.shape) == 3 and img.shape[2] == 4:
                img = cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)
            if len(img.shape) != 3 or img.shape[2] != 3:
                _ocr_log("[paddle] skip: invalid image shape")
                return None
            h, w = img.shape[:2]
            if h < 2 or w < 2:
                _ocr_log("[paddle] skip: tiny image")
                return None
            if img.dtype != np.uint8:
                img = img.astype(np.uint8)
            img = np.ascontiguousarray(img)
            # Hard cutoff if image exceeds Paddle max_side_limit (default 4000)
            max_side = 4000
            max_dim = max(h, w)
            if max_dim > max_side:
                _ocr_log(f"[paddle] skip: image too large ({w}x{h})")
                return None
        if PADDLE_USE_PREDICT:
            return PADDLE_ENGINE.predict(img)
        # Prefer classic OCR call path with tuned inference parameters for faint HUD text
        try:
            return PADDLE_ENGINE.ocr(
                img,
                det=True,
                rec=True,
                cls=False,
                det_db_thresh=0.2,
                det_db_box_thresh=0.3,
                det_db_unclip_ratio=2.0,
            )
        except Exception:
            # Aggressive retry for very faint/glowy text
            try:
                return PADDLE_ENGINE.ocr(
                    img,
                    det=True,
                    rec=True,
                    cls=False,
                    det_db_thresh=0.1,
                    det_db_box_thresh=0.2,
                    det_db_unclip_ratio=2.5,
                )
            except Exception:
                try:
                    return PADDLE_ENGINE.ocr(img, cls=False)
                except Exception:
                    try:
                        return PADDLE_ENGINE.ocr(img)
                    except Exception as e2:
                        try:
                            return PADDLE_ENGINE.predict(img)
                        except Exception as e3:
                            _ocr_log(f"[paddle] ocr error: {e3}")
                            _ocr_log(f"[paddle] ocr fallback errors: {e2}")
                            return None
    except Exception as e1:
        try:
            _ocr_log(f"[paddle] input shape={getattr(img,'shape',None)} dtype={getattr(img,'dtype',None)}")
        except Exception:
            pass
        _ocr_log(f"[paddle] ocr error: {e1}")
        return None

_PADDLE_RESULT_LOGGED = False
_PADDLE_DUMP_TS = {}

def _paddle_variants(img):
    def _ensure_bgr(v):
        try:
            if v is None:
                return v
            if len(v.shape) == 2:
                return cv2.cvtColor(v, cv2.COLOR_GRAY2BGR)
            if len(v.shape) == 3 and v.shape[2] == 4:
                return cv2.cvtColor(v, cv2.COLOR_BGRA2BGR)
        except Exception:
            pass
        return v

    variants = [("raw", _ensure_bgr(img))]
    try:
        up = _upscale_for_ocr(img)
        if up is not None:
            variants.append(("upscaled", _ensure_bgr(up)))
        up2 = _upscale_for_paddle(img)
        if up2 is not None:
            variants.append(("upscaled2", _ensure_bgr(up2)))
    except Exception:
        pass
    try:
        rgb = cv2.cvtColor(_ensure_bgr(img), cv2.COLOR_BGR2RGB)
        variants.append(("rgb", rgb))
    except Exception:
        pass
    try:
        if "up" in locals():
            rgb_up = cv2.cvtColor(_ensure_bgr(up), cv2.COLOR_BGR2RGB)
            variants.append(("rgb_up", rgb_up))
    except Exception:
        pass
    try:
        gray = cv2.cvtColor(_ensure_bgr(img), cv2.COLOR_BGR2GRAY)
        gray3 = cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)
        variants.append(("gray", gray3))
    except Exception:
        pass
    # De-dup by shape + first pixel hash
    seen = set()
    unique = []
    for tag, v in variants:
        try:
            key = (tag, v.shape, int(v[0,0,0]) if v.ndim == 3 else int(v[0,0]))
        except Exception:
            key = tag
        if key in seen:
            continue
        seen.add(key)
        unique.append((tag, v))
    return unique

def _dump_paddle_variants(label, variants):
    try:
        now = time.time()
        last = _PADDLE_DUMP_TS.get(label, 0)
        if now - last < 8:
            return
        _PADDLE_DUMP_TS[label] = now
        out_dir = _BASE_DIR / "paddle_debug"
        out_dir.mkdir(exist_ok=True)
        stamp = time.strftime("%Y%m%d_%H%M%S")
        for tag, img in variants:
            try:
                path = out_dir / f"{label}_{tag}_{stamp}.png"
                cv2.imwrite(str(path), img)
            except Exception:
                pass
        _ocr_log(f"[paddle] debug dump saved: {out_dir}")
    except Exception:
        pass

def _extract_from_ocrresult(res):
    texts = []
    scores = []
    # Try common PaddleX OCRResult attributes directly
    for name in ("text", "rec_text", "text_rec", "rec", "pred", "prediction", "predictions"):
        try:
            val = getattr(res, name)
            if callable(val):
                val = val()
            if isinstance(val, str):
                texts.append(val)
            elif isinstance(val, (list, tuple)):
                for v in val:
                    if isinstance(v, str):
                        texts.append(v)
        except Exception:
            pass
    for name in ("score", "rec_score", "text_rec_score", "prob", "probability", "probs", "score_list"):
        try:
            val = getattr(res, name)
            if callable(val):
                val = val()
            if isinstance(val, (int, float)):
                scores.append(float(val))
            elif isinstance(val, (list, tuple)):
                for v in val:
                    try:
                        scores.append(float(v))
                    except Exception:
                        pass
        except Exception:
            pass
    for name in ("text", "rec_text", "texts", "rec_texts"):
        try:
            val = getattr(res, name)
            if callable(val):
                val = val()
            if isinstance(val, str):
                texts.append(val)
            elif isinstance(val, list):
                texts.extend([v for v in val if isinstance(v, str)])
        except Exception:
            pass
    for name in ("score", "rec_score", "scores", "rec_scores"):
        try:
            val = getattr(res, name)
            if callable(val):
                val = val()
            if isinstance(val, (int, float)):
                scores.append(float(val))
            elif isinstance(val, list):
                for v in val:
                    try:
                        scores.append(float(v))
                    except Exception:
                        pass
        except Exception:
            pass
    return texts, scores

def _paddle_extract_text_and_conf(img, label=None):
    last_result = None
    last_text = ""
    last_conf = 0.0
    last_tag = None
    best_text = ""
    best_conf = 0.0
    best_tag = None
    expected = _sample_expected_for_label(label)
    variants = _paddle_variants(img)
    for tag, variant in variants:
        result = _paddle_ocr_result(variant)
        last_result = result
        if not result:
            continue
        # If result is an iterable (e.g., generator), materialize it
        if not isinstance(result, (list, tuple, dict, str)) and hasattr(result, "__iter__"):
            try:
                result = list(result)
            except Exception:
                pass
        # PaddleOCR 2.x style: list of lines
        if isinstance(result, list) and result and isinstance(result[0], list):
            try:
                best = max(result[0], key=lambda x: x[1][1])
                text = best[1][0]
                conf = float(best[1][1]) * 100.0
                if label:
                    score = _score_text_against_sample(text, expected)
                    _ocr_log(f"[paddle] {label} variant={tag} text='{text[:48]}' conf={conf:.1f} match_score={score:.2f}")
                else:
                    _ocr_log(f"[paddle] variant={tag} text='{text[:48]}' conf={conf:.1f}")
                last_text, last_conf, last_tag = text, conf, tag
                if expected:
                    score = _score_text_against_sample(text, expected)
                    if score > _score_text_against_sample(best_text, expected):
                        best_text, best_conf, best_tag = text, conf, tag
            except Exception:
                pass
        # PaddleOCR 3.x style: list of Result objects / dicts
        texts = []
        scores = []
        if isinstance(result, list):
            for res in result:
                j = None
                try:
                    if hasattr(res, "json"):
                        j = res.json() if callable(res.json) else res.json
                    elif hasattr(res, "to_dict"):
                        j = res.to_dict()
                except Exception:
                    j = None
                if j is None:
                    extra_texts, extra_scores = _extract_from_ocrresult(res)
                    texts.extend(extra_texts)
                    scores.extend(extra_scores)
                if j is None and isinstance(res, dict):
                    j = res
                if j is not None:
                    _collect_texts_scores(j, texts, scores)
        if texts:
            text = " ".join([t for t in texts if t]).strip()
            conf = max(scores) if scores else 0
            if conf <= 1:
                conf *= 100.0
            if label:
                score = _score_text_against_sample(text, expected)
                _ocr_log(f"[paddle] {label} variant={tag} text='{text[:48]}' conf={conf:.1f} match_score={score:.2f}")
            else:
                _ocr_log(f"[paddle] variant={tag} text='{text[:48]}' conf={conf:.1f}")
            last_text, last_conf, last_tag = text, conf, tag
            if expected:
                score = _score_text_against_sample(text, expected)
                if score > _score_text_against_sample(best_text, expected):
                    best_text, best_conf, best_tag = text, conf, tag
        if label:
            _ocr_log(f"[paddle] {label} variant={tag} no_text parsed")
        else:
            _ocr_log(f"[paddle] variant={tag} no_text parsed")
    if last_text:
        if label and expected and best_text:
            score = _score_text_against_sample(best_text, expected)
            _ocr_log(f"[paddle] {label} chosen variant={best_tag} match_score={score:.2f} expected='{expected[:24]}' text='{best_text[:48]}'")
            return best_text, best_conf
        if label:
            score = _score_text_against_sample(last_text, expected)
            _ocr_log(f"[paddle] {label} chosen variant={last_tag} match_score={score:.2f} expected='{expected[:24]}' text='{last_text[:48]}'")
        else:
            _ocr_log(f"[paddle] chosen variant={last_tag} text='{last_text[:48]}' conf={last_conf:.1f}")
        return last_text, last_conf
    if label:
        _ocr_log(f"[paddle] {label} empty result")
    else:
        _ocr_log("[paddle] empty result")
    _dump_paddle_variants(label or "paddle", variants)
    # Debug: log result shape once if we couldn't parse
    result = last_result
    if not result:
        return "", 0
    # If result is an iterable (e.g., generator), materialize it
    if not isinstance(result, (list, tuple, dict, str)) and hasattr(result, "__iter__"):
        try:
            result = list(result)
        except Exception:
            pass
    global _PADDLE_RESULT_LOGGED
    if not _PADDLE_RESULT_LOGGED:
        try:
            _ocr_log(f"[paddle] unparsed result type={type(result)} len={len(result) if hasattr(result,'__len__') else 'n/a'}")
            if isinstance(result, list) and result:
                _ocr_log(f"[paddle] first item type={type(result[0])}")
                # Log any attribute names containing text/score once
                attrs = [a for a in dir(result[0]) if "text" in a.lower() or "score" in a.lower()]
                if attrs:
                    _ocr_log(f"[paddle] OCRResult attrs: {', '.join(attrs[:10])}")
                # Try to dump a shallow dict/json if available
                try:
                    r0 = result[0]
                    if hasattr(r0, "to_dict"):
                        _ocr_log(f"[paddle] OCRResult to_dict keys: {list(r0.to_dict().keys())[:10]}")
                    elif hasattr(r0, "json"):
                        j = r0.json() if callable(r0.json) else r0.json
                        if isinstance(j, dict):
                            _ocr_log(f"[paddle] OCRResult json keys: {list(j.keys())[:10]}")
                            if "res" in j:
                                res_obj = j.get("res")
                                if isinstance(res_obj, dict):
                                    _ocr_log(f"[paddle] OCRResult res keys: {list(res_obj.keys())[:10]}")
                                    for k in ("text", "rec_text", "texts", "rec_texts"):
                                        if k in res_obj:
                                            _ocr_log(f"[paddle] OCRResult res.{k} sample: {str(res_obj.get(k))[:80]}")
                                elif isinstance(res_obj, list) and res_obj:
                                    _ocr_log(f"[paddle] OCRResult res[0] type: {type(res_obj[0])}")
                                    if isinstance(res_obj[0], dict):
                                        _ocr_log(f"[paddle] OCRResult res[0] keys: {list(res_obj[0].keys())[:10]}")
                except Exception:
                    pass
            _PADDLE_RESULT_LOGGED = True
        except Exception:
            pass
    return "", 0

_purge_paddle_debug()
_ensure_sample_template()
SAMPLE_TEMPLATE = _load_sample_template()
_init_paddleocr()
_paddle_self_test()

def extract_mining_data(crop_img):
    global LAST_OCR_ENGINE, LAST_OCR_CONF
    text = ""
    try:
        processed = _adaptive_threshold_hud(crop_img)
        text, avg_conf = _tesseract_text_and_conf(processed, HUD_TESS_CONFIG)
        LAST_OCR_ENGINE = "tesseract"
        LAST_OCR_CONF = avg_conf
        if avg_conf >= PADDLE_CONF_THRESHOLD and text:
            return text, avg_conf, "tesseract"
    except Exception as e:
        _ocr_log(f"[hybrid] tesseract stage error: {e}")

    if PADDLE_ENGINE is None:
        return text, 0, "tesseract"
    try:
        _ocr_log("[paddle] fallback: hud")
        paddle_text, paddle_conf = _paddle_extract_text_and_conf(crop_img, label="hud")
        if _paddle_wins(text, paddle_text, None):
            LAST_OCR_ENGINE = "paddle"
            LAST_OCR_CONF = paddle_conf
            return paddle_text, paddle_conf, "paddle"
    except Exception as e:
        _ocr_log(f"[paddle] ocr error: {e}")
    return text, 0, LAST_OCR_ENGINE

def _hybrid_ocr_text(raw_img, processed_img, tess_config):
    """
    Hybrid OCR for rock panels: Tesseract with confidence gate, PaddleOCR fallback.
    """
    global LAST_OCR_ENGINE, LAST_OCR_CONF
    text = ""
    try:
        text, avg_conf = _tesseract_text_and_conf(processed_img, tess_config)
        LAST_OCR_ENGINE = "tesseract"
        LAST_OCR_CONF = avg_conf
        if avg_conf >= PADDLE_CONF_THRESHOLD and text:
            return text
    except Exception as e:
        _ocr_log(f"[hybrid] tesseract stage error: {e}")

    if PADDLE_ENGINE is None:
        return text
    try:
        _ocr_log("[paddle] fallback: rock")
        paddle_text, paddle_conf = _paddle_extract_text_and_conf(raw_img, label="rock")
        if _paddle_wins(text, paddle_text, None):
            LAST_OCR_ENGINE = "paddle"
            LAST_OCR_CONF = paddle_conf
            return paddle_text
    except Exception as e:
        _ocr_log(f"[paddle] ocr error: {e}")
    return text

def _hybrid_ocr_text_with_engine(raw_img, processed_img, tess_config, min_conf=None, require_pattern=None, label=None):
    """
    Returns (text, engine) where engine is 'tesseract' or 'paddle'.
    """
    text = ""
    try:
        text, avg_conf = _tesseract_text_and_conf(processed_img, tess_config)
        if label:
            _ocr_log(f"[tess] {label} conf={avg_conf:.1f}")
        threshold = PADDLE_CONF_THRESHOLD if min_conf is None else min_conf
        ok = bool(text) and avg_conf >= threshold
        if ok and require_pattern:
            try:
                ok = re.search(require_pattern, text or "", re.IGNORECASE) is not None
            except Exception:
                ok = False
        if ok:
            return text, "tesseract"
    except Exception as e:
        _ocr_log(f"[hybrid] tesseract stage error: {e}")
    if PADDLE_ENGINE is None:
        return text, "tesseract"
    try:
        _ocr_log("[paddle] fallback: rock")
        paddle_text, _ = _paddle_extract_text_and_conf(raw_img, label=label or "rock")
        if _paddle_wins(text, paddle_text, require_pattern):
            return paddle_text, "paddle"
    except Exception as e:
        _ocr_log(f"[paddle] ocr error: {e}")
    return text, "tesseract"

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
def _read_number_legacy(img, lookup, active_modes):
    global LAST_OCR_ENGINE, LAST_OCR_CONF
    LAST_OCR_ENGINE = "tesseract"
    LAST_OCR_CONF = 0.0
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


def _read_number_internal(img, lookup, active_modes):
    img = crop_to_number(img)
    text, _, _ = extract_mining_data(img)
    raw_candidates = _extract_numeric_candidates_from_text(text)

    if raw_candidates:
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

    # Fallback to legacy multi-pass if hybrid produced no numeric candidates.
    return _read_number_legacy(img, lookup, active_modes)


def read_number(img, lookup, active_modes):
    value, _, _ = _read_number_internal(img, lookup, active_modes)
    return value


def _clean_lines(text):
    lines = []
    for raw in text.splitlines():
        s = re.sub(r"\s+", " ", raw).strip()
        if s:
            lines.append(s)
    return lines

def _parse_stat_value(line, key):
    m = re.search(rf"{key}\\s*[:]?\\s*([0-9.,]+\\s*(?:%|SCU)?)", line, re.IGNORECASE)
    if not m:
        return None
    return m.group(1).strip()

def _extract_stat_from_text(full_text, key):
    """
    Heuristic parse for MASS/RES/INST from raw OCR text.
    """
    if not full_text:
        return None
    upper = full_text.upper()
    if key == "MASS":
        m = re.search(r"(?:MASS|MST|MAS)[^0-9]{0,6}([0-9]{1,6}(?:[.,][0-9]{1,3})?)", upper)
        if m:
            raw = m.group(1)
            if "." in raw or "," in raw:
                compact = raw.replace(".", "").replace(",", "")
                if compact.isdigit() and 3 <= len(compact) <= 6:
                    return compact
            return raw
    if key == "RES":
        m = re.search(r"RES[^0-9]{0,4}([0-9]+(?:[.,][0-9]+)?)\\s*%?", upper)
        if m:
            return _normalize_num(m.group(1)) + "%"
    if key == "INST":
        m = re.search(r"INS(?:T)?[^0-9]{0,6}([0-9]+(?:[.,][0-9]+)?)", upper)
        if m:
            return _normalize_num(m.group(1))
    return None

def _normalize_num(s):
    return s.replace(",", ".").strip()

def _clean_quality_token(s):
    # Fix common OCR confusions in quality column
    if not s:
        return ""
    rep = (s.upper()
           .replace("O", "0")
           .replace("I", "1")
           .replace("L", "1")
           .replace("S", "5")
           .replace("B", "8")
           .replace("G", "6")
           .replace("Z", "2"))
    m = re.findall(r"\d{1,4}", rep)
    if not m:
        return ""
    # Prefer last 3-4 digits if available
    for tok in reversed(m):
        if len(tok) >= 3:
            return tok
    return m[-1]

def _normalize_comp_value(text):
    if not text:
        return None
    u = text.upper()
    # Normalize common OCR confusions
    u = (u.replace("O", "0")
           .replace("I", "1")
           .replace("L", "1")
           .replace("B", "8")
           .replace("Z", "2")
           .replace("A", "4"))
    # Targeted fixes around SCU
    u = u.replace("SSCU", "48SCU").replace("S8CU", "48SCU").replace("SBCU", "48SCU")
    u = re.sub(r"S[ETJ]U", "SCU", u)
    u = u.replace("SCU", " SCU")
    # Find numeric token before SCU
    m = re.search(r"([0-9][0-9.,]{0,4})\s*SCU", u)
    if not m:
        return None
    raw = m.group(1).replace(",", ".")
    # If looks like 148/146, interpret as 1.48/1.46
    if raw.isdigit() and len(raw) == 3 and raw.startswith("1"):
        raw = f"{raw[0]}.{raw[1:]}"
    return f"{raw} SCU"

def _normalize_percent_token(tok):
    if not tok:
        return None
    u = tok.upper()
    u = (u.replace("O", "0")
           .replace("I", "1")
           .replace("L", "1")
           .replace("Z", "2")
           .replace("S", "5")
           .replace("B", "8")
           .replace("G", "6")
           .replace("A", "4")
           .replace("J", "3"))
    digits = re.sub(r"[^0-9]", "", u)
    if not digits:
        return None
    if len(digits) >= 3:
        # Interpret 3246 -> 32.46, 324 -> 32.4
        pct = digits[:-2] + "." + digits[-2:]
    else:
        pct = digits
    return pct

def _extract_percent_tokens(text):
    if not text:
        return []
    tokens = []
    u = text.upper()
    u = (u.replace("O", "0")
           .replace("I", "1")
           .replace("L", "1")
           .replace("Z", "2")
           .replace("S", "5")
           .replace("B", "8")
           .replace("G", "6")
           .replace("A", "4")
           .replace("J", "3"))
    u = u.replace("-", "")
    # Prefer numeric tokens directly before %
    for m in re.findall(r"(\\d{1,4})\\s*%", u):
        digits = m
        if len(digits) == 4:
            pct = digits[:2] + "." + digits[2:]
        elif len(digits) == 3:
            pct = digits[0] + "." + digits[1:]
        else:
            pct = digits
        tokens.append(pct)
    # Fallback to looser tokens
    if not tokens:
        for m in re.findall(r"([A-Z0-9.,-]{1,6})\\s*%", text.upper()):
            pct = _normalize_percent_token(m.replace("-", "."))
            if pct:
                tokens.append(pct)
    return tokens

def _rock_preprocess(img, mode):
    if mode == "bright":
        return preprocess_bright(img)
    if mode == "adaptive":
        return preprocess_adaptive(img)
    if mode == "color":
        return preprocess_support_color(img)
    return preprocess_gray(img)

def _rock_preprocess_preview(img, mode):
    # Same pipelines as OCR, but WITHOUT upscaling for 1:1 preview
    if mode == "bright":
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        gray = cv2.GaussianBlur(gray, (3, 3), 0)
        gray = cv2.convertScaleAbs(gray, alpha=1.6, beta=18)
        _, binary = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        return cv2.morphologyEx(binary, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
    if mode == "adaptive":
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        gray = cv2.bilateralFilter(gray, 5, 35, 35)
        binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                       cv2.THRESH_BINARY, 31, -2)
        return cv2.morphologyEx(binary, cv2.MORPH_CLOSE, np.ones((2, 2), np.uint8))
    if mode == "color":
        hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
        mask_low_sat = cv2.inRange(hsv, np.array([0, 0, 125]), np.array([180, 120, 255]))
        v = hsv[:, :, 2]
        _, mask_bright = cv2.threshold(v, 150, 255, cv2.THRESH_BINARY)
        mask = cv2.bitwise_or(mask_low_sat, mask_bright)
        return cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
    return preprocess_gray(img)

def _ocr_rock_name(img, ocr_mode="gray"):
    try:
        proc = _rock_preprocess(img, ocr_mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        text, engine = _hybrid_ocr_text_with_engine(
            img, proc, ROCK_NAME_TESS_CONFIG,
            min_conf=60, require_pattern=r"[A-Z]", label="name"
        )
        text = (text or "").strip()
        if text:
            _ocr_log(f"[rock_field] name='{text[:32]}' engine={engine}")
        lines = _clean_lines(text)
        return lines[0] if lines else ""
    except Exception as e:
        _ocr_log(f"[rock] name ocr exception: {e}")
        return ""

def _ocr_rock_numeric(img, ocr_mode="gray"):
    try:
        proc = _rock_preprocess(img, ocr_mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        text, engine = _hybrid_ocr_text_with_engine(
            img, proc, ROCK_NUM_TESS_CONFIG,
            min_conf=60, require_pattern=r"\\d", label="numeric"
        )
        text = (text or "").strip()
        if text:
            _ocr_log(f"[rock_field] numeric engine={engine}")
        return text
    except Exception as e:
        _ocr_log(f"[rock] numeric ocr exception: {e}")
        return ""

def _ocr_rock_numeric_with_engine(img, ocr_mode="gray"):
    try:
        proc = _rock_preprocess(img, ocr_mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        text, engine = _hybrid_ocr_text_with_engine(
            img, proc, ROCK_NUM_TESS_CONFIG,
            min_conf=60, require_pattern=r"\\d", label="numeric"
        )
        return (text or "").strip(), engine
    except Exception as e:
        _ocr_log(f"[rock] numeric ocr exception: {e}")
        return "", "tesseract"

def _ocr_rock_quality(img, ocr_mode="gray", psm_line=False):
    try:
        # Digits-focused OCR: try multiple preprocess passes and keep the one with most digits
        cfg = ROCK_QUALITY_TESS_CONFIG_LINE
        gate_proc = _rock_preprocess(img, ocr_mode)
        if len(gate_proc.shape) == 3:
            gate_proc = cv2.cvtColor(gate_proc, cv2.COLOR_BGR2GRAY)
        gate_text, gate_engine = _hybrid_ocr_text_with_engine(
            img, gate_proc, cfg,
            min_conf=60, require_pattern=r"\\d", label="quality"
        )
        if gate_text and sum(ch.isdigit() for ch in gate_text) >= 2:
            _ocr_log(f"[rock_field] quality engine={gate_engine}")
            return gate_text.strip()
        candidates = []
        proc = _rock_preprocess(img, ocr_mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        candidates.append(pytesseract.image_to_string(proc, config=cfg))

        proc2 = preprocess_support_color(img)
        if len(proc2.shape) == 3:
            proc2 = cv2.cvtColor(proc2, cv2.COLOR_BGR2GRAY)
        candidates.append(pytesseract.image_to_string(proc2, config=cfg))

        proc3 = _upscale_for_ocr(img)
        gray = cv2.cvtColor(proc3, cv2.COLOR_BGR2GRAY)
        thr = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                    cv2.THRESH_BINARY, 31, -2)
        inv = cv2.bitwise_not(thr)
        candidates.append(pytesseract.image_to_string(inv, config=cfg))

        def _digit_score(s): return sum(ch.isdigit() for ch in s)
        best = max(candidates, key=_digit_score) if candidates else ""
        return best.strip()
    except Exception as e:
        _ocr_log(f"[rock] quality ocr exception: {e}")
        return ""

def _extract_quality_from_table_boxes(img, ocr_mode="gray"):
    try:
        return []
        # Sort by y then x
        items.sort(key=lambda t: (t["y"], t["x"]))
        rows = []
        for it in items:
            y_mid = it["y"] + it["h"] / 2.0
            placed = False
            for row in rows:
                if abs(y_mid - row["y_mid"]) <= row["h"] * 0.6:
                    row["items"].append(it)
                    row["y_mid"] = (row["y_mid"] + y_mid) / 2.0
                    row["h"] = max(row["h"], it["h"])
                    placed = True
                    break
            if not placed:
                rows.append({"y_mid": y_mid, "h": it["h"], "items": [it], "engine": "tesseract"})
        qualities = []
        for row in rows:
            row_items = sorted(row["items"], key=lambda t: t["x"])
            token = "".join([t["text"] for t in row_items])
            token = _clean_quality_token(token)
            if token:
                qualities.append(token)
        return qualities
    except Exception as e:
        _ocr_log(f"[rock] quality box exception: {e}")
        return []

def _segment_table_rows_by_projection(table_img, ocr_mode="gray"):
    try:
        proc = _rock_preprocess(table_img, ocr_mode)
        if len(proc.shape) == 3:
            proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        _, bw = cv2.threshold(proc, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        # Treat dark pixels as ink
        ink = (bw == 0).astype(np.uint8)
        row_sums = ink.sum(axis=1)
        # Smooth to reduce noise (slightly wider window for HUD text bands)
        if row_sums.size >= 7:
            row_sums = np.convolve(row_sums, np.ones(7)/7.0, mode="same")
        thresh = max(1, int(0.02 * ink.shape[1]))
        in_row = row_sums > thresh
        segments = []
        start = None
        for i, val in enumerate(in_row):
            if val and start is None:
                start = i
            if not val and start is not None:
                if i - start >= max(4, int(0.03 * ink.shape[0])):
                    segments.append((start, i))
                start = None
        if start is not None and (len(in_row) - start) >= max(4, int(0.03 * ink.shape[0])):
            segments.append((start, len(in_row)))
        # Merge very small gaps
        merged = []
        for seg in segments:
            if not merged:
                merged.append(seg)
                continue
            prev = merged[-1]
            if seg[0] - prev[1] <= max(3, int(0.02 * ink.shape[0])):
                merged[-1] = (prev[0], seg[1])
            else:
                merged.append(seg)
        # Keep most prominent rows by ink density if too many
        if len(merged) > 0:
            strengths = []
            for (y0, y1) in merged:
                strengths.append((row_sums[y0:y1].sum(), (y0, y1)))
            strengths.sort(reverse=True, key=lambda x: x[0])
            # Heuristic: limit to top 10 rows to avoid runaway
            keep = [seg for _, seg in strengths[:10]]
            keep.sort()
            return keep
        # Fallback: contour-based row bands (better for thin HUD text)
        try:
            h, w = bw.shape[:2]
            # Dilate horizontally to merge characters into lines
            kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (max(10, int(w * 0.15)), 1))
            band = cv2.dilate(255 - bw, kernel, iterations=1)
            contours, _ = cv2.findContours(band, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            bands = []
            for c in contours:
                x, y, ww, hh = cv2.boundingRect(c)
                if ww < int(w * 0.35):
                    continue
                if hh < max(4, int(h * 0.03)):
                    continue
                bands.append((y, y + hh))
            bands.sort()
            # Merge overlapping bands
            merged2 = []
            for seg in bands:
                if not merged2:
                    merged2.append(seg); continue
                prev = merged2[-1]
                if seg[0] <= prev[1] + max(2, int(h * 0.01)):
                    merged2[-1] = (prev[0], max(prev[1], seg[1]))
                else:
                    merged2.append(seg)
            return merged2
        except Exception:
            return []
    except Exception:
        return []

def parse_rock_details(img, ocr_mode="gray"):
    """
    Extracts rock details from a single captured panel.
    Returns (data_dict, raw_text) or (None, raw_text) if not confident.
    """
    try:
        proc = _rock_preprocess(img, ocr_mode)
        if len(proc.shape) == 2:
            proc_for_ocr = proc
        else:
            proc_for_ocr = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
        text, panel_engine = _hybrid_ocr_text_with_engine(
            img, proc_for_ocr, ROCK_TESS_CONFIG,
            min_conf=65, require_pattern=r"[A-Z0-9]", label="panel"
        )
        text = (text or "").strip()
        if text:
            _ocr_log(f"[rock_field] panel engine={panel_engine}")
        lines = _clean_lines(text)
        if not lines:
            return None, text

        upper_lines = [l.upper() for l in lines]
        name = None
        try:
            h, w = img.shape[:2]
            boxes = rock_boxes_for_shape(h, w)
            if not boxes:
                _ocr_log("[rock] missing calibration boxes; aborting OCR")
                return None, text
            x1, y1, x2, y2 = boxes.get("name", (0, 0, w, h))
            name_crop = img[y1:y2, x1:x2]
            name_cal = _get_calibration_field("name")
            if name_cal:
                name = _ocr_with_calibration("name", name_crop, ROCK_NAME_TESS_CONFIG, r"[A-Z]", ocr_mode, name_cal)
            else:
                name = _ocr_rock_name(name_crop, ocr_mode)
        except Exception:
            name = None
        if not name:
            if "RESULTS" in upper_lines[0]:
                for l in lines[1:4]:
                    if l and not any(k in l.upper() for k in ("MASS", "RES", "INST", "COMP", "%")):
                        name = l.strip()
                        break
        if not name:
            for l in lines:
                u = l.upper()
                if "(" in u and ")" in u and not any(k in u for k in ("MASS", "RES", "INST", "COMP", "%")):
                    name = l.strip()
                    break

        mass = None
        res = None
        inst = None
        comp = None

        # OCR numeric crops for stats/comp/table to improve accuracy
        stats_text = ""
        comp_text = ""
        table_text = ""
        quality_text = ""
        try:
            h, w = img.shape[:2]
            boxes = rock_boxes_for_shape(h, w)
            sx1, sy1, sx2, sy2 = boxes.get("stats", (0, 0, w, h))
            cx1, cy1, cx2, cy2 = boxes.get("comp", (0, 0, w, h))
            tx1, ty1, tx2, ty2 = boxes.get("table", (0, 0, w, h))
            stats_crop = img[sy1:sy2, sx1:sx2]
            comp_crop = img[cy1:cy2, cx1:cx2]
            stats_cal = _get_calibration_field("stats")
            if stats_cal:
                stats_text = _ocr_with_calibration("stats", stats_crop, ROCK_NUM_TESS_CONFIG, r"\\d", ocr_mode, stats_cal)
                stats_engine = stats_cal.get("engine", "tesseract")
            else:
                stats_text, stats_engine = _ocr_rock_numeric_with_engine(stats_crop, ocr_mode)
            comp_cal = _get_calibration_field("comp")
            if comp_cal:
                comp_text = _ocr_with_calibration("comp", comp_crop, ROCK_NUM_TESS_CONFIG, r"\\d", ocr_mode, comp_cal)
                comp_engine = comp_cal.get("engine", "tesseract")
            else:
                comp_text, comp_engine = _ocr_rock_numeric_with_engine(comp_crop, ocr_mode)
            table_img = img[ty1:ty2, tx1:tx2]
            table_cal = _get_calibration_field("table")
            if table_cal:
                table_text = _ocr_with_calibration("table", table_img, ROCK_NUM_TESS_CONFIG, r"\\d", ocr_mode, table_cal)
                table_engine = table_cal.get("engine", "tesseract")
            else:
                table_text, table_engine = _ocr_rock_numeric_with_engine(table_img, ocr_mode)
            # Quality column: take a right-justified slice (wider)
            qw = max(1, int((tx2 - tx1) * 0.35))
            qx1 = max(tx1, tx2 - qw)
            if ENABLE_COLUMN_WHOLE_OCR:
                if "quality" in boxes:
                    q1, qy1, q2, qy2 = boxes.get("quality", (qx1, ty1, tx2, ty2))
                    quality_text = _ocr_rock_quality(img[qy1:qy2, q1:q2], ocr_mode)
                else:
                    quality_text = _ocr_rock_quality(img[ty1:ty2, qx1:tx2], ocr_mode)
                # Percent column for row boundary detection
                # Widen percent column to capture full % values
                if "percent" in boxes:
                    p1, py1, p2, py2 = boxes.get("percent", (tx1, ty1, tx1 + int((tx2 - tx1) * 0.30), ty2))
                    percent_img = img[py1:py2, p1:p2]
                else:
                    pw = max(1, int((tx2 - tx1) * 0.30))
                    percent_img = img[ty1:ty2, tx1:tx1 + pw]
        except Exception:
            pass

        # Parse stats by row order: MASS, RES, INST
        stat_lines = _clean_lines(stats_text)
        stat_nums = []
        for l in stat_lines:
            nums = re.findall(r"\d+(?:[\.,]\d+)?", l)
            stat_nums.append(nums)

        # Heuristic parse from full OCR text first
        if mass is None:
            mass = _extract_stat_from_text(text, "MASS")
        if res is None:
            res = _extract_stat_from_text(text, "RES")
        if inst is None:
            inst = _extract_stat_from_text(text, "INST")

        if len(stat_nums) >= 1 and mass is None:
            for n in stat_nums[0]:
                if n.isdigit() and 3 <= len(n) <= 6:
                    mass = n
                    break
            # Avoid treating decimals as mass (often INST)
            if mass is None and stat_nums[0]:
                if stat_nums[0][0].isdigit():
                    mass = _normalize_num(stat_nums[0][0])

        if len(stat_nums) >= 2 and res is None:
            if stat_nums[1]:
                res = _normalize_num(stat_nums[1][0]) + "%"

        if len(stat_nums) >= 3 and inst is None:
            if stat_nums[2]:
                inst = _normalize_num(stat_nums[2][0])

        # If only one stat line is present and it looks like a decimal, treat as INST
        if inst is None and len(stat_nums) >= 1:
            decs = [n for n in stat_nums[0] if "." in n or "," in n]
            if decs:
                inst = _normalize_num(decs[0])

        # If RES line has no numbers (often OCRs as just 'S'), treat as 0%
        if res is None and len(stat_nums) >= 2:
            if not stat_nums[1]:
                res = "0%"
        # If OCR saw RES but no digits anywhere, default to 0%
        if res is None and text and "RES" in text.upper():
            # Only treat as 0% if no digits appear shortly after RES
            if not re.search(r"RES[^0-9]{0,4}[0-9]", text.upper()):
                res = "0%"
        # If RES is still missing but INST is present and stats look single-line, assume 0%
        if res is None and inst is not None:
            if "RES" not in (text or "").upper() and "RES" not in (stats_text or "").upper():
                if len(stat_nums) <= 1:
                    res = "0%"

        if mass or res or inst:
            _ocr_log(f"[rock_field] stats mass={mass or '—'} res={res or '—'} inst={inst or '—'}")

        # Parse comp from comp_text
        if comp is None and text:
            comp = _normalize_comp_value(text)

        if comp is None:
            for l in _clean_lines(comp_text):
                comp = _normalize_comp_value(l)
                if comp:
                    break

        if comp is None and comp_text:
            comp = _normalize_comp_value(comp_text)

        if comp:
            _ocr_log(f"[rock_field] comp={comp}")

        quality_lines = []
        if quality_text:
            # Extract all numeric tokens in order
            for l in _clean_lines(quality_text):
                toks = re.findall(r"\d{1,4}", _clean_quality_token(l) or l)
                if toks:
                    quality_lines.extend(toks)

        # If quality crop failed, try per-row right-slice OCR from the table image
        if not quality_lines and 'table_img' in locals():
            source_lines_tmp = _clean_lines(table_text) if table_text else []
            row_count = len([l for l in source_lines_tmp if '%' in l]) or 0
            if row_count > 0:
                th, tw = table_img.shape[:2]
                slice_w = max(1, int(tw * 0.25))
                for i in range(row_count):
                    y0 = int(i * th / row_count)
                    y1 = int((i + 1) * th / row_count)
                    row_img = table_img[y0:y1, tw - slice_w:tw]
                    qtxt = _ocr_rock_quality(row_img, ocr_mode, psm_line=True)
                    tok = _clean_quality_token(qtxt)
                    if tok:
                        quality_lines.append(tok)
            # If still empty, use box-level OCR grouping
            if not quality_lines:
                quality_lines = _extract_quality_from_table_boxes(table_img, ocr_mode)
        # Row-boundary driven quality OCR (right-justified), using percent column boxes
        percent_rows = []
        if ENABLE_COLUMN_WHOLE_OCR and not quality_lines and 'table_img' in locals():
            try:
                row_bounds = []
                if 'percent_img' in locals():
                    proc = _rock_preprocess(percent_img, ocr_mode)
                    if len(proc.shape) == 3:
                        proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
                    data = pytesseract.image_to_data(proc, config=ROCK_NUM_TESS_CONFIG, output_type=_TESS_OUTPUT.DICT)
                    n = len(data.get("text", []))
                    boxes = []
                    for i in range(n):
                        txt = (data["text"][i] or "").strip()
                        if not txt:
                            continue
                        if "%" not in txt and not any(ch.isdigit() for ch in txt):
                            continue
                        y = data["top"][i]; h = data["height"][i]
                        boxes.append((y, y + h))
                    boxes.sort()
                    for y0, y1 in boxes:
                        placed = False
                        for j, (a0, a1) in enumerate(row_bounds):
                            if abs(y0 - a0) <= 6:
                                row_bounds[j] = (min(a0, y0), max(a1, y1))
                                placed = True
                                break
                        if not placed:
                            row_bounds.append((y0, y1))
                if row_bounds:
                    th, tw = table_img.shape[:2]
                    slice_w = max(1, int(tw * 0.30))
                    for y0, y1 in row_bounds:
                        y0 = max(0, y0 - 2); y1 = min(th, y1 + 2)
                        row_img = table_img[y0:y1, tw - slice_w:tw]
                        row_img = _upscale_for_ocr(row_img)
                        qtxt = _ocr_rock_quality(row_img, ocr_mode, psm_line=True)
                        tok = _clean_quality_token(qtxt)
                        if tok:
                            quality_lines.append(tok)
                    # Also OCR percent column per row for better % recovery
                    try:
                        ph, pw = percent_img.shape[:2]
                        for y0, y1 in row_bounds:
                            y0 = max(0, y0 - 2); y1 = min(ph, y1 + 2)
                            prow = percent_img[y0:y1, 0:pw]
                            proc = _rock_preprocess(prow, ocr_mode)
                            if len(proc.shape) == 3:
                                proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
                            row_text, engine = _hybrid_ocr_text_with_engine(
                                prow, proc, ROCK_NUM_TESS_CONFIG,
                                min_conf=60, require_pattern=r"\\d", label="percent_row"
                            )
                            pct_tokens = _extract_percent_tokens(row_text)
                            if pct_tokens:
                                percent_rows.append((pct_tokens[0], engine))
                                _ocr_log(f"[rock_field] percent_row engine={engine} text='{row_text[:24]}' pct={pct_tokens[0]}")
                    except Exception:
                        pass
            except Exception:
                pass

        # Row segmentation using calibrated row height or projection gaps
        seg_rows = []
        row_segments = []
        row_height = None
        sample_row_count = 0
        if 'boxes' in locals() and "row" in boxes:
            try:
                _, ry1, _, ry2 = boxes.get("row")
                row_height = max(6, int(ry2 - ry1))
            except Exception:
                row_height = None
        if 'table_img' in locals():
            th, tw = table_img.shape[:2]
            if AUTO_CONTENT_ROWS:
                row_segments = _segment_table_rows_by_projection(table_img, ocr_mode)
            if not row_segments:
                if sample_row_count:
                    est_count = max(1, int(sample_row_count))
                    if row_height is None:
                        row_height = max(8, int(th / est_count))
                elif row_height:
                    est_count = max(1, int((th + row_height - 1) / row_height))
                else:
                    est_count = 1
                    row_height = max(8, int(th / est_count))
                for i in range(est_count):
                    y0 = i * row_height
                    y1 = min(th, (i + 1) * row_height)
                    if y1 > y0:
                        row_segments.append((y0, y1))
            _ocr_log(f"[rock_rows] seg_count={len(row_segments)} row_height={row_height or 'auto'} table_h={th}")

        if row_segments and 'table_img' in locals():
            th, tw = table_img.shape[:2]
            # Default column bounds (relative to table)
            p_left, p_right = 0, max(1, int(tw * 0.30))
            q_left, q_right = max(0, int(tw * 0.65)), tw
            if 'boxes' in locals() and 'tx1' in locals():
                if "percent" in boxes:
                    p1, py1, p2, py2 = boxes.get("percent", (tx1, ty1, tx1 + int((tx2 - tx1) * 0.30), ty2))
                    p_left = max(0, p1 - tx1); p_right = min(tw, p2 - tx1)
                if "quality" in boxes:
                    q1, qy1, q2, qy2 = boxes.get("quality", (tx1 + int((tx2 - tx1) * 0.65), ty1, tx2, ty2))
                    q_left = max(0, q1 - tx1); q_right = min(tw, q2 - tx1)

            # Heuristic padding to avoid cutting off row names if percent box is too wide
            name_pad = max(1, int(tw * 0.06))
            p_right = min(tw, max(p_right, int(tw * 0.18)))
            q_left = max(0, min(q_left, int(tw * 0.85)))

            for y0, y1 in row_segments:
                row_img = table_img[y0:y1, :]
                pct = ""
                pct_engine = "tesseract"
                name_engine = "tesseract"
                # Percent per-row OCR
                if 'percent_img' in locals():
                    prow = percent_img[y0:y1, :]
                    pproc = _rock_preprocess(prow, ocr_mode)
                    if len(pproc.shape) == 3:
                        pproc = cv2.cvtColor(pproc, cv2.COLOR_BGR2GRAY)
                    row_idx = len(seg_rows) + 1
                    p_cal = _get_calibration_field(f"percent_row_{row_idx}")
                    if p_cal:
                        ptxt = _ocr_with_calibration(f"percent_row_{row_idx}", prow, ROCK_NUM_TESS_CONFIG, r"\\d", ocr_mode, p_cal)
                        p_eng = p_cal.get("engine", "tesseract")
                    else:
                        ptxt, p_eng = _hybrid_ocr_text_with_engine(
                            prow, pproc, ROCK_NUM_TESS_CONFIG,
                            min_conf=55, require_pattern=r"\\d", label=f"percent_row_{row_idx}"
                        )
                    pct_tokens = _extract_percent_tokens(ptxt)
                    if pct_tokens:
                        pct = pct_tokens[0]
                        pct_engine = p_eng
                    _ocr_log(f"[rock_col] percent_row engine={p_eng} text='{(ptxt or '')[:28]}' pct={pct}")

                # Name per-row OCR (middle columns)
                nx1, nx2 = max(0, p_right - name_pad), min(tw, q_left)
                if nx2 <= nx1:
                    nx1, nx2 = 0, tw
                nrow = row_img[:, nx1:nx2]
                nproc = _rock_preprocess(nrow, ocr_mode)
                if len(nproc.shape) == 3:
                    nproc = cv2.cvtColor(nproc, cv2.COLOR_BGR2GRAY)
                row_idx = len(seg_rows) + 1
                n_cal = _get_calibration_field(f"row_name_{row_idx}")
                if n_cal:
                    ntext = _ocr_with_calibration(f"row_name_{row_idx}", nrow, ROCK_NAME_TESS_CONFIG, r"[A-Z]", ocr_mode, n_cal)
                    n_eng = n_cal.get("engine", "tesseract")
                else:
                    ntext, n_eng = _hybrid_ocr_text_with_engine(
                        nrow, nproc, ROCK_NAME_TESS_CONFIG,
                        min_conf=55, require_pattern=r"[A-Z]", label=f"row_name_{row_idx}"
                    )
                name_engine = n_eng
                nlines = _clean_lines(ntext)
                name_row = nlines[0] if nlines else ""
                if not DISABLE_ROCK_NAME_MATCHING:
                    name_row = _fuzzy_match_name(name_row, load_rock_names())
                _ocr_log(f"[rock_col] name_row engine={n_eng} text='{(ntext or '')[:28]}' name='{name_row[:24]}'")

                # Quality per-row OCR (right columns)
                qrow = row_img[:, q_left:q_right] if q_right > q_left else row_img[:, int(tw * 0.70):tw]
                row_idx = len(seg_rows) + 1
                q_cal = _get_calibration_field(f"quality_row_{row_idx}")
                if q_cal:
                    qtxt = _ocr_with_calibration(f"quality_row_{row_idx}", qrow, ROCK_QUALITY_TESS_CONFIG_LINE, r"\\d", ocr_mode, q_cal)
                else:
                    qtxt = _ocr_rock_quality(qrow, ocr_mode, psm_line=True)
                quality = _clean_quality_token(qtxt)
                _ocr_log(f"[rock_col] quality_row text='{(qtxt or '')[:28]}' quality={quality}")

                if pct or name_row or quality:
                    row_engine = pct_engine if pct else name_engine
                    seg_rows.append({"pct": pct, "name": name_row, "quality": quality, "engine": row_engine})
                    _ocr_log(f"[rock_row] seg pct={pct} name={name_row} quality={quality} pct_engine={pct_engine} name_engine={name_engine}")

        rows = []
        if seg_rows:
            rows = seg_rows
        row_re = re.compile(r"(\d+(?:[.,]\d+)?)\s*%\s*([A-Z0-9 ()/\-]+?)(?:\s+(\d{1,4}))?\s*$", re.IGNORECASE)
        if len(rows) < 2:
            if table_text:
                source_lines = [s.strip() for s in table_text.replace("\n", " ").split("|") if s.strip()]
            else:
                source_lines = lines
            for idx, l in enumerate(source_lines):
                u = l.upper()
                if "%" not in u:
                    continue
                m = row_re.search(u)
                if not m:
                    continue
                pct = m.group(1).replace(",", ".")
                name_row = m.group(2).strip()
                if not DISABLE_ROCK_NAME_MATCHING:
                    name_row = _fuzzy_match_name(name_row, load_rock_names())
                quality = _clean_quality_token(m.group(3) or "")
                # Prefer 3-4 digit quality from right-column OCR if available
                if (len(quality) < 3 or not quality.isdigit()) and idx < len(quality_lines):
                    quality = quality_lines[idx]
                if not quality:
                    # Try trailing digits from the segment itself
                    tail = _clean_quality_token(u)
                    if tail:
                        quality = tail
                try:
                    qv = int(quality) if quality else None
                    if qv is not None and (qv < 0 or qv > 1000):
                        qv = None
                except Exception:
                    qv = None
                # Accept any numeric quality (0-1000), even if fewer than 3 digits
                rows.append({"pct": pct, "name": name_row, "quality": str(qv) if qv is not None else "", "engine": "tesseract"})

        # Fallback: extract percent/value pairs if table_text is noisy and rows are too few
        if table_text and len(rows) < 2:
            pairs = re.findall(r"(\\d+(?:[.,]\\d+)?)\\s*%[^0-9]{0,8}(\\d{1,4})", table_text)
            if pairs:
                for i, (pct_raw, qty_raw) in enumerate(pairs):
                    pct = pct_raw.replace(",", ".")
                    quality = qty_raw if qty_raw else (quality_lines[i] if i < len(quality_lines) else "")
                    rows.append({"pct": pct, "name": "", "quality": quality, "engine": "tesseract"})
            # If still too few rows, at least capture all % tokens
            if len(rows) < 2:
                pct_tokens = re.findall(r"(\\d+(?:[.,]\\d+)?)\\s*%", table_text)
                for i, pct_raw in enumerate(pct_tokens):
                    pct = pct_raw.replace(",", ".")
                    quality = quality_lines[i] if i < len(quality_lines) else ""
                    rows.append({"pct": pct, "name": "", "quality": quality, "engine": "tesseract"})

        if not rows and table_text:
            for idx, l in enumerate(lines):
                u = l.upper()
                if "%" not in u:
                    continue
                m = row_re.search(u)
                if not m:
                    continue
                pct = m.group(1).replace(",", ".")
                name_row = m.group(2).strip()
                if not DISABLE_ROCK_NAME_MATCHING:
                    name_row = _fuzzy_match_name(name_row, load_rock_names())
                quality = (m.group(3) or "").strip()
                if (len(quality) < 3 or not quality.isdigit()) and idx < len(quality_lines):
                    quality = quality_lines[idx]
                try:
                    qv = int(quality) if quality else None
                    if qv is not None and (qv < 0 or qv > 1000):
                        qv = None
                except Exception:
                    qv = None
                rows.append({"pct": pct, "name": name_row, "quality": str(qv) if qv is not None else "", "engine": "tesseract"})

        # Final fallback: parse rows from raw OCR text segments
        if not rows:
            raw_segments = (text or "").replace("\n", " ").split("|")
            for idx, seg in enumerate(raw_segments):
                u = seg.upper()
                if "%" not in u:
                    continue
                m = row_re.search(u)
                if not m:
                    continue
                pct = m.group(1).replace(",", ".")
                name_row = m.group(2).strip()
                if not DISABLE_ROCK_NAME_MATCHING:
                    name_row = _fuzzy_match_name(name_row, load_rock_names())
                quality = (m.group(3) or "").strip()
                if (len(quality) < 3 or not quality.isdigit()) and idx < len(quality_lines):
                    quality = quality_lines[idx]
                try:
                    qv = int(quality) if quality else None
                    if qv is not None and (qv < 0 or qv > 1000):
                        qv = None
                except Exception:
                    qv = None
                if qv is not None and len(str(qv)) < 3 and qv != 0:
                    qv = None
                rows.append({"pct": pct, "name": name_row, "quality": str(qv) if qv is not None else "", "engine": "tesseract"})

        # Ultra-loose fallback: grab percent tokens + nearest numeric quality from full text
        if len(rows) < 2 and text:
            loose_pairs = re.findall(r"([A-Z0-9.,-]{1,6})\\s*%[^0-9]{0,8}([0-9]{1,4})", text.upper())
            for i, (ptok, qty) in enumerate(loose_pairs):
                pct = _normalize_percent_token(ptok)
                if not pct:
                    continue
                quality = qty if qty else (quality_lines[i] if i < len(quality_lines) else "")
                rows.append({"pct": pct, "name": "", "quality": quality, "engine": "tesseract"})
            if len(rows) < 2:
                pct_tokens = _extract_percent_tokens(text)
                for i, pct in enumerate(pct_tokens):
                    rows.append({"pct": pct, "name": "", "quality": quality_lines[i] if i < len(quality_lines) else "", "engine": "tesseract"})
                if pct_tokens:
                    _ocr_log(f"[rock_field] percent tokens(raw)={pct_tokens}")

        # Percent-column OCR fallback
        if ENABLE_COLUMN_WHOLE_OCR and len(rows) < 2 and 'percent_img' in locals():
            try:
                proc = _rock_preprocess(percent_img, ocr_mode)
                if len(proc.shape) == 3:
                    proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY)
                percent_text, engine = _hybrid_ocr_text_with_engine(
                    percent_img, proc, ROCK_NUM_TESS_CONFIG,
                    min_conf=60, require_pattern=r"\\d", label="percent"
                )
                pct_tokens = _extract_percent_tokens(percent_text)
                for i, pct in enumerate(pct_tokens):
                    rows.append({"pct": pct, "name": "", "quality": quality_lines[i] if i < len(quality_lines) else "", "engine": engine})
                if pct_tokens:
                    _ocr_log(f"[rock_field] percent engine={engine} tokens={pct_tokens}")
            except Exception:
                pass

        # If we captured per-row percents from the percent column, use them
        if len(rows) < 2 and percent_rows:
            for i, (pct, eng) in enumerate(percent_rows):
                rows.append({"pct": pct, "name": "", "quality": quality_lines[i] if i < len(quality_lines) else "", "engine": eng})
        # OpenAI contents pass (always attempt when enabled)
        if 'table_img' in locals():
            oai_rows = _openai_contents_rows(table_img, table_text)
            if oai_rows:
                rows = oai_rows
                _ocr_log(f"[ai-{load_ai_provider()}] using rows from API")
        if rows:
            for i, r in enumerate(rows, 1):
                _ocr_log(f"[rock_row] idx={i} pct={r.get('pct','')} name={r.get('name','')} quality={r.get('quality','')} engine={r.get('engine','')}")

        if not name and not rows and not any([mass, res, inst, comp]):
            return None, text

        raw_name = name or ""
        if not DISABLE_ROCK_NAME_MATCHING:
            name_list = load_rock_names()
            name = _fuzzy_match_name(raw_name, name_list)
        data = {
            "name": name or "",
            "raw_name": raw_name,
            "mass": mass or "",
            "res": res or "",
            "inst": inst or "",
            "comp": comp or "",
            "rows": rows,
            "raw_text": text,
            "raw_stats": stats_text,
            "raw_comp": comp_text,
            "raw_table": table_text,
            "raw_quality": quality_text,
        }
        return data, text
    except Exception as e:
        _ocr_log(f"[rock] exception parsing panel: {e}")
        return None, ""

def format_rock_details(data):
    lines = []
    if data.get("name"): lines.append(f"Name: {data['name']}")
    if data.get("mass"): lines.append(f"Mass: {data['mass']}")
    if data.get("res"): lines.append(f"Res: {data['res']}")
    if data.get("inst"): lines.append(f"Inst: {data['inst']}")
    if data.get("comp"): lines.append(f"Comp: {data['comp']}")
    if data.get("rows"):
        lines.append("Contents:")
        for r in data["rows"]:
            lines.append(f"  {r['pct']}%  {r['name']}  {r['quality']}")
    return "\n".join(lines).strip()

def load_rock_names(path=None):
    try:
        p = Path(path) if path else (_BASE_DIR / "rock_names.txt")
        if not p.exists():
            return []
        lines = [l.strip() for l in p.read_text(encoding="utf-8", errors="ignore").splitlines()]
        names = [l for l in lines if l and not l.startswith("#")]
        return names
    except Exception as e:
        _ocr_log(f"[rock] error loading rock_names.txt: {e}")
        return []

def _fuzzy_match_name(raw_name, choices):
    if not raw_name or not choices:
        return raw_name
    raw = raw_name.strip()
    if raw in choices:
        return raw
    def _norm(s):
        return re.sub(r"[^A-Za-z0-9]+", "", s).upper()
    def _variants(s):
        # Generate a few aggressive variants to handle OCR confusions
        swaps = {
            "0": "O", "1": "I", "2": "Z", "5": "S", "6": "G", "8": "B",
            "W": "I", "M": "N", "RN": "M", "VV": "W",
        }
        base = _norm(s)
        vars = {base}
        for k, v in swaps.items():
            vars.add(base.replace(k, v))
        return vars
    raw_vars = _variants(raw)
    best = (0.0, raw)
    for c in choices:
        cn = _norm(c)
        if not cn:
            continue
        for rv in raw_vars:
            score = difflib.SequenceMatcher(None, rv, cn).ratio()
            if score > best[0]:
                best = (score, c)
    return best[1] if best[0] >= 0.30 else raw

_ROCK_BOX_CACHE = None
_ROCK_BOX_MTIME = None
_ROCK_CALIB_CACHE = None
_ROCK_CALIB_MTIME = None

def _load_rock_boxes_from_config():
    global _ROCK_BOX_CACHE, _ROCK_BOX_MTIME
    try:
        if not ROCK_CONFIG_FILE.exists():
            return None
        mtime = ROCK_CONFIG_FILE.stat().st_mtime
        if _ROCK_BOX_CACHE is not None and _ROCK_BOX_MTIME == mtime:
            return _ROCK_BOX_CACHE
        payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
        if isinstance(payload, dict) and isinstance(payload.get("boxes"), dict):
            _ROCK_BOX_CACHE = payload["boxes"]
            _ROCK_BOX_MTIME = mtime
            return _ROCK_BOX_CACHE
    except Exception:
        return None
    return None

def _load_rock_calibration_from_config():
    global _ROCK_CALIB_CACHE, _ROCK_CALIB_MTIME
    try:
        if not ROCK_CONFIG_FILE.exists():
            return None
        mtime = ROCK_CONFIG_FILE.stat().st_mtime
        if _ROCK_CALIB_CACHE is not None and _ROCK_CALIB_MTIME == mtime:
            return _ROCK_CALIB_CACHE
        payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            cal = payload.get("calibration")
            if isinstance(cal, dict):
                _ROCK_CALIB_CACHE = cal
                _ROCK_CALIB_MTIME = mtime
                return _ROCK_CALIB_CACHE
    except Exception:
        return None
    return None

def _get_calibration_field(field_key):
    cal = _load_rock_calibration_from_config()
    if not cal:
        return None
    return cal.get(field_key)
def _rock_calibration_ready():
    try:
        if not ROCK_CONFIG_FILE.exists():
            return False
        payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            return False
        boxes = payload.get("boxes")
        if not isinstance(boxes, dict):
            return False
        required = {"name", "stats", "comp", "table", "row", "percent", "quality"}
        if not required.issubset(set(boxes.keys())):
            return False
        return True
    except Exception:
        return False

def rock_boxes_for_shape(h, w):
    # If calibration boxes exist, use them
    boxes = _load_rock_boxes_from_config()
    if boxes:
        out = {}
        for key, vals in boxes.items():
            if not isinstance(vals, (list, tuple)) or len(vals) != 4:
                continue
            x1 = int(max(0.0, min(1.0, vals[0])) * w)
            y1 = int(max(0.0, min(1.0, vals[1])) * h)
            x2 = int(max(0.0, min(1.0, vals[2])) * w)
            y2 = int(max(0.0, min(1.0, vals[3])) * h)
            if x2 > x1 and y2 > y1:
                out[key] = (x1, y1, x2, y2)
        if out:
            return out
    return {}


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

class RockBoxWizard:
    def __init__(self, parent, panel_region):
        self.result = None
        self.panel_region = panel_region
        self._rect = None
        self._start_x = self._start_y = 0
        self._selection = None
        self._step_idx = 0
        self._boxes = {}
        self._ready_for_calibration = False
        self._steps = [
            ("name", "Select NAME area"),
            ("stats", "Select STATS area (MASS/RES/INST)"),
            ("comp", "Select COMP area"),
            ("table", "Select TABLE area (contents)"),
            ("row", "Select ONE ROW height (any row)"),
            ("percent", "Select % column"),
            ("quality", "Select QUALITY column"),
        ]
        self._sample_entries = {}
        self._row_entries = []
        self._row_count = 3

        with mss.mss() as sct:
            raw = sct.grab(panel_region)
            img = np.frombuffer(raw.bgra, dtype=np.uint8).reshape(raw.height, raw.width, 4)
            self._img = cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)

        self.win = tk.Toplevel(parent)
        self.win.title("Rock Calibration")
        self.win.configure(bg=BG)
        self.win.attributes("-topmost", True)
        self.win.protocol("WM_DELETE_WINDOW", self._cancel)
        self.win.bind("<Escape>", lambda e: self._cancel())

        self.lbl_title = tk.Label(self.win, text="", bg=BG, fg=TEXT, font=f_alt(10, "bold"))
        self.lbl_title.pack(padx=10, pady=(10, 4))

        # Render image
        h, w = self._img.shape[:2]
        ok, buf = cv2.imencode(".png", cv2.cvtColor(self._img, cv2.COLOR_BGR2RGB))
        data = base64.b64encode(buf).decode("ascii") if ok else ""
        self._photo = tk.PhotoImage(data=data, format="PNG") if data else None
        self.canvas = tk.Canvas(self.win, width=w, height=h, bg="#000000", highlightthickness=1, highlightbackground=BORDER, cursor="crosshair")
        self.canvas.pack(padx=10, pady=6)
        if self._photo:
            self.canvas.create_image(0, 0, anchor="nw", image=self._photo)
        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)

        btn_row = tk.Frame(self.win, bg=BG)
        btn_row.pack(fill="x", padx=10, pady=(4, 10))
        self.btn_reset = tk.Button(btn_row, text="Reset", bg=PANEL, fg=TEXT, relief="solid", bd=1,
                                   highlightbackground=BORDER, font=f_alt(9), command=self._reset)
        self.btn_reset.pack(side="left")
        self.btn_run_cal = tk.Button(btn_row, text="Run Calibration", bg=GOLD, fg=BG, relief="solid", bd=1,
                                     highlightbackground=BORDER, font=f_alt(9, "bold"), command=self._run_calibration, state="disabled")
        self.btn_run_cal.pack(side="left", padx=(8, 0))
        self.btn_confirm = tk.Button(btn_row, text="Confirm", bg=ACCENT, fg=BG, relief="solid", bd=1,
                                     highlightbackground=BORDER, font=f_alt(9, "bold"), command=self._confirm)
        self.btn_confirm.pack(side="right")

        # Sample form
        self.form = tk.Frame(self.win, bg=BG)
        self.form.pack(fill="x", padx=10, pady=(4, 10))
        self._build_sample_form()

        self._update_title()
        parent.wait_window(self.win)

    def _build_sample_form(self):
        for w in self.form.winfo_children():
            w.destroy()
        row = 0
        def add_field(label, key, default=""):
            nonlocal row
            tk.Label(self.form, text=label, bg=BG, fg=TEXT, font=f_alt(8)).grid(row=row, column=0, sticky="w")
            ent = tk.Entry(self.form, width=24, bg=PANEL, fg=TEXT, insertbackground=TEXT)
            ent.insert(0, default)
            ent.grid(row=row, column=1, padx=(6, 12), pady=2, sticky="w")
            self._sample_entries[key] = ent
            row += 1

        add_field("Name", "name", "IRON (ORE)")
        add_field("Mass", "mass", "1132")
        add_field("Res", "res", "0%")
        add_field("Inst", "inst", "1.32")
        add_field("Comp", "comp", "1.48")

        # Row count
        tk.Label(self.form, text="Row count", bg=BG, fg=TEXT, font=f_alt(8)).grid(row=row, column=0, sticky="w")
        self.row_count_var = tk.StringVar(value=str(self._row_count))
        rc_ent = tk.Entry(self.form, textvariable=self.row_count_var, width=6, bg=PANEL, fg=TEXT, insertbackground=TEXT)
        rc_ent.grid(row=row, column=1, padx=(6, 6), pady=2, sticky="w")
        btn = tk.Button(self.form, text="Set Rows", bg=PANEL, fg=TEXT, relief="solid", bd=1,
                        highlightbackground=BORDER, font=f_alt(8), command=self._set_rows)
        btn.grid(row=row, column=1, padx=(70, 0), pady=2, sticky="w")
        row += 1

        # Rows
        self._row_entries = []
        for i in range(self._row_count):
            tk.Label(self.form, text=f"Row {i+1} %", bg=BG, fg=TEXT, font=f_alt(8)).grid(row=row, column=0, sticky="w")
            e_pct = tk.Entry(self.form, width=10, bg=PANEL, fg=TEXT, insertbackground=TEXT)
            e_pct.grid(row=row, column=1, padx=(6, 12), pady=2, sticky="w")
            row += 1
            tk.Label(self.form, text=f"Row {i+1} Name", bg=BG, fg=TEXT, font=f_alt(8)).grid(row=row, column=0, sticky="w")
            e_name = tk.Entry(self.form, width=24, bg=PANEL, fg=TEXT, insertbackground=TEXT)
            e_name.grid(row=row, column=1, padx=(6, 12), pady=2, sticky="w")
            row += 1
            tk.Label(self.form, text=f"Row {i+1} Quality", bg=BG, fg=TEXT, font=f_alt(8)).grid(row=row, column=0, sticky="w")
            e_q = tk.Entry(self.form, width=10, bg=PANEL, fg=TEXT, insertbackground=TEXT)
            e_q.grid(row=row, column=1, padx=(6, 12), pady=2, sticky="w")
            row += 1
            self._row_entries.append((e_pct, e_name, e_q))

    def _set_rows(self):
        try:
            n = int(self.row_count_var.get().strip())
            self._row_count = max(1, min(12, n))
        except Exception:
            self._row_count = 3
        self._build_sample_form()

    def _collect_sample(self):
        data = {}
        for k, ent in self._sample_entries.items():
            data[k] = ent.get().strip()
        data["row_count"] = str(self._row_count)
        for i, (e_pct, e_name, e_q) in enumerate(self._row_entries, 1):
            data[f"row{i}_pct"] = e_pct.get().strip()
            data[f"row{i}_name"] = e_name.get().strip()
            data[f"row{i}_quality"] = e_q.get().strip()
        return data

    def _update_title(self):
        key, label = self._steps[self._step_idx]
        self.lbl_title.config(text=f"{label} ({self._step_idx + 1}/{len(self._steps)})")

    def _on_press(self, e):
        self._start_x, self._start_y = e.x, e.y
        if self._rect: self.canvas.delete(self._rect)

    def _on_drag(self, e):
        if self._rect: self.canvas.delete(self._rect)
        self._rect = self.canvas.create_rectangle(self._start_x, self._start_y, e.x, e.y, outline=ACCENT, width=2)

    def _on_release(self, e):
        x1 = min(self._start_x, e.x); y1 = min(self._start_y, e.y)
        x2 = max(self._start_x, e.x); y2 = max(self._start_y, e.y)
        if (x2 - x1) > 5 and (y2 - y1) > 5:
            self._selection = (x1, y1, x2, y2)

    def _reset(self):
        if self._rect:
            self.canvas.delete(self._rect)
            self._rect = None
        self._selection = None

    def _confirm(self):
        if not self._selection:
            messagebox.showwarning("Calibration", "Please select a region first.")
            return
        h, w = self._img.shape[:2]
        x1, y1, x2, y2 = self._selection
        # Store normalized coords
        key, _ = self._steps[self._step_idx]
        self._boxes[key] = [x1 / w, y1 / h, x2 / w, y2 / h]
        self._reset()
        self._step_idx += 1
        if self._step_idx >= len(self._steps):
            self._ready_for_calibration = True
            self.btn_run_cal.config(state="normal")
            self.btn_confirm.config(state="disabled")
            self.lbl_title.config(text="Ready to run calibration")
            return
        self._update_title()

    def _run_calibration(self):
        if not self._ready_for_calibration:
            messagebox.showwarning("Calibration", "Please finish all box selections first.")
            return
        sample = self._collect_sample()
        _save_sample_template(sample)
        # Progress dialog for calibration runs
        progress_win = tk.Toplevel(self.win)
        progress_win.title("Calibrating OCR")
        progress_win.configure(bg=BG)
        progress_win.attributes("-topmost", True)
        progress_win.geometry("+%d+%d" % (self.win.winfo_rootx() + 20, self.win.winfo_rooty() + 20))
        lbl = tk.Label(progress_win, text="Starting calibration…", bg=BG, fg=TEXT, font=f_alt(9))
        lbl.pack(padx=12, pady=12)

        def _progress(field, engine, mode, scale):
            try:
                lbl.config(text=f"Calibrating {field} | {engine} | {mode} | x{scale}")
                progress_win.update_idletasks()
            except Exception:
                pass

        cal = _run_rock_calibration(self._img, self._boxes, sample, progress_cb=_progress)
        try:
            progress_win.destroy()
        except Exception:
            pass
        self.result = {"panel": self.panel_region, "boxes": self._boxes, "sample": sample, "calibration": cal, "ai_prompt": AI_DEFAULT_PROMPT}
        self.win.destroy()

    def _cancel(self):
        self.result = None
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
        self.openai_key_hidden = True
        self.root = tk.Tk()
        self.market_enabled_var = tk.BooleanVar(master=self.root, value=load_market_enabled())
        self.openai_enabled_var = tk.BooleanVar(master=self.root, value=load_ai_enabled())
        self.ai_provider_var = tk.StringVar(master=self.root, value=load_ai_provider())
        self.history_duration_var = tk.StringVar(master=self.root, value=str(load_history_duration()))
        self.ocr_sensitivity_var = tk.StringVar(master=self.root, value=load_ocr_sensitivity())
        self.calibration_hotkey_var = tk.StringVar(master=self.root, value=load_calibration_hotkey())
        self.openai_model_var = tk.StringVar(master=self.root, value=load_ai_model(self.ai_provider_var.get()))
        self.hotkeys = GlobalHotkeyManager()
        self.support_popup_shown_this_session = False
        self.root.title(f"{T('app_title')} {APP_VERSION_LABEL}")
        self.root.configure(bg=BG)
        self.root.resizable(False, False)
        self.root.geometry("620x840")
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
        for key in ["asteroid","material","hand","salvage","rock"]:
            var = tk.BooleanVar(value=(key in selected_modes)); self.mode_vars[key] = var
            cb = tk.Checkbutton(self.mode_frame, text=mode_label(key), variable=var, bg=BG, fg=MODE_INFO[key]["color"], activebackground=BG, activeforeground=MODE_INFO[key]["color"], selectcolor=PANEL, font=f_alt(10), anchor="w")
            cb.pack(fill="x", padx=10, pady=2); self.mode_checkbuttons[key] = cb

        btn_frame = tk.Frame(self.root, bg=BG); btn_frame.pack(fill="x", padx=16, pady=6)
        self.btn_calibrate = tk.Button(btn_frame, text=T("calibrate_zone"), bg=PANEL, fg=ACCENT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(11, "bold"), padx=12, pady=8, command=self.calibrate)
        self.btn_calibrate.pack(fill="x", pady=4)
        self.btn_calibrate_rock = tk.Button(btn_frame, text=T("calibrate_rock"), bg=PANEL, fg=TEXT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(10, "bold"), padx=12, pady=8, command=self.calibrate_rock)
        self.btn_calibrate_rock.pack(fill="x", pady=4)
        self.btn_run_rock_cal = tk.Button(btn_frame, text=T("run_rock_calibration"), bg=GOLD, fg=BG, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(10, "bold"), padx=12, pady=8, command=self.run_rock_calibration, state="disabled")
        self.btn_run_rock_cal.pack(fill="x", pady=4)
        self.btn_start = tk.Button(btn_frame, text=T("start_system"), bg=ACCENT, fg=BG, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(11, "bold"), padx=12, pady=10, command=self.start)
        self.btn_start.pack(fill="x", pady=4)

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

        self.openai_frame = tk.LabelFrame(self.root, text=T("ai_settings"), bg=BG, fg=TEXT, bd=1, font=f_ui(10, "bold"), relief="groove", highlightbackground=BORDER)
        self.openai_frame.pack(fill="x", padx=16, pady=(0,10))
        top_openai = tk.Frame(self.openai_frame, bg=BG); top_openai.pack(fill="x", padx=10, pady=(8,4))
        self.chk_openai = tk.Checkbutton(top_openai, text=T("ai_enable"), variable=self.openai_enabled_var, command=self._toggle_openai_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(10))
        self.chk_openai.pack(side="left")

        provider_row = tk.Frame(self.openai_frame, bg=BG); provider_row.pack(fill="x", padx=10, pady=(2,4))
        self.lbl_ai_provider = tk.Label(provider_row, text=T("ai_provider"), bg=BG, fg=TEXT, font=f_alt(10, "bold")); self.lbl_ai_provider.pack(side="left")
        self.ai_provider_menu = tk.OptionMenu(provider_row, self.ai_provider_var, *AI_PROVIDERS)
        self.ai_provider_menu.config(bg=PANEL, fg=TEXT, activebackground=PANEL_2, activeforeground=TEXT, relief="flat", highlightthickness=0)
        self.ai_provider_menu["menu"].config(bg=PANEL, fg=TEXT)
        self.ai_provider_menu.pack(side="left", padx=8)
        self._refresh_ai_provider_menu()
        self.ai_provider_var.trace_add("write", lambda *args: self._on_ai_provider_change())

        model_row = tk.Frame(self.openai_frame, bg=BG); model_row.pack(fill="x", padx=10, pady=(2,4))
        self.lbl_openai_model = tk.Label(model_row, text=T("ai_model"), bg=BG, fg=TEXT, font=f_alt(10, "bold")); self.lbl_openai_model.pack(side="left")
        self.entry_openai_model = tk.Entry(model_row, textvariable=self.openai_model_var, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="solid", bd=1, font=f_mono(10))
        self.entry_openai_model.pack(side="left", fill="x", expand=True, padx=8)

        key_row = tk.Frame(self.openai_frame, bg=BG); key_row.pack(fill="x", padx=10, pady=(2,4))
        self.lbl_openai_key = tk.Label(key_row, text=T("ai_key"), bg=BG, fg=TEXT, font=f_alt(10, "bold")); self.lbl_openai_key.pack(side="left")
        self.openai_key_var = tk.StringVar(master=self.root, value="")
        self.entry_openai_key = tk.Entry(key_row, textvariable=self.openai_key_var, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="solid", bd=1, font=f_mono(10), show="*")
        self.entry_openai_key.pack(side="left", fill="x", expand=True, padx=8)
        self.btn_openai_show = tk.Button(key_row, text=T("show"), bg=PANEL, fg=TEXT, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(9), command=self.toggle_openai_key_visibility)
        self.btn_openai_show.pack(side="left")

        openai_buttons = tk.Frame(self.openai_frame, bg=BG); openai_buttons.pack(fill="x", padx=10, pady=(2,8))
        self.btn_openai_save = tk.Button(openai_buttons, text=T("save"), bg=PANEL, fg=ACCENT, relief="solid", bd=1, highlightbackground=BORDER, font=f_ui(9, "bold"), command=self.save_openai_settings)
        self.btn_openai_save.pack(side="left")
        self.lbl_openai_status = tk.Label(openai_buttons, text="", bg=BG, fg=MUTED, font=f_alt(9))
        self.lbl_openai_status.pack(side="left", padx=(12,0))

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

        extra_frame = tk.Frame(self.root, bg=BG); extra_frame.pack(fill="x", padx=16, pady=(6,6))
        self.btn_guide = tk.Button(extra_frame, text=T("guide"), bg=PANEL, fg=TEXT, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(10), command=self.show_guide)
        self.btn_guide.pack(side="left")
        self.btn_donate = tk.Button(extra_frame, text=T("donate"), bg=PANEL, fg=GOLD, relief="solid", bd=1, highlightbackground=BORDER, font=f_alt(10, "bold"), command=self.open_donate)
        self.btn_donate.pack(side="right")

        status_text = T("csv_loaded") if self.mapping else T("csv_error")
        status_fg = GREEN if self.mapping else RED
        self.status = tk.Label(self.root, text=status_text, bg=BG, fg=status_fg, font=f_alt(9)); self.status.pack(pady=(8,6))
        self.lbl_hint = tk.Label(self.root, text=T("calibration_hint"), bg=BG, fg=MUTED, font=f_alt(9), wraplength=560, justify="left"); self.lbl_hint.pack(padx=16, pady=(0,10))

        self.refresh_token_status(); self._toggle_market_enabled(); self._toggle_openai_enabled(); self.refresh_openai_status(); self._refresh_run_cal_button()
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
        # Support popup disabled
        self.root.mainloop()

    def close_menu(self):
        try:
            self.hotkeys.stop()
        except Exception:
            pass
        self.root.destroy()

    def _refresh_run_cal_button(self):
        try:
            if _rock_calibration_ready():
                self.btn_run_rock_cal.config(state="normal")
            else:
                self.btn_run_rock_cal.config(state="disabled")
        except Exception:
            pass

    def run_rock_calibration(self):
        if not _rock_calibration_ready():
            messagebox.showwarning(T("calibrate_rock"), T("rock_missing_calibration"))
            return
        try:
            payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
            if not isinstance(payload, dict):
                messagebox.showwarning(T("calibrate_rock"), T("rock_missing_calibration"))
                return
            panel_region = payload.get("panel")
            boxes = payload.get("boxes")
            sample = payload.get("sample", {})
            if not panel_region or not boxes:
                messagebox.showwarning(T("calibrate_rock"), T("rock_missing_calibration"))
                return
            # Capture panel image from screen
            with mss.mss() as sct:
                raw = sct.grab(panel_region)
                img = np.frombuffer(raw.bgra, dtype=np.uint8).reshape(raw.height, raw.width, 4)
                panel_img = cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)
            # Run calibration with progress window
            progress_win = tk.Toplevel(self.root)
            progress_win.title("Calibrating OCR")
            progress_win.configure(bg=BG)
            progress_win.attributes("-topmost", True)
            lbl = tk.Label(progress_win, text="Starting calibration…", bg=BG, fg=TEXT, font=f_alt(9))
            lbl.pack(padx=12, pady=12)

            def _progress(field, engine, mode, scale):
                try:
                    lbl.config(text=f"Calibrating {field} | {engine} | {mode} | x{scale}")
                    progress_win.update_idletasks()
                except Exception:
                    pass

            cal = _run_rock_calibration(panel_img, boxes, sample, progress_cb=_progress)
            payload["calibration"] = cal
            if not payload.get("ai_prompt"):
                payload["ai_prompt"] = AI_DEFAULT_PROMPT
            ROCK_CONFIG_FILE.write_text(json.dumps(payload, indent=2), encoding="utf-8")
            try:
                progress_win.destroy()
            except Exception:
                pass
            messagebox.showinfo(T("calibrate_rock"), "Calibration complete.")
        except Exception as e:
            _ocr_log(f"[calibration] run error: {e}")
            messagebox.showerror(T("calibrate_rock"), str(e))

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
        self.openai_frame.config(text=T("ai_settings")); self.chk_openai.config(text=T("ai_enable"))
        self.lbl_ai_provider.config(text=T("ai_provider")); self._refresh_ai_provider_menu()
        self.lbl_openai_model.config(text=T("ai_model")); self.lbl_openai_key.config(text=T("ai_key"))
        self.btn_openai_show.config(text=T("hide") if not self.openai_key_hidden else T("show")); self.btn_openai_save.config(text=T("save"))
        self.lbl_history_duration.config(text=T("history_duration")); self.btn_history_save.config(text=T("save"))
        self.lbl_ocr_sensitivity.config(text=T("ocr_sensitivity")); self.btn_ocr_save.config(text=T("save")); self.lbl_ocr_status.config(text=ocr_sensitivity_label(self.ocr_sensitivity_var.get()))
        self.lbl_preview_mode.config(text=T("preview_mode")); self._refresh_preview_menu()
        self.chk_verify.config(text=T("verify_candidates"))
        self.chk_rock_preview.config(text=T("rock_preview"))
        self.chk_rock_boxes.config(text=T("rock_boxes"))
        self.chk_rock_quality_crop.config(text=T("rock_quality_crop"))
        # Rock OCR mode selector removed (calibration determines per-field settings)
        self.lbl_rock_preview_zoom.config(text=T("rock_preview_zoom"))
        self.lbl_calibration_hotkey.config(text=T("calibration_hotkey")); self.btn_hotkey_save.config(text=T("save"))
        self.btn_calibrate.config(text=T("calibrate_zone")); self.btn_calibrate_rock.config(text=T("calibrate_rock")); self.btn_run_rock_cal.config(text=T("run_rock_calibration")); self.btn_start.config(text=T("start_system")); self.btn_guide.config(text=T("guide")); self.btn_donate.config(text=T("donate"))
        status_text = T("csv_loaded") if self.mapping else T("csv_error"); status_fg = GREEN if self.mapping else RED
        self.status.config(text=status_text, fg=status_fg); self.lbl_hint.config(text=T("calibration_hint")); self.refresh_token_status(); self.refresh_openai_status()

    def _toggle_market_enabled(self):
        enabled = self.market_enabled_var.get(); save_market_enabled(enabled)
        state = "normal" if enabled else "disabled"
        self.entry_token.config(state=state); self.btn_show.config(state=state); self.btn_save.config(state=state); self.btn_test.config(state=state); self.btn_help.config(state=state)
        self.refresh_token_status()

    def _toggle_openai_enabled(self):
        enabled = self.openai_enabled_var.get()
        save_ai_enabled(enabled)
        self._set_openai_controls_state()
        self.refresh_openai_status()

    def _set_openai_controls_state(self):
        state = "normal" if self.openai_enabled_var.get() else "disabled"
        self.entry_openai_key.config(state=state)
        self.btn_openai_show.config(state=state)
        self.btn_openai_save.config(state=state)
        self.entry_openai_model.config(state=state)
        self.ai_provider_menu.config(state=state)

    def _preview_label(self, mode):
        if mode == "raw": return T("preview_raw")
        if mode == "processed": return T("preview_processed")
        return T("preview_none")

    def _refresh_preview_menu(self):
        menu = self.preview_menu["menu"]
        menu.delete(0, "end")
        for mode in PREVIEW_MODES:
            menu.add_command(label=self._preview_label(mode), command=lambda m=mode: self.preview_mode_var.set(m))

    def _refresh_ai_provider_menu(self):
        menu = self.ai_provider_menu["menu"]
        menu.delete(0, "end")
        for key in AI_PROVIDERS:
            label = AI_PROVIDER_LABELS.get(key, key)
            menu.add_command(label=label, command=lambda k=key: self.ai_provider_var.set(k))

    def _on_ai_provider_change(self):
        provider = self.ai_provider_var.get().strip().lower()
        save_ai_provider(provider)
        self.openai_model_var.set(load_ai_model(provider))
        self.refresh_openai_status()

    def _set_preview_mode(self, mode):
        save_preview_mode(mode)

    def refresh_token_status(self):
        if not self.market_enabled_var.get(): self.lbl_token_status.config(text=T("market_disabled"), fg=MUTED); return
        token = self.token_var.get().strip()
        if token: self.lbl_token_status.config(text=T("token_saved"), fg=GREEN)
        else: self.lbl_token_status.config(text=T("token_not_set"), fg=MUTED)

    def refresh_openai_status(self):
        if not self.openai_enabled_var.get():
            self.lbl_openai_status.config(text=T("ai_not_set"), fg=MUTED)
            return
        provider = self.ai_provider_var.get().strip().lower()
        key = _get_ai_api_key(provider)
        if key:
            status = T("ai_saved")
            fg = GREEN
        else:
            status = T("ai_not_set")
            fg = MUTED
        if keyring is None:
            status = f"{status} | {T('ai_keyring_missing')}"
            if key:
                fg = GOLD
        label = AI_PROVIDER_LABELS.get(provider, provider)
        status = f"{label}: {status}"
        self.lbl_openai_status.config(text=status, fg=fg)

    def toggle_token_visibility(self):
        self.token_hidden = not self.token_hidden
        self.entry_token.config(show="*" if self.token_hidden else "")
        self.btn_show.config(text=T("hide") if not self.token_hidden else T("show"))

    def toggle_openai_key_visibility(self):
        self.openai_key_hidden = not self.openai_key_hidden
        self.entry_openai_key.config(show="*" if self.openai_key_hidden else "")
        self.btn_openai_show.config(text=T("hide") if not self.openai_key_hidden else T("show"))

    def save_token(self):
        save_uex_token(self.token_var.get().strip()); self.refresh_token_status()

    def save_openai_settings(self):
        provider = self.ai_provider_var.get().strip().lower()
        save_ai_enabled(self.openai_enabled_var.get())
        save_ai_provider(provider)
        save_ai_model(provider, self.openai_model_var.get().strip())
        key = self.openai_key_var.get().strip()
        if key:
            _save_ai_api_key(provider, key)
            self.openai_key_var.set("")
        self.refresh_openai_status()

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

    def calibrate_rock(self):
        self.root.withdraw()
        try:
            selector = RegionSelector(self.root)
            if selector.result:
                wizard = RockBoxWizard(self.root, selector.result)
                if wizard.result:
                    try:
                        if isinstance(wizard.result, dict) and wizard.result.get("sample"):
                            global SAMPLE_TEMPLATE
                            SAMPLE_TEMPLATE = dict(wizard.result.get("sample") or {})
                    except Exception:
                        pass
                    ROCK_CONFIG_FILE.write_text(json.dumps(wizard.result, indent=2), encoding="utf-8")
                self.status.config(text=T("csv_loaded") if self.mapping else T("csv_error"), fg=GREEN if self.mapping else RED)
        except Exception as e:
            messagebox.showerror(T("calibrate_rock"), str(e))
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
        if "rock" in modes and not _rock_calibration_ready():
            messagebox.showwarning(T("calibrate_rock"), T("rock_missing_calibration")); return
        region = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        self.hotkeys.stop()
        self.root.destroy()
        try:
            rock_region = None
            if ROCK_CONFIG_FILE.exists():
                payload = json.loads(ROCK_CONFIG_FILE.read_text(encoding="utf-8"))
                rock_region = payload.get("panel") if isinstance(payload, dict) and payload.get("panel") else payload
            App(region, self.mapping, modes, rock_region)
        except Exception as e:
            _ocr_log(f"[overlay] failed to start: {e}")
            messagebox.showerror("Overlay error", str(e))


class App:
    def _ui_after(self, delay_ms, fn):
        try:
            if self.running and self.root is not None and int(self.root.winfo_exists()) == 1:
                holder = {"id": None}
                def _wrapped():
                    try:
                        if holder["id"] is not None:
                            self._after_ids.discard(holder["id"])
                    except Exception:
                        pass
                    fn()
                holder["id"] = self.root.after(delay_ms, _wrapped)
                self._after_ids.add(holder["id"])
        except Exception:
            pass

    def _cancel_afters(self):
        try:
            if self.root is None:
                return
            for aid in list(self._after_ids):
                try:
                    self.root.after_cancel(aid)
                except Exception:
                    pass
            self._after_ids.clear()
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

    def _toggle_rock_preview_enabled(self):
        self.rock_preview_enabled = bool(self.rock_preview_var.get())
        save_rock_preview_enabled(self.rock_preview_enabled)
        if not self.rock_preview_enabled:
            try:
                self.rock_preview_label.config(image="", text="")
                self._rock_preview_photo = None
            except Exception:
                pass

    def _toggle_rock_boxes_enabled(self):
        self.rock_boxes_enabled = bool(self.rock_boxes_var.get())
        save_rock_boxes_enabled(self.rock_boxes_enabled)

    def _toggle_rock_quality_crop_enabled(self):
        self.rock_quality_crop_enabled = bool(self.rock_quality_crop_var.get())
        save_rock_quality_crop_enabled(self.rock_quality_crop_enabled)

    def _rock_ocr_label(self, mode):
        return

    def _set_rock_preview_zoom(self, value):
        try:
            v = float(value)
        except Exception:
            v = 1.0
        self.rock_preview_zoom = max(1.0, min(10.0, v))
        save_rock_preview_zoom(self.rock_preview_zoom)

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

    def _set_rock_text(self, text):
        try:
            self.rock_label.config(text=text)
        except Exception:
            pass

    def _render_rock_preview(self, img):
        try:
            if not self.rock_preview_enabled:
                return
            h, w = img.shape[:2]
            # Ensure preview area matches captured size (1:1)
            try:
                cur_h = int(self.rock_preview_frame.winfo_height())
            except Exception:
                cur_h = 0
            target_h = int(h * self.rock_preview_zoom)
            if target_h < 20: target_h = h
            if cur_h != target_h:
                self.rock_preview_frame.config(height=target_h)
            display_img = img
            # Optionally show just the quality crop
            if self.rock_quality_crop_enabled:
                try:
                    tb = rock_boxes_for_shape(h, w).get("table")
                    if tb:
                        tx1, ty1, tx2, ty2 = tb
                        tw = tx2 - tx1
                        qw = max(1, int(tw * 0.35))
                        q1 = max(tx1, tx2 - qw)
                        display_img = display_img[ty1:ty2, q1:tx2]
                except Exception:
                    pass
            colors = {
                "header": (255, 0, 0),
                "name": (0, 255, 0),
                "stats": (0, 128, 255),
                "comp": (255, 0, 255),
                "table": (0, 255, 255),
                "col_pct": (255, 200, 0),
                "col_name": (0, 255, 150),
                "col_quality": (200, 0, 255),
                "qual_box": (255, 255, 255),
                "row_band": (120, 255, 120),
            }
            if self.rock_boxes_enabled:
                for key, (x1, y1, x2, y2) in rock_boxes_for_shape(h, w).items():
                    color = colors.get(key, (0, 255, 255))
                    cv2.rectangle(display_img, (x1, y1), (x2, y2), color, 1)
            # Column guides + row bands inside table area (always show bands)
            tb = rock_boxes_for_shape(h, w).get("table")
            if tb:
                tx1, ty1, tx2, ty2 = tb
                tw = tx2 - tx1
                th = ty2 - ty1
                # Percent column ~ left 22% (widened for 2-digit percent)
                p1 = tx1
                p2 = int(tx1 + tw * 0.22)
                # Name column ~ middle 57%
                n1 = p2
                n2 = int(tx1 + tw * 0.75)
                # Quality column ~ right 25%
                q1 = n2
                q2 = tx2
                if self.rock_boxes_enabled:
                    cv2.rectangle(display_img, (p1, ty1), (p2, ty2), colors["col_pct"], 1)
                    cv2.rectangle(display_img, (n1, ty1), (n2, ty2), colors["col_name"], 1)
                    cv2.rectangle(display_img, (q1, ty1), (q2, ty2), colors["col_quality"], 1)
                # Row band overlay using projection segmentation
                try:
                    table_img = display_img[ty1:ty2, tx1:tx2]
                    row_segments = _segment_table_rows_by_projection(table_img, "gray") if AUTO_CONTENT_ROWS else []
                    if not row_segments:
                        try:
                            boxes = rock_boxes_for_shape(h, w)
                            row_box = boxes.get("row")
                            if row_box:
                                _, ry1, _, ry2 = row_box
                                row_h = max(6, int(ry2 - ry1))
                                est = max(1, int((th + row_h - 1) / row_h))
                                row_segments = [(i * row_h, min(th, (i + 1) * row_h)) for i in range(est)]
                        except Exception:
                            row_segments = []
                    if not row_segments and th > 0:
                        # Last resort: draw 3 equal bands so user can see alignment
                        est = 3
                        row_h = max(6, int(th / est))
                        row_segments = [(i * row_h, min(th, (i + 1) * row_h)) for i in range(est)]
                    if self.rock_boxes_enabled and hasattr(self, "_last_row_overlay") is False:
                        self._last_row_overlay = 0
                    if getattr(self, "_last_row_overlay", 0) == 0:
                        _ocr_log(f"[rock_rows_overlay] table={tx1},{ty1},{tx2},{ty2} segments={len(row_segments)}")
                        self._last_row_overlay = 1
                    for y0, y1 in row_segments:
                        cv2.rectangle(display_img, (tx1, ty1 + y0), (tx2, ty1 + y1), colors["row_band"], 1)
                except Exception:
                    pass
                # Debug: draw boxes in quality column (green for digits, white for other chars)
                if self.rock_boxes_enabled:
                    try:
                        q_crop = display_img[ty1:ty2, q1:q2]
                        proc = cv2.cvtColor(q_crop, cv2.COLOR_BGR2GRAY)
                        data = pytesseract.image_to_data(proc, config="--psm 7", output_type=_TESS_OUTPUT.DICT)
                        n = len(data.get("text", []))
                        for i in range(n):
                            txt = (data["text"][i] or "").strip()
                            if not txt:
                                continue
                            x = data["left"][i]; y = data["top"][i]; w2 = data["width"][i]; h2 = data["height"][i]
                            has_digit = any(ch.isdigit() for ch in txt)
                            color = (0, 255, 0) if has_digit else (255, 255, 255)
                            cv2.rectangle(display_img, (q1 + x, ty1 + y), (q1 + x + w2, ty1 + y + h2), color, 1)
                    except Exception:
                        pass
            # Render at preview zoom
            if self.rock_preview_zoom != 1.0:
                display_img = cv2.resize(display_img, (max(1, int(w * self.rock_preview_zoom)), max(1, int(h * self.rock_preview_zoom))), interpolation=cv2.INTER_NEAREST)
            ok, buf = cv2.imencode(".png", display_img)
            if not ok:
                return
            data = base64.b64encode(buf).decode("ascii")
            photo = tk.PhotoImage(data=data, format="PNG")
            self._rock_preview_photo = photo
            self.rock_preview_label.config(image=photo)
        except Exception as e:
            _ocr_log(f"[rock_preview] {e}")

    def _maybe_update_rock(self, data):
        if not data:
            if not self.rock_data:
                self._ui_call(lambda: _safe_widget_call(self.rock_label, lambda: self._set_rock_text(T("rock_scanning"))))
            return
        text = format_rock_details(data)
        raw_name = data.get("raw_name", "").strip()
        matched_name = data.get("name", "").strip()
        if self.verify_enabled:
            extra = f"Name OCR: {raw_name or '—'}  |  Matched: {matched_name or '—'}"
            text = f"{extra}\n{text}" if text else extra
            raw_text = (data.get("raw_text") or "").strip()
            if raw_text:
                _ocr_log(f"[rock_raw] {raw_text.replace(chr(10),' | ')}")
            raw_stats = (data.get("raw_stats") or "").strip()
            if raw_stats:
                _ocr_log(f"[rock_raw_stats] {raw_stats.replace(chr(10),' | ')}")
            raw_comp = (data.get("raw_comp") or "").strip()
            if raw_comp:
                _ocr_log(f"[rock_raw_comp] {raw_comp.replace(chr(10),' | ')}")
            raw_table = (data.get("raw_table") or "").strip()
            if raw_table:
                _ocr_log(f"[rock_raw_table] {raw_table.replace(chr(10),' | ')}")
            raw_quality = (data.get("raw_quality") or "").strip()
            _ocr_log(f"[rock_raw_quality] {raw_quality.replace(chr(10),' | ')}" if raw_quality else "[rock_raw_quality] —")
            parsed = f"Name={matched_name or '—'} Mass={data.get('mass','') or '—'} Res={data.get('res','') or '—'} Inst={data.get('inst','') or '—'} Comp={data.get('comp','') or '—'} Rows={len(data.get('rows',[]))}"
            _ocr_log(f"[rock_parsed] {parsed}")
        now = time.time()
        if self.rock_data is None or text != self.rock_data:
            if self.rock_data is None or (now - self.rock_last_update) >= self.history_duration:
                self.rock_data = text
                self.rock_last_update = now
                self._ui_call(lambda t=text: _safe_widget_call(self.rock_label, lambda: self._set_rock_text(t)))
                _ocr_log(f"[rock] {text.replace(chr(10),' | ')}")

    def __init__(self, region, mapping, active_modes, rock_region=None):
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
        self.rock_region = rock_region
        self.rock_data = None
        self.rock_last_update = 0
        self._rock_last_ts = 0.0
        self._rock_table_hash = ""
        self.rock_preview_enabled = load_rock_preview_enabled()
        self.rock_boxes_enabled = load_rock_boxes_enabled()
        self.rock_ocr_mode = "gray"
        self.rock_preview_zoom = load_rock_preview_zoom()
        self.rock_quality_crop_enabled = load_rock_quality_crop_enabled()
        self._rock_preview_photo = None
        self.market_enabled = load_market_enabled(); self.market_client = UEXMarketClient(token=load_uex_token()); self.market_request_id = 0; self.current_market_material = None; self.current_market_kind = None
        self.hotkeys = GlobalHotkeyManager()
        self._last_rock_ocr_mode_logged = None
        self._after_ids = set()

        self._last_ocr_engine = None

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
        for key in ["asteroid","material","hand","salvage","rock"]:
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
        self.rock_preview_var = tk.BooleanVar(value=self.rock_preview_enabled)
        self.chk_rock_preview = tk.Checkbutton(verify_row, text=T("rock_preview"), variable=self.rock_preview_var, command=self._toggle_rock_preview_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(9))
        self.chk_rock_preview.pack(side="left", padx=(10,0))
        self.rock_boxes_var = tk.BooleanVar(value=self.rock_boxes_enabled)
        self.chk_rock_boxes = tk.Checkbutton(verify_row, text=T("rock_boxes"), variable=self.rock_boxes_var, command=self._toggle_rock_boxes_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(9))
        self.chk_rock_boxes.pack(side="left", padx=(10,0))
        self.rock_quality_crop_var = tk.BooleanVar(value=self.rock_quality_crop_enabled)
        self.chk_rock_quality_crop = tk.Checkbutton(verify_row, text=T("rock_quality_crop"), variable=self.rock_quality_crop_var, command=self._toggle_rock_quality_crop_enabled, bg=BG, fg=TEXT, activebackground=BG, activeforeground=TEXT, selectcolor=PANEL, font=f_alt(9))
        self.chk_rock_quality_crop.pack(side="left", padx=(10,0))
        # Rock OCR mode selector removed (calibration determines per-field OCR)
        self.lbl_rock_preview_zoom = tk.Label(verify_row, text=T("rock_preview_zoom"), bg=BG, fg=TEXT, font=f_alt(9, "bold"))
        self.lbl_rock_preview_zoom.pack(side="left", padx=(12,4))
        self.rock_preview_zoom_var = tk.DoubleVar(value=self.rock_preview_zoom)
        self.rock_preview_zoom_scale = tk.Scale(verify_row, from_=1, to=10, resolution=0.5, orient="horizontal", length=140,
                                                showvalue=True, variable=self.rock_preview_zoom_var, command=self._set_rock_preview_zoom,
                                                bg=BG, fg=TEXT, troughcolor=PANEL, highlightthickness=0)
        self.rock_preview_zoom_scale.pack(side="left")

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

        self.ocr_mode_label = tk.Label(self.root, text=T("ocr_mode_fast"), bg=BG, fg=MUTED, font=f_alt(8), anchor="w")
        self.ocr_mode_label.pack(fill="x", padx=8, pady=(0,4))

        self.rock_frame = tk.Frame(self.root, bg=BG)
        self.rock_frame.pack(fill="x", padx=8, pady=(0,4))
        self.rock_title = tk.Label(self.rock_frame, text=T("rock_panel"), bg=BG, fg=ACCENT, font=f_ui(9, "bold"), anchor="w")
        self.rock_title.pack(fill="x")
        self.rock_label = tk.Label(self.rock_frame, text=T("rock_scanning") if "rock" in self.active_modes else "", bg=BG, fg=TEXT, font=f_mono(9), anchor="w", justify="left", wraplength=680)
        self.rock_label.pack(fill="x")

        self.rock_preview_frame = tk.Frame(self.root, bg=BG, height=120)
        self.rock_preview_frame.pack(fill="x", padx=8, pady=(0,4))
        self.rock_preview_frame.pack_propagate(False)
        self.rock_preview_label = tk.Label(self.rock_preview_frame, text="", bg=PANEL, fg=MUTED, font=f_mono(8), anchor="center")
        self.rock_preview_label.pack(fill="both", expand=True)
        if not self.rock_preview_enabled:
            self.rock_preview_label.config(text="")
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
        self._cancel_afters()
        try: self.root.destroy()
        except Exception: pass
        self.root = None

    def back_to_menu(self):
        self.running = False
        try: self.hotkeys.stop()
        except Exception: pass
        try: save_overlay_geometry(self.root.geometry())
        except Exception: pass
        self._cancel_afters()
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

                if "rock" in self.active_modes and self.rock_region:
                    now = time.time()
                    if now - self._rock_last_ts >= 0.6:
                        self._rock_last_ts = now
                        global _CURRENT_ROCK_MODE
                        _CURRENT_ROCK_MODE = "calibrated"
                        if self.rock_data and (now - self.rock_last_update) < self.history_duration:
                            continue
                        rock_img = capture_region(self.rock_region)
                        if self.rock_preview_enabled:
                            self._ui_call(lambda im=rock_img.copy(): _safe_widget_call(self.rock_preview_label, lambda: self._render_rock_preview(im)))
                        table_hash = _rock_table_hash(rock_img)
                        if table_hash and table_hash == self._rock_table_hash:
                            continue
                        self._rock_table_hash = table_hash or self._rock_table_hash
                        rock_data, _ = parse_rock_details(rock_img, "gray")
                        self._maybe_update_rock(rock_data)
                raw, raw_candidates, validated = _read_number_internal(img, self.lookup, self.active_modes)
                if self.verify_enabled:
                    raw_set = ", ".join(sorted(set(raw_candidates))) if raw_candidates else "—"
                    val_set = ", ".join(sorted(set(validated))) if validated else "—"
                    self._ui_call(lambda r=raw_set, v=val_set: _safe_widget_call(self.verify_label, lambda: self.verify_label.config(text=f"OCR raw: {r}  |  valid: {v}")))
                else:
                    self._ui_call(lambda: _safe_widget_call(self.verify_label, lambda: self.verify_label.config(text="")))
                engine = LAST_OCR_ENGINE
                if engine != self._last_ocr_engine:
                    self._last_ocr_engine = engine
                    if engine == "paddle":
                        self._ui_call(lambda: _safe_widget_call(self.ocr_mode_label, lambda: self.ocr_mode_label.config(text=T("ocr_mode_high"), fg=GOLD)))
                    else:
                        self._ui_call(lambda: _safe_widget_call(self.ocr_mode_label, lambda: self.ocr_mode_label.config(text=T("ocr_mode_fast"), fg=MUTED)))
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
