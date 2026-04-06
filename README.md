

#### 🙌 Agradecimientos

En agradecimiento a una de las mejores comunidades de Twitch:

Gracias a **Norrisplay** por descubrirme el juego, por hacer cada día más entretenido con cada transmisión y por crear una comunidad hispana donde compartir esta experiencia.

👉 https://www.twitch.tv/norrisplay





# Pitipen Mining System — Release Notes




#### 🙌 Acknowledgements

Special thanks to one of the best Twitch communities:

Thanks to **Norrisplay** for introducing me to the game, making every day more enjoyable with each stream, and building a great Spanish-speaking community.

👉 https://www.twitch.tv/norrisplay


## 🇪🇸 Español

### v1.0.0 — Lanzamiento inicial

**Fecha de lanzamiento:** Abril 2026  
**Autor:** [danypolo](https://discord.com/users/danypolo)

---

#### ¿Qué es Pitipen Mining System?

Overlay táctico para **Star Citizen** que lee en tiempo real las firmas de radar del HUD y las cruza con una base de datos de minerales para identificar depósitos, tipos de asteroide y precios de venta actualizados desde la API de UEX Corp.

---

#### ✨ Características de esta versión

**Detección de firmas (OCR)**
- Lectura automática de la zona de pantalla calibrada cada 20 ms mediante Tesseract OCR
- Tres pipelines de preprocesado de imagen (color, contraste CLAHE, escala de grises) para máxima fiabilidad
- Corrección automática de errores comunes de OCR (confusiones entre 8, 6, 3, 0)
- Sistema de votación por historial: el valor debe confirmarse varias lecturas consecutivas antes de aceptarse
- Soporte de multiplicadores de firma (1× a 50×) para detectar el mismo mineral a distintas distancias
- Modo manual: introduce el valor de firma a mano sin necesidad de captura de pantalla

**Modos de búsqueda**
- **Asteroides** — Identifica el tipo de asteroide (C, E, M, P, Q, S) y muestra sus minerales comunes y raros
- **Minería con nave** — Identifica el mineral concreto y consulta precios refinados por SCU
- **Minería en superficie** — Modo FPS/ROC, muestra precios de todos los materiales de superficie
- **Chatarrería** — Modo salvage, muestra precios de Construction Materials y Recycled Material Composite

**Mercado UEX**
- Integración con la API pública de UEX Corp (v2.0)
- Precios de venta refinados por SCU para los sistemas Stanton, Pyro y Nyx
- Caché SQLite local de 12 horas para minimizar llamadas a la API y permitir consultas sin conexión
- Indicador de estado del dato: `live` / `caché` / `antigua`
- Token de API configurable desde la propia interfaz, con botón de prueba de conexión

**Overlay e interfaz**
- Overlay translúcido siempre encima, arrastrable desde la barra superior
- Redimensionable libremente desde el grip `◢` de la esquina inferior derecha
- Historial de las últimas 3 detecciones; clic en cualquier entrada recarga los precios
- Campo de entrada manual con placeholder y botón CONSULTAR
- Soporte multiidioma: 🇪🇸 ES · 🇬🇧 EN · 🇫🇷 FR · 🇩🇪 DE · 🇷🇺 RU
- Todos los ajustes persistentes en `preferences.json` (idioma, modos, token, geometría, duración de mensajes)

**Distribución**
- Instalador `.exe` autónomo: incluye Tesseract OCR y todas las dependencias
- No requiere instalar Python ni ningún componente externo
- Base de datos de firmas editable (`Minerales.csv`) para adaptarse a futuras actualizaciones del juego

---

#### ⚠️ Advertencia de uso

Este programa puede operar en **modo automático** (OCR de pantalla) o en **modo manual** (introducción de valores a mano).

> El modo automático captura píxeles de pantalla para leer el HUD del juego. Esta técnica puede ser considerada una infracción de los Términos de Servicio de Cloud Imperium Games. **El uso es bajo la exclusiva responsabilidad del usuario.**
>
> El modo manual no implica captura de pantalla y no infringe ninguna norma del juego.

---

#### 📦 Archivos incluidos

| Archivo | Descripción |
|---|---|
| `Pitipen_Mining_System.exe` | Instalador del programa |
| `Minerales.csv` | Base de datos de firmas de radar (editable) |
| `RELEASE_NOTES.md` | Este documento |
| `README.docx` | Manual de usuario completo (ES + EN) |

---

#### 🔧 Actualización de firmas en futuras versiones del juego

Si una actualización de Star Citizen cambia los valores de las firmas de radar, el sistema puede dejar de identificar minerales correctamente. Para corregirlo:

1. Abre `Minerales.csv` con Excel, LibreOffice Calc o cualquier editor de texto.
2. Localiza el mineral afectado y edita el valor de la columna `signature_radar`.
3. Guarda el archivo y reinicia el programa.

No es necesario esperar a una nueva versión del instalador para mantener la base de datos actualizada.

---

#### 🐛 Problemas conocidos

- En monitores con escalado superior al 125% el OCR puede necesitar recalibración tras cambiar la escala.
- En modo pantalla completa exclusiva el overlay puede quedar oculto bajo el juego; se recomienda usar modo ventana sin bordes.

---

#### 💬 Contacto y soporte

Creado por **[danypolo](https://discord.com/users/danypolo)** — contacto vía Discord.  
Si encuentras un error o quieres proponer una mejora, abre un [Issue](../../issues) en este repositorio.

#### ☕ Apoya el proyecto

Si te gusta este proyecto y quieres apoyarlo, puedes hacerlo aquí:

👉 https://www.paypal.com/paypalme/Danielpolopradanos
---

## 🇬🇧 English

### v1.0.0 — Initial Release

**Release date:** April 2026  
**Author:** [danypolo](https://discord.com/users/danypolo)

---

#### What is Pitipen Mining System?

A tactical overlay for **Star Citizen** that reads radar signatures from the HUD in real time and cross-references them against a mineral database to identify deposits, asteroid types and up-to-date sell prices sourced from the UEX Corp API.

---

#### ✨ Features in this release

**Signature detection (OCR)**
- Automatic reading of the calibrated screen area every 20 ms using Tesseract OCR
- Three image pre-processing pipelines (colour, CLAHE contrast, greyscale) for maximum reliability
- Automatic correction of common OCR errors (confusion between 8, 6, 3, 0)
- History-based voting system: a value must be confirmed across several consecutive reads before being accepted
- Signature multiplier support (1× to 50×) to detect the same mineral at varying distances
- Manual mode: enter signature values by hand with no screen capture required

**Search modes**
- **Asteroids** — Identifies asteroid type (C, E, M, P, Q, S) and shows its common and rare minerals
- **Ship mining** — Identifies the specific mineral and queries refined prices per SCU
- **Surface mining** — FPS/ROC mode, shows prices for all surface materials
- **Salvage** — Shows prices for Construction Materials and Recycled Material Composite

**UEX Market**
- Integration with the UEX Corp public API (v2.0)
- Refined sell prices per SCU for the Stanton, Pyro and Nyx systems
- Local SQLite cache (12 hours) to minimise API calls and allow offline lookups
- Data status indicator: `live` / `cache` / `old`
- API token configurable from within the UI, with a connection test button

**Overlay and interface**
- Translucent always-on-top overlay, draggable from the top bar
- Freely resizable from the `◢` grip in the bottom-right corner
- History of the last 3 detections; clicking any entry reloads prices for that material
- Manual input field with placeholder text and QUERY button
- Multi-language support: 🇪🇸 ES · 🇬🇧 EN · 🇫🇷 FR · 🇩🇪 DE · 🇷🇺 RU
- All settings persisted in `preferences.json` (language, modes, token, geometry, message duration)

**Distribution**
- Self-contained `.exe` installer: includes Tesseract OCR and all dependencies
- No Python or external components required
- Editable signature database (`Minerales.csv`) to adapt to future game updates

---

#### ⚠️ Usage warning

This program can operate in **automatic mode** (screen OCR) or **manual mode** (entering values by hand).

> Automatic mode captures screen pixels to read the game HUD. This technique may be considered a violation of Cloud Imperium Games' Terms of Service. **Use is entirely at the user's own risk.**
>
> Manual mode does not involve screen capture and does not violate any game rules.

---

#### 📦 Included files

| File | Description |
|---|---|
| `Pitipen_Mining_System.exe` | Program installer |
| `Minerales.csv` | Radar signature database (editable) |
| `RELEASE_NOTES.md` | This document |
| `README.docx` | Full user manual (ES + EN) |

---

#### 🔧 Updating signatures for future game versions

If a Star Citizen update changes radar signature values, the system may stop identifying minerals correctly. To fix this:

1. Open `Minerales.csv` in Excel, LibreOffice Calc or any text editor.
2. Find the affected mineral and edit the value in the `signature_radar` column.
3. Save the file and restart the program.

No new installer version is needed to keep the database up to date.

---

#### 🐛 Known issues

- On monitors with display scaling above 125%, the OCR may need recalibration after changing the scale.
- In exclusive full-screen mode the overlay may be hidden beneath the game; borderless windowed mode is recommended.

#### ☕ Support the project

If you like this project and want to support it, you can do it here:

👉 https://www.paypal.com/paypalme/Danielpolopradanos

#### 💬 Contact and support

Created by **[danypolo](https://discord.com/users/danypolo)** — contact via Discord.  
If you find a bug or want to suggest an improvement, open an [Issue](../../issues) in this repository.
