"""
Kalyan East rental tracker - STRICT mode
----------------------------------------
Checks the main property websites and sends a listing to Telegram only if it
passes ALL of these checks:

  1. 1 BHK or 1 RK only (1.5 / 2 / 3 BHK are dropped)
  2. Kalyan East only - anything that says Kalyan West is dropped
  3. Within 2 km of Kalyan railway station (east entry) - Lokgram, Kolsewadi /
     Shivaji Colony, Tisgao Naka / Santosh Nagar - plus Chakki Naka, which
     sits a little further out and is accepted up to 3 km on the map.
  4. Four-wheeler (car) parking clearly mentioned - "no car parking",
     "two-wheeler only" or no mention at all is dropped

How the 2 km check works:
  * If the listing has a map pin (latitude/longitude in the page data, or a
    Google plus code such as "64HQ+V34" in its address), the real straight-line
    distance to the station is used, and the pin must be on the east side of
    the railway line.
  * Otherwise the listing must name a locality from NEAR_LOCALITIES.
  * No map pin and no known nearby locality = skipped as "location unclear".

Each Telegram alert carries the rent, deposit, maintenance, size, furnishing,
floor, parking type, availability and posting date (whatever the site shows),
whether it is an owner listing (no brokerage), how to contact, and the link.

Alerts also go to WhatsApp (free CallMeBot service, personal use) for every
number in the GitHub secret WHATSAPP_RECIPIENTS, written as
    919876543210:1234567,919812345678:7654321
(phone with country code : that phone's CallMeBot apikey). Each person gets
their apikey once by sending "I allow callmebot to send me messages" on
WhatsApp to the CallMeBot number listed on callmebot.com.

The summary message after each run shows how many listings were read on each
site and why the rest were skipped, so you can see the filter working.
Runs on GitHub Actions every 6 hours. (Housing.com is not included: it blocks
automated visits.)
"""
import copy
import datetime
import hashlib
import html
import json
import math
import os
import re
import time
from collections import Counter
from urllib.parse import unquote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID")
WHATSAPP_RECIPIENTS = os.environ.get("WHATSAPP_RECIPIENTS", "")
STATE_FILE = "seen_listings.json"

# =================================================================== settings
# Kalyan Junction railway station, east entry (lat, lng)
STATION = (19.234802, 73.131218)
MAX_DISTANCE_KM = 2.0
# Areas you asked for that sit a little beyond 2 km: listings naming them may
# be up to EXTENDED_AREA_MAX_KM away on the map.
EXTENDED_AREAS = ["chakki naka", "chakkinaka"]
EXTENDED_AREA_MAX_KM = 3.0

# True = only listings that clearly mention car / four-wheeler parking.
REQUIRE_CAR_PARKING = True

# Vijay Nagar / Amrai / Tisgaon sit right around the 2 km line.
# False = skip them (strict). True = include them.
INCLUDE_BORDERLINE = False

# Send a short "what was checked" summary after every run.
SEND_SUMMARY_EVERY_RUN = True

# WhatsApp: the 6-hourly "check done" summary stays on Telegram only (False).
WHATSAPP_SEND_SUMMARY = False
WHATSAPP_MAX_PER_RUN = 10     # new-listing messages per number per run
WHATSAPP_WELCOME_MAX = 10     # a newly added number first gets this many current matches

LISTINGS_PER_MESSAGE = 4  # detailed alerts are longer (Telegram max 4096 chars)
MAX_MESSAGES_PER_RUN = 6  # anything beyond this is sent on the next run

# ------------------------------------------------------------------ areas
# Kalyan East localities inside the 2 km zone (used when there is no map pin).
NEAR_LOCALITIES = [
    "lokgram", "lok gram", "atmaram nagar",
    "kolsewadi", "kolshewadi", "kolsevadi", "kolse wadi", "kolshe wadi",
    "shivaji colony", "prabhuram nagar",
    "tisgao naka", "tisgaon naka", "santosh nagar",
    "chakki naka", "chakkinaka",
]
# Right around 2 km - only used when INCLUDE_BORDERLINE = True.
BORDERLINE_LOCALITIES = [
    "vijay nagar", "vijaynagar", "vijayanagar", "vijaya nagar",
    "amrai", "tisgaon", "tisgao", "netivali",
]
# Kalyan East / nearby areas that are further than 2 km from the station.
# (Roads such as Kalyan-Shil Road or Malang Road start next to the station,
# so they are deliberately not listed here.)
FAR_LOCALITIES = [
    "katemanivali", "kate manivali", "chinchpada", "suchak naka",
    "kailash nagar", "pisavli", "pisavali", "adivali", "dhokali",
    "nandivli", "nandivali", "hanuman nagar",
    "vithalwadi", "vitthalwadi", "ulhasnagar",
    "ambernath", "badlapur", "dombivli", "dombivali", "thakurli", "titwala",
    "shahad", "mohone", "ambivli", "bhiwandi", "palava", "kalyan rural",
]
# Kalyan West - always dropped.
WEST_LOCALITIES = [
    "khadakpada", "birla college", "godrej hill", "adharwadi", "durgadi",
    "wayle nagar", "gandhare", "gandhari", "barave", "rambaug", "ram baug",
    "santoshi mata road", "agra road", "chikanghar", "bail bazar", "subhash road",
]


def _words_re(words):
    return re.compile(r"\b(" + "|".join(re.escape(w) for w in words) + r")\b")


NEAR_RE = _words_re(NEAR_LOCALITIES)
EXTENDED_RE = _words_re(EXTENDED_AREAS)
BORDER_RE = _words_re(BORDERLINE_LOCALITIES)
FAR_RE = _words_re(FAR_LOCALITIES)
WEST_RE = re.compile(
    r"\bkalyan\s*\(?\s*w(?:est)?\b|\b421301\b|" + _words_re(WEST_LOCALITIES).pattern
)
EAST_RE = re.compile(r"\bkalyan\s*\(?\s*e(?:ast)?\b|\b421306\b")

# Railway line through Kalyan (Thakurli -> Kalyan Jn -> Shahad).
# Kalyan West is north of this line, Kalyan East is south of it.
RAIL_LINE = [(19.225507, 73.096730), (19.235250, 73.130500), (19.243889, 73.166389)]
TRACK_BUFFER_KM = 0.2  # pins this close to the tracks need "Kalyan East" in the text

# ------------------------------------------------------------------ size
ONE_SIZE_RE = re.compile(r"(?<![\d.])1\s*(?:bhk|rk)\b|\b(?:bhk|rk)1\b")
OTHER_SIZE_RE = re.compile(r"(?<![\d.])(?:[2-9]|1\.5|2\.5|3\.5)\s*bhk\b|\bbhk[2-9]\b")
JSON_ONE_BED_RE = re.compile(r'"(?:bedroom_num|bedrooms|bedroom|noofbedrooms|bhk)"\s*:\s*"?1\b')

# ------------------------------------------------------------------ parking
CAR = r"(?:cars?|four\s*wheelers?|4\s*wheelers?|4w)"
CAR_PARKING_RE = re.compile(
    rf"\b{CAR}\s+(?:parking|park)\b"
    rf"|\bparking\s*(?:for|:|available for|-)?\s*(?:a\s+|one\s+|1\s+)?{CAR}\b"
)
NO_CAR_PARKING_RE = re.compile(
    rf"\b(?:no|not|without|nil)\s+(?:any\s+|covered\s+|open\s+|reserved\s+)?{CAR}\s+park"
    rf"|\b{CAR}\s+parking\s*(?::|is)?\s*(?:not\s+available|unavailable|not\s+allowed|not\s+provided"
    rf"|no\b|none\b|nil\b|na\b|n/a|0\b)"
    r"|\bonly\s+(?:two|2)\s*wheeler|\b(?:two|2)\s*wheeler\s+(?:parking\s+)?only"
    r"|\bbike\s+parking\s+only|\bonly\s+bike\s+parking"
)
# NoBroker page data: "parking": "BOTH" / "FOUR_WHEELER" / "TWO_WHEELER" / "NONE"
NB_PARKING_RE = re.compile(r'"parking"\s*:\s*"(both|four_wheeler|two_wheeler|none)"')
JSON_CAR_FIELD_RE = re.compile(
    r'"(?:car_?parking|four_?wheeler_?parking|covered_?car_?parking)"\s*:\s*"?([^",}]*)'
)

# ------------------------------------------------------------------ sites
SITES = {
    "NoBroker": {
        "urls": [
            "https://www.nobroker.in/1bhk-flats-for-rent-in-lokgram_kalyan_mumbai",
            "https://www.nobroker.in/1rk-flats-for-rent-in-lokgram_kalyan_mumbai",
            "https://www.nobroker.in/1bhk-flats-for-rent-in-shivaji_colony_kalyan_mumbai",
            "https://www.nobroker.in/1rk-flats-for-rent-in-shivaji_colony_kalyan_mumbai",
            "https://www.nobroker.in/flats-for-rent-in-kolsewadi_kalyan_east_kalyan_mumbai",
            "https://www.nobroker.in/1bhk-flats-for-rent-in-santosh_nagar_kalyan_mumbai",
            "https://www.nobroker.in/1bhk-flats-for-rent-near-chakki_naka_mumbai",
            "https://www.nobroker.in/1bhk-flats-for-rent-in-vijay_nagar_kalyan_mumbai",
            "https://www.nobroker.in/1bhk-flats-for-rent-in-kalyan_east_mumbai",
            "https://www.nobroker.in/flats-for-rent-in-kalyan_east_mumbai",
        ],
        "link_pattern": r"/property/",
        "must_match": r"/property/.+/detail",  # skips search-result pages
        "brokerage": "Owner listing - no brokerage",
        "contact": "tap 'Contact Owner' on the NoBroker page (free login)",
    },
    "99acres": {
        "urls": [
            "https://www.99acres.com/1-bhk-flats-for-rent-in-kalyan-east-mumbai-beyond-thane-ffid",
            "https://www.99acres.com/flats-for-rent-in-kalyan-east-mumbai-beyond-thane-ffid",
        ],
        "link_pattern": r"(spid-|-r\d{6,}|-npxid-)",
        "brokerage": "Owner or agent - check the listing",
        "contact": "phone button on the 99acres page",
    },
    "MagicBricks": {
        "urls": [
            "https://www.magicbricks.com/1-bhk-flats-for-rent-in-kalyan-east-thane-pppfr",
            "https://www.magicbricks.com/flats-for-rent-in-kalyan-east-thane-pppfr",
        ],
        "link_pattern": r"(propertyDetails|pdpid)",
        "must_match": r"(propertyDetails|pdpid)",
        "brokerage": "Owner or agent - check the listing",
        "contact": "'Contact' button on the MagicBricks page",
    },
    "Square Yards": {
        "urls": [
            "https://www.squareyards.com/rent/property-for-rent-in-kalyan-east-thane",
            "https://www.squareyards.com/rent/1-rk-for-rent-in-kalyan-thane",
        ],
        "link_pattern": r"/rent/.*\d{5,}",
        "brokerage": "May be an agent - ask about brokerage",
        "contact": "'Contact' button on the Square Yards page",
    },
}

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-IN,en;q=0.9",
}

BAD_URL_KEYS = ["image", "img", "photo", "thumb", "logo", "video", "canonical", "builder", "agent"]
BULKY_KEYS = ["image", "img", "photo", "thumb", "video", "gallery", "media", "banner"]
IMAGE_RE = re.compile(r"\.(jpe?g|png|webp|gif|svg)(\?|$)", re.I)
LD_LISTING_TYPES = {
    "listitem", "apartment", "residence", "singlefamilyresidence", "house",
    "accommodation", "product", "offer", "realestatelisting",
}
TITLE_KEYS = ["propertyTitle", "title", "name", "PROP_HEADING", "heading", "projectName"]
PRICE_KEYS = [
    "rent", "price", "PRICE", "formattedPrice", "displayPrice", "expectedRent",
    "monthlyRent", "priceD", "MIN_PRICE",
]
LAT_KEYS = {"latitude", "lat", "lattitude", "geolat", "maplat"}
LNG_KEYS = {"longitude", "lng", "lon", "long", "geolng", "geolon", "maplng", "maplong"}

SKIP_REASONS = {
    "size": "not 1BHK/1RK",
    "west": "Kalyan West",
    "far": "too far",
    "border": "~2 km borderline",
    "unclear": "location unclear",
    "parking": "no car parking",
}


# ------------------------------------------------------------------ state
def load_seen():
    try:
        with open(STATE_FILE, "r") as f:
            return set(json.load(f))
    except Exception:
        return set()


def save_seen(seen):
    with open(STATE_FILE, "w") as f:
        json.dump(sorted(seen), f, indent=0)


# ------------------------------------------------------------------ telegram
def send_telegram(text):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        print("Telegram secrets missing - message not sent.")
        return False
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    try:
        r = requests.post(url, json=payload, timeout=15)
        if r.ok:
            print("Telegram message sent.")
            return True
        # Telegram explains the problem in the response body - show it.
        print(f"Telegram error {r.status_code}: {r.text}")
    except Exception as e:
        print(f"Telegram request failed: {e}")
    return False


# ------------------------------------------------------------------ whatsapp
def whatsapp_recipients():
    """[(phone, apikey)] from the WHATSAPP_RECIPIENTS secret."""
    out = []
    for part in re.split(r"[,;\n]+", WHATSAPP_RECIPIENTS or ""):
        part = part.strip()
        if not part:
            continue
        if ":" not in part:
            print("WhatsApp: an entry has no ':apikey' part - skipped")
            continue
        phone, key = part.split(":", 1)
        phone = re.sub(r"\D", "", phone)
        key = key.strip()
        if len(phone) == 10:  # Indian mobile written without 91
            phone = "91" + phone
        if len(phone) < 11 or not key:
            print("WhatsApp: an entry looks incomplete - skipped")
            continue
        # hide the number and key in the GitHub Actions log
        print(f"::add-mask::{key}")
        print(f"::add-mask::{phone}")
        out.append(("+" + phone, key))
    return out


def masked(phone):
    return phone[:3] + "*****" + phone[-3:]


def whatsapp_id(phone):
    return "WA|" + hashlib.sha256(phone.encode()).hexdigest()[:16]


def to_whatsapp_text(html_text):
    """Telegram HTML -> WhatsApp text (*bold*, _italic_, plain links)."""
    t = re.sub(r'<a href="([^"]+)">([^<]*)</a>', lambda m: f"{m.group(2)}: {m.group(1)}", html_text)
    t = re.sub(r"</?b>", "*", t)
    t = re.sub(r"</?i>", "_", t)
    t = re.sub(r"<[^>]+>", "", t)
    return html.unescape(t)


def send_whatsapp(phone, apikey, text):
    try:
        r = requests.get(
            "https://api.callmebot.com/whatsapp.php",
            params={"phone": phone, "text": text, "apikey": apikey},
            timeout=30,
        )
        reply = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", r.text)).strip()
        ok = r.ok and not re.search(r"\b(error|invalid|wrong|not allowed|blocked)\b", reply, re.I)
        print(f"WhatsApp {masked(phone)}: {'sent' if ok else 'FAILED'} - {reply[:120]}")
        time.sleep(3)  # CallMeBot asks for a gentle pace
        return ok
    except Exception as e:
        print(f"WhatsApp {masked(phone)}: request failed: {e}")
        return False


def whatsapp_listing(item):
    return to_whatsapp_text("🚨 <b>New rental near Kalyan station (East)</b>\n\n" + format_listing(item))


def whatsapp_welcome(matches):
    """Messages for a newly added number: hello + current matches (compact)."""
    msgs = [to_whatsapp_text(
        "✅ <b>Kalyan rent alerts connected</b>\n"
        f"<i>{html.escape(criteria_line())}</i>\n\n"
        "New listings will come here as soon as they appear. "
        + (f"Here are the {min(len(matches), WHATSAPP_WELCOME_MAX)} current matches:" if matches
           else "No listing matches right now.")
    )]
    lines = []
    for n, m in enumerate(matches[:WHATSAPP_WELCOME_MAX], start=1):
        price = f"{_money(m['price'])}/month" if m["price"] else "rent not shown"
        lines.append(f"{n}. *{price}* · {m.get('place', '')}\n{m['title'][:70]}\n{m['url']}")
    for i in range(0, len(lines), 5):
        msgs.append("\n\n".join(lines[i:i + 5]))
    if len(matches) > WHATSAPP_WELCOME_MAX:
        msgs.append(f"+ {len(matches) - WHATSAPP_WELCOME_MAX} more matches - see Telegram.")
    return msgs


# ------------------------------------------------------------------ geo helpers
def distance_km(a, b):
    lat1, lng1, lat2, lng2 = map(math.radians, (*a, *b))
    h = math.sin((lat2 - lat1) / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin((lng2 - lng1) / 2) ** 2
    return 6371.0 * 2 * math.asin(math.sqrt(h))


def side_of_tracks(point):
    """'east', 'west', or 'unclear' (pin sits on / right next to the tracks)."""
    lat0 = math.radians(STATION[0])

    def xy(p):  # local km coordinates
        return ((p[1] - STATION[1]) * 111.32 * math.cos(lat0), (p[0] - STATION[0]) * 110.57)

    px, py = xy(point)
    best = None
    for a, b in zip(RAIL_LINE, RAIL_LINE[1:]):
        (ax, ay), (bx, by) = xy(a), xy(b)
        dx, dy = bx - ax, by - ay
        seg_len2 = dx * dx + dy * dy
        t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / seg_len2))
        cx, cy = ax + t * dx, ay + t * dy
        dist = math.hypot(px - cx, py - cy)
        cross = dx * (py - ay) - dy * (px - ax)  # > 0 means north of the line
        if best is None or dist < best[0]:
            best = (dist, cross)
    dist, cross = best
    if dist < TRACK_BUFFER_KM:
        return "unclear"
    return "west" if cross > 0 else "east"


def valid_coords(lat, lng):
    return 18.9 < lat < 19.6 and 72.8 < lng < 73.5  # roughly Mumbai-Kalyan region


# Google plus codes ("64HQ+V34", "7JFM64HQ+V34") - often in NoBroker addresses
OLC_ALPHABET = "23456789CFGHJMPQRVWX"
PLUS_CODE_RE = re.compile(
    r"(?<![0-9a-z])((?:[23456789cfghjmpqrvwx]{4})?[23456789cfghjmpqrvwx]{4})"
    r"\+([23456789cfghjmpqrvwx]{2,3})(?![0-9a-z])",
    re.I,
)


def _olc_decode(code):
    code = code.upper().replace("+", "")
    lat = lng = 0.0
    lat_res = lng_res = 400.0
    for i in range(0, min(len(code), 10), 2):
        lat_res /= 20
        lng_res /= 20
        lat += OLC_ALPHABET.index(code[i]) * lat_res
        lng += OLC_ALPHABET.index(code[i + 1]) * lng_res
    for ch in code[10:]:
        lat_res /= 5
        lng_res /= 4
        idx = OLC_ALPHABET.index(ch)
        lat += (idx // 4) * lat_res
        lng += (idx % 4) * lng_res
    return lat - 90 + lat_res / 2, lng - 180 + lng_res / 2


def _olc_prefix(lat, lng):
    lat, lng, out = lat + 90, lng + 180, ""
    for res in (20.0, 1.0):
        a, b = int(lat // res), int(lng // res)
        out += OLC_ALPHABET[a] + OLC_ALPHABET[b]
        lat, lng = lat - a * res, lng - b * res
    return out


def coords_from_plus_code(text):
    m = PLUS_CODE_RE.search(text)
    if not m:
        return None
    head, tail = m.group(1).upper(), m.group(2).upper()
    if len(head) == 4:  # short code -> recover it near Kalyan station
        lat, lng = _olc_decode(_olc_prefix(*STATION) + head + tail)
        if STATION[0] + 0.5 < lat:
            lat -= 1
        elif STATION[0] - 0.5 > lat:
            lat += 1
        if STATION[1] + 0.5 < lng:
            lng -= 1
        elif STATION[1] - 0.5 > lng:
            lng += 1
    else:
        lat, lng = _olc_decode(head + tail)
    return (lat, lng) if valid_coords(lat, lng) else None


def coords_from_node(node):
    """Find a latitude/longitude pair in a listing's page data (shallow first)."""
    queue = [(node, 0)]
    while queue:
        cur, depth = queue.pop(0)
        if isinstance(cur, dict):
            lat = lng = None
            for k, v in cur.items():
                kl = k.lower()
                try:
                    if kl in LAT_KEYS:
                        lat = float(v)
                    elif kl in LNG_KEYS:
                        lng = float(v)
                except (TypeError, ValueError):
                    pass
            if lat is not None and lng is not None and valid_coords(lat, lng):
                return (lat, lng)
            if depth < 4:
                queue.extend((v, depth + 1) for v in cur.values() if isinstance(v, (dict, list)))
        elif isinstance(cur, list) and depth < 4:
            queue.extend((v, depth + 1) for v in cur[:20])
    return None


# ------------------------------------------------------------------ criteria
def normalize(text):
    t = unquote(text).lower()
    t = t.replace("-", " ")
    return re.sub(r"\s+", " ", t)


def check_size(title, text):
    for part in (normalize(title), text):
        one = ONE_SIZE_RE.search(part) or JSON_ONE_BED_RE.search(part)
        other = OTHER_SIZE_RE.search(part)
        if one or other:
            return bool(one) and not other
    return False


def check_parking(raw, text):
    """Returns 'yes', 'no' or 'unknown'."""
    m = NB_PARKING_RE.search(raw)
    if m and m.group(1) in ("two_wheeler", "none"):
        return "no"
    for value in JSON_CAR_FIELD_RE.findall(raw):
        v = value.strip().lower()
        if v in ("", "0", "no", "none", "null", "false", "na", "n/a", "not available"):
            return "no"
    if NO_CAR_PARKING_RE.search(text):
        return "no"
    if m or CAR_PARKING_RE.search(text):
        return "yes"
    for value in JSON_CAR_FIELD_RE.findall(raw):
        if value.strip():
            return "yes"
    return "unknown"


def _area_verdict(scope):
    """Decide from locality names in one piece of text. None = no names found."""
    west = WEST_RE.search(scope)
    near = NEAR_RE.search(scope)
    border = BORDER_RE.search(scope)
    far = FAR_RE.search(scope)
    if not (west or near or border or far):
        return None
    if west and not (near or border):
        return False, "west", west.group(0)
    if far and not (near or border):
        return False, "far", far.group(1)
    if near and not (far or west):
        return True, "", near.group(1).title()
    if border and not (far or west):
        if INCLUDE_BORDERLINE:
            return True, "", border.group(1).title() + " (~2 km)"
        return False, "border", border.group(1)
    return False, "unclear", "mixed localities"


def check_location(headline, text, coords):
    """Returns (ok, skip_reason_key, place_label)."""
    if coords:
        dist = distance_km(STATION, coords)
        side = side_of_tracks(coords)
        extended = EXTENDED_RE.search(headline) or EXTENDED_RE.search(text)
        limit = EXTENDED_AREA_MAX_KM if extended else MAX_DISTANCE_KM
        if dist > limit:
            return False, "far", f"{dist:.1f} km"
        # Title/link naming a far-off or West area beats a wrong map pin
        # (e.g. "Flat in Badlapur" pinned next to Kalyan station).
        head = _area_verdict(headline)
        if head and head[1] in ("far", "west"):
            return False, head[1], f"{head[2]} (pin said {dist:.1f} km)"
        if side == "west" or (WEST_RE.search(headline) and not NEAR_RE.search(headline)):
            return False, "west", f"{dist:.1f} km, west side"
        if side == "unclear" and not (EAST_RE.search(text) or NEAR_RE.search(text)):
            return False, "unclear", "pin on the tracks"
        name = NEAR_RE.search(text) or BORDER_RE.search(text)
        label = f"{name.group(1).title()} · " if name else ""
        return True, "", f"{label}{dist:.1f} km from station (map pin)"
    # no map pin -> the title/link decides first, then the full text
    head = _area_verdict(headline)
    full = _area_verdict(text)
    verdict = head
    if head is None or head[1] in ("border", "unclear"):
        # title is vague (e.g. "Omkar Nagar Netivali") - let the address decide
        if full and (full[0] or head is None):
            verdict = full
    if verdict is None:
        return False, "unclear", "no locality"
    if verdict[0] and EXTENDED_RE.search(verdict[2].lower()):
        # "Chakki Naka" is used loosely - drop it if the address is a far area
        far = FAR_RE.search(text)
        if far:
            return False, "far", f"{verdict[2]} listing in {far.group(1)}"
    return verdict


def evaluate(item):
    """Returns (ok, skip_reason_key)."""
    raw = item["text"].lower()
    text = normalize(item["text"])
    headline = normalize(item["title"] + " " + item["url"])

    if not check_size(item["title"], text):
        return False, "size"

    coords = item.get("coords") or coords_from_plus_code(unquote(raw))
    ok, reason, place = check_location(headline, text, coords)
    item["place"] = place
    if not ok:
        return False, reason

    parking = check_parking(raw, text)
    item["parking"] = parking == "yes"
    if parking == "no" or (REQUIRE_CAR_PARKING and parking != "yes"):
        return False, "parking"
    return True, ""


# ------------------------------------------------------------------ page parsing
def normalize_url(url):
    return url.split("#")[0].split("?")[0].rstrip("/")


DETAIL_KEYS = {
    "deposit": ["deposit", "securitydeposit", "depositamount", "formatteddeposit"],
    "maintenance": ["maintenanceamount", "formattedmaintenanceamount", "maintenancecharges", "maintenance"],
    "size": ["propertysize", "builtuparea", "carpetarea", "superbuiltuparea", "floorsize", "area"],
    "furnishing": ["furnishing", "furnishingdesc", "furnished"],
    "floor": ["floor", "floorno"],
    "total_floors": ["totalfloor", "totalfloors"],
    "available": ["availablefrom", "possessiondate", "availabledate", "availability"],
    "tenants": ["leasetype", "tenanttype", "preferredtenants"],
    "parking": ["parking", "parkingdesc", "carparking"],
    "address": ["street", "address", "propertyaddress", "locality", "society"],
    "posted": ["activationdate", "creationdate", "postedon", "createdon"],
}
ENUM_WORDS = {
    "both": "Bike + Car", "four_wheeler": "Car", "two_wheeler": "Bike only", "none": "None",
    "semi_furnished": "Semi furnished", "full_furnished": "Fully furnished",
    "fully_furnished": "Fully furnished", "not_furnished": "Unfurnished",
    "family": "Family", "bachelor": "Bachelor", "company": "Company", "anyone": "Anyone",
}


def _fmt_date(v):
    try:
        ms = float(v)
        if ms > 1e11:
            ms /= 1000
        d = datetime.datetime.fromtimestamp(ms, datetime.timezone.utc)
        if 2010 < d.year < 2035:
            return d.strftime("%d %b %Y")
    except (TypeError, ValueError, OverflowError, OSError):
        pass
    return str(v)


def _fmt_value(key, v):
    if isinstance(v, dict):
        v = first_value(v, ["value", "name", "displayName", "label"])
    if isinstance(v, str) and v.lower() in ENUM_WORDS:
        return ENUM_WORDS[v.lower()]
    if isinstance(v, str) and re.fullmatch(r"[A-Z0-9_]+", v) and "_" in v:
        return v.replace("_", " ").capitalize()  # e.g. BACHELOR_MALE -> Bachelor male
    if key in ("available", "posted"):
        return _fmt_date(v)
    if key in ("deposit", "maintenance") and str(v).replace(",", "").replace(".", "").isdigit():
        return f"₹{float(str(v).replace(',', '')):,.0f}"
    if key == "size" and str(v).replace(".", "").isdigit():
        return f"{float(v):,.0f} sqft"
    return str(v).strip()


def details_from_node(node):
    """Rent details that the site's page data carries (keys vary by site)."""
    lower = {k.lower(): v for k, v in node.items() if isinstance(k, str)}
    out = {}
    for field, keys in DETAIL_KEYS.items():
        for k in keys:
            v = lower.get(k)
            if isinstance(v, bool):  # yes/no flags are not values to show
                continue
            if v not in (None, "", [], {}):
                val = _fmt_value(field, v)
                if field == "size" and not re.search(r"\d", val):
                    continue
                if (val and val.lower() not in ("null", "none", "0")) or field == "maintenance":
                    out[field] = val
                    break
    return out


def nobroker_posted(url):
    """NoBroker listing ids carry the date the listing was first posted."""
    m = re.search(r"/([0-9a-f]{32})/detail", url)
    if m:
        try:
            d = datetime.datetime.fromtimestamp(int(m.group(1)[16:28], 16) / 1000, datetime.timezone.utc)
            if 2014 < d.year < 2035:
                return d.strftime("%d %b %Y")
        except (ValueError, OverflowError, OSError):
            pass
    return ""


def first_value(d, keys):
    for k in keys:
        v = d.get(k)
        if isinstance(v, (str, int, float)) and str(v).strip():
            return str(v).strip()
    return ""


def compact(node, depth=0):
    """Listing data without photo lists etc., so the useful fields fit in the text."""
    if depth > 5:
        return None
    if isinstance(node, dict):
        return {
            k: compact(v, depth + 1) for k, v in node.items()
            if not any(b in k.lower() for b in BULKY_KEYS)
        }
    if isinstance(node, list):
        return [compact(v, depth + 1) for v in node[:5]]
    return node


def extract_json_blobs(soup, raw):
    """Find JSON data embedded in the page (JSON-LD and app state)."""
    blobs = []
    names = []
    for s in soup.find_all("script"):
        text = s.string or s.get_text() or ""
        if not text.strip():
            continue
        if s.get("type") == "application/ld+json" or s.get("id") == "__NEXT_DATA__":
            try:
                blobs.append(json.loads(text))
                names.append(s.get("id") or "ld+json")
            except Exception:
                pass
            continue
        # window.SOMETHING = JSON.parse("...")
        for m in re.finditer(r'([\w$.]+)\s*=\s*JSON\.parse\((["\'])(.*?)(?<!\\)\2\)', text, re.S):
            try:
                inner = json.loads('"' + m.group(3).replace('\\\'', "'") + '"')
                blobs.append(json.loads(inner))
                names.append(m.group(1))
            except Exception:
                pass
        # window.SOMETHING = { ... }
        for m in re.finditer(r'([\w$.]+)\s*=\s*\{', text):
            start = m.end() - 1
            obj = cut_braces(text, start)
            if obj and len(obj) > 500:
                try:
                    blobs.append(json.loads(obj))
                    names.append(m.group(1))
                except Exception:
                    pass
    return blobs, names


def cut_braces(text, start):
    """Return the {...} block starting at text[start], respecting strings."""
    depth, i, in_str, quote = 0, start, False, ""
    while i < len(text):
        c = text[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == quote:
                in_str = False
        elif c in "\"'":
            in_str, quote = True, c
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
        i += 1
    return None


def listings_from_json(blobs, base_url, link_pattern):
    found = {}
    domain = urlparse(base_url).netloc

    def walk(node, depth=0):
        if depth > 40:
            return
        if isinstance(node, dict):
            url = ""
            for k, v in node.items():
                kl = k.lower()
                if not isinstance(v, str) or any(b in kl for b in BAD_URL_KEYS):
                    continue
                if ("url" in kl or kl in ("link", "href")) and not IMAGE_RE.search(v):
                    if v.startswith("/") or domain in v:
                        url = v
                        break
            has_price = any(k in node for k in PRICE_KEYS) or "offers" in node
            ld_type = str(node.get("@type", "")).lower()
            is_ld_listing = ld_type in LD_LISTING_TYPES
            if url and (has_price or is_ld_listing or re.search(link_pattern, url)):
                full = normalize_url(urljoin(base_url, url))
                if full != normalize_url(base_url) and full not in found:
                    price = first_value(node, PRICE_KEYS)
                    if not price and isinstance(node.get("offers"), dict):
                        price = first_value(node["offers"], ["price", "lowPrice"])
                    found[full] = {
                        "title": first_value(node, TITLE_KEYS),
                        "price": price,
                        "url": full,
                        "coords": coords_from_node(node),
                        "details": details_from_node(node),
                        "keys": sorted(node.keys())[:80],
                        "text": json.dumps(compact(node), ensure_ascii=False)[:10000] + " " + full,
                    }
            for v in node.values():
                walk(v, depth + 1)
        elif isinstance(node, list):
            for v in node:
                walk(v, depth + 1)

    for b in blobs:
        walk(b)
    return list(found.values())


def listings_from_links(soup, base_url, link_pattern):
    found = {}
    domain = urlparse(base_url).netloc

    def is_listing_link(href):
        full = urljoin(base_url, href)
        if urlparse(full).netloc != domain:
            return False
        return bool(re.search(link_pattern, full) or (
            re.search(r"\d{6,}", full) and re.search(r"(bhk|rk|rent)", full.lower())
        ))

    anchors = soup.find_all("a", href=True)
    for a in anchors:
        if not is_listing_link(a["href"]):
            continue
        key = normalize_url(urljoin(base_url, a["href"]))
        if key in found or key == normalize_url(base_url):
            continue
        # climb up to the listing "card" around the link
        card = a
        for _ in range(6):
            parent = card.parent
            if parent is None:
                break
            links_inside = {
                normalize_url(urljoin(base_url, x["href"]))
                for x in parent.find_all("a", href=True)
                if is_listing_link(x["href"])
            }
            if links_inside - {key}:  # parent holds another listing -> stop
                break
            card = parent
            if len(card.get_text(" ", strip=True)) > 250:
                break
        # leave out other links inside the card (e.g. NoBroker's "Nearby:
        # Dombivali Station, Wayle Nagar..." chips) - they are not the flat's area
        card = copy.copy(card)
        for x in card.find_all("a", href=True):
            if normalize_url(urljoin(base_url, x["href"])) != key:
                x.decompose()
        text = card.get_text(" ", strip=True)[:1500]
        price = ""
        m = re.search(r"₹\s?[\d,\.]+\s*(?:k|lac|lakh|/month)?", text, re.I)
        if m:
            price = m.group(0).strip()
        found[key] = {
            "title": (a.get_text(" ", strip=True) or a.get("title") or "")[:120],
            "price": price,
            "url": key,
            "coords": None,
            "text": text + " " + key,
        }
    return list(found.values())


# ------------------------------------------------------------------ scraping
def check_site(session, site, cfg):
    """Reads every page of a site. Returns (matches, status_text)."""
    merged, pages_ok, problems = {}, 0, []
    for n, url in enumerate(cfg["urls"]):
        if n:
            time.sleep(2)  # be polite between pages
        try:
            r = session.get(url, headers=HEADERS, timeout=25, allow_redirects=True)
        except Exception as e:
            print(f"[{site}] {url} -> request failed: {e}")
            problems.append("could not connect")
            continue

        soup = BeautifulSoup(r.text, "html.parser")
        title = soup.title.get_text(strip=True)[:80] if soup.title else ""
        print(f"[{site}] {url}")
        print(f"    HTTP {r.status_code}, {len(r.text)} bytes, page title: {title!r}")

        if r.status_code in (401, 403, 429):
            problems.append(f"blocked automated access (HTTP {r.status_code})")
            continue
        if r.status_code != 200:
            problems.append(f"HTTP {r.status_code}")
            continue

        blobs, names = extract_json_blobs(soup, r.text)
        from_json = listings_from_json(blobs, r.url, cfg["link_pattern"])
        from_links = listings_from_links(soup, r.url, cfg["link_pattern"])
        print(f"    listings found: {len(from_json)} from page data, {len(from_links)} from links")

        page = {item["url"]: item for item in from_links}
        for item in from_json:  # page data is richer, prefer it
            if item["url"] in page:
                item["text"] += " " + page[item["url"]]["text"]
                item["title"] = item["title"] or page[item["url"]]["title"]
                item["price"] = item["price"] or page[item["url"]]["price"]
            page[item["url"]] = item
        if cfg.get("must_match"):
            page = {u: i for u, i in page.items() if re.search(cfg["must_match"], u)}
        if page:
            pages_ok += 1
        elif "captcha" in r.text.lower() or "access denied" in r.text[:3000].lower():
            problems.append("blocked automated access (captcha page)")
        for u, item in page.items():
            merged.setdefault(u, item)

    if not merged:
        return [], (problems[-1] if problems else "page loaded but no listings could be read")

    sample = next((i for i in merged.values() if i.get("keys")), None)
    if sample:
        print(f"    page-data fields (sample): {sample['keys']}")

    # The same pin on 3+ listings is a locality centre, not the flat - ignore it.
    pins = Counter(
        (round(i["coords"][0], 4), round(i["coords"][1], 4))
        for i in merged.values() if i.get("coords")
    )
    for item in merged.values():
        c = item.get("coords")
        if c and pins[(round(c[0], 4), round(c[1], 4))] >= 3:
            item["coords"] = None

    matches, skipped = [], Counter()
    for item in merged.values():
        ok, reason = evaluate(item)
        if ok:
            item["site"] = site
            item["brokerage"] = cfg.get("brokerage", "")
            item["contact"] = cfg.get("contact", "")
            matches.append(item)
        else:
            skipped[reason] += 1
            if skipped[reason] <= 3:
                print(f"    skip ({SKIP_REASONS[reason]}, {item.get('place', '')}): {item['url']}")
    for item in matches:
        print(f"    MATCH {item['title'][:60]!r} {item['price']} {item['place']} {item['url']}")
    if matches:
        print("    sample alert:\n      " + format_listing(matches[0]).replace("\n", "\n      "))
    print(f"    {len(merged)} listings from {pages_ok} pages, matching: {len(matches)}, skipped: {dict(skipped)}")

    status = f"{len(merged)} listings read ({pages_ok} pages), {len(matches)} match"
    if skipped:
        status += " (skipped: " + ", ".join(
            f"{n} {SKIP_REASONS[k]}" for k, n in skipped.most_common()
        ) + ")"
    return matches, status


def _money(v):
    v = str(v).strip()
    if v.replace(",", "").replace(".", "").isdigit():
        return f"₹{float(v.replace(',', '')):,.0f}"
    return v


def format_listing(item):
    e = html.escape
    d = dict(item.get("details") or {})
    if not d.get("posted") and item["site"] == "NoBroker":
        d["posted"] = nobroker_posted(item["url"])

    money = [f"{_money(item['price'])}/month" if item["price"] else "rent not shown"]
    if d.get("deposit"):
        money.append(f"Deposit {d['deposit']}")
    if d.get("maintenance"):
        maint = d["maintenance"]
        money.append("No maintenance" if maint in ("0", "₹0") else f"Maint. {maint}")

    flat = [x for x in (d.get("size"), d.get("furnishing")) if x]
    if d.get("floor"):
        flat.append(f"Floor {d['floor']}" + (f"/{d['total_floors']}" if d.get("total_floors") else ""))
    if d.get("tenants"):
        flat.append(f"For {d['tenants']}")

    when = []
    if d.get("available"):
        when.append(f"Available {d['available']}")
    if d.get("posted"):
        when.append(f"Posted {d['posted']}")

    lines = [
        f"🏠 <b>{e((item['title'] or '1 BHK / 1 RK')[:120])}</b>",
        "💰 " + e(" · ".join(money)),
    ]
    if flat:
        lines.append("📐 " + e(" · ".join(flat)))
    lines.append("🚗 " + e(d.get("parking") or "Car parking mentioned"))
    lines.append("📍 " + e(item.get("place") or "Kalyan East")
                 + (f" · {e(d['address'][:80])}" if d.get("address") else ""))
    if when:
        lines.append("🗓 " + e(" · ".join(when)))
    if item.get("brokerage"):
        lines.append("👤 " + e(item["brokerage"]))
    if item.get("contact"):
        lines.append("📞 Contact: " + e(item["contact"]))
    lines.append(f"🔗 <a href=\"{e(item['url'])}\">Open on {e(item['site'])}</a>")
    return "\n".join(lines)


def criteria_line():
    parts = [
        f"Kalyan East · ≤{MAX_DISTANCE_KM:g} km from station "
        f"(Lokgram, Kolsewadi, Tisgao Naka) + Chakki Naka ≤{EXTENDED_AREA_MAX_KM:g} km",
        "1BHK/1RK",
    ]
    if REQUIRE_CAR_PARKING:
        parts.append("4-wheeler parking")
    return " · ".join(parts)


def main():
    print(f"Checking rentals: {criteria_line()}\n")
    seen = load_seen()
    session = requests.Session()
    recipients = whatsapp_recipients()
    wa_new = [r for r in recipients if whatsapp_id(r[0]) not in seen]   # just added
    wa_old = [r for r in recipients if whatsapp_id(r[0]) in seen]
    print(f"WhatsApp numbers: {len(recipients)} ({len(wa_new)} new)\n")

    new_items, all_matches, summary = [], [], []
    for site, cfg in SITES.items():
        matches, status = check_site(session, site, cfg)
        all_matches.extend(matches)
        fresh = [m for m in matches if f"{site}|{m['url']}" not in seen and m["url"] not in seen]
        new_items.extend(fresh)
        icon = "✅" if "listings read" in status else "⚠️"
        summary.append(f"{icon} {site}: {html.escape(status)}" + (f", {len(fresh)} new" if fresh else ""))
        print()
        time.sleep(2)  # be polite between sites

    print(f"New listings this run: {len(new_items)}")
    sent = 0
    wa_sent = Counter()
    chunks = [new_items[i:i + LISTINGS_PER_MESSAGE] for i in range(0, len(new_items), LISTINGS_PER_MESSAGE)]
    for n, chunk in enumerate(chunks[:MAX_MESSAGES_PER_RUN], start=1):
        header = (
            f"🚨 <b>New rentals near Kalyan station (East)</b> "
            f"({n}/{min(len(chunks), MAX_MESSAGES_PER_RUN)})\n"
            f"<i>{html.escape(criteria_line())}</i>\n\n"
        )
        tg_ok = send_telegram(header + "\n\n".join(format_listing(i) for i in chunk))
        time.sleep(1)
        for item in chunk:
            wa_ok = False
            for phone, key in wa_old:
                if wa_sent[phone] < WHATSAPP_MAX_PER_RUN and send_whatsapp(phone, key, whatsapp_listing(item)):
                    wa_sent[phone] += 1
                    wa_ok = True
            if tg_ok or wa_ok:
                seen.add(f"{item['site']}|{item['url']}")
                sent += 1

    # numbers added since the last run: a welcome + the current matches (also a test)
    for phone, key in wa_new:
        msgs = whatsapp_welcome(all_matches)
        if all([send_whatsapp(phone, key, m) for m in msgs]):
            seen.add(whatsapp_id(phone))
            wa_sent[phone] += len(msgs)

    if SEND_SUMMARY_EVERY_RUN:
        left = len(new_items) - sent
        text = "ℹ️ <b>Kalyan rental check done</b>\n"
        text += f"<i>{html.escape(criteria_line())}</i>\n\n" + "\n".join(summary)
        text += f"\n\nNew listings sent: {sent}"
        if left > 0:
            text += f" ({left} more will come next run)"
        if recipients:
            text += f"\nWhatsApp: {len(recipients)} number(s), {sum(wa_sent.values())} message(s) sent"
        send_telegram(text)
        if WHATSAPP_SEND_SUMMARY:
            for phone, key in recipients:
                send_whatsapp(phone, key, to_whatsapp_text(text))

    save_seen(seen)
    print(f"Done. Sent {sent} new listings.")


if __name__ == "__main__":
    main()
