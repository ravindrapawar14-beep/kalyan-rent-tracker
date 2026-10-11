"""
Kalyan East rental tracker
--------------------------
Checks the main property websites for 1 BHK / 1 RK rentals in Kalyan East
and sends new matches to Telegram. Runs on GitHub Actions every 6 hours.

Sites that block automated visits are skipped and reported in the summary
message, so you always know which sites were really checked.
(Housing.com is not included: it blocks automated visits.)
"""
import html
import json
import os
import re
import time
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID")
STATE_FILE = "seen_listings.json"

# ------------------------------------------------------------------ settings
# Most listing cards don't say anything about parking. With False, every
# 1 BHK / 1 RK in Kalyan East is sent and marked "car parking mentioned" or
# "parking not mentioned". Change to True to only get listings that mention it.
REQUIRE_CAR_PARKING = False

# Send a short "what was checked" summary after every run.
SEND_SUMMARY_EVERY_RUN = True

LISTINGS_PER_MESSAGE = 8
MAX_MESSAGES_PER_RUN = 6  # anything beyond this is sent on the next run

SIZE_WORDS = ["1 bhk", "1bhk", "1-bhk", "1 rk", "1rk", "1-rk", "bhk1", "rk1"]
AREA_WORDS = [
    "kalyan east", "kalyan (east)", "kalyan (e)", "kalyan-east", "kalyan_east",
    "durgadi", "lokgram", "vijay nagar", "suchak naka", "netivali",
    "kolsewadi", "tisgaon", "chinchpada", "katemanivali", "kailash nagar",
    "chakki naka",
]
PARKING_WORDS = [
    "car parking", "four wheeler", "4 wheeler", "4-wheeler", "four_wheeler",
    "covered parking", "open parking", "car park",
]

SITES = {
    "NoBroker": {
        "urls": [
            "https://www.nobroker.in/1bhk-flats-for-rent-in-kalyan_east_mumbai",
            "https://www.nobroker.in/flats-for-rent-in-kalyan_east_mumbai",
        ],
        "link_pattern": r"/property/",
    },
    "99acres": {
        "urls": [
            "https://www.99acres.com/1-bhk-flats-for-rent-in-kalyan-east-mumbai-beyond-thane-ffid",
            "https://www.99acres.com/flats-for-rent-in-kalyan-east-mumbai-beyond-thane-ffid",
        ],
        "link_pattern": r"(spid-|-r\d{6,}|-npxid-)",
    },
    "MagicBricks": {
        "urls": [
            "https://www.magicbricks.com/1-bhk-flats-for-rent-in-kalyan-east-thane-pppfr",
            "https://www.magicbricks.com/flats-for-rent-in-kalyan-east-thane-pppfr",
        ],
        "link_pattern": r"(propertyDetails|pdpid)",
    },
    "Square Yards": {
        "urls": [
            "https://www.squareyards.com/rent/property-for-rent-in-kalyan-east-thane",
        ],
        "link_pattern": r"/rent/.*\d{5,}",
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


# ------------------------------------------------------------------ helpers
def normalize_url(url):
    return url.split("#")[0].split("?")[0].rstrip("/")


def classify(text):
    t = text.lower()
    size_ok = any(w in t for w in SIZE_WORDS) or bool(
        re.search(r'"(?:bedroom_num|bedrooms|bedroom|noofbedrooms|bhk)"\s*:\s*"?1\b', t)
    )
    area_ok = any(w in t for w in AREA_WORDS)
    parking = any(w in t for w in PARKING_WORDS) or bool(
        re.search(r'"parking"\s*:\s*"(both|four_wheeler)"', t)
    )
    return size_ok, area_ok, parking


def first_value(d, keys):
    for k in keys:
        v = d.get(k)
        if isinstance(v, (str, int, float)) and str(v).strip():
            return str(v).strip()
    return ""


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
                        "text": json.dumps(node, ensure_ascii=False)[:3000] + " " + full,
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
        text = card.get_text(" ", strip=True)[:1500]
        price = ""
        m = re.search(r"₹\s?[\d,\.]+\s*(?:k|lac|lakh|/month)?", text, re.I)
        if m:
            price = m.group(0)
        found[key] = {
            "title": (a.get_text(" ", strip=True) or a.get("title") or "")[:120],
            "price": price,
            "url": key,
            "text": text + " " + key,
        }
    return list(found.values())


# ------------------------------------------------------------------ scraping
def check_site(session, site, cfg):
    """Returns (matches, status_text)."""
    last_problem = "no page loaded"
    for url in cfg["urls"]:
        try:
            r = session.get(url, headers=HEADERS, timeout=25, allow_redirects=True)
        except Exception as e:
            print(f"[{site}] {url} -> request failed: {e}")
            last_problem = "could not connect"
            continue

        soup = BeautifulSoup(r.text, "html.parser")
        title = soup.title.get_text(strip=True)[:80] if soup.title else ""
        print(f"[{site}] {url}")
        print(f"    HTTP {r.status_code}, {len(r.text)} bytes, final URL: {r.url}")
        print(f"    page title: {title!r}")

        if r.status_code in (401, 403, 429):
            last_problem = f"blocked automated access (HTTP {r.status_code})"
            continue
        if r.status_code != 200:
            last_problem = f"HTTP {r.status_code}"
            continue

        blobs, names = extract_json_blobs(soup, r.text)
        from_json = listings_from_json(blobs, r.url, cfg["link_pattern"])
        from_links = listings_from_links(soup, r.url, cfg["link_pattern"])
        print(f"    embedded data: {names[:8]}")
        print(f"    listings found: {len(from_json)} from page data, {len(from_links)} from links")

        merged = {item["url"]: item for item in from_links}
        for item in from_json:  # page data is richer, prefer it
            if item["url"] in merged:
                item["text"] += " " + merged[item["url"]]["text"]
                item["title"] = item["title"] or merged[item["url"]]["title"]
                item["price"] = item["price"] or merged[item["url"]]["price"]
            merged[item["url"]] = item

        matches = []
        for item in merged.values():
            size_ok, area_ok, parking = classify(item["text"])
            if size_ok and area_ok and (parking or not REQUIRE_CAR_PARKING):
                item["parking"] = parking
                item["site"] = site
                matches.append(item)
        for item in matches[:3]:
            print(f"    e.g. {item['title'][:60]!r} {item['price']} {item['url']}")
        print(f"    matching your criteria: {len(matches)}")

        if merged:
            return matches, f"{len(merged)} listings read, {len(matches)} match"
        if "captcha" in r.text.lower() or "access denied" in r.text[:3000].lower():
            last_problem = "blocked automated access (captcha page)"
        else:
            last_problem = "page loaded but no listings could be read"
    return [], last_problem


def format_listing(item):
    title = html.escape(item["title"] or "1 BHK / 1 RK")
    price = html.escape(item["price"]) if item["price"] else "price not shown"
    park = "🚗 car parking mentioned" if item["parking"] else "🅿️ parking not mentioned"
    return (
        f"🏠 <b>{title}</b>\n"
        f"💰 {price} · {park}\n"
        f"🔗 <a href=\"{html.escape(item['url'])}\">Open on {html.escape(item['site'])}</a>"
    )


def main():
    print("Checking Kalyan East rentals on all sites...\n")
    seen = load_seen()
    session = requests.Session()

    new_items, summary = [], []
    for site, cfg in SITES.items():
        matches, status = check_site(session, site, cfg)
        fresh = [m for m in matches if f"{site}|{m['url']}" not in seen and m["url"] not in seen]
        new_items.extend(fresh)
        icon = "✅" if "listings read" in status else "⚠️"
        summary.append(f"{icon} {site}: {html.escape(status)}" + (f", {len(fresh)} new" if fresh else ""))
        print()
        time.sleep(2)  # be polite between sites

    print(f"New listings this run: {len(new_items)}")
    sent = 0
    chunks = [new_items[i:i + LISTINGS_PER_MESSAGE] for i in range(0, len(new_items), LISTINGS_PER_MESSAGE)]
    for n, chunk in enumerate(chunks[:MAX_MESSAGES_PER_RUN], start=1):
        header = f"🚨 <b>New Kalyan East rentals</b> ({n}/{min(len(chunks), MAX_MESSAGES_PER_RUN)})\n\n"
        if send_telegram(header + "\n\n".join(format_listing(i) for i in chunk)):
            for item in chunk:
                seen.add(f"{item['site']}|{item['url']}")
            sent += len(chunk)
        time.sleep(1)

    if SEND_SUMMARY_EVERY_RUN:
        left = len(new_items) - sent
        text = "ℹ️ <b>Kalyan rental check done</b>\n\n" + "\n".join(summary)
        text += f"\n\nNew listings sent: {sent}"
        if left > 0:
            text += f" ({left} more will come next run)"
        send_telegram(text)

    save_seen(seen)
    print(f"Done. Sent {sent} new listings.")


if __name__ == "__main__":
    main()
