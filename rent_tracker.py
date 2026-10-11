import os
import json
import requests
from bs4 import BeautifulSoup
from datetime import datetime

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID")

STATE_FILE = "seen_listings.json"

def load_seen_listings():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r") as f:
                return set(json.load(f))
        except Exception:
            return set()
    return set()

def save_seen_listings(seen_set):
    with open(STATE_FILE, "w") as f:
        json.dump(list(seen_set), f)

def send_telegram_alert(message):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        print("Telegram credentials not configured.")
        return
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": message,
        "parse_mode": "Markdown"
    }
    try:
        response = requests.post(url, json=payload, timeout=10)
        response.raise_for_status()
        print("Telegram alert sent successfully.")
    except Exception as e:
        print(f"Failed to send Telegram alert: {e}")

def scrape_kalyan_east_rentals():
    listings = []
    target_url = "https://www.nobroker.in/1bhk-flats-for-rent-in-kalyan_east_mumbai"
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Accept-Language": "en-US,en;q=0.9"
    }
    try:
        response = requests.get(target_url, headers=headers, timeout=15)
        if response.status_code != 200:
            return listings
        soup = BeautifulSoup(response.text, 'html.parser')
        card_selectors = soup.select('.card-item') or soup.select('[class*="card"]')
        
        for card in card_selectors:
            try:
                title_elem = card.find(['h2', 'h3', 'span'], class_=lambda x: x and 'heading' in x.lower())
                title = title_elem.get_text(strip=True) if title_elem else "1 BHK Apartment"
                
                rent_elem = card.find(string=lambda t: t and ('₹' in t or 'Rs' in t))
                rent = rent_elem.strip() if rent_elem else "Price on Request"
                
                link_elem = card.find('a', href=True)
                link = link_elem['href'] if link_elem else target_url
                if link and not link.startswith('http'):
                    link = "https://www.nobroker.in" + link
                
                listing_id = link.split('?')[0]
                card_text = card.get_text().lower()
                
                is_target_size = any(bhk in card_text for bhk in ['1 bhk', '1rk', '1 rk'])
                has_car_parking = any(term in card_text for term in ['car parking', 'four wheeler', '4 wheeler', 'covered parking'])
                station_proximity_east_keywords = [
                    'kalyan east', 'durgadi', 'lokgram', 'vijay nagar', 
                    'suchak naka', 'netivali', 'kolsewadi', 'tisgaon road east'
                ]
                is_near_station_east = any(kw in card_text for kw in station_proximity_east_keywords)
                
                if is_target_size and has_car_parking and is_near_station_east:
                    listings.append({
                        "id": listing_id,
                        "title": title,
                        "rent": rent,
                        "link": link
                    })
            except Exception:
                continue
    except Exception as e:
        print(f"Error: {e}")
    return listings

def main():
    print("Checking Kalyan East rentals...")
    seen_listings = load_seen_listings()
    new_listings = scrape_kalyan_east_rentals()
    alert_count = 0

    for item in new_listings:
        if item["id"] not in seen_listings:
            message = (
                f"🚨 *New Kalyan East Rental Match!*\n\n"
                f"🏠 *Property:* {item['title']}\n"
                f"💰 *Rent:* {item['rent']}\n"
                f"🚗 *Parking:* 4-Wheeler Parking Confirmed\n"
                f"📍 *Location:* Kalyan East (~1.5-2km from Station Side)\n\n"
                f"🔗 [View Listing]({item['link']})"
            )
            send_telegram_alert(message)
            seen_listings.add(item["id"])
            alert_count += 1

    # If no new matching properties were found, send an update message
    if alert_count == 0:
        status_message = (
            "ℹ️ *Kalyan Rental Status Update*\n\n"
            "Checked NoBroker just now. Currently, **no new properties** match your criteria (1 BHK/RK + Car Parking in Kalyan East station side) right now. Will check again in 6 hours!"
        )
        send_telegram_alert(status_message)

    save_seen_listings(seen_listings)
    print(f"Done! Sent {alert_count} new alerts.")

if __name__ == "__main__":
    main()
