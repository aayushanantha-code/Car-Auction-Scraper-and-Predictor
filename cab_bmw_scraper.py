"""
cab_bmw_scraper.py - resumable Cars & Bids scraper for BMW sedans and coupes.

Builds on cab_test_scraper.py. Same rules: one browser, sequential page loads,
robots.txt respected, a polite delay between pages, and it STOPS (never
bypasses) on a bot check, HTTP 429, or a 403 from the site's pages/API.

Where the speed comes from (none of it adds load on the site):
 - Filters on the closed-auctions list (title + subtitle) before opening any
   auction, so SUVs, convertibles, wagons and non-BMWs are never loaded.
 - Confirms "Body Style" on the auction page and skips the bid history if it
   isn't a Sedan or Coupe.
 - Blocks images, video, fonts, and third-party analytics/ad scripts. Every
   photo URL is still in the JSON.
 - Waits for the specific API responses instead of "networkidle" + fixed sleeps.
 - Resumable: everything goes into SQLite, and finished or skipped auction IDs
   are never reopened on a later run.

Two tabs are used one at a time: one stays on the list (so "next page" works),
the other opens auctions. They never load at the same time.

Setup
 pip install playwright
 playwright install chromium

Run
 python cab_bmw_scraper.py                  # visible browser, up to 250 listings
 python cab_bmw_scraper.py --limit 10       # small test run first
 python cab_bmw_scraper.py --headless
 python cab_bmw_scraper.py --export         # write auctions.csv from the DB, no scraping
"""

import argparse
import asyncio
import csv
import json
import random
import re
import sqlite3
import time
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlparse, urlunparse
from urllib.robotparser import RobotFileParser

from playwright.async_api import async_playwright

# ---------------------------------------------------------------- settings
BASE = "https://carsandbids.com"
START_URL = f"{BASE}/past-auctions/"  # ?q= search isn't honored; the title filter does the work
MAX_LISTINGS = 250            # qualifying auctions saved per run
MAX_LIST_PAGES = 150          # safety stop on list paging (~10% of auctions qualify)
DELAY_RANGE = (3.0, 5.0)      # seconds between page loads
LOAD_FULL_HISTORY = True      # click "Bid History" + "Load more" for every bid
MAX_LOAD_MORE = 25            # cap on "Load more" clicks per view, per auction
M_CARS_ONLY = False           # True = only M cars (M2-M8, 1M, M Coupe)
DB_PATH = Path("cab_bmw.sqlite")
CSV_PATH = Path("auctions.csv")
BIDS_CSV_PATH = Path("bids.csv")
COMMENTS_CSV_PATH = Path("comments.csv")

BLOCK_TYPES = {"image", "media", "font"}
BLOCK_HOSTS = ("google-analytics", "googletagmanager", "doubleclick", "facebook",
               "hotjar", "clarity.ms", "amazon-adsystem", "adservice", "segment.",
               "tiktok", "pinterest", "bing.com")

CHALLENGE_MARKERS = ("just a moment", "attention required", "verify you are human",
                     "checking your browser")

# ---------------------------------------------------------------- title filters
BMW_RE = re.compile(r"\bBMW\b", re.I)
SUV_RE = re.compile(r"\b(X[1-7](\s?M)?|XM|iX\d?)\b", re.I)
OPEN_RE = re.compile(r"\b(Z[1348]|Convertible|Cabrio(let)?|Roadster|Spyder|Targa)\b", re.I)
HATCH_WAGON_RE = re.compile(r"\b(Touring|Wagon|Gran Turismo|[356] Series GT|3GT|i3s?)\b", re.I)
M_RE = re.compile(r"\b(1M|M[2-8]|M Coupe)\b", re.I)
BODY_OK = re.compile(r"sedan|coupe", re.I)
BODY_STYLE_TEXT = re.compile(r"Body Style\s*[:\n]?\s*([A-Za-z][A-Za-z /-]{1,30})")
AUCTION_HREF = re.compile(r"^/auctions/([A-Za-z0-9]+)")


class Blocked(Exception):
    pass


def title_ok(title, sub_title=""):
    t = f"{title or ''} {sub_title or ''}"
    if not BMW_RE.search(title or ""):
        return False, "not BMW"
    if SUV_RE.search(title or ""):
        return False, "SUV"
    if OPEN_RE.search(t) and not re.search(r"coupe", title or "", re.I):
        return False, "convertible/roadster"
    if HATCH_WAGON_RE.search(t):
        return False, "wagon/hatchback"
    if M_CARS_ONLY and not M_RE.search(title or ""):
        return False, "not an M car"
    return True, ""


def looks_like_challenge(title, body_text):
    blob = f"{title} {body_text[:2000]}".lower()
    return any(m in blob for m in CHALLENGE_MARKERS)


def dig(d, *keys):
    for k in keys:
        if not isinstance(d, dict) or k not in d:
            return None
        d = d[k]
    return d


def first(*vals):
    for v in vals:
        if v is not None:
            return v
    return None


def money(v):
    if isinstance(v, dict):
        v = v.get("amount")
    return v if isinstance(v, (int, float)) else None


def find_items(data):
    """Return the list of auction dicts inside a list response, wherever it sits."""
    if isinstance(data, list):
        if data and isinstance(data[0], dict) and "id" in data[0] and "title" in data[0]:
            return data
        return []
    if isinstance(data, dict):
        for v in data.values():
            found = find_items(v)
            if found:
                return found
    return []


def with_param(url, key, value):
    parts = urlparse(url)
    q = parse_qs(parts.query)
    q[key] = [str(value)]
    return urlunparse(parts._replace(query=urlencode(q, doseq=True)))


async def wait_for(cond, timeout):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        if cond():
            return True
        await asyncio.sleep(0.2)
    return cond()


async def polite_sleep():
    await asyncio.sleep(random.uniform(*DELAY_RANGE))


def now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


# ---------------------------------------------------------------- database
def open_db():
    db = sqlite3.connect(DB_PATH)
    db.executescript("""
    CREATE TABLE IF NOT EXISTS auctions(
        id TEXT PRIMARY KEY, url TEXT, title TEXT, status TEXT,
        body_style TEXT, body_style_code TEXT,
        sale_amount REAL, high_bid REAL, auction_end TEXT,
        list_json TEXT, detail_json TEXT, comments_json TEXT, scraped_at TEXT);
    CREATE TABLE IF NOT EXISTS skipped(
        id TEXT PRIMARY KEY, title TEXT, reason TEXT, at TEXT);
    """)
    return db


# Coded fields, confirmed against listing text in the test runs.
TRANSMISSION = {1: "Automatic", 2: "Manual"}
DRIVE_TRAIN = {2: "RWD", 3: "AWD"}
BODY_STYLE = {1: "Coupe", 4: "Sedan"}
SELLER_TYPE = {1: "Private Party", 2: "Dealer"}
SECTIONS = ["highlights", "equipment", "known_flaws", "modifications",
            "recent_service_history", "ownership_history", "seller_notes", "other_items"]


def entries_by_type(comments_json):
    """comments_and_bids types: 1 = comment, 2 = bid (has "amount"), 5 = result notice."""
    ents = {}
    for resp in json.loads(comments_json or "[]"):
        for e in find_comment_list(resp):
            ents[e.get("id")] = e
    out = {1: [], 2: [], 5: []}
    for e in sorted(ents.values(), key=lambda e: e.get("timestamp") or ""):
        out.setdefault(e.get("type"), []).append(e)
    return out


def export_csv(db):
    rows = db.execute("SELECT id, url, title, status, body_style, sale_amount, high_bid,"
                      " auction_end, detail_json, comments_json FROM auctions").fetchall()
    cols = (["id", "url", "title", "sub_title", "year", "make", "model", "vin", "mileage",
             "engine", "transmission", "transmission_details", "drive_train", "body_style",
             "exterior_color", "interior_color", "title_status", "seller_type", "location",
             "status", "sale_amount", "high_bid", "no_reserve", "auction_start", "auction_end",
             "bids", "comments", "watchers", "views", "n_photos_exterior", "n_photos_interior",
             "n_photos_mechanical", "has_inspection_report", "bids_captured",
             "comments_captured"] + SECTIONS)
    n_bids = n_comments = 0
    with CSV_PATH.open("w", newline="") as fa, BIDS_CSV_PATH.open("w", newline="") as fb, \
            COMMENTS_CSV_PATH.open("w", newline="") as fc:
        wa, wb, wc = csv.writer(fa), csv.writer(fb), csv.writer(fc)
        wa.writerow(cols)
        wb.writerow(["auction_id", "bid_id", "timestamp", "amount", "user_id", "username"])
        wc.writerow(["auction_id", "comment_id", "timestamp", "user_id", "username",
                     "is_seller", "upvotes", "reply_to", "text"])
        for aid, url, title, status, body, sale, bid, end, dj, cj in rows:
            d = json.loads(dj or "{}")
            L = d.get("listing") or {}
            photos = L.get("photos") or {}
            by_type = entries_by_type(cj)
            wa.writerow([
                aid, url, title, L.get("sub_title"), L.get("year"), L.get("make"), L.get("model"),
                L.get("vin"), L.get("mileage"), L.get("engine"),
                TRANSMISSION.get(L.get("transmission"), L.get("transmission")),
                L.get("transmission_details"),
                DRIVE_TRAIN.get(L.get("drive_train"), L.get("drive_train")),
                body or BODY_STYLE.get(L.get("body_style"), L.get("body_style")),
                L.get("exterior_color"), L.get("interior_color"), L.get("title_status"),
                SELLER_TYPE.get(L.get("seller_type"), L.get("seller_type")), L.get("location"),
                status, sale, bid, d.get("no_reserve"), dig(d, "stats", "auction_start"), end,
                dig(d, "stats", "bids"), dig(d, "stats", "comments"), dig(d, "stats", "watchers"),
                d.get("views"), len(photos.get("exterior") or []),
                len(photos.get("interior") or []), len(photos.get("mechanical") or []),
                bool(L.get("inspection_report_url")), len(by_type[2]), len(by_type[1])]
                + [(L.get("sections") or {}).get(s) for s in SECTIONS])
            for e in by_type[2]:
                if e.get("amount") is not None:
                    wb.writerow([aid, e["id"], e.get("timestamp"), e["amount"],
                                 dig(e, "user", "id"), dig(e, "user", "username")])
                    n_bids += 1
            for e in by_type[1]:
                wc.writerow([aid, e["id"], e.get("timestamp"), dig(e, "user", "id"),
                             dig(e, "user", "username"), dig(e, "user", "is_seller"),
                             e.get("upvotes"), e.get("reply_to"), e.get("text")])
                n_comments += 1
    print(f"Wrote {len(rows)} auctions -> {CSV_PATH}, {n_bids} bids -> {BIDS_CSV_PATH}, "
          f"{n_comments} comments -> {COMMENTS_CSV_PATH}")


def find_comment_list(data):
    if isinstance(data, dict):
        v = data.get("comments_and_bids")
        if isinstance(v, list):
            return v
    return []


# ---------------------------------------------------------------- scraper
async def main(limit, headless):
    db = open_db()
    done = {r[0] for r in db.execute("SELECT id FROM auctions UNION SELECT id FROM skipped")}
    print(f"{len(done)} auctions already in the database will be skipped.")

    state = {"list": [], "detail": {}, "comments": [], "blocked": None}

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=headless)
        context = await browser.new_context()

        async def route_filter(route):
            req = route.request
            host = urlparse(req.url).hostname or ""
            if req.resource_type in BLOCK_TYPES or any(h in host for h in BLOCK_HOSTS):
                await route.abort()
            else:
                await route.continue_()

        await context.route("**/*", route_filter)
        list_page = await context.new_page()
        auction_page = await context.new_page()

        async def on_response(resp):
            url = resp.url
            if "carsandbids.com" not in url:
                return
            path = urlparse(url).path
            if resp.status == 429:
                state["blocked"] = "HTTP 429 (rate limited)"
            elif resp.status == 403 and (resp.request.resource_type == "document"
                                         or re.search(r"/v[12]/", path)):
                state["blocked"] = f"HTTP 403 on {path}"
            if "application/json" not in resp.headers.get("content-type", ""):
                return
            try:
                data = await resp.json()
                src = resp.frame.page
            except Exception:
                return
            if src is list_page and re.search(r"/v2/autos/auctions/?$", path):
                state["list"].append(data)
            elif src is auction_page:
                m = re.search(r"/v2/autos/auctions/([A-Za-z0-9]+)/?$", path)
                if m:
                    state["detail"][m.group(1)] = data
                elif re.search(r"/v1/autos/auctions/[A-Za-z0-9]+/comments", path):
                    state["comments"].append(data)

        context.on("response", on_response)

        def check_blocked():
            if state["blocked"]:
                raise Blocked(state["blocked"])

        async def check_page(page):
            check_blocked()
            if looks_like_challenge(await page.title(), await page.inner_text("body")):
                raise Blocked("bot check page")

        # robots.txt
        robots = RobotFileParser()
        r = await context.request.get(f"{BASE}/robots.txt")
        if r.status != 200:
            print(f"robots.txt returned HTTP {r.status}. Stopping.")
            await browser.close()
            return
        robots.parse((await r.text()).splitlines())

        def captured():
            """(bids, comments) captured so far for the current auction, deduped by id."""
            ents = {}
            for resp in state["comments"]:
                for e in find_comment_list(resp):
                    ents[e.get("id")] = e
            types = [e.get("type") for e in ents.values()]
            return types.count(2), types.count(1)

        async def click_tab(name):
            tab = auction_page.locator(f'button:has-text("{name}"), a:has-text("{name}"),'
                                       f' [role="tab"]:has-text("{name}")').first
            if await tab.count():
                n = len(state["comments"])
                try:
                    await tab.click(timeout=3000)
                    await wait_for(lambda: len(state["comments"]) > n, 6)
                except Exception:
                    pass

        async def load_history(want_bids, want_comments):
            # The default view mixes comments and bids, so loading it fully gets both.
            await click_load_more()
            bids, comments = captured()
            # Fall back to the dedicated tabs for anything still missing.
            if bids < want_bids:
                await click_tab("Bid History")
                await click_load_more()
            if captured()[1] < want_comments:
                await click_tab("Comments")
                await click_load_more()

        async def click_load_more():
            for _ in range(MAX_LOAD_MORE):
                btn = auction_page.locator('button:has-text("Load more"),'
                                           ' a:has-text("Load more")').first
                if not await btn.count() or not await btn.is_visible():
                    break
                n = len(state["comments"])
                try:
                    await btn.click(timeout=3000)
                except Exception:
                    break
                if not await wait_for(lambda: len(state["comments"]) > n, 8):
                    break
                check_blocked()
                await asyncio.sleep(0.7)

        async def scrape_auction(aid, url, item):
            state["detail"].clear()
            state["comments"].clear()
            await auction_page.goto(url, wait_until="domcontentloaded", timeout=45_000)
            got = await wait_for(lambda: bool(state["detail"]), 20)
            await check_page(auction_page)
            if not got:
                return "skip", "detail JSON never arrived"
            detail = state["detail"].get(aid) or next(iter(state["detail"].values()))

            try:
                await auction_page.get_by_text("Body Style").first.wait_for(timeout=5000)
            except Exception:
                pass
            m = BODY_STYLE_TEXT.search(await auction_page.inner_text("body"))
            body_label = m.group(1).split("\n")[0].strip() if m else None
            if body_label and not BODY_OK.search(body_label):
                return "skip", f"body style {body_label}"

            want_bids = dig(detail, "stats", "bids") or 0
            want_comments = dig(detail, "stats", "comments") or 0
            if LOAD_FULL_HISTORY:
                await load_history(want_bids, want_comments)
            bids, comments = captured()
            completeness = f"bids {bids}/{want_bids}, comments {comments}/{want_comments}"

            db.execute("INSERT OR REPLACE INTO auctions VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)", (
                aid, url, item.get("title"),
                first(detail.get("status"), item.get("status")),
                body_label, str(dig(detail, "listing", "body_style")),
                first(money(dig(detail, "stats", "sale_amount")), money(detail.get("sale_amount")),
                      money(item.get("sale_amount"))),
                first(money(dig(detail, "stats", "current_bid")), money(item.get("current_bid"))),
                first(dig(detail, "stats", "auction_end"), item.get("auction_end")),
                json.dumps(item), json.dumps(detail), json.dumps(state["comments"]), now()))
            db.commit()
            return "saved", f"{body_label or 'body style not shown'}; {completeness}"

        # list paging
        saved = 0
        try:
            if not robots.can_fetch("*", START_URL):
                print("robots.txt disallows the start URL. Stopping.")
                return
            print(f"Loading {START_URL}")
            await list_page.goto(START_URL, wait_until="domcontentloaded", timeout=60_000)
            if not await wait_for(lambda: bool(state["list"]), 20):
                await check_page(list_page)
                print("No auction list response arrived. Check START_URL.")
                return
            total = state["list"][-1].get("total") if isinstance(state["list"][-1], dict) else None
            print(f"Search reports {total} matching auctions (filter still applied below).")

            for page_no in range(1, MAX_LIST_PAGES + 1):
                await check_page(list_page)
                items = find_items(state["list"][-1])
                hrefs = await list_page.eval_on_selector_all(
                    "a[href]", "els => els.map(e => e.getAttribute('href'))")
                paths = {}
                for h in hrefs:
                    mm = AUCTION_HREF.match(h or "")
                    if mm:
                        paths.setdefault(mm.group(1), h.split("?")[0])

                fresh = [it for it in items if str(it.get("id")) not in done]
                print(f"List page {page_no}: {len(items)} auctions, {len(fresh)} not seen before.")

                for it in fresh:
                    if saved >= limit:
                        break
                    aid = str(it["id"])
                    done.add(aid)
                    ok, reason = title_ok(it.get("title"), it.get("sub_title"))
                    if not ok:
                        db.execute("INSERT OR REPLACE INTO skipped VALUES (?,?,?,?)",
                                   (aid, it.get("title"), reason, now()))
                        continue
                    url = BASE + paths.get(aid, f"/auctions/{aid}")
                    if not robots.can_fetch("*", url):
                        continue
                    await polite_sleep()
                    result, note = await scrape_auction(aid, url, it)
                    if result == "saved":
                        saved += 1
                        print(f"  [{saved}/{limit}] {it.get('title')} ({note})")
                    else:
                        db.execute("INSERT OR REPLACE INTO skipped VALUES (?,?,?,?)",
                                   (aid, it.get("title"), note, now()))
                        print(f"  skip: {it.get('title')} ({note})")
                db.commit()
                if saved >= limit:
                    break

                # next list page: click a pager control, else try ?page=N
                await polite_sleep()
                before = len(state["list"])
                clicked = False
                for sel in ('a[rel="next"]', 'li.arrow.next a', '[aria-label*="next" i]',
                            'a:has-text("Next")', 'button:has-text("Load more")'):
                    loc = list_page.locator(sel).first
                    if await loc.count() and await loc.is_visible():
                        try:
                            await loc.click(timeout=3000)
                            clicked = True
                            break
                        except Exception:
                            pass
                if not clicked:
                    await list_page.goto(with_param(START_URL, "page", page_no + 1),
                                         wait_until="domcontentloaded", timeout=60_000)
                if not await wait_for(lambda: len(state["list"]) > before, 20):
                    print("No further list pages. Done.")
                    break
                new_ids = {str(i.get("id")) for i in find_items(state["list"][-1])}
                old_ids = {str(i.get("id")) for i in items}
                if not new_ids or new_ids <= old_ids:
                    print("Paging returned the same auctions. Done.")
                    break
        except Blocked as e:
            print(f"\nStopped: {e}. Not bypassing it. Progress is saved; wait before rerunning.")
        except KeyboardInterrupt:
            print("\nInterrupted. Progress is saved.")
        finally:
            db.commit()
            await browser.close()

    n = db.execute("SELECT COUNT(*) FROM auctions").fetchone()[0]
    print(f"\nSaved {saved} this run. {n} total in {DB_PATH}. Run with --export for a CSV.")


async def debug_comments(url, headless):
    """Open one auction and report how its comments load. Reads only; saves nothing."""
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=headless)
        page = await browser.new_page()

        async def on_response(resp):
            if "/comments" not in resp.url or "carsandbids.com" not in resp.url:
                return
            try:
                data = await resp.json()
            except Exception:
                return
            ents = data.get("comments_and_bids") or [] if isinstance(data, dict) else []
            types = {t: [e.get("type") for e in ents].count(t) for t in (1, 2, 5)}
            q = parse_qs(urlparse(resp.url).query)
            q = {k: v for k, v in q.items() if k not in ("timestamp", "signature")}
            extra = [k for k in data if k != "comments_and_bids"] if isinstance(data, dict) else []
            print(f"  COMMENTS REQUEST params={q} -> {len(ents)} entries {types} keys={extra}")

        page.on("response", on_response)

        async def controls(label):
            texts = await page.eval_on_selector_all(
                "button, a, [role=tab], [role=button]",
                "els => els.filter(e => e.offsetParent !== null)"
                ".map(e => (e.innerText || '').trim().replace(/\\s+/g, ' '))"
                ".filter(t => t && t.length < 40)")
            hits = sorted({t for t in texts if re.search(
                r"comment|bid|more|load|show|view|repl|all|newest|oldest|top", t, re.I)})
            print(f"\n[{label}] visible controls mentioning comments/bids/more:")
            for t in hits:
                print(f"   - {t!r}")

        print(f"Opening {url}")
        await page.goto(url, wait_until="domcontentloaded", timeout=60_000)
        await asyncio.sleep(6)
        if looks_like_challenge(await page.title(), await page.inner_text("body")):
            print("Bot check page. Stopping.")
            return
        await controls("after load")
        print("\nScrolling to the bottom a few times...")
        for _ in range(6):
            await page.mouse.wheel(0, 4000)
            await asyncio.sleep(2)
        await controls("after scrolling")
        await asyncio.sleep(2)
        await browser.close()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--headless", action="store_true")
    ap.add_argument("--limit", type=int, default=MAX_LISTINGS)
    ap.add_argument("--export", action="store_true", help="write auctions.csv and exit")
    ap.add_argument("--debug-comments", metavar="AUCTION_URL",
                    help="report how comments load on one auction, then exit")
    args = ap.parse_args()
    if args.debug_comments:
        asyncio.run(debug_comments(args.debug_comments, args.headless))
    elif args.export:
        export_csv(open_db())
    else:
        asyncio.run(main(args.limit, args.headless))
