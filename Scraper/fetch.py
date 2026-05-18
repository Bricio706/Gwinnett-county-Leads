#!/usr/bin/env python3
"""
Gwinnett County, GA – Automated Motivated Seller Lead Scraper
=================================================================
Clerk Portal  : https://search.gsccca.org/RealEstate/
Parcel Source : Gwinnett County Assessor / ArcGIS / Open Data
Lookback      : Last 7 days  (DAYS_BACK env var overrides)
Output        : dashboard/records.json | data/records.json | data/ghl_export.csv
Schedule      : Daily 07:00 UTC via GitHub Actions
=================================================================
"""
from __future__ import annotations

import asyncio
import csv
import io
import json
import logging
import os
import re
import sys
import tempfile
import time
import traceback
import zipfile
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import urljoin, urlencode

import requests
from bs4 import BeautifulSoup
from dbfread import DBF
from playwright.async_api import (
    async_playwright,
    Browser,
    BrowserContext,
    Page,
    TimeoutError as PWTimeout,
    Error as PWError,
)

# ══════════════════════════════════════════════════════════════════════════════
#  LOGGING
# ══════════════════════════════════════════════════════════════════════════════
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-8s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("gwinnett_scraper")

# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION
# ══════════════════════════════════════════════════════════════════════════════
GSCCCA_BASE       = "https://search.gsccca.org"
GSCCCA_SEARCH_URL = "https://search.gsccca.org/RealEstate/"

GWINNETT_NAME     = "Gwinnett"
GWINNETT_CODE     = "67"        # GSCCCA county numeric code

DAYS_BACK         = int(os.getenv("DAYS_BACK", "7"))
TODAY             = datetime.today()
START_DATE        = TODAY - timedelta(days=DAYS_BACK)
DATE_FMT          = "%m/%d/%Y"

RETRY_ATTEMPTS    = 3
RETRY_DELAY_SEC   = 4.0
REQUEST_DELAY_SEC = 1.5
PAGE_TIMEOUT_MS   = 40_000
NAV_TIMEOUT_MS    = 60_000

# ── Parcel data download candidates (tried in order) ──────────────────────────
# Gwinnett County may update these URLs; update PARCEL_ZIP_URL as needed.
PARCEL_ZIP_URL = (
    "https://www.gwinnettcounty.com/static/departments/FinancialServices/"
    "TaxAssessor/ParcelExports/GwinnettParcelData.zip"
)

# ArcGIS Online REST endpoint – Gwinnett County Real Property
ARCGIS_PARCEL_BASE = (
    "https://services1.arcgis.com/Ike2xeaU5c42OjL5/arcgis/rest/services/"
    "Real_Property_Information/FeatureServer/0/query"
)

# Gwinnett County Open Data / Socrata
SOCRATA_PARCEL_URL = (
    "https://opendata.gwinnettcounty.com/resource/parcel-data.csv?$limit=600000"
)

# Assessor portal direct link (used to discover download links)
ASSESSOR_PORTAL = "https://www.gwinnettassessor.manatron.com/"

# ══════════════════════════════════════════════════════════════════════════════
#  DOCUMENT TYPES
# ══════════════════════════════════════════════════════════════════════════════
DOC_TYPES: Dict[str, Tuple[str, str]] = {
    "LP":        ("foreclosure", "Lis Pendens"),
    "NOFC":      ("foreclosure", "Notice of Foreclosure"),
    "TAXDEED":   ("tax",         "Tax Deed"),
    "JUD":       ("judgment",    "Judgment"),
    "CCJ":       ("judgment",    "Certified Judgment"),
    "DRJUD":     ("judgment",    "Domestic Relations Judgment"),
    "LNCORPTX":  ("lien",        "Corporate Tax Lien"),
    "LNIRS":     ("lien",        "IRS Lien"),
    "LNFED":     ("lien",        "Federal Lien"),
    "LN":        ("lien",        "Lien"),
    "LNMECH":    ("lien",        "Mechanic Lien"),
    "LNHOA":     ("lien",        "HOA Lien"),
    "MEDLN":     ("lien",        "Medicaid Lien"),
    "PRO":       ("probate",     "Probate"),
    "NOC":       ("notice",      "Notice of Commencement"),
    "RELLP":     ("release",     "Release Lis Pendens"),
}

# ══════════════════════════════════════════════════════════════════════════════
#  OUTPUT PATHS
# ══════════════════════════════════════════════════════════════════════════════
OUTPUT_PATHS = [Path("dashboard/records.json"), Path("data/records.json")]
GHL_CSV_PATH = Path("data/ghl_export.csv")
CACHE_DIR    = Path(".cache")

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
}


# ══════════════════════════════════════════════════════════════════════════════
#  UTILITY HELPERS
# ══════════════════════════════════════════════════════════════════════════════

def clean(s: Any) -> str:
    """Normalize whitespace and convert to string."""
    if s is None:
        return ""
    return re.sub(r"\s+", " ", str(s)).strip()


def parse_amount(s: str) -> Optional[float]:
    """Parse a dollar amount string to float, or None."""
    if not s:
        return None
    digits = re.sub(r"[^\d.]", "", str(s))
    try:
        return float(digits) if digits else None
    except ValueError:
        return None


def fmt_date(raw: Any) -> str:
    """Return YYYY-MM-DD string from various date formats."""
    if isinstance(raw, datetime):
        return raw.strftime("%Y-%m-%d")
    if not raw:
        return ""
    s = clean(str(raw))
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%Y%m%d", "%d-%b-%Y"):
        try:
            return datetime.strptime(s, fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    return s


def name_variants(name: str) -> List[str]:
    """
    Produce lookup variants for an owner name:
      "FIRST LAST", "LAST FIRST", "LAST, FIRST", "LAST"
    """
    name = clean(name).upper()
    if not name:
        return []
    variants: List[str] = [name]
    parts = name.split()
    if len(parts) >= 2:
        first = parts[0]
        last  = " ".join(parts[1:])
        variants += [f"{last} {first}", f"{last}, {first}", last]
    return list(dict.fromkeys(v for v in variants if v))


def split_owner_name(owner: str) -> Tuple[str, str]:
    """Best-effort split into (first, last)."""
    owner = clean(owner)
    if not owner:
        return ("", "")
    if "," in owner:
        last, *rest = owner.split(",", 1)
        return (clean("".join(rest)), clean(last))
    parts = owner.split()
    if len(parts) == 1:
        return ("", parts[0])
    return (" ".join(parts[:-1]), parts[-1])


def make_empty_record() -> Dict:
    return {
        "doc_num":      "",
        "doc_type":     "",
        "filed":        "",
        "cat":          "",
        "cat_label":    "",
        "owner":        "",
        "grantee":      "",
        "amount":       None,
        "legal":        "",
        "prop_address": "",
        "prop_city":    "",
        "prop_state":   "GA",
        "prop_zip":     "",
        "mail_address": "",
        "mail_city":    "",
        "mail_state":   "",
        "mail_zip":     "",
        "clerk_url":    "",
        "flags":        [],
        "score":        0,
    }


def retry_sync(fn, attempts: int = RETRY_ATTEMPTS, delay: float = RETRY_DELAY_SEC):
    """Retry a synchronous callable; re-raise on final failure."""
    last_exc: Exception = RuntimeError("no attempts made")
    for attempt in range(attempts):
        try:
            return fn()
        except Exception as exc:
            last_exc = exc
            if attempt < attempts - 1:
                log.warning("  Attempt %d/%d failed: %s – retrying in %.1fs",
                            attempt + 1, attempts, exc, delay)
                time.sleep(delay)
    raise last_exc


async def retry_async(coro_fn, attempts: int = RETRY_ATTEMPTS, delay: float = RETRY_DELAY_SEC):
    """Retry an async callable; re-raise on final failure."""
    last_exc: Exception = RuntimeError("no attempts made")
    for attempt in range(attempts):
        try:
            return await coro_fn()
        except Exception as exc:
            last_exc = exc
            if attempt < attempts - 1:
                log.warning("  Async attempt %d/%d failed: %s – retrying in %.1fs",
                            attempt + 1, attempts, exc, delay)
                await asyncio.sleep(delay)
    raise last_exc


# ══════════════════════════════════════════════════════════════════════════════
#  PARCEL DATA – DOWNLOAD & LOOKUP
# ══════════════════════════════════════════════════════════════════════════════

def _add_parcel_to_lookup(lookup: Dict[str, Dict], parcel: Dict) -> None:
    """Insert all owner name variants into the lookup dict."""
    owner = parcel.get("owner", "")
    if not owner:
        return
    for variant in name_variants(owner):
        if variant not in lookup:
            lookup[variant] = parcel


def _normalize_parcel(
    owner: str,
    site_addr: str,
    site_city: str,
    site_zip: str,
    mail_addr: str,
    mail_city: str,
    mail_state: str,
    mail_zip: str,
) -> Dict:
    return {
        "owner":        clean(owner),
        "prop_address": clean(site_addr),
        "prop_city":    clean(site_city) or "Lawrenceville",
        "prop_state":   "GA",
        "prop_zip":     clean(site_zip)[:5],
        "mail_address": clean(mail_addr) or clean(site_addr),
        "mail_city":    clean(mail_city) or clean(site_city),
        "mail_state":   clean(mail_state) or "GA",
        "mail_zip":     clean(mail_zip)[:5],
    }


def _fetch_arcgis_parcels(session: requests.Session) -> Dict[str, Dict]:
    """
    Pull parcel records from Gwinnett County's ArcGIS Online REST service
    using paginated JSON requests.
    """
    lookup: Dict[str, Dict] = {}
    offset, page_size = 0, 1000
    FIELDS = (
        "OWNER,OWN1,SITE_ADDR,SITEADDR,SITE_CITY,SITE_ZIP,"
        "ADDR_1,MAILADR1,CITY,MAILCITY,STATE,ZIP,MAILZIP"
    )

    log.info("  Fetching parcel data from ArcGIS Online …")
    while True:
        params = {
            "where":             "1=1",
            "outFields":         FIELDS,
            "returnGeometry":    "false",
            "resultOffset":      offset,
            "resultRecordCount": page_size,
            "f":                 "json",
        }
        resp = session.get(ARCGIS_PARCEL_BASE, params=params, timeout=90)
        resp.raise_for_status()
        data = resp.json()

        features = data.get("features", [])
        if not features:
            break

        for feat in features:
            a = feat.get("attributes", {})
            g = lambda *ks: next((clean(a.get(k)) for k in ks if a.get(k)), "")
            parcel = _normalize_parcel(
                g("OWNER", "OWN1"),
                g("SITE_ADDR", "SITEADDR"),
                g("SITE_CITY"),
                g("SITE_ZIP"),
                g("ADDR_1", "MAILADR1"),
                g("CITY", "MAILCITY"),
                g("STATE"),
                g("ZIP", "MAILZIP"),
            )
            _add_parcel_to_lookup(lookup, parcel)

        if len(features) < page_size:
            break
        offset += page_size
        time.sleep(0.4)

    return lookup


def _fetch_parcel_zip(session: requests.Session) -> Dict[str, Dict]:
    """
    Download the Gwinnett County parcel ZIP file and parse the DBF inside it.
    Also tries the assessor portal to discover a dynamic download link.
    """
    lookup: Dict[str, Dict] = {}
    urls_to_try = [PARCEL_ZIP_URL]

    # Attempt to discover download link from assessor portal
    try:
        resp = session.get(ASSESSOR_PORTAL, timeout=30)
        soup = BeautifulSoup(resp.text, "lxml")
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if href.lower().endswith(".zip") and "parcel" in href.lower():
                urls_to_try.insert(0, urljoin(ASSESSOR_PORTAL, href))
    except Exception:
        pass

    for url in urls_to_try:
        try:
            log.info("  Downloading parcel ZIP from: %s", url)
            resp = session.get(url, timeout=180, stream=True)
            resp.raise_for_status()

            with tempfile.TemporaryDirectory() as tmp:
                zip_path = Path(tmp) / "parcels.zip"
                with open(zip_path, "wb") as fh:
                    for chunk in resp.iter_content(8192):
                        fh.write(chunk)

                with zipfile.ZipFile(zip_path) as zf:
                    dbf_names = [n for n in zf.namelist() if n.lower().endswith(".dbf")]
                    if not dbf_names:
                        log.warning("  No DBF in ZIP from %s", url)
                        continue
                    dbf_name = dbf_names[0]
                    log.info("  Extracting DBF: %s", dbf_name)
                    zf.extract(dbf_name, tmp)
                    dbf_path = Path(tmp) / dbf_name

                def g(rec, *keys):
                    for k in keys:
                        v = rec.get(k)
                        if v and str(v).strip():
                            return clean(str(v))
                    return ""

                for rec in DBF(str(dbf_path), encoding="latin-1",
                               ignore_missing_memofile=True):
                    owner = g(rec, "OWNER", "OWN1", "OWNNAME", "OWNER_NAME")
                    if not owner:
                        continue
                    parcel = _normalize_parcel(
                        owner,
                        g(rec, "SITE_ADDR", "SITEADDR", "SITADDR", "PROP_ADDR"),
                        g(rec, "SITE_CITY", "SITECITY"),
                        g(rec, "SITE_ZIP", "SITEZIP"),
                        g(rec, "ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADR"),
                        g(rec, "CITY", "MAILCITY", "MAIL_CITY"),
                        g(rec, "STATE", "MAIL_STATE"),
                        g(rec, "ZIP", "MAILZIP", "MAIL_ZIP"),
                    )
                    _add_parcel_to_lookup(lookup, parcel)

                if lookup:
                    return lookup
        except Exception as exc:
            log.warning("  Parcel ZIP failed for %s: %s", url, exc)

    return lookup


def _fetch_socrata_csv(session: requests.Session) -> Dict[str, Dict]:
    """Fetch parcel data from a Socrata/Open Data CSV endpoint."""
    lookup: Dict[str, Dict] = {}
    log.info("  Fetching parcel CSV from Open Data portal …")
    resp = session.get(SOCRATA_PARCEL_URL, timeout=120)
    resp.raise_for_status()

    reader = csv.DictReader(io.StringIO(resp.text))
    for row in reader:
        def g(*keys):
            for k in keys:
                for kk in (k, k.lower(), k.upper()):
                    v = row.get(kk)
                    if v and str(v).strip():
                        return clean(str(v))
            return ""

        owner = g("OWNER", "OWN1", "owner", "Owner")
        if not owner:
            continue
        parcel = _normalize_parcel(
            owner,
            g("SITE_ADDR", "SITEADDR", "site_addr", "prop_address"),
            g("SITE_CITY", "site_city"),
            g("SITE_ZIP", "site_zip"),
            g("ADDR_1", "MAILADR1", "addr_1", "mail_addr"),
            g("CITY", "MAILCITY", "mail_city"),
            g("STATE", "mail_state"),
            g("ZIP", "MAILZIP", "mail_zip"),
        )
        _add_parcel_to_lookup(lookup, parcel)

    return lookup


def download_parcel_data(session: requests.Session) -> Dict[str, Dict]:
    """
    Try each parcel data source in order; return owner-name → parcel lookup.
    Never raises – returns empty dict if all sources fail.
    """
    sources = [
        ("ArcGIS Online",   _fetch_arcgis_parcels),
        ("Parcel ZIP/DBF",  _fetch_parcel_zip),
        ("Socrata CSV",     _fetch_socrata_csv),
    ]
    for label, fn in sources:
        try:
            lookup = fn(session)
            if lookup:
                log.info("Parcel lookup built: %d entries via %s", len(lookup), label)
                return lookup
        except Exception as exc:
            log.warning("Parcel source '%s' failed: %s", label, exc)

    log.warning("All parcel sources failed – address enrichment will be skipped")
    return {}


def lookup_parcel(owner: str, lookup: Dict[str, Dict]) -> Optional[Dict]:
    """Return parcel dict for an owner name (tries all variants)."""
    if not owner or not lookup:
        return None
    for variant in name_variants(owner):
        if variant in lookup:
            return lookup[variant]
    # Fallback: match on last word only (surname)
    words = owner.upper().split()
    if words:
        for variant in name_variants(words[-1]):
            if variant in lookup:
                return lookup[variant]
    return None


# ══════════════════════════════════════════════════════════════════════════════
#  GSCCCA SCRAPER  (Playwright async)
# ══════════════════════════════════════════════════════════════════════════════

async def _safe_select(page: Page, selectors: List[str],
                       value: str = None, label: str = None,
                       timeout: int = 5000) -> bool:
    """Try multiple CSS selectors; select by value or label. Return True on success."""
    for sel in selectors:
        try:
            await page.wait_for_selector(sel, timeout=timeout)
            if label:
                try:
                    await page.select_option(sel, label=label)
                    return True
                except Exception:
                    pass
            if value:
                try:
                    await page.select_option(sel, value=value)
                    return True
                except Exception:
                    pass
            # Scan options manually
            opts = await page.query_selector_all(f"{sel} option")
            for opt in opts:
                txt = (await opt.inner_text()).strip()
                val = await opt.get_attribute("value") or ""
                if (value and (val.upper() == value.upper() or value.upper() in txt.upper())) or \
                   (label and label.lower() in txt.lower()):
                    await page.select_option(sel, value=val)
                    return True
        except (PWTimeout, PWError):
            continue
    return False


async def _safe_fill(page: Page, selectors: List[str], text: str,
                     timeout: int = 5000) -> bool:
    """Try multiple CSS selectors to fill a text field."""
    for sel in selectors:
        try:
            await page.wait_for_selector(sel, timeout=timeout)
            await page.fill(sel, text)
            return True
        except (PWTimeout, PWError):
            continue
    return False


async def _safe_click(page: Page, selectors: List[str], timeout: int = 5000) -> bool:
    """Try multiple CSS selectors to click a button."""
    for sel in selectors:
        try:
            await page.wait_for_selector(sel, timeout=timeout)
            await page.click(sel)
            return True
        except (PWTimeout, PWError):
            continue
    return False


async def _select_county(page: Page) -> None:
    ok = await _safe_select(
        page,
        [
            "select#ContentPlaceHolder1_ddlCounty",
            "select[name*='County']",
            "select[id*='County']",
            "#ddlCounty",
            "select",
        ],
        value=GWINNETT_CODE,
        label=GWINNETT_NAME,
    )
    if not ok:
        log.warning("  County dropdown not set – proceeding anyway")


async def _select_doc_type(page: Page, doc_code: str) -> None:
    ok = await _safe_select(
        page,
        [
            "select#ContentPlaceHolder1_ddlBookType",
            "select[name*='BookType']",
            "select[name*='DocType']",
            "select[id*='BookType']",
            "#ddlBookType",
            "#ddlDocType",
        ],
        value=doc_code,
    )
    if not ok:
        log.warning("  DocType dropdown not set for %s", doc_code)


async def _fill_dates(page: Page, start: datetime, end: datetime) -> None:
    start_s, end_s = start.strftime(DATE_FMT), end.strftime(DATE_FMT)
    await _safe_fill(page, [
        "#ContentPlaceHolder1_txtFromDate",
        "input[name*='FromDate']",
        "input[id*='From']",
        "input[name*='DateFrom']",
        "input[type='text']:nth-of-type(1)",
    ], start_s)
    await _safe_fill(page, [
        "#ContentPlaceHolder1_txtThruDate",
        "#ContentPlaceHolder1_txtToDate",
        "input[name*='ThruDate']",
        "input[name*='ToDate']",
        "input[id*='Thru']",
        "input[id*='To']",
        "input[type='text']:nth-of-type(2)",
    ], end_s)


async def _submit_search(page: Page) -> None:
    ok = await _safe_click(page, [
        "input#ContentPlaceHolder1_btnSearch",
        "input[type='submit'][value*='Search']",
        "input[type='button'][value*='Search']",
        "button:has-text('Search')",
        "#btnSearch",
        "input[id*='Search']",
    ])
    if ok:
        await page.wait_for_load_state("domcontentloaded", timeout=NAV_TIMEOUT_MS)
    else:
        await page.keyboard.press("Enter")
        await page.wait_for_load_state("domcontentloaded", timeout=NAV_TIMEOUT_MS)


def _map_headers(headers: List[str]) -> Dict[str, int]:
    """Map logical field names to column indices from header row text."""
    FIELD_KEYWORDS: Dict[str, List[str]] = {
        "doc_num":  ["book", "instrument", "doc#", "doc num", "document number",
                     "deed book", "bk/pg"],
        "doc_type": ["type", "book type", "doc type", "instrument type"],
        "filed":    ["filed", "filing date", "recorded", "date filed", "date"],
        "owner":    ["grantor", "party 1", "owner", "seller"],
        "grantee":  ["grantee", "party 2", "buyer"],
        "legal":    ["legal", "legal description", "description"],
        "amount":   ["amount", "consideration", "value", "price", "debt"],
    }
    col_map: Dict[str, int] = {}
    for field, keywords in FIELD_KEYWORDS.items():
        for idx, h in enumerate(headers):
            hl = h.lower()
            if any(kw in hl for kw in keywords):
                col_map.setdefault(field, idx)
    return col_map


def _extract_row(
    cells: Any,
    col_map: Dict[str, int],
    doc_code: str,
    cat: str,
    cat_label: str,
) -> Optional[Dict]:
    """Turn a list of <td> elements into a record dict."""
    def cell_text(idx: int) -> str:
        if 0 <= idx < len(cells):
            return clean(cells[idx].get_text())
        return ""

    def cell_link(idx: int) -> str:
        if 0 <= idx < len(cells):
            a = cells[idx].find("a", href=True)
            if a:
                href = a["href"]
                return urljoin(GSCCCA_BASE, href) if not href.startswith("http") else href
        return ""

    rec = make_empty_record()
    rec["doc_type"]  = doc_code
    rec["cat"]       = cat
    rec["cat_label"] = cat_label

    if "doc_num" in col_map:
        rec["doc_num"]   = cell_text(col_map["doc_num"])
        link             = cell_link(col_map["doc_num"])
        if link:
            rec["clerk_url"] = link

    if "filed" in col_map:
        rec["filed"]   = fmt_date(cell_text(col_map["filed"]))
    if "owner" in col_map:
        rec["owner"]   = cell_text(col_map["owner"])
    if "grantee" in col_map:
        rec["grantee"] = cell_text(col_map["grantee"])
    if "legal" in col_map:
        rec["legal"]   = cell_text(col_map["legal"])
    if "amount" in col_map:
        rec["amount"]  = parse_amount(cell_text(col_map["amount"]))

    # Fallback link scan
    if not rec["clerk_url"]:
        for cell in cells:
            a = cell.find("a", href=True)
            if a and ("RealEstate" in a["href"] or "deed" in a["href"].lower()):
                href = a["href"]
                rec["clerk_url"] = (
                    urljoin(GSCCCA_BASE, href) if not href.startswith("http") else href
                )
                break

    # Build synthetic URL if still missing
    if not rec["clerk_url"] and rec["doc_num"]:
        rec["clerk_url"] = (
            f"{GSCCCA_SEARCH_URL}?county={GWINNETT_CODE}"
            f"&doctype={doc_code}&docnum={rec['doc_num']}"
        )

    # Reject completely empty rows
    if not any([rec["doc_num"], rec["owner"], rec["filed"]]):
        return None

    return rec


async def _parse_results_page(
    page: Page, doc_code: str, cat: str, cat_label: str
) -> List[Dict]:
    """Parse one HTML results page into a list of records."""
    html  = await page.content()
    soup  = BeautifulSoup(html, "lxml")
    records: List[Dict] = []

    # No-results indicators
    body_text = soup.get_text().lower()
    if any(p in body_text for p in
           ["no records found", "no results", "returned 0", "0 records"]):
        return []

    # Find results table
    table = (
        soup.find("table", id=re.compile(r"GridView|gvResult|tblResult|dgResult", re.I))
        or soup.find("table", class_=re.compile(r"grid|result|data", re.I))
        or soup.find("table", attrs={"cellpadding": True})
    )
    if not table:
        log.debug("  No results table found (doc=%s)", doc_code)
        return []

    rows = table.find_all("tr")
    if len(rows) < 2:
        return []

    header_cells = rows[0].find_all(["th", "td"])
    headers      = [clean(h.get_text()) for h in header_cells]
    col_map      = _map_headers(headers)

    for row in rows[1:]:
        cells = row.find_all("td")
        if not cells or len(cells) < 2:
            continue
        try:
            rec = _extract_row(cells, col_map, doc_code, cat, cat_label)
            if rec:
                records.append(rec)
        except Exception as exc:
            log.debug("  Row parse error: %s", exc)

    return records


async def _next_page(page: Page) -> bool:
    """Click Next pagination link. Returns True if navigated."""
    selectors = [
        "a:has-text('Next')",
        "a[title='Next Page']",
        "input[value='Next']",
        "a:has-text('>')",
        "a.next",
        "li.next > a",
    ]
    for sel in selectors:
        try:
            el = await page.query_selector(sel)
            if not el:
                continue
            cls = await el.get_attribute("class") or ""
            if "disabled" in cls.lower():
                return False
            aria = await el.get_attribute("aria-disabled") or ""
            if aria.lower() == "true":
                return False
            await el.click()
            await page.wait_for_load_state("domcontentloaded", timeout=NAV_TIMEOUT_MS)
            await page.wait_for_timeout(1000)
            return True
        except (PWTimeout, PWError):
            continue
    return False


async def _scrape_doc_type(
    page: Page,
    doc_code: str,
    cat: str,
    cat_label: str,
    start_date: datetime,
    end_date: datetime,
) -> List[Dict]:
    """Scrape all pages for one document type; return records list."""
    records: List[Dict] = []

    for attempt in range(RETRY_ATTEMPTS):
        try:
            # ── Navigate ──────────────────────────────────────────────────
            await page.goto(GSCCCA_SEARCH_URL, wait_until="domcontentloaded",
                            timeout=NAV_TIMEOUT_MS)
            await page.wait_for_timeout(2000)

            # ── Fill search form ──────────────────────────────────────────
            await _select_county(page)
            await page.wait_for_timeout(800)
            await _select_doc_type(page, doc_code)
            await page.wait_for_timeout(500)
            await _fill_dates(page, start_date, end_date)
            await page.wait_for_timeout(500)
            await _submit_search(page)
            await page.wait_for_timeout(2000)

            # ── Paginate ──────────────────────────────────────────────────
            page_num = 1
            while True:
                page_recs = await _parse_results_page(page, doc_code, cat, cat_label)
                records.extend(page_recs)
                log.debug("    %s page %d → %d records", doc_code, page_num, len(page_recs))
                if not page_recs:
                    break
                has_next = await _next_page(page)
                if not has_next:
                    break
                page_num += 1
                await asyncio.sleep(REQUEST_DELAY_SEC)

            break  # success

        except (PWTimeout, PWError) as exc:
            if attempt == RETRY_ATTEMPTS - 1:
                log.error("  Playwright failed for %s after %d attempts: %s",
                          doc_code, RETRY_ATTEMPTS, exc)
            else:
                log.warning("  Retrying %s (attempt %d): %s", doc_code, attempt + 1, exc)
                await asyncio.sleep(RETRY_DELAY_SEC)
        except Exception as exc:
            log.error("  Unexpected error for %s: %s", doc_code, exc)
            log.debug(traceback.format_exc())
            break

    return records


async def scrape_all_doc_types(
    start_date: datetime,
    end_date: datetime,
) -> List[Dict]:
    """
    Launch a single Playwright browser and scrape all document types
    for Gwinnett County. Returns deduplicated list of record dicts.
    """
    all_records: List[Dict] = []

    async with async_playwright() as pw:
        browser: Browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-dev-shm-usage",
                  "--disable-setuid-sandbox", "--disable-gpu"],
        )
        ctx: BrowserContext = await browser.new_context(
            user_agent=(
                "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36"
            ),
            viewport={"width": 1280, "height": 900},
            locale="en-US",
        )
        page: Page = await ctx.new_page()
        page.set_default_timeout(PAGE_TIMEOUT_MS)
        page.set_default_navigation_timeout(NAV_TIMEOUT_MS)

        for doc_code, (cat, cat_label) in DOC_TYPES.items():
            log.info("Searching GSCCCA %-12s (%s) …", doc_code, cat_label)
            try:
                recs = await _scrape_doc_type(
                    page, doc_code, cat, cat_label, start_date, end_date
                )
                log.info("  → %d records", len(recs))
                all_records.extend(recs)
            except Exception as exc:
                log.error("  Error scraping %s: %s", doc_code, exc)
            finally:
                await asyncio.sleep(REQUEST_DELAY_SEC)

        await browser.close()

    # ── Deduplicate by doc_num (then clerk_url fallback) ──────────────────────
    seen: Set[str] = set()
    deduped: List[Dict] = []
    for rec in all_records:
        key = rec.get("doc_num") or rec.get("clerk_url") or json.dumps(rec, sort_keys=True)
        if key not in seen:
            seen.add(key)
            deduped.append(rec)

    log.info("Total unique records scraped: %d", len(deduped))
    return deduped


# ══════════════════════════════════════════════════════════════════════════════
#  REQUESTS + BS4 FALLBACK SCRAPER
# ══════════════════════════════════════════════════════════════════════════════

def _bs4_scrape_doc_type(
    session: requests.Session,
    doc_code: str,
    cat: str,
    cat_label: str,
    start_date: datetime,
    end_date: datetime,
) -> List[Dict]:
    """
    Fallback scraper using requests + BeautifulSoup.
    Handles ASP.NET __doPostBack and ViewState manually.
    """
    records: List[Dict] = []

    def _get_aspnet_state(soup: BeautifulSoup) -> Dict[str, str]:
        state: Dict[str, str] = {}
        for name in ("__VIEWSTATE", "__EVENTVALIDATION", "__VIEWSTATEGENERATOR"):
            el = soup.find("input", {"name": name})
            if el:
                state[name] = el.get("value", "")
        return state

    try:
        resp = session.get(GSCCCA_SEARCH_URL, timeout=30)
        resp.raise_for_status()
        soup  = BeautifulSoup(resp.text, "lxml")
        state = _get_aspnet_state(soup)

        # Build POST payload
        payload = {
            **state,
            "__EVENTTARGET":   "",
            "__EVENTARGUMENT": "",
        }

        # County
        county_sel = soup.find("select", id=re.compile(r"County", re.I))
        if county_sel:
            for opt in county_sel.find_all("option"):
                if GWINNETT_NAME.lower() in opt.get_text().lower():
                    payload[county_sel["name"]] = opt.get("value", "")
                    break

        # Doc type
        book_sel = soup.find("select", id=re.compile(r"Book|DocType", re.I))
        if book_sel:
            for opt in book_sel.find_all("option"):
                if opt.get("value", "").upper() == doc_code.upper():
                    payload[book_sel["name"]] = opt.get("value", "")
                    break

        # Dates
        for sel_re, val in [
            (r"From|from", start_date.strftime(DATE_FMT)),
            (r"Thru|To|to",  end_date.strftime(DATE_FMT)),
        ]:
            el = soup.find("input", id=re.compile(sel_re, re.I))
            if el:
                payload[el["name"]] = val

        # Search button
        btn = soup.find("input", {"type": re.compile(r"submit|button", re.I),
                                   "value": re.compile(r"search", re.I)})
        if btn:
            payload[btn.get("name", "btnSearch")] = btn.get("value", "Search")

        page_num = 1
        while True:
            post_resp = session.post(
                GSCCCA_SEARCH_URL, data=payload, timeout=45,
                headers={"Referer": GSCCCA_SEARCH_URL}
            )
            post_resp.raise_for_status()
            psoup = BeautifulSoup(post_resp.text, "lxml")
            state = _get_aspnet_state(psoup)
            payload.update(state)

            table = (
                psoup.find("table", id=re.compile(r"GridView|gvResult", re.I))
                or psoup.find("table", attrs={"cellpadding": True})
            )
            if not table:
                break

            rows = table.find_all("tr")
            if len(rows) < 2:
                break

            headers  = [clean(h.get_text()) for h in rows[0].find_all(["th", "td"])]
            col_map  = _map_headers(headers)

            for row in rows[1:]:
                cells = row.find_all("td")
                if not cells or len(cells) < 2:
                    continue
                try:
                    rec = _extract_row(cells, col_map, doc_code, cat, cat_label)
                    if rec:
                        records.append(rec)
                except Exception:
                    continue

            # Next page via __doPostBack
            next_link = psoup.find("a", string=re.compile(r"Next|>", re.I))
            if not next_link:
                break
            href = next_link.get("href", "")
            js_match = re.match(r"javascript:__doPostBack\('(.+?)','(.+?)'\)", href)
            if not js_match:
                break
            payload["__EVENTTARGET"]   = js_match.group(1)
            payload["__EVENTARGUMENT"] = js_match.group(2)
            payload.pop(btn.get("name", "btnSearch"), None)  # remove submit on pagination
            page_num += 1
            time.sleep(REQUEST_DELAY_SEC)

    except Exception as exc:
        log.error("  BS4 fallback error for %s: %s", doc_code, exc)

    return records


def scrape_all_fallback(
    start_date: datetime,
    end_date: datetime,
) -> List[Dict]:
    """requests+BS4 fallback scraper for all document types."""
    session = requests.Session()
    session.headers.update(HEADERS)
    all_records: List[Dict] = []

    for doc_code, (cat, cat_label) in DOC_TYPES.items():
        log.info("[Fallback] %s (%s) …", doc_code, cat_label)
        try:
            recs = _bs4_scrape_doc_type(
                session, doc_code, cat, cat_label, start_date, end_date
            )
            log.info("  → %d records", len(recs))
            all_records.extend(recs)
        except Exception as exc:
            log.error("  Fallback error for %s: %s", doc_code, exc)
        time.sleep(REQUEST_DELAY_SEC)

    return all_records


# ══════════════════════════════════════════════════════════════════════════════
#  ENRICHMENT – attach parcel address data
# ══════════════════════════════════════════════════════════════════════════════

def enrich_records(
    records: List[Dict],
    owner_lookup: Dict[str, Dict],
) -> List[Dict]:
    """Attach property and mailing addresses from parcel lookup."""
    enriched = 0
    for rec in records:
        parcel = lookup_parcel(rec.get("owner", ""), owner_lookup)
        if parcel:
            rec.setdefault("prop_address", parcel.get("prop_address", ""))
            rec.setdefault("prop_city",    parcel.get("prop_city", ""))
            rec.setdefault("prop_state",   parcel.get("prop_state", "GA"))
            rec.setdefault("prop_zip",     parcel.get("prop_zip", ""))
            rec["mail_address"] = parcel.get("mail_address", "")
            rec["mail_city"]    = parcel.get("mail_city", "")
            rec["mail_state"]   = parcel.get("mail_state", "")
            rec["mail_zip"]     = parcel.get("mail_zip", "")
            enriched += 1
    log.info("Enriched %d / %d records with parcel addresses", enriched, len(records))
    return records


# ══════════════════════════════════════════════════════════════════════════════
#  SCORING & FLAGS
# ══════════════════════════════════════════════════════════════════════════════

def build_flags(rec: Dict) -> List[str]:
    """Return ordered list of motivation flags for a record."""
    flags: List[str] = []
    doc   = rec.get("doc_type", "").upper()
    cat   = rec.get("cat", "")
    owner = rec.get("owner", "").upper()
    filed = rec.get("filed", "")
    amt   = rec.get("amount") or 0

    # Foreclosure / Lis Pendens
    if doc == "LP":
        flags.append("Lis pendens")
    if doc in ("LP", "NOFC"):
        flags.append("Pre-foreclosure")

    # Judgments
    if doc in ("JUD", "CCJ", "DRJUD"):
        flags.append("Judgment lien")

    # Tax liens
    if doc in ("TAXDEED", "LNCORPTX", "LNIRS", "LNFED"):
        flags.append("Tax lien")

    # Mechanic / HOA / other liens
    if doc == "LNMECH":
        flags.append("Mechanic lien")
    elif doc == "LNHOA":
        flags.append("HOA lien")
    elif doc in ("LN", "MEDLN"):
        flags.append("Lien")

    # Probate
    if doc == "PRO" or cat == "probate":
        flags.append("Probate / estate")

    # LLC / corporate owner
    if any(kw in owner for kw in
           ["LLC", " INC", " CORP", "L.L.C", "LTD", " TRUST", "PROP", "HOLDINGS"]):
        flags.append("LLC / corp owner")

    # New this week
    if filed:
        try:
            age = (TODAY - datetime.strptime(filed, "%Y-%m-%d")).days
            if age <= 7:
                flags.append("New this week")
        except ValueError:
            pass

    return list(dict.fromkeys(flags))  # deduplicate, preserve order


def calculate_score(rec: Dict, all_records: List[Dict]) -> int:
    """
    Motivated Seller Score (0 – 100)

    Base            : 30
    Per flag        : +10 (each unique flag)
    LP + FC combo   : +20 (same owner has both LP and NOFC)
    Amount > $100k  : +15
    Amount > $50k   : +10  (mutually exclusive with above)
    New this week   : +5
    Has address     : +5
    """
    score  = 30
    flags  = rec.get("flags", [])
    amount = rec.get("amount") or 0
    doc    = rec.get("doc_type", "")

    # Flag bonus (capped to prevent runaway)
    score += min(len(flags) * 10, 50)

    # LP + Foreclosure combo for same owner
    if doc == "LP":
        owner = rec.get("owner", "").upper()
        has_fc = any(
            r is not rec
            and r.get("owner", "").upper() == owner
            and r.get("doc_type") == "NOFC"
            for r in all_records
        )
        if has_fc:
            score += 20

    # Amount bonuses (mutually exclusive)
    if amount >= 100_000:
        score += 15
    elif amount >= 50_000:
        score += 10

    if "New this week" in flags:
        score += 5

    if rec.get("prop_address") or rec.get("mail_address"):
        score += 5

    return min(score, 100)


# ══════════════════════════════════════════════════════════════════════════════
#  OUTPUT  –  JSON  &  GHL CSV
# ══════════════════════════════════════════════════════════════════════════════

def save_json(records: List[Dict], start_date: datetime, end_date: datetime) -> None:
    """Write records.json to all OUTPUT_PATHS."""
    with_addr = sum(
        1 for r in records if r.get("prop_address") or r.get("mail_address")
    )
    payload = {
        "fetched_at":  datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source":      "GSCCCA – Gwinnett County Superior Court Clerk",
        "date_range": {
            "start": start_date.strftime("%Y-%m-%d"),
            "end":   end_date.strftime("%Y-%m-%d"),
        },
        "total":        len(records),
        "with_address": with_addr,
        "records":      records,
    }
    for path in OUTPUT_PATHS:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, default=str)
        log.info("Saved %d records → %s", len(records), path)


GHL_FIELDS = [
    "First Name", "Last Name",
    "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
    "Property Address", "Property City", "Property State", "Property Zip",
    "Lead Type", "Document Type", "Date Filed", "Document Number",
    "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
    "Source", "Public Records URL",
]


def export_ghl_csv(records: List[Dict]) -> None:
    """Write GoHighLevel-ready CSV."""
    GHL_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(GHL_CSV_PATH, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=GHL_FIELDS)
        writer.writeheader()
        for rec in records:
            first, last = split_owner_name(rec.get("owner", ""))
            amt = rec.get("amount")
            writer.writerow({
                "First Name":            first,
                "Last Name":             last,
                "Mailing Address":       rec.get("mail_address") or rec.get("prop_address", ""),
                "Mailing City":          rec.get("mail_city")    or rec.get("prop_city", ""),
                "Mailing State":         rec.get("mail_state")   or rec.get("prop_state", "GA"),
                "Mailing Zip":           rec.get("mail_zip")     or rec.get("prop_zip", ""),
                "Property Address":      rec.get("prop_address", ""),
                "Property City":         rec.get("prop_city", ""),
                "Property State":        rec.get("prop_state", "GA"),
                "Property Zip":          rec.get("prop_zip", ""),
                "Lead Type":             rec.get("cat_label", ""),
                "Document Type":         rec.get("doc_type", ""),
                "Date Filed":            rec.get("filed", ""),
                "Document Number":       rec.get("doc_num", ""),
                "Amount/Debt Owed":      f"${amt:,.2f}" if amt else "",
                "Seller Score":          rec.get("score", 0),
                "Motivated Seller Flags": "; ".join(rec.get("flags", [])),
                "Source":               "GSCCCA – Gwinnett County Clerk",
                "Public Records URL":    rec.get("clerk_url", ""),
            })
    log.info("GHL export → %s (%d rows)", GHL_CSV_PATH, len(records))


# ══════════════════════════════════════════════════════════════════════════════
#  MAIN
# ══════════════════════════════════════════════════════════════════════════════

async def main() -> None:
    log.info("=" * 65)
    log.info("  Gwinnett County Motivated Seller Lead Scraper")
    log.info("  Range : %s → %s", START_DATE.strftime("%Y-%m-%d"), TODAY.strftime("%Y-%m-%d"))
    log.info("  Types : %d document categories", len(DOC_TYPES))
    log.info("=" * 65)

    # ── 1. Parcel data ────────────────────────────────────────────────────────
    log.info("\n[1/4] Downloading parcel data …")
    session = requests.Session()
    session.headers.update(HEADERS)
    owner_lookup: Dict[str, Dict] = {}
    try:
        owner_lookup = retry_sync(lambda: download_parcel_data(session))
    except Exception as exc:
        log.warning("Parcel download failed (will proceed without): %s", exc)

    # ── 2. Scrape GSCCCA ──────────────────────────────────────────────────────
    log.info("\n[2/4] Scraping GSCCCA clerk portal (Playwright) …")
    records: List[Dict] = []
    try:
        records = await scrape_all_doc_types(START_DATE, TODAY)
    except Exception as exc:
        log.error("Playwright scraper failed: %s – trying BS4 fallback …", exc)
        try:
            records = scrape_all_fallback(START_DATE, TODAY)
        except Exception as exc2:
            log.error("BS4 fallback also failed: %s", exc2)

    if not records:
        log.warning("No records found – saving empty output.")
        save_json([], START_DATE, TODAY)
        return

    # ── 3. Enrich + score ─────────────────────────────────────────────────────
    log.info("\n[3/4] Enriching %d records …", len(records))
    records = enrich_records(records, owner_lookup)

    for rec in records:
        rec["flags"] = build_flags(rec)

    for rec in records:                          # second pass (LP+FC combo needs full list)
        rec["score"] = calculate_score(rec, records)

    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # ── 4. Save ───────────────────────────────────────────────────────────────
    log.info("\n[4/4] Saving output …")
    save_json(records, START_DATE, TODAY)
    export_ghl_csv(records)

    # ── Summary ───────────────────────────────────────────────────────────────
    with_addr  = sum(1 for r in records if r.get("prop_address") or r.get("mail_address"))
    avg_score  = sum(r.get("score", 0) for r in records) // max(len(records), 1)
    top_score  = max((r.get("score", 0) for r in records), default=0)

    log.info("\n%s", "=" * 65)
    log.info("  ✓  Total records   : %d", len(records))
    log.info("  ✓  With address    : %d  (%.0f%%)",
             with_addr, 100 * with_addr / max(len(records), 1))
    log.info("  ✓  Avg score       : %d / 100", avg_score)
    log.info("  ✓  Top score       : %d / 100", top_score)
    # Breakdown by category
    from collections import Counter
    cats = Counter(r.get("cat_label", "Unknown") for r in records)
    for lbl, cnt in cats.most_common():
        log.info("       %-30s %d", lbl, cnt)
    log.info("=" * 65)


if __name__ == "__main__":
    asyncio.run(main())
