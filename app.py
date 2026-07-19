import io
import os
import re
import json
import math
import time
import datetime
import zipfile
import requests
import feedparser
import yfinance as yf
import anthropic
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlparse, quote
from flask import Flask, render_template, jsonify, request
from dotenv import load_dotenv

load_dotenv()

app = Flask(__name__)

# ── 종목 목록 (watchlist.json) ────────────────────────────────────
_WATCHLIST_PATH = os.path.join(os.path.dirname(__file__), "watchlist.json")

def load_watchlist():
    with open(_WATCHLIST_PATH, encoding="utf-8") as f:
        items = json.load(f)
    kr = [(s["name"], s["ticker"]) for s in items if s["market"] == "KR"]
    us = [(s["name"], s["ticker"]) for s in items if s["market"] == "US"]
    return kr, us

KR_STOCKS, US_STOCKS = load_watchlist()

# ── 인증 정보 ─────────────────────────────────────────────────────
NAVER_ID       = os.getenv("NAVER_CLIENT_ID")
NAVER_SECRET   = os.getenv("NAVER_CLIENT_SECRET")
KIS_APP_KEY    = os.getenv("KIS_APP_KEY")
KIS_APP_SECRET = os.getenv("KIS_APP_SECRET")
KIS_BASE       = "https://openapi.koreainvestment.com:9443"  # 실전투자
DART_KEY       = os.getenv("DART_API_KEY", "")
ANTHROPIC_KEY  = os.getenv("ANTHROPIC_API_KEY", "")

# 해외 종목 한글 검색 키워드
_US_KR_KEYWORDS = {          # Naver 뉴스 검색용
    "MSFT": "마이크로소프트",
    "AVGO": "브로드컴",
    "GOOGL": "구글",
    "AMAT": "어플라이드머티리얼즈",
    "TSM":  "TSMC",
    "AMZN": "아마존",
    "DELL": "델테크놀로지스",
}
_GOOGLE_KR_KEYWORDS = {      # Google News 한국어 RSS용
    "MSFT": "마이크로소프트",
    "AVGO": "브로드컴",
    "GOOGL": "구글 주식",
    "AMAT": "어플라이드머티리얼즈",
    "TSM":  "TSMC",
    "AMZN": "아마존 주식",
}

# ── 캐시 설정 ─────────────────────────────────────────────────────
NEWS_TTL  = 1800  # 30분
PRICE_TTL = 60    # 1분
MIN_FORCE = 60    # 수동 새로고침 최소 간격

_news_cache      = {"data": None, "fetched_at": 0}
_price_cache     = {"data": None, "fetched_at": 0}
_token_cache     = {"value": None, "expires_at": 0}
_dart_corp_cache  = {}   # stock_code(6자리) → corp_code(8자리)
_dart_code_map    = {}   # corpCode.xml 전체 매핑
_dart_code_loaded = False
_detail_cache     = {}   # ticker → {data, fetched_at}
DETAIL_TTL        = 3600


# ── 언론사 도메인 → 이름 매핑 ────────────────────────────────────
_PRESS_MAP = {
    "yna.co.kr": "연합뉴스", "einfomax.co.kr": "연합인포맥스",
    "newsis.com": "뉴시스", "mk.co.kr": "매일경제",
    "chosun.com": "조선일보", "joongang.co.kr": "중앙일보",
    "donga.com": "동아일보", "hani.co.kr": "한겨레",
    "sedaily.com": "서울경제", "etoday.co.kr": "이투데이",
    "news1.kr": "뉴스1", "newspim.com": "뉴스핌",
    "asiae.co.kr": "아시아경제", "mt.co.kr": "머니투데이",
    "fnnews.com": "파이낸셜뉴스", "edaily.co.kr": "이데일리",
    "inews24.com": "아이뉴스24", "etnews.com": "전자신문",
    "hankyung.com": "한국경제", "ytn.co.kr": "YTN",
    "kbs.co.kr": "KBS", "mbc.co.kr": "MBC",
    "sbs.co.kr": "SBS", "jtbc.co.kr": "JTBC",
    "ebn.co.kr": "EBN", "newstomato.com": "뉴스토마토",
    "econotimes.com": "EconoTimes", "newsworks.co.kr": "뉴스웍스",
    "businesspost.co.kr": "비즈니스포스트", "thebell.co.kr": "더벨",
    "womaneconomy.co.kr": "우먼이코노미", "coinreaders.com": "코인리더스",
    "kfenews.co.kr": "KFE뉴스", "abcn.kr": "ABCN",
}

def _domain_to_press(url):
    try:
        host = urlparse(url).netloc.lower()
        if host.startswith("www."):
            host = host[4:]
        for domain, name in _PRESS_MAP.items():
            if host == domain or host.endswith("." + domain):
                return name
        parts = host.split(".")
        if len(parts) >= 3 and parts[-2] in ("co", "or", "ne", "go"):
            return parts[-3]
        return parts[-2] if len(parts) >= 2 else host
    except Exception:
        return ""

# ── 유틸 ──────────────────────────────────────────────────────────
def clean(text):
    text = re.sub(r"<[^>]+>", "", text)
    for ent, ch in [("&quot;", '"'), ("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"), ("&#39;", "'")]:
        text = text.replace(ent, ch)
    return text.strip()


# ── 네이버 뉴스 ───────────────────────────────────────────────────
def naver_news(query, n=5):
    resp = requests.get(
        "https://openapi.naver.com/v1/search/news.json",
        headers={"X-Naver-Client-Id": NAVER_ID, "X-Naver-Client-Secret": NAVER_SECRET},
        params={"query": query, "display": n, "sort": "date"},
        timeout=5,
    )
    resp.raise_for_status()
    return [
        {
            "title":   clean(i["title"]),
            "link":    i["link"],
            "pubDate": i.get("pubDate", ""),
            "source":  _domain_to_press(i.get("originallink") or i.get("link", "")),
        }
        for i in resp.json().get("items", [])
    ]


# ── Yahoo Finance RSS ─────────────────────────────────────────────
def yahoo_news(symbol, n=5):
    feed = feedparser.parse(
        f"https://feeds.finance.yahoo.com/rss/2.0/headline?s={symbol}&region=US&lang=en-US"
    )
    return [
        {"title": e.get("title", ""), "link": e.get("link", ""), "pubDate": e.get("published", "")}
        for e in feed.entries[:n]
    ]


# ── Google News 한국어 RSS ────────────────────────────────────────
def google_news_kr(keyword, n=5):
    url = (
        "https://news.google.com/rss/search"
        f"?q={quote(keyword)}&hl=ko&gl=KR&ceid=KR:ko"
    )
    feed = feedparser.parse(url, agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64)")
    results = []
    for e in feed.entries[:n]:
        raw = e.get("title", "").strip()
        title, source = raw, ""
        if " - " in raw:
            title, source = raw.rsplit(" - ", 1)
            title, source = title.strip(), source.strip()
        results.append({
            "title":   title,
            "link":    e.get("link", ""),
            "pubDate": e.get("published", ""),
            "source":  source,
        })
    return results


# ── KIS: 액세스 토큰 ──────────────────────────────────────────────
def get_token():
    now = time.time()
    if _token_cache["value"] and now < _token_cache["expires_at"]:
        return _token_cache["value"]
    resp = requests.post(
        f"{KIS_BASE}/oauth2/tokenP",
        json={"grant_type": "client_credentials", "appkey": KIS_APP_KEY, "appsecret": KIS_APP_SECRET},
        timeout=10,
    )
    resp.raise_for_status()
    d = resp.json()
    _token_cache["value"]      = d["access_token"]
    _token_cache["expires_at"] = time.time() + d.get("expires_in", 86400) - 60
    return _token_cache["value"]


# ── KIS: 국내 현재가 ──────────────────────────────────────────────
def fetch_kr_price(code):
    token = get_token()
    resp = requests.get(
        f"{KIS_BASE}/uapi/domestic-stock/v1/quotations/inquire-price",
        headers={
            "authorization": f"Bearer {token}",
            "appkey":    KIS_APP_KEY,
            "appsecret": KIS_APP_SECRET,
            "tr_id":     "FHKST01010100",
        },
        params={"FID_COND_MRKT_DIV_CODE": "J", "FID_INPUT_ISCD": code},
        timeout=10,
    )
    resp.raise_for_status()
    o = resp.json().get("output", {})
    return {
        "price":    int(o.get("stck_prpr",  0) or 0),
        "change":   int(o.get("prdy_vrss",  0) or 0),
        "rate":     float(o.get("prdy_ctrt", 0) or 0),
        "sign":     o.get("prdy_vrss_sign", "3"),
        "currency": "KRW",
    }


# ── yfinance: 미국 현재가 ─────────────────────────────────────────
def fetch_us_price(symbol):
    info  = yf.Ticker(symbol).fast_info
    price = float(info.last_price     or 0)
    prev  = float(info.previous_close or 0)
    if not price or not prev:
        raise ValueError("No data")
    chg  = round(price - prev, 2)
    rate = round(chg / prev * 100, 2)
    sign = "2" if chg > 0 else ("5" if chg < 0 else "3")
    return {
        "price":    round(price, 2),
        "change":   round(chg, 2),
        "rate":     rate,
        "sign":     sign,
        "currency": "USD",
    }


# ── 통합 가격 조회 ────────────────────────────────────────────────
def get_prices():
    now = time.time()
    if _price_cache["data"] is None or now - _price_cache["fetched_at"] >= PRICE_TTL:
        kr = {}
        for name, code in KR_STOCKS:
            try:
                kr[name] = fetch_kr_price(code)
            except Exception as e:
                kr[name] = {"price": 0, "change": 0, "rate": 0, "sign": "3",
                            "currency": "KRW", "error": "조회 실패"}
            time.sleep(0.15)   # KIS 연속 호출 간격

        us = {}
        for name, sym in US_STOCKS:
            try:
                us[name] = fetch_us_price(sym)
            except Exception as e:
                us[name] = {"price": 0, "change": 0, "rate": 0, "sign": "3",
                            "currency": "USD", "error": "조회 실패"}

        _price_cache["data"]       = {"kr": kr, "us": us, "fetched_at": int(now)}
        _price_cache["fetched_at"] = now
    return _price_cache["data"]


# ── 뉴스 빌더 ─────────────────────────────────────────────────────
def build_news():
    kr = []
    for name, code in KR_STOCKS:
        try:    news = naver_news(name)
        except: news = []
        kr.append({"name": name, "code": code, "ticker": code, "news": news})

    us = []
    for name, sym in US_STOCKS:
        try:    news = yahoo_news(sym)
        except: news = []

        kr_pool = []

        # 1. Naver 뉴스 API
        kw_nv = _US_KR_KEYWORDS.get(sym)
        if kw_nv:
            try:
                time.sleep(0.15)
                kr_pool.extend(naver_news(kw_nv, n=5))
            except Exception:
                pass

        # 2. Google News 한국어 RSS
        kw_gn = _GOOGLE_KR_KEYWORDS.get(sym)
        if kw_gn:
            try:
                kr_pool.extend(google_news_kr(kw_gn, n=5))
            except Exception:
                pass

        # 제목 앞 15자 기준 중복 제거
        seen, kr_news = [], []
        for item in kr_pool:
            if not _is_dup(item["title"], seen):
                seen.append(item["title"])
                kr_news.append(item)

        us.append({"name": name, "symbol": sym, "ticker": sym, "news": news, "kr_news": kr_news})

    return {"kr": kr, "us": us, "fetched_at": int(time.time())}


def get_news(force=False):
    now = time.time()
    stale  = _news_cache["data"] is None or now - _news_cache["fetched_at"] >= NEWS_TTL
    man_ok = force and now - _news_cache["fetched_at"] >= MIN_FORCE
    if stale or man_ok:
        _news_cache["data"]       = build_news()
        _news_cache["fetched_at"] = now
    return _news_cache["data"]


# ── 티커 자동검색 ────────────────────────────────────────────────
_krx_cache = {"data": None, "fetched_at": 0}
KRX_TTL = 86400  # 24시간

def get_krx_stocks():
    """KRX 전체 종목 목록 (24시간 캐시)"""
    now = time.time()
    if _krx_cache["data"] is None or now - _krx_cache["fetched_at"] > KRX_TTL:
        resp = requests.post(
            "https://data.krx.co.kr/comm/bldAttendant/getJsonData.cmd",
            data={"bld": "dbms/comm/finder/finder_stkisu", "locale": "ko_KR",
                  "keyword": "", "pageFirstCall": "Y"},
            timeout=15,
            headers={"User-Agent": "Mozilla/5.0", "Referer": "https://data.krx.co.kr/"},
        )
        resp.raise_for_status()
        _krx_cache["data"]       = resp.json().get("block1", [])
        _krx_cache["fetched_at"] = now
    return _krx_cache["data"]

def search_kr_ticker(name):
    """KRX 캐시에서 종목명 부분 일치 검색"""
    stocks  = get_krx_stocks()
    keyword = name.strip()
    results = []
    for s in stocks:
        if keyword in s.get("codeName", ""):
            results.append({
                "ticker": s["short_code"],
                "name":   s["codeName"],
            })
            if len(results) >= 5:
                break
    return results


def search_us_ticker(name):
    """Yahoo Finance Search API로 US 종목 티커 검색"""
    resp = requests.get(
        "https://query2.finance.yahoo.com/v1/finance/search",
        params={"q": name, "lang": "en-US", "region": "US",
                "quotesCount": 6, "newsCount": 0, "enableFuzzyQuery": "false"},
        timeout=5,
        headers={"User-Agent": "Mozilla/5.0"},
    )
    resp.raise_for_status()
    results = []
    for q in resp.json().get("quotes", []):
        if q.get("quoteType") in ("EQUITY", "ETF"):
            results.append({
                "ticker": q.get("symbol", ""),
                "name":   q.get("shortname") or q.get("longname") or q.get("symbol", ""),
            })
    return results[:5]


@app.route("/api/ticker-lookup")
def api_ticker_lookup():
    name   = (request.args.get("name") or "").strip()
    market = (request.args.get("market") or "").strip().upper()
    if not name:
        return jsonify({"error": "name is required"}), 400
    try:
        if market == "KR":
            results = search_kr_ticker(name)
        elif market == "US":
            results = search_us_ticker(name)
        else:
            return jsonify({"error": "market must be KR or US"}), 400
    except Exception:
        results = []
    return jsonify({"results": results})


# ── 시장 이슈 키워드 뉴스 ────────────────────────────────────────
MARKET_CATEGORIES = [
    {"name": "국내 증시", "keywords": ["코스피", "코스닥", "서킷브레이커", "사이드카", "외국인 순매도"]},
    {"name": "미국 증시", "keywords": ["나스닥", "S&P500", "다우존스", "연준 금리"]},
    {"name": "반도체",   "keywords": ["반도체 수출", "HBM", "파운드리", "메모리 가격"]},
    {"name": "매크로",   "keywords": ["원달러 환율", "국제유가", "미국 국채금리", "한국은행 기준금리"]},
    {"name": "지정학",   "keywords": ["중동 정세", "호르무즈 해협", "미중 무역"]},
]

# ── 경제 RSS 피드 (한국경제 RSS 차단 → 연합인포맥스·뉴시스 대체) ──
RSS_FEEDS = [
    "https://www.yna.co.kr/rss/economy.xml",          # 연합뉴스 경제  (120건)
    "https://news.einfomax.co.kr/rss/allArticle.xml",  # 연합인포맥스   ( 50건)
    "https://www.newsis.com/RSS/economy.xml",          # 뉴시스 경제    (100건)
    "https://www.mk.co.kr/rss/30100041/",              # 매일경제 경제  ( 50건)
]
_rss_cache    = {"data": None, "fetched_at": 0}
_market_cache = {"data": None, "fetched_at": 0}

def get_rss_items():
    now = time.time()
    if _rss_cache["data"] is None or now - _rss_cache["fetched_at"] >= NEWS_TTL:
        items = []
        ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
        for url in RSS_FEEDS:
            try:
                for e in feedparser.parse(url, agent=ua).entries[:200]:
                    t = clean(e.get("title", ""))
                    l = e.get("link", "")
                    if t and l:
                        items.append({
                            "title":   t,
                            "link":    l,
                            "pubDate": e.get("published", ""),
                            "source":  _domain_to_press(l),
                        })
            except Exception:
                pass
        _rss_cache["data"]       = items
        _rss_cache["fetched_at"] = now
    return _rss_cache["data"]

def _is_dup(title, seen_titles):
    """제목 앞 15자 기반 중복 판별 (공백·말줄임 정규화 후 비교)"""
    def _norm(t):
        t = re.sub(r'\s+', '', t)   # 공백 제거
        return t.replace('…', '...')[:15]
    prefix = _norm(title)
    if not prefix:
        return False
    for t in seen_titles:
        if prefix == _norm(t):
            return True
    return False

def _build_category(cat_name, keywords, rss_pool):
    seen_links  = set()
    seen_titles = []
    items       = []

    # 1. Naver 뉴스 키워드 검색 (키워드당 50개)
    naver_pool = []
    for i, kw in enumerate(keywords):
        if i > 0:
            time.sleep(0.15)
        try:
            for art in naver_news(kw, n=50):
                naver_pool.append({**art, "keyword": kw})
        except Exception:
            pass

    # 2. RSS 피드에서 키워드 매칭
    rss_matched = []
    for art in rss_pool:
        for kw in keywords:
            if kw in art["title"]:
                rss_matched.append({**art, "keyword": kw})
                break

    # 3. 합산 후 링크·제목 중복 제거 (상한 없음)
    for art in naver_pool + rss_matched:
        if art["link"] in seen_links:
            continue
        if _is_dup(art["title"], seen_titles):
            continue
        seen_links.add(art["link"])
        seen_titles.append(art["title"])
        items.append({**art, "cat": cat_name})

    return {"name": cat_name, "items": items}

def build_market_news():
    rss_pool   = get_rss_items()
    categories = [_build_category(c["name"], c["keywords"], rss_pool) for c in MARKET_CATEGORIES]
    return {"categories": categories, "fetched_at": int(time.time())}

def get_market_news(force=False):
    now    = time.time()
    stale  = _market_cache["data"] is None or now - _market_cache["fetched_at"] >= NEWS_TTL
    man_ok = force and now - _market_cache["fetched_at"] >= MIN_FORCE
    if stale or man_ok:
        _market_cache["data"]       = build_market_news()
        _market_cache["fetched_at"] = now
    return _market_cache["data"]

@app.route("/api/market-news")
def api_market_news():
    return jsonify(get_market_news(force=request.args.get("force") == "1"))


# ── DART 공시 ────────────────────────────────────────────────────
def _load_dart_code_map():
    """corpCode.xml ZIP 다운로드 → stock_code(6자리) : corp_code(8자리) 매핑 구축 (1회 실행)"""
    global _dart_code_loaded, _dart_code_map
    if _dart_code_loaded:
        return
    resp = requests.get(
        "https://opendart.fss.or.kr/api/corpCode.xml",
        params={"crtfc_key": DART_KEY},
        timeout=30,
    )
    resp.raise_for_status()
    with zipfile.ZipFile(io.BytesIO(resp.content)) as z:
        with z.open("CORPCODE.xml") as f:
            tree = ET.parse(f)
    for item in tree.getroot().findall("list"):
        sc = (item.findtext("stock_code") or "").strip()
        cc = (item.findtext("corp_code")  or "").strip()
        if sc and cc:
            _dart_code_map[sc] = cc
    _dart_code_loaded = True

def _get_dart_corp_code(stock_code):
    if stock_code in _dart_corp_cache:
        return _dart_corp_cache[stock_code]
    _load_dart_code_map()
    corp_code = _dart_code_map.get(stock_code)
    if not corp_code:
        raise ValueError(f"DART corp_code not found for {stock_code}")
    _dart_corp_cache[stock_code] = corp_code
    return corp_code

def _dart_badge(report_nm):
    nm = report_nm
    if any(k in nm for k in ["지분", "대량보유", "임원", "주요주주"]):
        return "지분공시"
    if any(k in nm for k in ["배당", "현금배당", "주식배당"]):
        return "배당"
    if any(k in nm for k in ["조회공시", "풍문", "보도내용"]):
        return "풍문"
    if any(k in nm for k in ["사업보고서", "분기보고서", "반기보고서", "영업실적", "잠정실적"]):
        return "실적"
    return None

def _fetch_dart_disclosures(corp_code, days=180):
    bgn = (datetime.date.today() - datetime.timedelta(days=days)).strftime("%Y%m%d")
    resp = requests.get(
        "https://opendart.fss.or.kr/api/list.json",
        params={
            "crtfc_key": DART_KEY,
            "corp_code":  corp_code,
            "bgn_de":     bgn,
            "sort":       "date",
            "sort_mth":   "desc",
            "page_count": "40",
        },
        timeout=10,
    )
    resp.raise_for_status()
    d = resp.json()
    if d.get("status") not in ("000", "013"):   # 013 = 조회 결과 없음
        raise ValueError(d.get("message", "DART error"))
    results = []
    for item in d.get("list", []):
        badge = _dart_badge(item.get("report_nm", ""))
        if not badge:
            continue
        rcept_no = item.get("rcept_no", "")
        results.append({
            "badge": badge,
            "title": item.get("report_nm", ""),
            "date":  item.get("rcept_dt", ""),
            "link":  f"https://dart.fss.or.kr/dsaf001/main.do?rcpNo={rcept_no}",
        })
    return results


# ── 네이버 금융 증권사 리포트 ────────────────────────────────────
def _fetch_naver_reports(stock_code, n=10):
    # 실제 HTML 구조: <td><a href="company_read.naver?nid=...">제목</a></td><td>증권사</td>
    #                 <td class="file">...</td><td class="date" ...>YY.MM.DD</td>
    url = (
        "https://finance.naver.com/research/company_list.naver"
        f"?searchType=itemCode&itemCode={stock_code}&page=1"
    )
    resp = requests.get(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
            "Referer":    "https://finance.naver.com/",
        },
        timeout=8,
    )
    resp.encoding = "euc-kr"
    html = resp.text
    rows = re.findall(
        r'<td><a href="(company_read\.naver\?nid=\d+[^"]*?)"[^>]*>(.*?)</a></td>\s*'
        r'<td>(.*?)</td>\s*'
        r'<td class="file">.*?</td>\s*'
        r'<td class="date"[^>]*>(\d{2}\.\d{2}\.\d{2})</td>',
        html, re.DOTALL,
    )
    results = []
    for path, title, firm, date in rows[:n]:
        title = re.sub(r"<[^>]+>", "", title).strip()
        firm  = re.sub(r"<[^>]+>", "", firm).strip()
        if not title:
            continue
        results.append({
            "title": title,
            "firm":  firm,
            "date":  "20" + date,   # YY.MM.DD → 20YY.MM.DD
            "link":  f"https://finance.naver.com/research/{path}",
        })
    return results


# ── 네이버 금융 업종·경제·시장 분석 리포트 (주요 뉴스 탭용) ─────────────
_REPORT_CONFIGS = [
    ("업종분석",  "industry_list",    "industry_read"),
    ("경제분석",  "economy_list",     "economy_read"),
    ("시장분석",  "market_info_list", "market_info_read"),
]
_broker_cache = {"data": None, "fetched_at": 0}
BROKER_TTL    = 1800   # 30분

def _fetch_general_reports(n_each=20):
    _date_re = re.compile(r'(\d{2}\.\d{2}\.\d{2})')
    results  = []
    for label, list_page, read_prefix in _REPORT_CONFIGS:
        url = f"https://finance.naver.com/research/{list_page}.naver"
        try:
            resp = requests.get(url, headers={
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                "Referer":    "https://finance.naver.com/research/",
            }, timeout=8)
            resp.encoding = "euc-kr"
            html = resp.text
        except Exception:
            continue

        link_re = re.compile(
            rf'href="({re.escape(read_prefix)}\.naver\?nid=\d+[^"]*?)"[^>]*>(.*?)</a>',
            re.DOTALL
        )
        count = 0
        for m in link_re.finditer(html):
            if count >= n_each:
                break
            path  = m.group(1)
            title = re.sub(r"<[^>]+>", "", m.group(2)).strip()
            title = clean(title)
            if not title or len(title) < 5:
                continue

            # 링크 이후 600자에서 날짜·증권사 추출
            rest = html[m.end(): m.end() + 600]
            dm   = _date_re.search(rest)
            if not dm:
                continue

            # <td> 내용 중 2-15자 한글 포함 텍스트 → 증권사명
            snippet = rest[: dm.start()]
            firm = ""
            for td_html in re.findall(r'<td[^>]*>\s*(.*?)\s*</td>', snippet, re.DOTALL):
                td_txt = re.sub(r"<[^>]+>", "", td_html).strip()
                if 2 <= len(td_txt) <= 15 and re.search(r'[가-힣]', td_txt):
                    firm = td_txt

            results.append({
                "title":   title,
                "firm":    firm,
                "date":    "20" + dm.group(1),
                "link":    f"https://finance.naver.com/research/{path}",
                "type":    label,
            })
            count += 1

    results.sort(key=lambda x: x["date"], reverse=True)
    return results


@app.route("/api/broker-reports")
def api_broker_reports():
    now = time.time()
    if _broker_cache["data"] is None or now - _broker_cache["fetched_at"] >= BROKER_TTL:
        try:
            data = _fetch_general_reports(n_each=20)
        except Exception:
            data = []
        _broker_cache["data"]       = data
        _broker_cache["fetched_at"] = now
    return jsonify(_broker_cache["data"])


@app.route("/api/detail/<ticker>")
def api_detail(ticker):
    market = "KR" if re.fullmatch(r"\d{6}", ticker) else "US"

    now    = time.time()
    cached = _detail_cache.get(ticker)
    if cached and now - cached["fetched_at"] < DETAIL_TTL:
        return jsonify(cached["data"])

    disclosures, reports = [], []

    if market == "KR":
        if DART_KEY:
            try:
                corp_code   = _get_dart_corp_code(ticker)
                disclosures = _fetch_dart_disclosures(corp_code)
            except Exception:
                pass
        try:
            reports = _fetch_naver_reports(ticker)
        except Exception:
            pass

    data = {"disclosures": disclosures, "reports": reports, "market": market}
    _detail_cache[ticker] = {"data": data, "fetched_at": now}
    return jsonify(data)


# ── 52주 신고가 ───────────────────────────────────────────────────
_high52_cache = {"data": None, "fetched_at": 0}

def _high52_ttl():
    """장 마감(16:00 KST) 이후 or 주말이면 자정까지, 장중엔 10분"""
    KST = datetime.timezone(datetime.timedelta(hours=9))
    now = datetime.datetime.now(KST)
    if now.weekday() >= 5:  # 주말
        midnight = (now + datetime.timedelta(days=1)).replace(
            hour=0, minute=0, second=0, microsecond=0)
        return max(int((midnight - now).total_seconds()), 7200)
    close_t = now.replace(hour=16, minute=0, second=0, microsecond=0)
    if now >= close_t:  # 장 마감 후
        midnight = (now + datetime.timedelta(days=1)).replace(
            hour=0, minute=0, second=0, microsecond=0)
        return max(int((midnight - now).total_seconds()), 3600)
    open_t = now.replace(hour=9, minute=0, second=0, microsecond=0)
    if now < open_t:    # 장 시작 전
        return int((open_t - now).total_seconds())
    return 600          # 장중 10분


def _fetch_52w_raw(mrkt):
    token = get_token()
    resp = requests.get(
        f"{KIS_BASE}/uapi/domestic-stock/v1/ranking/high-low",
        headers={
            "authorization": f"Bearer {token}",
            "appkey":        KIS_APP_KEY,
            "appsecret":     KIS_APP_SECRET,
            "tr_id":         "FHPST01700000",
            "custtype":      "P",
        },
        params={
            "fid_cond_mrkt_div_code": mrkt,   # J=KOSPI, K=KOSDAQ
            "fid_cond_scr_div_code":  "20170",
            "fid_input_iscd":         "0000",
            "fid_rank_sort_cls_code": "0",
            "fid_high_low_gb":        "1",     # 1=신고가
            "fid_vol_cnt":            "",
            "fid_aply_rang_prc_1":    "",
            "fid_aply_rang_prc_2":    "",
        },
        timeout=10,
    )
    resp.raise_for_status()
    return resp.json().get("output", [])


def build_high52():
    # KOSPI + KOSDAQ 합산 → 중복 제거 → 상위 30개
    pool = []
    for mrkt in ("J", "K"):
        try:
            pool.extend(_fetch_52w_raw(mrkt))
        except Exception:
            pass

    seen, stocks = set(), []
    for s in pool:
        code = (s.get("stck_shrn_iscd") or "").strip()
        if not code or code in seen:
            continue
        seen.add(code)
        stocks.append({
            "code":      code,
            "name":      (s.get("hts_kor_isnm") or "").strip(),
            "price":     s.get("stck_prpr", "0"),
            "rate":      s.get("prdy_ctrt", "0.00"),
            "sign":      s.get("prdy_vrss_sign", "3"),
            "high_date": s.get("d250_hgst_date", ""),
        })
        if len(stocks) >= 30:
            break

    def _add_news(s):
        try:
            s["news"] = naver_news(s["name"], n=2)
        except Exception:
            s["news"] = []
        return s

    with ThreadPoolExecutor(max_workers=5) as ex:
        stocks = list(ex.map(_add_news, stocks))

    return {"stocks": stocks, "fetched_at": int(time.time())}


def get_high52(force=False):
    now = time.time()
    ttl = _high52_ttl()
    if force or _high52_cache["data"] is None or now - _high52_cache["fetched_at"] >= ttl:
        _high52_cache["data"]       = build_high52()
        _high52_cache["fetched_at"] = now
    return _high52_cache["data"]


@app.route("/api/high52")
def api_high52():
    if not KIS_APP_KEY or not KIS_APP_SECRET:
        return jsonify({"stocks": [], "error": "KIS API 키 미설정"}), 200
    try:
        return jsonify(get_high52(force=request.args.get("force") == "1"))
    except Exception as e:
        return jsonify({"stocks": [], "error": str(e)}), 200


# ── 투자자별 매매동향 ──────────────────────────────────────────────
_investor_cache = {"data": None, "fetched_at": 0}

def _fetch_investor_stock(code):
    """당일 투자자별 매매동향 (FHKST01010900) - 단일 종목"""
    token = get_token()
    today = datetime.date.today().strftime("%Y%m%d")
    resp = requests.get(
        f"{KIS_BASE}/uapi/domestic-stock/v1/quotations/inquire-investor",
        headers={
            "authorization": f"Bearer {token}",
            "appkey":        KIS_APP_KEY,
            "appsecret":     KIS_APP_SECRET,
            "tr_id":         "FHKST01010900",
        },
        params={
            "FID_COND_MRKT_DIV_CODE": "J",
            "FID_INPUT_ISCD":         code,
            "FID_BEG_DATE":           today,
            "FID_END_DATE":           today,
        },
        timeout=8,
    )
    resp.raise_for_status()
    rows = resp.json().get("output", [])
    if not rows:
        return None
    r = rows[0]
    def _i(key):
        return int(r.get(key, 0) or 0)
    return {
        "prsn_qty": _i("prsn_ntby_qty"),
        "frgn_qty": _i("frgn_ntby_qty"),
        "orgn_qty": _i("orgn_ntby_qty"),
        "prsn_amt": _i("prsn_ntby_tr_pbmn"),   # 백만원
        "frgn_amt": _i("frgn_ntby_tr_pbmn"),
        "orgn_amt": _i("orgn_ntby_tr_pbmn"),
    }


def build_investor_trend():
    stocks_data = []
    for name, code in KR_STOCKS:
        try:
            inv = _fetch_investor_stock(code)
        except Exception:
            inv = None
        stocks_data.append({"code": code, "name": name, "investor": inv})
        time.sleep(0.1)   # 연속 호출 간격
    return {"stocks": stocks_data, "fetched_at": int(time.time())}


def get_investor_trend(force=False):
    now = time.time()
    ttl = _high52_ttl()   # 동일한 TTL 로직 공유
    if force or _investor_cache["data"] is None or now - _investor_cache["fetched_at"] >= ttl:
        _investor_cache["data"]       = build_investor_trend()
        _investor_cache["fetched_at"] = now
    return _investor_cache["data"]


@app.route("/api/investor-trend")
def api_investor_trend():
    if not KIS_APP_KEY or not KIS_APP_SECRET:
        return jsonify({"stocks": [], "error": "KIS API 키 미설정"}), 200
    try:
        return jsonify(get_investor_trend(force=request.args.get("force") == "1"))
    except Exception as e:
        return jsonify({"stocks": [], "error": str(e)}), 200


# ── 수급 동향 (투자자별 순매수/순매도 상위) ──────────────────────
_FLOW_INVESTOR_CODES = {
    "frgn":    "1",   # 외국인
    "orgn":    "2",   # 기관전체
    "pension": "9",   # 연기금
    "trust":   "3",   # 투신
    "prvt":    "4",   # 사모펀드
}
_flow_cache = {"data": None, "fetched_at": 0}


def _fetch_flow_raw(inv_code, sort_code, mrkt):
    """
    sort_code: "0" = 순매수 상위, "1" = 순매도 상위
    mrkt     : "J" = KOSPI, "K" = KOSDAQ
    """
    token = get_token()
    resp = requests.get(
        f"{KIS_BASE}/uapi/domestic-stock/v1/ranking/investor",
        headers={
            "authorization": f"Bearer {token}",
            "appkey":        KIS_APP_KEY,
            "appsecret":     KIS_APP_SECRET,
            "tr_id":         "FHPST01060000",
            "custtype":      "P",
        },
        params={
            "fid_cond_mrkt_div_code":  mrkt,
            "fid_cond_scr_div_code":   "20059",
            "fid_input_iscd":          "0000",
            "fid_trgt_cls_code":       inv_code,
            "fid_trgt_exls_cls_code":  "0",
            "fid_rank_sort_cls_code":  sort_code,
            "fid_input_cnt_1":         "0",
            "fid_vol_cnt":             "",
            "fid_aply_rang_prc_1":     "",
            "fid_aply_rang_prc_2":     "",
        },
        timeout=10,
    )
    resp.raise_for_status()
    return resp.json().get("output", [])


def _flow_merge_top(pool, n=10):
    """KOSPI+KOSDAQ 합산 중복 제거 → 순매수금액 절댓값 기준 재정렬 → 상위 n개"""
    seen, items = set(), []
    for s in pool:
        code = (s.get("stck_shrn_iscd") or "").strip()
        if code and code not in seen:
            seen.add(code)
            items.append(s)
    try:
        items.sort(
            key=lambda x: abs(int(float(x.get("ntby_tr_pbmn", "0") or "0"))),
            reverse=True,
        )
    except Exception:
        pass
    return items[:n]


def _normalize_flow(raw_list):
    items = []
    for s in raw_list:
        code = (s.get("stck_shrn_iscd") or "").strip()
        if not code:
            continue
        try:
            amt = abs(int(float(s.get("ntby_tr_pbmn", "0") or "0")))
        except (ValueError, TypeError):
            amt = 0
        items.append({
            "code":  code,
            "name":  (s.get("hts_kor_isnm") or "").strip(),
            "price": s.get("stck_prpr", "0"),
            "rate":  s.get("prdy_ctrt", "0.00"),
            "sign":  s.get("prdy_vrss_sign", "3"),
            "amt":   amt,   # 백만원, 절댓값
        })
    return items


def build_flow_data():
    # 5개 투자자 × 2방향 × 2시장 = 20 API 호출 → ThreadPoolExecutor로 병렬화
    tasks = [
        (inv_key, inv_code, sort_code, mrkt)
        for inv_key, inv_code in _FLOW_INVESTOR_CODES.items()
        for sort_code in ("0", "1")
        for mrkt in ("J", "K")
    ]

    def _fetch_one(args):
        inv_key, inv_code, sort_code, mrkt = args
        time.sleep(0.05)   # 연속 호출 최소 간격
        try:
            raw = _fetch_flow_raw(inv_code, sort_code, mrkt)
        except Exception:
            raw = []
        return inv_key, sort_code, raw

    with ThreadPoolExecutor(max_workers=4) as ex:
        fetched = list(ex.map(_fetch_one, tasks))

    # 투자자별, 방향별로 집계
    agg = {k: {"0": [], "1": []} for k in _FLOW_INVESTOR_CODES}
    for inv_key, sort_code, raw in fetched:
        agg[inv_key][sort_code].extend(raw)

    investors = {}
    for inv_key in _FLOW_INVESTOR_CODES:
        investors[inv_key] = {
            "buy":  _normalize_flow(_flow_merge_top(agg[inv_key]["0"])),
            "sell": _normalize_flow(_flow_merge_top(agg[inv_key]["1"])),
        }

    return {"investors": investors, "fetched_at": int(time.time())}


def get_flow_data(force=False):
    now = time.time()
    ttl = _high52_ttl()
    if force or _flow_cache["data"] is None or now - _flow_cache["fetched_at"] >= ttl:
        _flow_cache["data"]       = build_flow_data()
        _flow_cache["fetched_at"] = now
    return _flow_cache["data"]


@app.route("/api/flow")
def api_flow():
    if not KIS_APP_KEY or not KIS_APP_SECRET:
        return jsonify({"investors": {}, "error": "KIS API 키 미설정"}), 200
    try:
        return jsonify(get_flow_data(force=request.args.get("force") == "1"))
    except Exception as e:
        return jsonify({"investors": {}, "error": str(e)}), 200


# ── 글로벌 시장 (지수·원자재·환율) ───────────────────────────────
GLOBAL_MARKET_CONFIG = [
    # (그룹, yfinance 심볼, 표시명)
    ("지수_한국",   "^KS11",      "KOSPI"),
    ("지수_한국",   "^KQ11",      "KOSDAQ"),
    ("지수_미국",   "^DJI",       "다우존스"),
    ("지수_미국",   "^GSPC",      "S&P 500"),
    ("지수_미국",   "^IXIC",      "나스닥"),
    ("지수_아시아", "^N225",      "니케이 225"),
    ("지수_아시아", "^TWII",      "대만가권"),
    ("지수_아시아", "^HSI",       "항셍지수"),
    ("지수_유럽",   "^STOXX50E",  "유로스톡스50"),
    ("지수_유럽",   "^GDAXI",     "DAX 40"),
    ("지수_유럽",   "^FCHI",      "CAC 40"),
    ("지수_중국",   "000001.SS",  "상해종합"),
    ("지수_중국",   "399001.SZ",  "심천종합"),
    ("원자재",      "GC=F",       "금 ($/oz)"),
    ("원자재",      "SI=F",       "은 ($/oz)"),
    ("원자재",      "CL=F",       "WTI유 ($/bbl)"),
    ("원자재",      "BZ=F",       "브렌트유 ($/bbl)"),
    ("원자재",      "HG=F",       "구리 ($/lb)"),
    ("원자재",      "BTC-USD",    "비트코인 ($)"),
    ("원자재",      "ETH-USD",    "이더리움 ($)"),
    ("원자재",      "SOL-USD",    "솔라나 ($)"),
    ("환율",        "USDKRW=X",   "달러/원"),
    ("환율",        "USDJPY=X",   "달러/엔"),
    ("환율",        "EURUSD=X",   "유로/달러"),
]

GLOBAL_TTL    = 300   # 5분 캐시
_global_cache = {"data": None, "fetched_at": 0}


def _gm_clean(v):
    """NaN/inf → None so jsonify stays valid."""
    try:
        f = float(v)
        return None if (math.isnan(f) or math.isinf(f)) else f
    except (TypeError, ValueError):
        return None


def _fetch_gm_single(cfg):
    group, sym, name = cfg
    try:
        h = yf.Ticker(sym).history(period="5d")
        if len(h) < 1:
            return group, sym, name, None
        price = _gm_clean(h["Close"].iloc[-1])
        prev  = _gm_clean(h["Close"].iloc[-2]) if len(h) >= 2 else price
        high  = _gm_clean(h["High"].iloc[-1])
        low   = _gm_clean(h["Low"].iloc[-1])
        if price is None or prev is None:
            return group, sym, name, None
        change = round(price - prev, 6)
        rate   = round(change / prev * 100, 2) if prev else 0
        return group, sym, name, {
            "price":  price,
            "high":   high,
            "low":    low,
            "change": change,
            "rate":   rate,
            "sign":   "2" if change > 0 else ("5" if change < 0 else "3"),
        }
    except Exception:
        return group, sym, name, None


def build_global_market():
    with ThreadPoolExecutor(max_workers=8) as ex:
        raw = list(ex.map(_fetch_gm_single, GLOBAL_MARKET_CONFIG))

    groups = {}
    for group, sym, name, data in raw:
        if group not in groups:
            groups[group] = []
        groups[group].append({
            "sym":  sym,
            "name": name,
            **(data or {}),
            "ok":   data is not None,
        })

    return {
        "indices": {
            "한국":   groups.get("지수_한국",   []),
            "미국":   groups.get("지수_미국",   []),
            "아시아": groups.get("지수_아시아", []),
            "유럽":   groups.get("지수_유럽",   []),
            "중국":   groups.get("지수_중국",   []),
        },
        "commodities": groups.get("원자재", []),
        "fx":          groups.get("환율",   []),
        "fetched_at":  int(time.time()),
    }


def get_global_market(force=False):
    now = time.time()
    if force or _global_cache["data"] is None or now - _global_cache["fetched_at"] >= GLOBAL_TTL:
        _global_cache["data"]       = build_global_market()
        _global_cache["fetched_at"] = now
    return _global_cache["data"]


@app.route("/api/global-market")
def api_global_market():
    try:
        return jsonify(get_global_market(force=request.args.get("force") == "1"))
    except Exception as e:
        return jsonify({"error": str(e)}), 200


@app.route("/api/global-market/chart")
def api_gm_chart():
    sym    = request.args.get("sym", "").strip()
    period = request.args.get("period", "1mo")

    if not sym:
        return jsonify({"error": "sym 파라미터 필요"}), 400

    # 1d=일봉(2년, 200일MA 충분), 1wk=주봉(전체), 1mo=월봉(전체)
    _PERIOD_MAP = {
        "1d":  ("2y",  "1d"),
        "1wk": ("max", "1wk"),
        "1mo": ("max", "1mo"),
    }
    fetch_period, interval = _PERIOD_MAP.get(period, ("6mo", "1d"))

    try:
        h = yf.Ticker(sym).history(period=fetch_period, interval=interval)
        if len(h) == 0:
            return jsonify({"error": "데이터 없음"})

        candles = []
        for idx, row in h.iterrows():
            try:
                date_str = idx.to_pydatetime().strftime("%Y-%m-%d")
            except Exception:
                date_str = str(idx)[:10]

            o  = _gm_clean(row["Open"])
            hh = _gm_clean(row["High"])
            l  = _gm_clean(row["Low"])
            c  = _gm_clean(row["Close"])
            v  = int(row.get("Volume", 0) or 0)

            if all(x is not None for x in [o, hh, l, c]):
                candles.append({
                    "time":   date_str,
                    "open":   o,
                    "high":   hh,
                    "low":    l,
                    "close":  c,
                    "volume": v,
                })

        return jsonify({"sym": sym, "period": period, "candles": candles})
    except Exception as e:
        return jsonify({"error": str(e)})


# ── 관심종목 편집 ─────────────────────────────────────────────────
def save_watchlist(items):
    with open(_WATCHLIST_PATH, "w", encoding="utf-8") as f:
        json.dump(items, f, ensure_ascii=False, indent=2)
    global KR_STOCKS, US_STOCKS
    KR_STOCKS, US_STOCKS    = load_watchlist()
    _news_cache["data"]     = None   # 캐시 무효화
    _price_cache["data"]    = None


@app.route("/api/watchlist/add", methods=["POST"])
def api_watchlist_add():
    d      = request.get_json() or {}
    name   = (d.get("name",   "") or "").strip()
    ticker = (d.get("ticker", "") or "").strip().upper()
    market = (d.get("market", "") or "").strip().upper()

    if not name or not ticker:
        return jsonify({"error": "종목명과 티커를 입력해주세요."}), 400
    if market not in ("KR", "US"):
        return jsonify({"error": "시장 구분(KR/US)을 선택해주세요."}), 400

    with open(_WATCHLIST_PATH, encoding="utf-8") as f:
        items = json.load(f)

    if any(s["ticker"].upper() == ticker for s in items):
        return jsonify({"error": f"'{ticker}'은(는) 이미 등록된 종목입니다."}), 409

    items.append({"name": name, "ticker": ticker, "market": market})
    save_watchlist(items)
    return jsonify({"ok": True})


@app.route("/api/watchlist/remove", methods=["POST"])
def api_watchlist_remove():
    d      = request.get_json() or {}
    ticker = (d.get("ticker", "") or "").strip().upper()

    if not ticker:
        return jsonify({"error": "ticker가 필요합니다."}), 400

    with open(_WATCHLIST_PATH, encoding="utf-8") as f:
        items = json.load(f)

    new_items = [s for s in items if s["ticker"].upper() != ticker]
    if len(new_items) == len(items):
        return jsonify({"error": f"'{ticker}'을(를) 찾을 수 없습니다."}), 404

    save_watchlist(new_items)
    return jsonify({"ok": True})


# ── 라우트 ────────────────────────────────────────────────────────
@app.route("/")
def index():
    return render_template("index.html", news_ttl=NEWS_TTL, price_ttl=PRICE_TTL)


@app.route("/api/news")
def api_news():
    return jsonify(get_news(force=request.args.get("force") == "1"))


@app.route("/api/prices")
def api_prices():
    return jsonify(get_prices())


# ── 맞춤 뉴스 ─────────────────────────────────────────────────────
_personal_cache = {}   # frozenset(keywords) → {data, fetched_at}
PERSONAL_TTL    = 600  # 10분

@app.route("/api/personalized")
def api_personalized():
    kw_raw = request.args.get("kw", "").strip()
    if not kw_raw:
        return jsonify({"items": [], "keywords": []})

    keywords = [k.strip() for k in kw_raw.split(",") if k.strip()][:5]
    cache_key = frozenset(keywords)

    now = time.time()
    cached = _personal_cache.get(cache_key)
    if cached and now - cached["fetched_at"] < PERSONAL_TTL:
        return jsonify(cached["data"])

    def fetch(kw):
        try:
            items = naver_news(kw, n=15)
            for item in items:
                item["matched_kw"] = kw
            return items
        except Exception:
            return []

    with ThreadPoolExecutor(max_workers=5) as ex:
        results = list(ex.map(fetch, keywords))

    seen = set()
    all_items = []
    for items in results:
        for item in items:
            if item["link"] not in seen:
                seen.add(item["link"])
                all_items.append(item)

    all_items.sort(key=lambda x: x.get("pubDate", ""), reverse=True)

    result = {"items": all_items[:60], "keywords": keywords}
    _personal_cache[cache_key] = {"data": result, "fetched_at": now}
    return jsonify(result)


# ── 맞춤 뉴스 수혜 종목 분석 (Claude API) ────────────────────────
_benefit_cache = {}   # hash(titles) → {data, fetched_at}
BENEFIT_TTL    = 1800  # 30분

_BENEFIT_PROMPT = """당신은 한국 주식 시장 전문 애널리스트입니다.
아래는 투자자가 최근 관심 있게 읽은 경제·주식 뉴스 제목 목록입니다.

뉴스 제목:
{titles}

이 뉴스들을 분석해서 수혜를 받을 가능성이 높은 종목을 추천해주세요.
반드시 아래 JSON 형식으로만 응답하고, JSON 외 텍스트는 절대 포함하지 마세요.

{{
  "themes": [
    {{
      "theme": "테마명 (예: AI 반도체, 방산, 2차전지)",
      "reason": "이 테마가 주목받는 이유 1~2문장",
      "stocks": [
        {{
          "name": "종목명",
          "ticker": "티커 또는 종목코드 (모르면 빈 문자열)",
          "market": "KR 또는 US",
          "reason": "수혜 이유 1문장"
        }}
      ]
    }}
  ],
  "summary": "전체 시장 흐름 요약 2~3문장",
  "caution": "투자 시 주의사항 1문장"
}}"""


@app.route("/api/analyze-benefits", methods=["POST"])
def api_analyze_benefits():
    if not ANTHROPIC_KEY:
        return jsonify({"error": "ANTHROPIC_API_KEY가 설정되지 않았습니다."}), 500

    data   = request.get_json(silent=True) or {}
    titles = data.get("titles", [])
    if not titles:
        return jsonify({"error": "뉴스 제목이 없습니다."}), 400

    titles = titles[:40]  # 최대 40개
    cache_key = hash(tuple(titles))
    now = time.time()
    cached = _benefit_cache.get(cache_key)
    if cached and now - cached["fetched_at"] < BENEFIT_TTL:
        return jsonify(cached["data"])

    titles_text = "\n".join(f"- {t}" for t in titles)
    prompt = _BENEFIT_PROMPT.format(titles=titles_text)

    try:
        client = anthropic.Anthropic(api_key=ANTHROPIC_KEY)
        msg = client.messages.create(
            model="claude-haiku-4-5-20251001",
            max_tokens=1500,
            messages=[{"role": "user", "content": prompt}],
        )
        raw = msg.content[0].text.strip()
        # JSON만 추출
        m = re.search(r'\{[\s\S]*\}', raw)
        if not m:
            return jsonify({"error": "분석 결과 파싱 실패"}), 500
        result = json.loads(m.group())
        _benefit_cache[cache_key] = {"data": result, "fetched_at": now}
        return jsonify(result)
    except json.JSONDecodeError:
        return jsonify({"error": "JSON 파싱 오류"}), 500
    except anthropic.AuthenticationError:
        return jsonify({"error": "API 키가 올바르지 않습니다."}), 401
    except Exception as e:
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
