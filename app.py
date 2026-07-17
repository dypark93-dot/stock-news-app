import io
import os
import re
import json
import time
import datetime
import zipfile
import requests
import feedparser
import yfinance as yf
import xml.etree.ElementTree as ET
from urllib.parse import urlparse
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

# ── 캐시 설정 ─────────────────────────────────────────────────────
NEWS_TTL  = 600   # 10분
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
        us.append({"name": name, "symbol": sym, "ticker": sym, "news": news})

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
                for e in feedparser.parse(url, agent=ua).entries[:60]:
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

    # 1. Naver 뉴스 키워드 검색 (키워드당 5개)
    naver_pool = []
    for i, kw in enumerate(keywords):
        if i > 0:
            time.sleep(0.15)
        try:
            for art in naver_news(kw, n=5):
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


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
