"""API سامانه تکلیف کلاس ۹۰۱ - دبیرستان شهید بهشتی

FastAPI + SQLite + JWT. فرانت روی GitHub Pages و این سرویس روی Railway.
"""
import hashlib
import ipaddress
import json
import logging
import os
import re
import sqlite3
import time
import uuid
from collections import defaultdict, deque
from contextlib import asynccontextmanager
from datetime import date, datetime, timedelta
from typing import Dict, List, Optional
from zoneinfo import ZoneInfo

from fastapi import Depends, FastAPI, HTTPException, Request, Response
from fastapi.exceptions import RequestValidationError
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from fastapi.security import HTTPAuthorizationCredentials, HTTPBearer
from pydantic import BaseModel, Field

import security
from database import connect, get_db, init_db

log = logging.getLogger("homework")

TZ = ZoneInfo(os.getenv("APP_TZ", "Asia/Tehran"))
KEEP_DAYS = int(os.getenv("HOMEWORK_KEEP_DAYS", "45"))   # تکلیف‌های قدیمی‌تر حذف موند
MAX_AHEAD_DAYS = 120                                      # حداکثر فاصله تاریخ تکلیف از امروز
MAX_PERIODS = 8

# سهمیه‌ی روزانه (بر اساس تاریخ روز در منطقه‌ی زمانی APP_TZ؛ حذف کردن، سهمیه را برنمی‌گرداند)
STUDENT_HW_PER_DAY = int(os.getenv("STUDENT_HW_PER_DAY", "5"))        # ثبت تکلیف (برای هر تاریخی)
STUDENT_Q_PER_DAY = int(os.getenv("STUDENT_Q_PER_DAY", "2"))          # پرسیدن سؤال
STUDENT_A_PER_DAY = int(os.getenv("STUDENT_A_PER_DAY", "20"))         # پاسخ دادن
STAFF_Q_PER_DAY = 50
STAFF_A_PER_DAY = 200
MAX_QUESTIONS_PER_HW = 60
MAX_ANSWERS_PER_Q = 60

# امنیت
MAX_BODY = 64 * 1024                                                  # حداکثر حجم بدنه‌ی درخواست
GLOBAL_LIMIT = int(os.getenv("GLOBAL_LIMIT_PER_MIN", "600"))          # کل درخواست‌ها از هر IP در دقیقه
WRITE_LIMIT = int(os.getenv("WRITE_LIMIT_PER_MIN", "120"))            # درخواست‌های نوشتن از هر IP در دقیقه
USER_WRITE_LIMIT = int(os.getenv("USER_WRITE_LIMIT_PER_MIN", "20"))   # درخواست‌های نوشتن هر کاربر در دقیقه
TRUST_PROXY = os.getenv("TRUST_PROXY", "1") == "1"                    # پشت Railway هستیم؛ IP واقعی از X-Forwarded-For

ALLOWED_ORIGINS = [
    o.strip().rstrip("/")
    for o in os.getenv("ALLOWED_ORIGINS", "").split(",")
    if o.strip()
]

HID_RE = re.compile(r"^[0-9a-f]{32}$")
EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")
USERNAME_RE = re.compile(r"^[a-z0-9_]{3,20}$")
RESERVED_USERNAMES = {"admin", "administrator", "root", "teacher", "moderator", "support"}
STAFF_ROLES = ("teacher", "admin")   # نقش‌هایی که مثل معلم می‌توانند تکلیف و برنامه را مدیریت کنند


def today() -> date:
    return datetime.now(TZ).date()


def now_ms() -> int:
    return int(time.time() * 1000)


def to_fa(value) -> str:
    return str(value).translate(str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹"))


# ---------------------------------------------------------------- جدول‌های جدید
SCHEMA = """
CREATE TABLE IF NOT EXISTS questions (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    homework_id TEXT    NOT NULL,
    author_id   INTEGER NOT NULL,
    text        TEXT    NOT NULL,
    ip          TEXT    NOT NULL DEFAULT '',
    created_at  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_questions_hw ON questions(homework_id);
CREATE TABLE IF NOT EXISTS answers (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    question_id INTEGER NOT NULL,
    author_id   INTEGER NOT NULL,
    text        TEXT    NOT NULL,
    ip          TEXT    NOT NULL DEFAULT '',
    created_at  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_answers_q ON answers(question_id);
CREATE TABLE IF NOT EXISTS daily_usage (
    user_id INTEGER NOT NULL,
    day     TEXT    NOT NULL,
    kind    TEXT    NOT NULL,
    n       INTEGER NOT NULL DEFAULT 0,
    PRIMARY KEY (user_id, day, kind)
);
CREATE TABLE IF NOT EXISTS user_ips (
    user_id    INTEGER NOT NULL,
    ip         TEXT    NOT NULL,
    first_seen INTEGER NOT NULL,
    last_seen  INTEGER NOT NULL,
    hits       INTEGER NOT NULL DEFAULT 1,
    PRIMARY KEY (user_id, ip)
);
CREATE INDEX IF NOT EXISTS idx_user_ips_ip ON user_ips(ip);
CREATE TABLE IF NOT EXISTS bans (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    kind       TEXT    NOT NULL CHECK (kind IN ('user', 'ip')),
    value      TEXT    NOT NULL,
    reason     TEXT    NOT NULL DEFAULT '',
    created_at INTEGER NOT NULL,
    expires_at INTEGER,
    created_by TEXT    NOT NULL DEFAULT ''
);
CREATE UNIQUE INDEX IF NOT EXISTS idx_bans_kind_value ON bans(kind, value);
"""


def migrate(conn: sqlite3.Connection) -> None:
    """جدول‌های جدید (پرسش‌وپاسخ، سهمیه، IP، مسدودی) بدون دست زدن به database.py ساخته می‌شوند."""
    conn.executescript(SCHEMA)
    conn.commit()


# ---------------------------------------------------------------- راه‌اندازی
def ensure_teacher(conn: sqlite3.Connection) -> None:
    """حساب معلم از متغیرهای محیطی ساخته یا به‌روز می‌شود."""
    username = os.getenv("TEACHER_USERNAME", "").strip().lower()
    password = os.getenv("TEACHER_PASSWORD", "")
    if not username or not password:
        log.warning("TEACHER_USERNAME / TEACHER_PASSWORD تنظیم نشده؛ حساب معلم ساخته نشد.")
        return
    if not USERNAME_RE.match(username):
        log.error("TEACHER_USERNAME معتبر نیست (۳ تا ۲۰ حرف انگلیسی کوچک، عدد یا _).")
        return
    name = " ".join(os.getenv("TEACHER_NAME", "معلم کلاس").split()) or "معلم کلاس"
    email = os.getenv("TEACHER_EMAIL", "").strip().lower() or None

    row = conn.execute("SELECT id, password_hash FROM users WHERE username = ?", (username,)).fetchone()
    if row:
        if conn.execute("SELECT role FROM users WHERE id = ?", (row["id"],)).fetchone()["role"] == "admin":
            log.error("TEACHER_USERNAME با حساب مدیر یکی است؛ نادیده گرفته شد.")
            return
        if not security.verify_password(password, row["password_hash"]):
            conn.execute("UPDATE users SET password_hash = ? WHERE id = ?",
                         (security.hash_password(password), row["id"]))
        conn.execute("UPDATE users SET role = 'teacher', name = ? WHERE id = ?", (name, row["id"]))
    else:
        if email and conn.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
            email = None
        conn.execute(
            "INSERT INTO users (username, email, name, password_hash, role, created_at) "
            "VALUES (?, ?, ?, ?, 'teacher', ?)",
            (username, email, name, security.hash_password(password), now_ms()),
        )
    conn.commit()


def ensure_admin(conn: sqlite3.Connection) -> None:
    """حساب مدیر از متغیرهای محیطی ساخته یا به‌روز می‌شود (برای عوض کردن رمز، متغیر را عوض و دوباره دیپلوی کن)."""
    username = os.getenv("ADMIN_USERNAME", "").strip().lower()
    password = os.getenv("ADMIN_PASSWORD", "")
    if not username or not password:
        log.warning("ADMIN_USERNAME / ADMIN_PASSWORD تنظیم نشده؛ حساب مدیر ساخته نشد.")
        return
    if not USERNAME_RE.match(username):
        log.error("ADMIN_USERNAME معتبر نیست (۳ تا ۲۰ حرف انگلیسی کوچک، عدد یا _).")
        return
    if len(password) < 8:
        log.error("ADMIN_PASSWORD باید حداقل ۸ نویسه باشد؛ حساب مدیر ساخته نشد.")
        return
    name = " ".join(os.getenv("ADMIN_NAME", "مدیر سامانه").split()) or "مدیر سامانه"

    row = conn.execute("SELECT id, password_hash FROM users WHERE username = ?", (username,)).fetchone()
    if row:
        if not security.verify_password(password, row["password_hash"]):
            conn.execute("UPDATE users SET password_hash = ? WHERE id = ?",
                         (security.hash_password(password), row["id"]))
        conn.execute("UPDATE users SET role = 'admin', name = ? WHERE id = ?", (name, row["id"]))
    else:
        conn.execute(
            "INSERT INTO users (username, email, name, password_hash, role, created_at) "
            "VALUES (?, NULL, ?, ?, 'admin', ?)",
            (username, name, security.hash_password(password), now_ms()),
        )
    conn.commit()


def purge_orphans(conn: sqlite3.Connection) -> None:
    """پاک‌کردن داده‌های بی‌صاحب (حتی اگر کلید خارجی SQLite روشن نباشد)."""
    conn.execute("DELETE FROM questions WHERE homework_id NOT IN (SELECT id FROM homework) "
                 "OR author_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM answers WHERE question_id NOT IN (SELECT id FROM questions) "
                 "OR author_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM user_ips WHERE user_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM daily_usage WHERE user_id NOT IN (SELECT id FROM users)")


def purge_old(conn: sqlite3.Connection) -> None:
    cutoff = (today() - timedelta(days=KEEP_DAYS)).isoformat()
    conn.execute("DELETE FROM homework WHERE date < ?", (cutoff,))
    purge_orphans(conn)
    conn.execute("DELETE FROM daily_usage WHERE day < ?", ((today() - timedelta(days=3)).isoformat(),))
    conn.commit()


@asynccontextmanager
async def lifespan(_: FastAPI):
    logging.basicConfig(level=logging.INFO)
    security.require_secret()
    init_db()
    conn = connect()
    try:
        migrate(conn)
        ensure_admin(conn)
        ensure_teacher(conn)
        purge_old(conn)
    finally:
        conn.close()
    bans_cache.refresh(force=True)
    if not ALLOWED_ORIGINS:
        log.warning("ALLOWED_ORIGINS تنظیم نشده؛ CORS برای همه‌ی مبدأها باز است. آدرس GitHub Pages را تنظیم کن.")
    yield


app = FastAPI(
    title="Class Homework API",
    lifespan=lifespan,
    docs_url="/docs" if os.getenv("ENABLE_DOCS") == "1" else None,
    redoc_url=None,
    openapi_url="/openapi.json" if os.getenv("ENABLE_DOCS") == "1" else None,
)

@app.exception_handler(RequestValidationError)
async def validation_handler(_: Request, __: RequestValidationError):
    return JSONResponse(status_code=422, content={"detail": "اطلاعات ارسال‌شده معتبر نیست."})


@app.exception_handler(Exception)
async def unhandled_handler(request: Request, exc: Exception):
    log.exception("خطای پیش‌بینی‌نشده در %s %s", request.method, request.url.path)
    return JSONResponse(status_code=500, content={"detail": "خطای داخلی سرور. کمی بعد دوباره تلاش کن."})


# ---------------------------------------------------------------- محدودسازی تلاش‌ها
_hits: Dict[str, deque] = defaultdict(deque)
_last_gc = 0.0


def _gc() -> None:
    """کلیدهای قدیمی را پاک می‌کند (بدون ریست‌کردن محدودیت بقیه)."""
    global _last_gc
    now = time.time()
    if now - _last_gc < 60:
        return
    _last_gc = now
    for k in [k for k, q in _hits.items() if not q or q[-1] < now - 3600]:
        _hits.pop(k, None)
    if len(_hits) > 50000:  # آخرین راه جلوگیری از پر شدن حافظه
        _hits.clear()


def _prune(key: str, window: int) -> deque:
    _gc()
    q = _hits[key]
    cutoff = time.time() - window
    while q and q[0] < cutoff:
        q.popleft()
    return q


def check_limit(key: str, limit: int, window: int, message: Optional[str] = None) -> None:
    if len(_prune(key, window)) >= limit:
        raise HTTPException(429, message or "تلاش‌ها زیاد بود. چند دقیقه بعد دوباره امتحان کن.")


def add_hit(key: str, window: int) -> None:
    _prune(key, window).append(time.time())


_CGNAT = ipaddress.ip_network("100.64.0.0/10")


def _internal(ip) -> bool:
    return ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip in _CGNAT


def client_ip(request: Request) -> str:
    """IP واقعی کاربر. پشت پراکسی (Railway) از راست‌ترین IP عمومی در X-Forwarded-For استفاده می‌شود
    (مقدارهای سمت چپ را کاربر می‌تواند جعل کند، پس به آن‌ها اعتماد نمی‌کنیم)."""
    peer = request.client.host if request.client else "unknown"
    if TRUST_PROXY:
        parts = [p.strip() for p in request.headers.get("x-forwarded-for", "").split(",") if p.strip()]
        for cand in reversed(parts):
            try:
                ip = ipaddress.ip_address(cand)
            except ValueError:
                continue
            if not _internal(ip):
                return str(ip)
    return peer


# ---------------------------------------------------------------- مسدودسازی
def active_ban(db: sqlite3.Connection, kind: str, value: str) -> Optional[sqlite3.Row]:
    return db.execute(
        "SELECT id, reason, expires_at FROM bans WHERE kind = ? AND value = ? "
        "AND (expires_at IS NULL OR expires_at > ?)", (kind, value, now_ms()),
    ).fetchone()


def ban_message(ban: sqlite3.Row, who: str) -> str:
    msg = f"{who} مسدود شده است."
    if ban["expires_at"]:
        hours = max(1, -(-(ban["expires_at"] - now_ms()) // 3_600_000))
        msg += f" (حدود {to_fa(hours)} ساعت دیگر باز می‌شود)" if hours < 48 else f" (حدود {to_fa(-(-hours // 24))} روز دیگر باز می‌شود)"
    if ban["reason"]:
        msg += f" دلیل: {ban['reason']}"
    return msg


class BanCache:
    """فهرست IPهای مسدود در حافظه (هر چند ثانیه از دیتابیس تازه می‌شود تا هر درخواست به دیتابیس نخورد)."""
    TTL = 15

    def __init__(self) -> None:
        self.ips: set = set()
        self.loaded = 0.0

    def refresh(self, force: bool = False) -> None:
        if not force and time.time() - self.loaded < self.TTL:
            return
        conn = connect()
        try:
            conn.execute("DELETE FROM bans WHERE expires_at IS NOT NULL AND expires_at <= ?", (now_ms(),))
            conn.commit()
            self.ips = {r["value"] for r in conn.execute("SELECT value FROM bans WHERE kind = 'ip'")}
        except sqlite3.Error:
            log.exception("خواندن فهرست مسدودی‌ها ناموفق بود")
        finally:
            conn.close()
        self.loaded = time.time()

    def is_banned(self, ip: str) -> bool:
        self.refresh()
        return ip in self.ips


bans_cache = BanCache()

_NO_STORE_PREFIXES = ("/api/auth", "/api/admin", "/api/quota")


@app.middleware("http")
async def guard(request: Request, call_next):
    path, method = request.url.path, request.method
    if method != "OPTIONS" and path != "/api/health":
        ip = client_ip(request)
        if bans_cache.is_banned(ip):
            return JSONResponse(status_code=403, content={"detail": "دسترسی این شبکه به سامانه مسدود شده است."})
        length = request.headers.get("content-length", "")
        if length.isdigit() and int(length) > MAX_BODY:
            return JSONResponse(status_code=413, content={"detail": "حجم درخواست بیش از حد است."})
        try:
            check_limit(f"g:{ip}", GLOBAL_LIMIT, 60, "درخواست‌ها از این شبکه زیاد است. کمی صبر کن.")
            add_hit(f"g:{ip}", 60)
            if method in ("POST", "PUT", "DELETE"):
                check_limit(f"w:{ip}", WRITE_LIMIT, 60, "درخواست‌ها از این شبکه زیاد است. کمی صبر کن.")
                add_hit(f"w:{ip}", 60)
        except HTTPException as e:
            return JSONResponse(status_code=e.status_code, content={"detail": e.detail}, headers={"Retry-After": "30"})

    response = await call_next(request)
    h = response.headers
    h["X-Content-Type-Options"] = "nosniff"
    h["X-Frame-Options"] = "DENY"
    h["Referrer-Policy"] = "no-referrer"
    h["Permissions-Policy"] = "camera=(), microphone=(), geolocation=()"
    h["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    if os.getenv("ENABLE_DOCS") != "1":
        h["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    if path.startswith(_NO_STORE_PREFIXES):
        h["Cache-Control"] = "no-store"
    return response


# CORS آخر از همه اضافه می‌شود تا بیرونی‌ترین لایه باشد (پاسخ‌های ۴۰۳/۴۲۹ هم هدر CORS بگیرند)
app.add_middleware(
    CORSMiddleware,
    allow_origins=ALLOWED_ORIGINS or ["*"],   # در تولید ALLOWED_ORIGINS را حتماً تنظیم کن
    allow_credentials=False,                  # احراز هویت با هدر Authorization است، نه کوکی
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["Authorization", "Content-Type"],
    max_age=3600,
)


# ---------------------------------------------------------------- مدل‌ها و کمکی‌ها
class RegisterIn(BaseModel):
    name: str = Field(..., max_length=100)
    email: str = Field(..., max_length=300)
    username: str = Field(..., max_length=100)
    password: str = Field(..., max_length=200)


class LoginIn(BaseModel):
    username: str = Field(..., max_length=300)  # نام کاربری یا ایمیل
    password: str = Field(..., max_length=200)


class HomeworkIn(BaseModel):
    date: str = Field(..., max_length=20)
    subject: str = Field(..., max_length=100)
    text: str = Field(..., max_length=3000)
    day: Optional[int] = None  # نادیده گرفته می‌شود؛ از روی تاریخ محاسبه می‌شود


class TeacherIn(BaseModel):
    name: str = Field(..., max_length=100)
    username: str = Field(..., max_length=100)
    password: str = Field(..., max_length=200)
    subject: str = Field("", max_length=100)


class TeacherUpdateIn(BaseModel):
    name: str = Field(..., max_length=100)
    subject: str = Field("", max_length=100)
    password: Optional[str] = Field(None, max_length=200)  # خالی = رمز عوض نشود


class PeriodIn(BaseModel):
    subject: str = Field(..., max_length=100)
    teacher: str = Field("", max_length=100)


class QuestionIn(BaseModel):
    text: str = Field(..., max_length=2000)


class AnswerIn(BaseModel):
    text: str = Field(..., max_length=2000)


class BanIn(BaseModel):
    kind: str = Field(..., max_length=10)       # user | ip
    value: str = Field(..., max_length=100)     # نام کاربری یا آدرس IP
    reason: str = Field("", max_length=200)
    hours: Optional[int] = None                 # خالی یا ۰ = همیشگی


# نویسه‌های کنترلی و جهت‌دهنده‌ی نامرئی (برای جلوگیری از جعل ظاهر متن). ZWNJ (\u200c) نیم‌فاصله‌ی فارسی است و می‌ماند.
_BAD_CHARS = re.compile(r"[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f\u200b\u200e\u200f\u202a-\u202e\u2060-\u2069\ufeff]")


def clean(value: str, lo: int, hi: int, message: str) -> str:
    value = _BAD_CHARS.sub("", value)
    value = re.sub(r"[ \t\u200c]*\n[ \t\u200c]*", "\n", value.replace("\r", "")).strip()
    if not (lo <= len(value) <= hi):
        raise HTTPException(400, message)
    return value


def one_line(value: str, lo: int, hi: int, message: str) -> str:
    return clean(" ".join(value.split()), lo, hi, message)


def user_out(row: sqlite3.Row) -> dict:
    return {"username": row["username"], "name": row["name"], "role": row["role"], "subject": row["subject"]}


def teacher_out(row: sqlite3.Row) -> dict:
    return {"username": row["username"], "name": row["name"], "subject": row["subject"],
            "createdAt": row["created_at"]}


def clean_subject(value: str) -> str:
    value = " ".join(value.split())
    if len(value) > 30:
        raise HTTPException(400, "نام درس حداکثر ۳۰ حرف باشد.")
    return value


COMMON_PASSWORDS = {
    "12345678", "123456789", "1234567890", "password", "password1", "qwerty123", "11111111", "00000000",
    "iloveyou", "12341234", "123123123", "987654321", "abcd1234", "asdfghjkl", "qwertyuiop", "1q2w3e4r",
}


def check_password(password: str, username: str, email: str = "") -> None:
    if not (8 <= len(password) <= 64):
        raise HTTPException(400, "رمز عبور باید ۸ تا ۶۴ نویسه باشد.")
    low = password.lower()
    if password.isdigit():
        raise HTTPException(400, "رمز عبور نباید فقط عدد باشد.")
    if low in COMMON_PASSWORDS or len(set(low)) <= 2:
        raise HTTPException(400, "این رمز عبور خیلی ساده است؛ یکی سخت‌تر انتخاب کن.")
    if low in (username, email.split("@")[0]):
        raise HTTPException(400, "رمز عبور نباید با نام کاربری یا ایمیل یکی باشد.")


_FA_MAP = str.maketrans({"ي": "ی", "ك": "ک", "ة": "ه", "ۀ": "ه", "أ": "ا", "إ": "ا", "ؤ": "و"})


def _norm(text: str) -> str:
    return re.sub(r"[\u064b-\u065f\u0670\u200c\u200d_\W\d]+", "", text.translate(_FA_MAP).lower())


# کلمه‌های ممنوع از متغیر BLOCKED_WORDS (جداشده با ویرگول) خوانده می‌شود؛ پیام شامل آن‌ها ثبت نمی‌شود.
BLOCKED = [w for w in (_norm(x) for x in os.getenv("BLOCKED_WORDS", "").split(",")) if len(w) >= 2]


def check_blocked(text: str) -> None:
    n = _norm(text)
    if any(w in n for w in BLOCKED):
        raise HTTPException(400, "متن شامل کلمه‌ی نامناسب است. مؤدبانه بنویس.")


QUOTA_MSG = {
    "homework": "سهمیه‌ی ثبت تکلیف امروزت ({n} تکلیف) تمام شده است. فردا دوباره امتحان کن.",
    "question": "سهمیه‌ی سؤال امروزت ({n} سؤال) تمام شده است. فردا دوباره امتحان کن.",
    "answer": "امروز بیش از حد پاسخ داده‌ای ({n} پاسخ). فردا دوباره امتحان کن.",
}


def quota_limit(user: sqlite3.Row, kind: str) -> Optional[int]:
    staff = user["role"] in STAFF_ROLES
    if kind == "homework":
        return None if staff else STUDENT_HW_PER_DAY
    if kind == "question":
        return STAFF_Q_PER_DAY if staff else STUDENT_Q_PER_DAY
    return STAFF_A_PER_DAY if staff else STUDENT_A_PER_DAY


def consume(db: sqlite3.Connection, user: sqlite3.Row, kind: str) -> None:
    """یک واحد از سهمیه‌ی امروز را اتمی مصرف می‌کند؛ اگر تمام شده باشد خطای ۴۲۹ می‌دهد."""
    limit = quota_limit(user, kind)
    if limit is None:
        return
    day = today().isoformat()
    db.execute("INSERT OR IGNORE INTO daily_usage (user_id, day, kind, n) VALUES (?, ?, ?, 0)", (user["id"], day, kind))
    cur = db.execute("UPDATE daily_usage SET n = n + 1 WHERE user_id = ? AND day = ? AND kind = ? AND n < ?",
                     (user["id"], day, kind, limit))
    if cur.rowcount == 0:
        raise HTTPException(429, QUOTA_MSG[kind].format(n=to_fa(limit)))


def quota_out(db: sqlite3.Connection, user: sqlite3.Row) -> dict:
    used = {r["kind"]: r["n"] for r in db.execute(
        "SELECT kind, n FROM daily_usage WHERE user_id = ? AND day = ?", (user["id"], today().isoformat()))}
    return {k: {"used": used.get(k, 0), "limit": quota_limit(user, k)} for k in ("homework", "question", "answer")}


def touch_ip(db: sqlite3.Connection, uid: int, ip: str) -> None:
    """هر IP که یک حساب با آن وارد شده یا درخواست داده را ثبت می‌کند (حداکثر ۲۰ IP آخر برای هر حساب)."""
    if not ip or ip == "unknown":
        return
    now = now_ms()
    cur = db.execute("UPDATE user_ips SET last_seen = ?, hits = hits + 1 WHERE user_id = ? AND ip = ? AND last_seen < ?",
                     (now, uid, ip, now - 300_000))
    changed = cur.rowcount > 0
    if not changed:
        cur = db.execute("INSERT OR IGNORE INTO user_ips (user_id, ip, first_seen, last_seen, hits) VALUES (?, ?, ?, ?, 1)",
                         (uid, ip, now, now))
        changed = cur.rowcount > 0
        if changed:
            db.execute("DELETE FROM user_ips WHERE user_id = ? AND ip NOT IN "
                       "(SELECT ip FROM user_ips WHERE user_id = ? ORDER BY last_seen DESC LIMIT 20)", (uid, uid))
    if changed:
        db.commit()


def js_weekday(d: date) -> int:
    """مثل Date.getDay() در جاوااسکریپت: یکشنبه=۰ ... شنبه=۶"""
    return (d.weekday() + 1) % 7


HW_SELECT = (
    "SELECT h.id, h.date, h.subject, h.text, h.created_at, "
    "u.username, u.name, u.role, u.subject AS author_subject, "
    "(SELECT COUNT(*) FROM questions q WHERE q.homework_id = h.id) AS q_count "
    "FROM homework h JOIN users u ON u.id = h.author_id"
)


def hw_out(r: sqlite3.Row) -> dict:
    return {
        "id": r["id"],
        "day": js_weekday(date.fromisoformat(r["date"])),
        "date": r["date"],
        "subject": r["subject"],
        "text": r["text"],
        "author": r["name"],
        "authorRole": r["role"],
        "authorSubject": r["author_subject"],
        "authorId": r["username"],
        "createdAt": r["created_at"],
        "qCount": r["q_count"],
    }


def etag_json(request: Request, payload) -> Response:
    """پاسخ JSON با ETag؛ اگر چیزی عوض نشده باشد ۳۰۴ می‌دهد تا ترافیک کم شود."""
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode()
    tag = '"' + hashlib.sha1(body).hexdigest()[:24] + '"'
    headers = {"ETag": tag, "Cache-Control": "no-cache"}
    if request.headers.get("if-none-match") == tag:
        return Response(status_code=304, headers=headers)
    return Response(body, media_type="application/json", headers=headers)


bearer = HTTPBearer(auto_error=False)


def current_user(
    request: Request,
    cred: Optional[HTTPAuthorizationCredentials] = Depends(bearer),
    db: sqlite3.Connection = Depends(get_db),
) -> sqlite3.Row:
    if cred is None:
        raise HTTPException(401, "اول وارد شو.")
    uid = security.decode_token(cred.credentials)
    row = db.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone() if uid else None
    if row is None:
        raise HTTPException(401, "نشست معتبر نیست. دوباره وارد شو.")
    ban = active_ban(db, "user", row["username"])
    if ban:
        raise HTTPException(403, ban_message(ban, "حساب تو"))
    if request.method not in ("GET", "HEAD", "OPTIONS"):
        key = f"uw:{row['id']}"
        check_limit(key, USER_WRITE_LIMIT, 60, "درخواست‌های تو زیاد است. کمی صبر کن.")
        add_hit(key, 60)
    touch_ip(db, row["id"], client_ip(request))
    return row


def teacher_only(user: sqlite3.Row = Depends(current_user)) -> sqlite3.Row:
    if user["role"] not in STAFF_ROLES:
        raise HTTPException(403, "فقط معلم می‌تواند این کار را انجام دهد.")
    return user


def admin_only(user: sqlite3.Row = Depends(current_user)) -> sqlite3.Row:
    if user["role"] != "admin":
        raise HTTPException(403, "فقط مدیر می‌تواند این کار را انجام دهد.")
    return user


def parse_date(value: str, allow_past_equal: Optional[str] = None) -> str:
    try:
        d = date.fromisoformat(value.strip())
    except (ValueError, AttributeError):
        raise HTTPException(400, "تاریخ معتبر نیست.")
    t = today()
    if d < t and value.strip() != allow_past_equal:
        raise HTTPException(400, "نمی‌شود برای تاریخ گذشته تکلیف ثبت کرد.")
    if d > t + timedelta(days=MAX_AHEAD_DAYS):
        raise HTTPException(400, "این تاریخ بیش از حد دور است.")
    return d.isoformat()


# ---------------------------------------------------------------- مسیرها
@app.get("/api/health")
def health():
    return {"ok": True}


@app.post("/api/auth/register")
def register(body: RegisterIn, request: Request, db: sqlite3.Connection = Depends(get_db)):
    ip_key = f"reg:{client_ip(request)}"
    check_limit(ip_key, limit=10, window=3600)

    name = one_line(body.name, 3, 40, "نام و نام‌خانوادگی باید ۳ تا ۴۰ حرف باشد.")
    email = body.email.strip().lower()
    if len(email) > 254 or not EMAIL_RE.match(email):
        raise HTTPException(400, "ایمیل معتبر نیست.")
    username = body.username.strip().lower()
    if not USERNAME_RE.match(username):
        raise HTTPException(400, "نام کاربری ۳ تا ۲۰ حرف انگلیسی، عدد یا _ باشد.")
    if username in RESERVED_USERNAMES:
        raise HTTPException(400, "این نام کاربری مجاز نیست.")
    check_password(body.password, username, email)

    if db.execute("SELECT 1 FROM users WHERE username = ?", (username,)).fetchone():
        raise HTTPException(409, "این نام کاربری قبلاً گرفته شده است.")
    if db.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        raise HTTPException(409, "با این ایمیل قبلاً ثبت‌نام شده است.")

    try:
        cur = db.execute(
            "INSERT INTO users (username, email, name, password_hash, role, created_at) "
            "VALUES (?, ?, ?, ?, 'student', ?)",
            (username, email, name, security.hash_password(body.password), now_ms()),
        )
        db.commit()
    except sqlite3.IntegrityError:
        raise HTTPException(409, "این نام کاربری یا ایمیل قبلاً ثبت شده است.")

    add_hit(ip_key, 3600)
    row = db.execute("SELECT * FROM users WHERE id = ?", (cur.lastrowid,)).fetchone()
    touch_ip(db, row["id"], client_ip(request))
    return {"token": security.create_token(row["id"]), "user": user_out(row)}


@app.post("/api/auth/login")
def login(body: LoginIn, request: Request, db: sqlite3.Connection = Depends(get_db)):
    ident = body.username.strip().lower()[:254]
    ip = client_ip(request)
    ip_key, id_key = f"login-ip:{ip}", f"login:{ip}:{ident}"
    any_key = f"login-id:{ident}"   # حمله‌ی پخش‌شده از چند IP روی یک حساب
    check_limit(ip_key, limit=40, window=300)
    check_limit(id_key, limit=8, window=300)
    check_limit(any_key, limit=25, window=900)

    row = db.execute("SELECT * FROM users WHERE username = ? OR email = ?", (ident, ident)).fetchone()
    ok = False
    if row:
        ok = security.verify_password(body.password[:200], row["password_hash"])
    else:
        security.dummy_verify(body.password[:200])
    if not ok:
        add_hit(ip_key, 300)
        add_hit(id_key, 300)
        add_hit(any_key, 900)
        raise HTTPException(401, "نام کاربری یا رمز عبور درست نیست.")

    ban = active_ban(db, "user", row["username"])
    if ban:
        raise HTTPException(403, ban_message(ban, "حساب تو"))
    _hits.pop(id_key, None)
    touch_ip(db, row["id"], ip)
    return {"token": security.create_token(row["id"]), "user": user_out(row)}


@app.get("/api/auth/me")
def me(user: sqlite3.Row = Depends(current_user)):
    return {"user": user_out(user)}


@app.get("/api/schedule")
def get_schedule(request: Request, db: sqlite3.Connection = Depends(get_db)):
    rows = db.execute("SELECT day, periods FROM schedule ORDER BY day").fetchall()
    return etag_json(request, {str(r["day"]): json.loads(r["periods"]) for r in rows})


@app.put("/api/schedule")
def put_schedule(
    body: Dict[str, List[PeriodIn]],
    _: sqlite3.Row = Depends(teacher_only),
    db: sqlite3.Connection = Depends(get_db),
):
    result: Dict[str, list] = {}
    for key, periods in body.items():
        if not key.isdigit() or not (0 <= int(key) <= 6):
            raise HTTPException(400, "روز هفته معتبر نیست.")
        if len(periods) > MAX_PERIODS:
            raise HTTPException(400, f"هر روز حداکثر {MAX_PERIODS} زنگ دارد.")
        cleaned = []
        for p in periods:
            subject = " ".join(p.subject.split())
            teacher = " ".join(p.teacher.split())
            if not subject:
                continue
            if len(subject) > 30 or len(teacher) > 30:
                raise HTTPException(400, "نام درس و دبیر حداکثر ۳۰ حرف باشد.")
            cleaned.append({"subject": subject, "teacher": teacher})
        if cleaned:
            result[str(int(key))] = cleaned

    db.execute("DELETE FROM schedule")
    db.executemany(
        "INSERT INTO schedule (day, periods) VALUES (?, ?)",
        [(int(k), json.dumps(v, ensure_ascii=False)) for k, v in result.items()],
    )
    db.commit()
    return result


@app.get("/api/homework")
def list_homework(request: Request, db: sqlite3.Connection = Depends(get_db)):
    rows = db.execute(HW_SELECT + " ORDER BY h.date, h.created_at").fetchall()
    return etag_json(request, [hw_out(r) for r in rows])


@app.post("/api/homework", status_code=201)
def add_homework(
    body: HomeworkIn,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    d = parse_date(body.date)
    subject = one_line(body.subject, 1, 30, "نام درس باید ۱ تا ۳۰ حرف باشد.")
    text = clean(body.text, 1, 600, "توضیح تکلیف باید ۱ تا ۶۰۰ حرف باشد.")

    consume(db, user, "homework")   # دانش‌آموز: حداکثر STUDENT_HW_PER_DAY تکلیف در روز (برای هر تاریخی)

    hid = uuid.uuid4().hex
    db.execute(
        "INSERT INTO homework (id, date, subject, text, author_id, created_at) VALUES (?, ?, ?, ?, ?, ?)",
        (hid, d, subject, text, user["id"], now_ms()),
    )
    purge_old(db)
    row = db.execute(HW_SELECT + " WHERE h.id = ?", (hid,)).fetchone()
    return hw_out(row)


def _own_or_teacher(db: sqlite3.Connection, hid: str, user: sqlite3.Row) -> sqlite3.Row:
    row = db.execute("SELECT id, date, author_id FROM homework WHERE id = ?", (hid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این تکلیف پیدا نشد.")
    if user["role"] not in STAFF_ROLES and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط ثبت‌کننده یا معلم می‌تواند این تکلیف را تغییر دهد.")
    return row


@app.put("/api/homework/{hid}")
def update_homework(
    hid: str,
    body: HomeworkIn,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    existing = _own_or_teacher(db, hid, user)
    d = parse_date(body.date, allow_past_equal=existing["date"])
    subject = one_line(body.subject, 1, 30, "نام درس باید ۱ تا ۳۰ حرف باشد.")
    text = clean(body.text, 1, 600, "توضیح تکلیف باید ۱ تا ۶۰۰ حرف باشد.")
    db.execute("UPDATE homework SET date = ?, subject = ?, text = ? WHERE id = ?", (d, subject, text, hid))
    db.commit()
    return hw_out(db.execute(HW_SELECT + " WHERE h.id = ?", (hid,)).fetchone())


@app.delete("/api/homework/{hid}", status_code=204)
def delete_homework(
    hid: str,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    _own_or_teacher(db, hid, user)
    db.execute("DELETE FROM answers WHERE question_id IN (SELECT id FROM questions WHERE homework_id = ?)", (hid,))
    db.execute("DELETE FROM questions WHERE homework_id = ?", (hid,))
    db.execute("DELETE FROM homework WHERE id = ?", (hid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- مدیریت معلم‌ها (فقط مدیر)
@app.get("/api/admin/teachers")
def list_teachers(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    rows = db.execute(
        "SELECT username, name, subject, created_at FROM users WHERE role = 'teacher' ORDER BY created_at, id"
    ).fetchall()
    return JSONResponse([teacher_out(r) for r in rows], headers={"Cache-Control": "no-store"})


@app.post("/api/admin/teachers", status_code=201)
def create_teacher(
    body: TeacherIn,
    _: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    name = one_line(body.name, 3, 40, "نام و نام‌خانوادگی باید ۳ تا ۴۰ حرف باشد.")
    subject = clean_subject(body.subject)
    username = body.username.strip().lower()
    if not USERNAME_RE.match(username):
        raise HTTPException(400, "نام کاربری ۳ تا ۲۰ حرف انگلیسی، عدد یا _ باشد.")
    if username in RESERVED_USERNAMES:
        raise HTTPException(400, "این نام کاربری مجاز نیست.")
    if not (8 <= len(body.password) <= 64):
        raise HTTPException(400, "رمز عبور معلم باید ۸ تا ۶۴ نویسه باشد.")
    if db.execute("SELECT 1 FROM users WHERE username = ?", (username,)).fetchone():
        raise HTTPException(409, "این نام کاربری قبلاً گرفته شده است.")
    try:
        db.execute(
            "INSERT INTO users (username, email, name, password_hash, role, created_at, subject) "
            "VALUES (?, NULL, ?, ?, 'teacher', ?, ?)",
            (username, name, security.hash_password(body.password), now_ms(), subject),
        )
        db.commit()
    except sqlite3.IntegrityError:
        raise HTTPException(409, "این نام کاربری قبلاً گرفته شده است.")
    row = db.execute("SELECT username, name, subject, created_at FROM users WHERE username = ?", (username,)).fetchone()
    return teacher_out(row)


def _teacher_row(db: sqlite3.Connection, username: str) -> sqlite3.Row:
    row = db.execute(
        "SELECT id, username, name, subject, created_at FROM users WHERE username = ? AND role = 'teacher'",
        (username.strip().lower(),),
    ).fetchone()
    if row is None:
        raise HTTPException(404, "این معلم پیدا نشد.")
    return row


@app.put("/api/admin/teachers/{username}")
def update_teacher(
    username: str,
    body: TeacherUpdateIn,
    _: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    row = _teacher_row(db, username)
    name = one_line(body.name, 3, 40, "نام و نام‌خانوادگی باید ۳ تا ۴۰ حرف باشد.")
    subject = clean_subject(body.subject)
    if body.password and not (8 <= len(body.password) <= 64):
        raise HTTPException(400, "رمز عبور معلم باید ۸ تا ۶۴ نویسه باشد.")
    db.execute("UPDATE users SET name = ?, subject = ? WHERE id = ?", (name, subject, row["id"]))
    if body.password:
        db.execute("UPDATE users SET password_hash = ? WHERE id = ?",
                   (security.hash_password(body.password), row["id"]))
    db.commit()
    return teacher_out(_teacher_row(db, username))


@app.delete("/api/admin/teachers/{username}", status_code=204)
def delete_teacher(
    username: str,
    _: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    row = _teacher_row(db, username)
    db.execute("DELETE FROM users WHERE id = ?", (row["id"],))  # تکلیف‌های او هم (CASCADE) حذف می‌شود
    db.execute("DELETE FROM bans WHERE kind = 'user' AND value = ?", (row["username"],))
    purge_orphans(db)  # پرسش‌وپاسخ و ردپای IP او
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- سهمیه‌ی امروز
@app.get("/api/quota")
def my_quota(user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    return JSONResponse(quota_out(db, user), headers={"Cache-Control": "no-store"})


# ---------------------------------------------------------------- پرسش و پاسخ زیر هر تکلیف
def qa_out(r: sqlite3.Row) -> dict:
    return {
        "id": r["id"], "text": r["text"], "createdAt": r["created_at"],
        "author": r["name"], "authorId": r["username"],
        "authorRole": r["role"], "authorSubject": r["subject"],
    }


def _hw_exists(db: sqlite3.Connection, hid: str) -> None:
    if not HID_RE.match(hid) or not db.execute("SELECT 1 FROM homework WHERE id = ?", (hid,)).fetchone():
        raise HTTPException(404, "این تکلیف پیدا نشد.")


def _is_staff(user: sqlite3.Row) -> bool:
    return user["role"] in STAFF_ROLES


@app.get("/api/homework/{hid}/questions")
def list_questions(hid: str, db: sqlite3.Connection = Depends(get_db)):
    _hw_exists(db, hid)
    qs = db.execute(
        "SELECT q.id, q.text, q.created_at, u.username, u.name, u.role, u.subject "
        "FROM questions q JOIN users u ON u.id = q.author_id WHERE q.homework_id = ? ORDER BY q.created_at, q.id",
        (hid,),
    ).fetchall()
    answers: Dict[int, list] = defaultdict(list)
    if qs:
        marks = ",".join("?" * len(qs))
        for a in db.execute(
            "SELECT a.id, a.question_id, a.text, a.created_at, u.username, u.name, u.role, u.subject "
            f"FROM answers a JOIN users u ON u.id = a.author_id WHERE a.question_id IN ({marks}) "
            "ORDER BY a.created_at, a.id",
            [q["id"] for q in qs],
        ):
            answers[a["question_id"]].append(qa_out(a))
    out = [{**qa_out(q), "answers": answers.get(q["id"], [])} for q in qs]
    return JSONResponse(out, headers={"Cache-Control": "no-store"})


def _recent_duplicate(db: sqlite3.Connection, table: str, user_id: int, text: str) -> bool:
    return db.execute(f"SELECT 1 FROM {table} WHERE author_id = ? AND text = ? AND created_at > ?",
                      (user_id, text, now_ms() - 600_000)).fetchone() is not None


@app.post("/api/homework/{hid}/questions", status_code=201)
def add_question(
    hid: str,
    body: QuestionIn,
    request: Request,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    _hw_exists(db, hid)
    text = clean(body.text, 3, 300, "سؤال باید ۳ تا ۳۰۰ حرف باشد.")
    check_blocked(text)
    if _recent_duplicate(db, "questions", user["id"], text):
        raise HTTPException(409, "این سؤال را همین الان پرسیده‌ای.")
    if db.execute("SELECT COUNT(*) FROM questions WHERE homework_id = ?", (hid,)).fetchone()[0] >= MAX_QUESTIONS_PER_HW:
        raise HTTPException(400, "زیر این تکلیف تعداد سؤال‌ها به سقف رسیده است.")
    consume(db, user, "question")   # دانش‌آموز: حداکثر STUDENT_Q_PER_DAY سؤال در روز در کل
    cur = db.execute(
        "INSERT INTO questions (homework_id, author_id, text, ip, created_at) VALUES (?, ?, ?, ?, ?)",
        (hid, user["id"], text, client_ip(request), now_ms()),
    )
    db.commit()
    row = db.execute(
        "SELECT q.id, q.text, q.created_at, u.username, u.name, u.role, u.subject "
        "FROM questions q JOIN users u ON u.id = q.author_id WHERE q.id = ?", (cur.lastrowid,),
    ).fetchone()
    return {**qa_out(row), "answers": []}


@app.post("/api/questions/{qid}/answers", status_code=201)
def add_answer(
    qid: int,
    body: AnswerIn,
    request: Request,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    if not db.execute("SELECT 1 FROM questions WHERE id = ?", (qid,)).fetchone():
        raise HTTPException(404, "این سؤال پیدا نشد.")
    text = clean(body.text, 1, 500, "پاسخ باید ۱ تا ۵۰۰ حرف باشد.")
    check_blocked(text)
    if _recent_duplicate(db, "answers", user["id"], text):
        raise HTTPException(409, "این پاسخ را همین الان فرستاده‌ای.")
    if db.execute("SELECT COUNT(*) FROM answers WHERE question_id = ?", (qid,)).fetchone()[0] >= MAX_ANSWERS_PER_Q:
        raise HTTPException(400, "زیر این سؤال تعداد پاسخ‌ها به سقف رسیده است.")
    consume(db, user, "answer")
    cur = db.execute(
        "INSERT INTO answers (question_id, author_id, text, ip, created_at) VALUES (?, ?, ?, ?, ?)",
        (qid, user["id"], text, client_ip(request), now_ms()),
    )
    db.commit()
    row = db.execute(
        "SELECT a.id, a.text, a.created_at, u.username, u.name, u.role, u.subject "
        "FROM answers a JOIN users u ON u.id = a.author_id WHERE a.id = ?", (cur.lastrowid,),
    ).fetchone()
    return qa_out(row)


@app.delete("/api/questions/{qid}", status_code=204)
def delete_question(qid: int, user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    row = db.execute("SELECT id, author_id FROM questions WHERE id = ?", (qid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این سؤال پیدا نشد.")
    if not _is_staff(user) and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط پرسنده یا معلم می‌تواند این سؤال را حذف کند.")
    db.execute("DELETE FROM answers WHERE question_id = ?", (qid,))
    db.execute("DELETE FROM questions WHERE id = ?", (qid,))
    db.commit()
    return Response(status_code=204)


@app.delete("/api/answers/{aid}", status_code=204)
def delete_answer(aid: int, user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    row = db.execute("SELECT id, author_id FROM answers WHERE id = ?", (aid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این پاسخ پیدا نشد.")
    if not _is_staff(user) and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط پاسخ‌دهنده یا معلم می‌تواند این پاسخ را حذف کند.")
    db.execute("DELETE FROM answers WHERE id = ?", (aid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- پنل مدیر: حساب‌ها، IPها، مسدودی‌ها
NO_STORE = {"Cache-Control": "no-store"}


def ban_out(r: sqlite3.Row) -> dict:
    return {"id": r["id"], "kind": r["kind"], "value": r["value"], "reason": r["reason"],
            "createdAt": r["created_at"], "expiresAt": r["expires_at"], "createdBy": r["created_by"]}


def _active_bans(db: sqlite3.Connection) -> List[sqlite3.Row]:
    db.execute("DELETE FROM bans WHERE expires_at IS NOT NULL AND expires_at <= ?", (now_ms(),))
    db.commit()
    return db.execute("SELECT * FROM bans ORDER BY created_at DESC").fetchall()


@app.get("/api/admin/users")
def admin_users(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    banned = {r["value"]: r for r in _active_bans(db) if r["kind"] == "user"}
    rows = db.execute(
        "SELECT u.id, u.username, u.name, u.email, u.role, u.created_at, "
        "(SELECT ip FROM user_ips WHERE user_id = u.id ORDER BY last_seen DESC LIMIT 1) AS last_ip, "
        "(SELECT MAX(last_seen) FROM user_ips WHERE user_id = u.id) AS last_seen, "
        "(SELECT COUNT(*) FROM homework WHERE author_id = u.id) AS hw_count, "
        "(SELECT COUNT(*) FROM questions WHERE author_id = u.id) AS q_count, "
        "(SELECT COUNT(*) FROM answers WHERE author_id = u.id) AS a_count "
        "FROM users u ORDER BY u.created_at DESC, u.id DESC LIMIT 500"
    ).fetchall()
    out = []
    for r in rows:
        b = banned.get(r["username"])
        out.append({
            "username": r["username"], "name": r["name"], "email": r["email"], "role": r["role"],
            "createdAt": r["created_at"], "lastIp": r["last_ip"], "lastSeen": r["last_seen"],
            "homework": r["hw_count"], "questions": r["q_count"], "answers": r["a_count"],
            "banned": b is not None, "banId": b["id"] if b else None,
        })
    return JSONResponse(out, headers=NO_STORE)


@app.get("/api/admin/ips")
def admin_ips(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    banned = {r["value"]: r for r in _active_bans(db) if r["kind"] == "ip"}
    rows = db.execute(
        "SELECT ip, MIN(first_seen) AS first_seen, MAX(last_seen) AS last_seen, SUM(hits) AS hits, "
        "COUNT(DISTINCT user_id) AS accounts FROM user_ips GROUP BY ip ORDER BY last_seen DESC LIMIT 300"
    ).fetchall()
    who: Dict[str, list] = defaultdict(list)
    for r in db.execute(
        "SELECT ui.ip, u.username, u.name, u.role FROM user_ips ui JOIN users u ON u.id = ui.user_id "
        "ORDER BY ui.last_seen DESC"
    ):
        if len(who[r["ip"]]) < 8:
            who[r["ip"]].append({"username": r["username"], "name": r["name"], "role": r["role"]})
    out = [{
        "ip": r["ip"], "firstSeen": r["first_seen"], "lastSeen": r["last_seen"], "hits": r["hits"],
        "accountCount": r["accounts"], "accounts": who.get(r["ip"], []),
        "banned": r["ip"] in banned, "banId": banned[r["ip"]]["id"] if r["ip"] in banned else None,
    } for r in rows]
    return JSONResponse(out, headers=NO_STORE)


@app.get("/api/admin/bans")
def admin_bans(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    return JSONResponse([ban_out(r) for r in _active_bans(db)], headers=NO_STORE)


@app.post("/api/admin/bans", status_code=201)
def admin_add_ban(
    body: BanIn,
    request: Request,
    admin: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    kind = body.kind.strip().lower()
    reason = one_line(body.reason, 0, 120, "دلیل حداکثر ۱۲۰ حرف باشد.") if body.reason.strip() else ""
    hours = body.hours or 0
    if hours < 0 or hours > 24 * 365:
        raise HTTPException(400, "مدت مسدودی معتبر نیست.")
    expires = now_ms() + hours * 3_600_000 if hours else None

    if kind == "user":
        value = body.value.strip().lower()
        target = db.execute("SELECT id, role FROM users WHERE username = ?", (value,)).fetchone()
        if target is None:
            raise HTTPException(404, "این کاربر پیدا نشد.")
        if target["role"] == "admin" or target["id"] == admin["id"]:
            raise HTTPException(400, "حساب مدیر را نمی‌شود مسدود کرد.")
    elif kind == "ip":
        try:
            value = str(ipaddress.ip_address(body.value.strip()))
        except ValueError:
            raise HTTPException(400, "آدرس IP معتبر نیست.")
        if value == client_ip(request) or db.execute(
            "SELECT 1 FROM user_ips ui JOIN users u ON u.id = ui.user_id WHERE ui.ip = ? AND u.role = 'admin'", (value,)
        ).fetchone():
            raise HTTPException(400, "این IP متعلق به مدیر است؛ مسدودکردنش خودت را بیرون می‌اندازد.")
    else:
        raise HTTPException(400, "نوع مسدودی معتبر نیست.")

    db.execute("DELETE FROM bans WHERE kind = ? AND value = ?", (kind, value))
    cur = db.execute(
        "INSERT INTO bans (kind, value, reason, created_at, expires_at, created_by) VALUES (?, ?, ?, ?, ?, ?)",
        (kind, value, reason, now_ms(), expires, admin["username"]),
    )
    db.commit()
    bans_cache.refresh(force=True)
    return ban_out(db.execute("SELECT * FROM bans WHERE id = ?", (cur.lastrowid,)).fetchone())


@app.delete("/api/admin/bans/{bid}", status_code=204)
def admin_remove_ban(bid: int, _: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    if not db.execute("SELECT 1 FROM bans WHERE id = ?", (bid,)).fetchone():
        raise HTTPException(404, "این مسدودی پیدا نشد.")
    db.execute("DELETE FROM bans WHERE id = ?", (bid,))
    db.commit()
    bans_cache.refresh(force=True)
    return Response(status_code=204)


@app.get("/api/admin/qa")
def admin_qa(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    """آخرین سؤال‌ها و پاسخ‌ها برای بازبینی و حذف محتوای نامناسب."""
    items = []
    for r in db.execute(
        "SELECT q.id, q.text, q.ip, q.created_at, h.subject, h.date, u.username, u.name "
        "FROM questions q JOIN homework h ON h.id = q.homework_id JOIN users u ON u.id = q.author_id "
        "ORDER BY q.created_at DESC LIMIT 60"
    ):
        items.append({"type": "question", "id": r["id"], "text": r["text"], "ip": r["ip"], "createdAt": r["created_at"],
                      "author": r["name"], "authorId": r["username"], "context": f"{r['subject']} · {r['date']}"})
    for r in db.execute(
        "SELECT a.id, a.text, a.ip, a.created_at, q.text AS qtext, u.username, u.name "
        "FROM answers a JOIN questions q ON q.id = a.question_id JOIN users u ON u.id = a.author_id "
        "ORDER BY a.created_at DESC LIMIT 60"
    ):
        items.append({"type": "answer", "id": r["id"], "text": r["text"], "ip": r["ip"], "createdAt": r["created_at"],
                      "author": r["name"], "authorId": r["username"], "context": "پاسخ به: " + r["qtext"][:60]})
    items.sort(key=lambda x: x["createdAt"], reverse=True)
    return JSONResponse(items[:80], headers=NO_STORE)
