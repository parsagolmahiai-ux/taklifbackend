"""API سامانه تکلیف کلاس ۹۰۱ - دبیرستان شهید بهشتی

FastAPI + SQLite + JWT + Atria-Dawn AI Moderation & Study Assistant.
فرانت روی GitHub Pages و این سرویس روی Railway.
"""
import hashlib
import ipaddress
import json
import logging
import os
import re
import sqlite3
import time
import urllib.error
import urllib.request
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
KEEP_DAYS = int(os.getenv("HOMEWORK_KEEP_DAYS", "45"))   # تکلیف‌های قدیمی‌تر حذف می‌شوند
MAX_AHEAD_DAYS = 120                                      # حداکثر فاصله تاریخ تکلیف از امروز
MAX_PERIODS = 8

# سهمیه‌ی روزانه پیش‌فرض (بر اساس تاریخ روز در منطقه‌ی زمانی APP_TZ)
STUDENT_HW_PER_DAY = int(os.getenv("STUDENT_HW_PER_DAY", "5"))        # ثبت تکلیف
STUDENT_Q_PER_DAY = int(os.getenv("STUDENT_Q_PER_DAY", "2"))          # پرسیدن سؤال
STUDENT_A_PER_DAY = int(os.getenv("STUDENT_A_PER_DAY", "20"))         # پاسخ دادن
STUDENT_AI_PER_DAY = int(os.getenv("STUDENT_AI_PER_DAY", "0"))        # چت هوش مصنوعی (پیش‌فرض ۰ برای دانش‌آموز؛ فقط با اجازه ادمین)
TEACHER_AI_PER_DAY = int(os.getenv("TEACHER_AI_PER_DAY", "0"))        # چت هوش مصنوعی برای معلم (۰ پیش‌فرض؛ ادمین نامحدود)
STAFF_Q_PER_DAY = 50
STAFF_A_PER_DAY = 200
MAX_QUESTIONS_PER_HW = 60
MAX_ANSWERS_PER_Q = 60

# تنظیمات هوش مصنوعی Atria-Dawn
ATRIA_API_KEY = os.getenv("ATRIA_API_KEY", "").strip()
ATRIA_BASE_URL = os.getenv("ATRIA_BASE_URL", "https://api.atria-asi.ai/v1").rstrip("/")
ATRIA_MODEL = os.getenv("ATRIA_MODEL", "Atria-Dawn").strip() or "Atria-Dawn"
AI_MODERATION_ENABLED = os.getenv("AI_MODERATION_ENABLED", "1") == "1"
AUTO_BAN_STRIKES = int(os.getenv("AUTO_BAN_STRIKES", "3"))            # پس از ۳ تخلف در ۲۴ ساعت، مسدودسازی خودکار

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
DEVICE_ID_RE = re.compile(r"^[a-zA-Z0-9_-]{8,64}$")
PERSIAN_NAME_RE = re.compile(r"^[\u0600-\u06FF\u200c\s]+$")

RESERVED_USERNAMES = {
    "admin", "administrator", "root", "teacher", "moderator", "support",
    "system", "bot", "ai", "taklif", "school", "beheshti", "shahid",
    "modir", "moalem", "dabir", "ostad",
}
STAFF_ROLES = ("teacher", "admin")

# الگوهای ممنوع برای جلوگیری از جعل هویت آقای مرادی (معلم ریاضی) و سایر عناوین معلم/مدیر
FORBIDDEN_TEACHER_PATTERNS = [
    "مرادی", "مرادي", "ابوالفضل مرادی", "ابولفضل مرادی", "ابوالفضل", "ابولفضل",
    "moradi", "mooradi", "moraadi", "moardi", "mrd", "mr_moradi", "amoradi", "a_moradi",
    "abolfazl", "aboulfazl", "ostad", "moalem", "dabir", "modir",
    "استاد", "معلم", "دبیر", "مدیر", "آقای", "اقای", "خانم", "دکتر", "مهندس",
]


def today() -> date:
    return datetime.now(TZ).date()


def now_ms() -> int:
    return int(time.time() * 1000)


def to_fa(value) -> str:
    return str(value).translate(str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹"))


# ---------------------------------------------------------------- جدول‌های دیتابیس
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

CREATE TABLE IF NOT EXISTS user_devices (
    user_id    INTEGER NOT NULL,
    device_id  TEXT    NOT NULL,
    first_seen INTEGER NOT NULL,
    last_seen  INTEGER NOT NULL,
    hits       INTEGER NOT NULL DEFAULT 1,
    PRIMARY KEY (user_id, device_id)
);
CREATE INDEX IF NOT EXISTS idx_user_devices_dev ON user_devices(device_id);

CREATE TABLE IF NOT EXISTS bans (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    kind       TEXT    NOT NULL CHECK (kind IN ('user', 'ip', 'device')),
    value      TEXT    NOT NULL,
    reason     TEXT    NOT NULL DEFAULT '',
    created_at INTEGER NOT NULL,
    expires_at INTEGER,
    created_by TEXT    NOT NULL DEFAULT ''
);
CREATE UNIQUE INDEX IF NOT EXISTS idx_bans_kind_value ON bans(kind, value);

CREATE TABLE IF NOT EXISTS user_limits (
    user_id       INTEGER PRIMARY KEY,
    hw_limit      INTEGER,
    q_limit       INTEGER,
    a_limit       INTEGER,
    ai_chat_limit INTEGER
);

CREATE TABLE IF NOT EXISTS moderation_strikes (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id    INTEGER,
    ip         TEXT    NOT NULL DEFAULT '',
    device_id  TEXT    NOT NULL DEFAULT '',
    kind       TEXT    NOT NULL DEFAULT '',
    reason     TEXT    NOT NULL DEFAULT '',
    created_at INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_strikes_user ON moderation_strikes(user_id, created_at);
CREATE INDEX IF NOT EXISTS idx_strikes_ip ON moderation_strikes(ip, created_at);

CREATE TABLE IF NOT EXISTS exams (
    id         TEXT    PRIMARY KEY,
    date       TEXT    NOT NULL,
    subject    TEXT    NOT NULL,
    text       TEXT    NOT NULL DEFAULT '',
    author_id  INTEGER NOT NULL,
    created_at INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_exams_date ON exams(date);

CREATE TABLE IF NOT EXISTS notifications (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id    INTEGER,
    kind       TEXT    NOT NULL DEFAULT 'announcement',
    title      TEXT    NOT NULL,
    body       TEXT    NOT NULL DEFAULT '',
    link       TEXT    NOT NULL DEFAULT '',
    broadcast  INTEGER NOT NULL DEFAULT 0,
    created_at INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_notifs_user ON notifications(user_id, created_at);

CREATE TABLE IF NOT EXISTS notif_reads (
    user_id      INTEGER PRIMARY KEY,
    last_read_at INTEGER NOT NULL DEFAULT 0
);
"""


def migrate(conn: sqlite3.Connection) -> None:
    """جدول‌های جدید و ستون‌های تکمیلی را بدون تخریب داده‌های قبلی اضافه می‌کند."""
    # بررسی اینکه آیا جدول bans قدیمی CHECK (kind IN ('user', 'ip')) دارد یا خیر
    row = conn.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='bans'").fetchone()
    if row and "'device'" not in (row["sql"] or ""):
        conn.executescript("""
            ALTER TABLE bans RENAME TO bans_old;
            CREATE TABLE bans (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                kind       TEXT    NOT NULL CHECK (kind IN ('user', 'ip', 'device')),
                value      TEXT    NOT NULL,
                reason     TEXT    NOT NULL DEFAULT '',
                created_at INTEGER NOT NULL,
                expires_at INTEGER,
                created_by TEXT    NOT NULL DEFAULT ''
            );
            INSERT OR IGNORE INTO bans (id, kind, value, reason, created_at, expires_at, created_by)
                SELECT id, kind, value, reason, created_at, expires_at, created_by FROM bans_old;
            DROP TABLE bans_old;
            CREATE UNIQUE INDEX IF NOT EXISTS idx_bans_kind_value ON bans(kind, value);
        """)
    conn.executescript(SCHEMA)
    # افزودن ستون status و ai_note به جدول homework در صورت نبودن
    hw_cols = {r["name"] for r in conn.execute("PRAGMA table_info(homework)")}
    if "status" not in hw_cols:
        conn.execute("ALTER TABLE homework ADD COLUMN status TEXT NOT NULL DEFAULT 'approved'")
    if "ai_note" not in hw_cols:
        conn.execute("ALTER TABLE homework ADD COLUMN ai_note TEXT NOT NULL DEFAULT ''")
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
    """حساب مدیر از متغیرهای محیطی ساخته یا به‌روز می‌شود."""
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
    """پاک‌کردن داده‌های بی‌صاحب."""
    conn.execute("DELETE FROM questions WHERE homework_id NOT IN (SELECT id FROM homework) "
                 "OR author_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM answers WHERE question_id NOT IN (SELECT id FROM questions) "
                 "OR author_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM exams WHERE author_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM user_ips WHERE user_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM user_devices WHERE user_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM daily_usage WHERE user_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM user_limits WHERE user_id NOT IN (SELECT id FROM users)")
    conn.execute("DELETE FROM notif_reads WHERE user_id NOT IN (SELECT id FROM users)")


def purge_old(conn: sqlite3.Connection) -> None:
    cutoff = (today() - timedelta(days=KEEP_DAYS)).isoformat()
    conn.execute("DELETE FROM homework WHERE date < ?", (cutoff,))
    conn.execute("DELETE FROM exams WHERE date < ?", (cutoff,))
    purge_orphans(conn)
    conn.execute("DELETE FROM daily_usage WHERE day < ?", ((today() - timedelta(days=3)).isoformat(),))
    conn.execute("DELETE FROM moderation_strikes WHERE created_at < ?", (now_ms() - 7 * 86_400_000,))
    conn.execute("DELETE FROM notifications WHERE created_at < ?", (now_ms() - 60 * 86_400_000,))
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
    if not ATRIA_API_KEY:
        log.warning("ATRIA_API_KEY تنظیم نشده است! برای فعال شدن بررسی هوشمند و چت هوش مصنوعی، این متغیر را در Railway تنظیم کن.")
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
    global _last_gc
    now = time.time()
    if now - _last_gc < 60:
        return
    _last_gc = now
    for k in [k for k, q in _hits.items() if not q or q[-1] < now - 3600]:
        _hits.pop(k, None)
    if len(_hits) > 50000:
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


def client_device(request: Request) -> str:
    raw = request.headers.get("x-device-id", "").strip()
    return raw if DEVICE_ID_RE.match(raw) else ""


# ---------------------------------------------------------------- مسدودسازی (User + IP + Device)
def active_ban(db: sqlite3.Connection, kind: str, value: str) -> Optional[sqlite3.Row]:
    if not value:
        return None
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
    """فهرست IPها و دستگاه‌های مسدود در حافظه."""
    TTL = 15

    def __init__(self) -> None:
        self.ips: set = set()
        self.devices: set = set()
        self.loaded = 0.0

    def refresh(self, force: bool = False) -> None:
        if not force and time.time() - self.loaded < self.TTL:
            return
        conn = connect()
        try:
            conn.execute("DELETE FROM bans WHERE expires_at IS NOT NULL AND expires_at <= ?", (now_ms(),))
            conn.commit()
            self.ips = {r["value"] for r in conn.execute("SELECT value FROM bans WHERE kind = 'ip'")}
            self.devices = {r["value"] for r in conn.execute("SELECT value FROM bans WHERE kind = 'device'")}
        except sqlite3.Error:
            log.exception("خواندن فهرست مسدودی‌ها ناموفق بود")
        finally:
            conn.close()
        self.loaded = time.time()

    def is_ip_banned(self, ip: str) -> bool:
        self.refresh()
        return ip in self.ips

    def is_device_banned(self, dev: str) -> bool:
        if not dev:
            return False
        self.refresh()
        return dev in self.devices


bans_cache = BanCache()

_NO_STORE_PREFIXES = ("/api/auth", "/api/admin", "/api/quota", "/api/notifications", "/api/ai")


@app.middleware("http")
async def guard(request: Request, call_next):
    path, method = request.url.path, request.method
    if method != "OPTIONS" and path != "/api/health":
        ip = client_ip(request)
        dev = client_device(request)
        if bans_cache.is_ip_banned(ip) or bans_cache.is_device_banned(dev):
            return JSONResponse(status_code=403, content={"detail": "دسترسی این دستگاه یا شبکه به سامانه مسدود شده است."})
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


app.add_middleware(
    CORSMiddleware,
    allow_origins=ALLOWED_ORIGINS or ["*"],
    allow_credentials=False,
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["Authorization", "Content-Type", "X-Device-Id"],
    max_age=3600,
)


# ---------------------------------------------------------------- مدل‌ها
class RegisterIn(BaseModel):
    name: str = Field(..., max_length=100)
    email: str = Field(..., max_length=300)
    username: str = Field(..., max_length=100)
    password: str = Field(..., max_length=200)


class LoginIn(BaseModel):
    username: str = Field(..., max_length=300)
    password: str = Field(..., max_length=200)


class HomeworkIn(BaseModel):
    date: str = Field(..., max_length=20)
    subject: str = Field(..., max_length=100)
    text: str = Field(..., max_length=3000)
    day: Optional[int] = None


class ExamIn(BaseModel):
    date: str = Field(..., max_length=20)
    subject: str = Field(..., max_length=100)
    text: str = Field("", max_length=3000)


class TeacherIn(BaseModel):
    name: str = Field(..., max_length=100)
    username: str = Field(..., max_length=100)
    password: str = Field(..., max_length=200)
    subject: str = Field("", max_length=100)


class TeacherUpdateIn(BaseModel):
    name: str = Field(..., max_length=100)
    subject: str = Field("", max_length=100)
    password: Optional[str] = Field(None, max_length=200)


class PeriodIn(BaseModel):
    subject: str = Field(..., max_length=100)
    teacher: str = Field("", max_length=100)


class QuestionIn(BaseModel):
    text: str = Field(..., max_length=2000)


class AnswerIn(BaseModel):
    text: str = Field(..., max_length=2000)


class BanIn(BaseModel):
    kind: str = Field(..., max_length=10)       # user | ip | device
    value: str = Field(..., max_length=100)
    reason: str = Field("", max_length=200)
    hours: Optional[int] = None


class LimitsIn(BaseModel):
    homework: Optional[int] = None
    question: Optional[int] = None
    answer: Optional[int] = None
    ai: Optional[int] = None


class AnnouncementIn(BaseModel):
    title: str = Field(..., max_length=160)
    body: str = Field("", max_length=1000)


class AiChatMsg(BaseModel):
    role: str = Field(..., max_length=16)
    content: str = Field(..., max_length=4000)


class AiChatIn(BaseModel):
    messages: List[AiChatMsg] = Field(..., max_length=20)


# ---------------------------------------------------------------- پاک‌سازی و نرمال‌سازی متن
_BAD_CHARS = re.compile(r"[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f\u200b\u200e\u200f\u202a-\u202e\u2060-\u2069\ufeff]")
_FA_MAP = str.maketrans({"ي": "ی", "ك": "ک", "ة": "ه", "ۀ": "ه", "أ": "ا", "إ": "ا", "ؤ": "و", "آ": "ا"})
_LEET_MAP = str.maketrans({"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a"})


def clean(value: str, lo: int, hi: int, message: str) -> str:
    value = _BAD_CHARS.sub("", value)
    value = re.sub(r"[ \t\u200c]*\n[ \t\u200c]*", "\n", value.replace("\r", "")).strip()
    if not (lo <= len(value) <= hi):
        raise HTTPException(400, message)
    return value


def one_line(value: str, lo: int, hi: int, message: str) -> str:
    return clean(" ".join(value.split()), lo, hi, message)


def _norm(text: str) -> str:
    return re.sub(r"[\u064b-\u065f\u0670\u200c\u200d_\W\d]+", "", text.translate(_FA_MAP).lower())


def _norm_en(text: str) -> str:
    s = text.lower().translate(_LEET_MAP)
    s = re.sub(r"[^a-z]+", "", s)
    return re.sub(r"(.)\1+", r"\1", s)


def norm_persian_name(name: str) -> str:
    s = name.translate(str.maketrans({"ي": "ی", "ك": "ک", "ة": "ه", "ۀ": "ه", "أ": "ا", "إ": "ا", "ؤ": "و"}))
    s = re.sub(r"[\u064b-\u065f\u0670\u200c\s]+", " ", s).strip()
    return s


BLOCKED = [w for w in (_norm(x) for x in os.getenv("BLOCKED_WORDS", "").split(",")) if len(w) >= 2]


def check_blocked(text: str) -> None:
    n = _norm(text)
    if any(w in n for w in BLOCKED):
        raise HTTPException(400, "متن شامل کلمه‌ی نامناسب است. مؤدبانه بنویس.")


def get_known_teachers(db: sqlite3.Connection) -> List[str]:
    """فهرست نام معلم‌های ثبت‌شده در جدول کاربران و برنامه هفتگی را برمی‌گرداند."""
    names = {"مرادی", "ابوالفضل مرادی", "ابولفضل مرادی"}
    for r in db.execute("SELECT name, username FROM users WHERE role IN ('teacher', 'admin')"):
        if r["name"]:
            names.add(r["name"].strip())
        if r["username"]:
            names.add(r["username"].strip())
    for r in db.execute("SELECT periods FROM schedule"):
        try:
            for p in json.loads(r["periods"]):
                t = (p.get("teacher") or "").strip()
                if t:
                    names.add(t)
        except Exception:
            pass
    return sorted(names)


def validate_student_identity(db: sqlite3.Connection, name: str, username: str, email: str) -> str:
    """اعتبارسنجی سخت‌گیرانه نام و نام کاربری دانش‌آموز برای جلوگیری از جعل هویت معلم‌ها (به‌ویژه آقای مرادی) و اسامی تکراری."""
    cleaned_name = norm_persian_name(name)
    if not PERSIAN_NAME_RE.match(cleaned_name):
        raise HTTPException(400, "نام و نام‌خانوادگی را فقط با حروف فارسی بنویس (بدون عدد، ایموجی یا حروف انگلیسی).")
    parts = [p for p in cleaned_name.split(" ") if len(p) >= 2]
    if len(parts) < 2:
        raise HTTPException(400, "لطفاً هم نام و هم نام‌خانوادگی واقعی خودت را کامل بنویس (حداقل دو بخش).")
    if any(len(set(p)) == 1 and len(p) >= 3 for p in parts):
        raise HTTPException(400, "نام و نام‌خانوادگی معتبر نیست.")

    # بررسی عدم شباهت به «مرادی» و سایر معلم‌ها یا عناوین کادر مدرسه
    norm_fa_name = _norm(cleaned_name)
    norm_user = _norm_en(username)
    norm_email_local = _norm_en(email.split("@")[0])

    for pat in FORBIDDEN_TEACHER_PATTERNS:
        p_fa = _norm(pat)
        p_en = _norm_en(pat)
        if p_fa and len(p_fa) >= 3 and p_fa in norm_fa_name:
            raise HTTPException(400, "استفاده از نام دبیران (مثل آقای مرادی) یا عناوین معلم/مدیر مجاز نیست. با نام واقعی خودت ثبت‌نام کن.")
        if p_en and len(p_en) >= 3 and (p_en in norm_user or p_en in norm_email_local):
            raise HTTPException(400, "این نام کاربری یا ایمیل به دلیل شباهت به نام دبیران (مثل آقای مرادی) مجاز نیست.")

    # بررسی عدم شباهت به نام معلم‌های موجود در دیتابیس و برنامه زنگ‌ها
    for tname in get_known_teachers(db):
        tn = _norm(tname)
        if tn and len(tn) >= 3 and tn in norm_fa_name:
            raise HTTPException(400, "نمی‌توانی با نام دبیران یا مدیر مدرسه ثبت‌نام کنی.")

    # بررسی یکتا بودن نام و نام‌خانوادگی در بین کل کاربران
    for r in db.execute("SELECT name FROM users"):
        if _norm(r["name"]) == norm_fa_name:
            raise HTTPException(409, "دانش‌آموز دیگری قبلاً با این نام و نام‌خانوادگی ثبت‌نام کرده است.")

    # جلوگیری از نام کاربری عجیب‌وغریب (فقط عدد یا تکرار یک حرف)
    if username.isdigit() or len(set(username.replace("_", ""))) <= 2:
        raise HTTPException(400, "نام کاربری نباید فقط عدد یا تکرار حروف بی‌معنی باشد.")

    check_blocked(cleaned_name)
    check_blocked(username)
    return cleaned_name


# ---------------------------------------------------------------- سرویس هوش مصنوعی Atria-Dawn
def call_atria_json(system_prompt: str, user_prompt: str, timeout: int = 12) -> Optional[dict]:
    """ارسال درخواست غیر استریم به Atria-Dawn و دریافت خروجی ساختاریافته JSON."""
    if not ATRIA_API_KEY or not AI_MODERATION_ENABLED:
        return None
    payload = {
        "model": ATRIA_MODEL,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "stream": False,
        "temperature": 0.001,
        "max_tokens": 350,
    }
    req = urllib.request.Request(
        f"{ATRIA_BASE_URL}/chat/completions",
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {ATRIA_API_KEY}",
            "Content-Type": "application/json",
            "User-Agent": "TaklifSchoolApp/2.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = json.loads(resp.read().decode("utf-8"))
        content = (raw.get("choices") or [{}])[0].get("message", {}).get("content", "")
        if not content:
            return None
        # حذف تگ‌های <think>...</think> در صورت وجود و استخراج اولین آبجکت JSON
        content = re.sub(r"<think>[\s\S]*?</think>", "", content).strip()
        m = re.search(r"\{[\s\S]*\}", content)
        if not m:
            return None
        return json.loads(m.group(0))
    except Exception as e:
        log.warning("Atria moderation request failed or timed out: %s", e)
        return None


def record_strike_and_check_autoban(
    db: sqlite3.Connection,
    user: Optional[sqlite3.Row],
    ip: str,
    device_id: str,
    kind: str,
    reason: str,
) -> bool:
    """ثبت تخلف برای کاربر/IP/دستگاه و مسدودسازی خودکار در صورت رسیدن به سقف AUTO_BAN_STRIKES در ۲۴ ساعت."""
    now = now_ms()
    uid = user["id"] if user else None
    db.execute(
        "INSERT INTO moderation_strikes (user_id, ip, device_id, kind, reason, created_at) VALUES (?, ?, ?, ?, ?, ?)",
        (uid, ip or "", device_id or "", kind, reason[:120], now),
    )
    cutoff = now - 86_400_000
    if uid:
        cnt = db.execute(
            "SELECT COUNT(*) FROM moderation_strikes WHERE user_id = ? AND created_at > ?", (uid, cutoff)
        ).fetchone()[0]
    else:
        cnt = db.execute(
            "SELECT COUNT(*) FROM moderation_strikes WHERE ip = ? AND created_at > ?", (ip, cutoff)
        ).fetchone()[0]

    banned = False
    if cnt >= AUTO_BAN_STRIKES:
        expires = now + 24 * 3_600_000  # ۲۴ ساعت مسدودی خودکار
        ban_reason = f"مسدودی خودکار به دلیل تکرار ارسال محتوای نامعتبر ({reason[:60]})"
        if user and user["role"] == "student":
            db.execute("DELETE FROM bans WHERE kind = 'user' AND value = ?", (user["username"],))
            db.execute(
                "INSERT INTO bans (kind, value, reason, created_at, expires_at, created_by) VALUES ('user', ?, ?, ?, ?, 'هوش مصنوعی')",
                (user["username"], ban_reason, now, expires),
            )
        if device_id:
            db.execute("DELETE FROM bans WHERE kind = 'device' AND value = ?", (device_id,))
            db.execute(
                "INSERT INTO bans (kind, value, reason, created_at, expires_at, created_by) VALUES ('device', ?, ?, ?, ?, 'هوش مصنوعی')",
                (device_id, ban_reason, now, expires),
            )
        banned = True
    db.commit()
    if banned:
        bans_cache.refresh(force=True)
    return banned


def ai_verify_registration(db: sqlite3.Connection, name: str, username: str, email: str, ip: str, device_id: str) -> None:
    """تایید نام و نام کاربری دانش‌آموز هنگام ثبت‌نام با هوش مصنوعی Atria-Dawn."""
    teachers = get_known_teachers(db)
    existing_names = [r["name"] for r in db.execute("SELECT name FROM users ORDER BY id DESC LIMIT 80")]
    sys_prompt = (
        "تو نگهبان امنیتی سامانه مدرسه دبیرستان شهید بهشتی (کلاس ۹۰۱) هستی. "
        "وظیفه تو بررسی ثبت‌نام دانش‌آموز جدید است. فقط و فقط یک JSON معتبر با ساختار زیر برگردان:\n"
        '{"decision": "approve" | "reject", "reason": "توضیح کوتاه فارسی خطاب به دانش‌آموز"}\n'
        "قوانین رد کردن (reject):\n"
        "۱. اگر نام و نام‌خانوادگی یک نام واقعی و محترمانه ایرانی نباشد (مثلاً شوخی، فحش، نام شخصیت کارتونی، بازی، حیوان، شیء، کلمات بی‌معنی یا حروف تصادفی باشد).\n"
        "۲. اگر نام یا نام کاربری یا ایمیل به هر شکل (فارسی، فینگلیش، مخفف یا غلط املایی مثل moradi, moardi, ابولفضل مرادی) شبیه نام معلم ریاضی «ابوالفضل مرادی» یا سایر معلم‌ها باشد: "
        f"{', '.join(teachers)}\n"
        "۳. اگر نام انتخاب‌شده تکراری یا بسیار شبیه یکی از دانش‌آموزان قبلی باشد (با تغییر جزیی حروف): "
        f"{', '.join(existing_names[:50])}\n"
        "۴. اگر نام کاربری حاوی کلمات رکیک، توهین‌آمیز، شوخی‌های نامناسب یا ادعای معلم/مدیر بودن باشد."
    )
    user_prompt = json.dumps({"name": name, "username": username, "email": email}, ensure_ascii=False)
    res = call_atria_json(sys_prompt, user_prompt, timeout=10)
    if res and str(res.get("decision", "")).lower() == "reject":
        reason = str(res.get("reason") or "نام یا نام کاربری انتخاب‌شده معتبر نیست. لطفاً با مشخصات واقعی ثبت‌نام کن.").strip()
        record_strike_and_check_autoban(db, None, ip, device_id, "register", reason)
        raise HTTPException(400, reason)


def ai_moderate_homework(
    db: sqlite3.Connection,
    user: sqlite3.Row,
    subject: str,
    text: str,
    date_str: str,
    ip: str,
    device_id: str,
) -> tuple[str, str]:
    """بررسی هوشمند تکلیف با Atria-Dawn.
    خروجی: (status: 'approved' | 'pending', ai_note: str) یا پرتاب HTTPException در صورت رد شدن.
    """
    if user["role"] in STAFF_ROLES:
        return "approved", ""

    allowed_subjects = get_allowed_subjects(db)
    sys_prompt = (
        "تو ناظر هوشمند سامانه تکالیف کلاس ۹۰۱ دبیرستان شهید بهشتی (پایه نهم) هستی. "
        "دانش‌آموز می‌خواهد یک تکلیف برای کلاس ثبت کند. آن را بررسی کن و فقط یک JSON معتبر برگردان:\n"
        '{"decision": "approve" | "flag" | "reject", "reason": "توضیح کوتاه فارسی"}\n'
        "قوانین:\n"
        "- reject: اگر متن شوخی، چرت‌وپرت، فحش، اسپم، حروف تصادفی، بی‌ربط به درس، شایعه‌پراکنی درباره امتحان یا معلم (مثل آقای مرادی)، یا عددهای غیرواقعی (مثل صفحه ۹۰۰۰) باشد.\n"
        "- flag: اگر متن شبیه تکلیف هست ولی کمی مبهم، کوتاه، غیرمعمول یا نیازمند تایید معلم/مدیر است (تا در صف انتظار تایید مدیر قرار بگیرد).\n"
        "- approve: اگر کاملاً یک تکلیف درسی استاندارد، واقعی، دقیق و محترمانه متناسب با درس انتخاب‌شده است."
    )
    user_prompt = json.dumps(
        {"subject": subject, "text": text, "date": date_str, "student_name": user["name"], "known_subjects": allowed_subjects},
        ensure_ascii=False,
    )
    res = call_atria_json(sys_prompt, user_prompt, timeout=12)
    if not res:
        # اگر کلید AI تنظیم نشده یا سرویس موقتاً در دسترس نبود، به صورت pending ثبت می‌شود تا ادمین تایید کند
        return "pending", "در انتظار تایید مدیر"

    decision = str(res.get("decision", "flag")).lower().strip()
    reason = str(res.get("reason") or "").strip()
    if decision == "reject":
        msg = reason or "این متن به عنوان تکلیف درسی معتبر شناخته نشد. لطفاً فقط تکلیف واقعی ثبت کن."
        auto_banned = record_strike_and_check_autoban(db, user, ip, device_id, "homework", msg)
        if auto_banned:
            raise HTTPException(403, "به دلیل تکرار ثبت مطالب نامعتبر، حساب تو به مدت ۲۴ ساعت مسدود شد.")
        raise HTTPException(400, f"رد شد توسط هوش مصنوعی: {msg}")
    if decision == "approve":
        return "approved", ""
    return "pending", reason or "نیازمند بررسی و تایید معلم/مدیر"


def ai_moderate_qa(
    db: sqlite3.Connection,
    user: sqlite3.Row,
    kind_label: str,
    context_text: str,
    text: str,
    ip: str,
    device_id: str,
) -> None:
    """بررسی هوشمند پرسش یا پاسخ درسی با Atria-Dawn."""
    if user["role"] in STAFF_ROLES:
        return
    sys_prompt = (
        f"تو ناظر هوشمند بخش پرسش‌وپاسخ درسی کلاس ۹۰۱ دبیرستان شهید بهشتی هستی. "
        f"یک دانش‌آموز می‌خواهد این «{kind_label}» را زیر تکلیف ثبت کند. فقط یک JSON برگردان:\n"
        '{"decision": "approve" | "reject", "reason": "توضیح کوتاه فارسی"}\n'
        "اگر متن شامل شوخی بی‌ربط، مسخره‌بازی، چرت‌وپرت، فحش، توهین، اسپم یا جعل هویت معلم‌هاست، decision را reject بگذار. "
        "اگر یک سؤال یا پاسخ درسی و محترمانه است، approve بگذار."
    )
    user_prompt = json.dumps({"homework_context": context_text, "submitted_text": text, "author": user["name"]}, ensure_ascii=False)
    res = call_atria_json(sys_prompt, user_prompt, timeout=10)
    if res and str(res.get("decision", "")).lower() == "reject":
        reason = str(res.get("reason") or f"این {kind_label} مرتبط با درس نیست یا نامناسب تشخیص داده شد.").strip()
        auto_banned = record_strike_and_check_autoban(db, user, ip, device_id, "qa", reason)
        if auto_banned:
            raise HTTPException(403, "به دلیل تکرار ارسال پیام‌های نامعتبر، حساب تو به مدت ۲۴ ساعت مسدود شد.")
        raise HTTPException(400, f"رد شد توسط هوش مصنوعی: {reason}")


# ---------------------------------------------------------------- درس‌های مجاز
DEFAULT_SUBJECTS = [
    "ریاضی", "فیزیک", "شیمی", "زیست‌شناسی", "زیست", "علوم تجربی", "علوم",
    "ادبیات فارسی", "فارسی", "نگارش", "عربی", "زبان انگلیسی", "زبان",
    "پیام‌های آسمانی", "دینی", "قرآن", "مطالعات اجتماعی", "مطالعات",
    "آمادگی دفاعی", "فرهنگ و هنر", "کار و فناوری", "تفکر و سبک زندگی",
]


def get_allowed_subjects(db: sqlite3.Connection) -> List[str]:
    subs = set(DEFAULT_SUBJECTS)
    for r in db.execute("SELECT periods FROM schedule"):
        try:
            for p in json.loads(r["periods"]):
                s = (p.get("subject") or "").strip()
                if s:
                    subs.add(s)
        except Exception:
            pass
    for r in db.execute("SELECT subject FROM users WHERE role = 'teacher' AND subject != ''"):
        subs.add(r["subject"].strip())
    return sorted(subs)


# ---------------------------------------------------------------- کمکی‌های کاربران و سهمیه
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


QUOTA_MSG = {
    "homework": "سهمیه‌ی ثبت تکلیف امروزت ({n} تکلیف) تمام شده است. فردا دوباره امتحان کن.",
    "question": "سهمیه‌ی سؤال امروزت ({n} سؤال) تمام شده است. فردا دوباره امتحان کن.",
    "answer": "امروز بیش از حد پاسخ داده‌ای ({n} پاسخ). فردا دوباره امتحان کن.",
    "ai": "سهمیه‌ی چت با هوش مصنوعی امروزت ({n} پیام) تمام شده است یا دسترسی چت برایت فعال نیست.",
}

_LIMIT_COL = {
    "homework": "hw_limit",
    "question": "q_limit",
    "answer": "a_limit",
    "ai": "ai_chat_limit",
}


def default_quota_limit(role: str, kind: str) -> Optional[int]:
    if role == "admin":
        return None  # مدیر در همه‌چیز (از جمله چت هوش مصنوعی) نامحدود است
    if role == "teacher":
        if kind == "homework":
            return None
        if kind == "question":
            return STAFF_Q_PER_DAY
        if kind == "answer":
            return STAFF_A_PER_DAY
        if kind == "ai":
            return TEACHER_AI_PER_DAY
    # student
    if kind == "homework":
        return STUDENT_HW_PER_DAY
    if kind == "question":
        return STUDENT_Q_PER_DAY
    if kind == "answer":
        return STUDENT_A_PER_DAY
    if kind == "ai":
        return STUDENT_AI_PER_DAY  # پیش‌فرض ۰: هیچ دانش‌آموزی بدون اجازه ادمین حق چت ندارد
    return 0


def user_limits_info(db: sqlite3.Connection, uid: int, role: str) -> dict:
    row = db.execute("SELECT * FROM user_limits WHERE user_id = ?", (uid,)).fetchone()
    out = {}
    for kind, col in _LIMIT_COL.items():
        dval = default_quota_limit(role, kind)
        cval = row[col] if (row and row[col] is not None) else None
        out[kind] = {
            "value": cval if cval is not None else (dval if dval is not None else 999),
            "default": dval if dval is not None else 999,
            "custom": cval is not None,
        }
    return out


def quota_limit(db: sqlite3.Connection, user: sqlite3.Row, kind: str) -> Optional[int]:
    if user["role"] == "admin":
        return None
    col = _LIMIT_COL.get(kind)
    if col:
        row = db.execute(f"SELECT {col} FROM user_limits WHERE user_id = ?", (user["id"],)).fetchone()
        if row and row[col] is not None:
            return int(row[col])
    return default_quota_limit(user["role"], kind)


def consume(db: sqlite3.Connection, user: sqlite3.Row, kind: str) -> None:
    """یک واحد از سهمیه‌ی امروز را اتمی مصرف می‌کند؛ اگر تمام شده باشد خطای ۴۲۹ یا ۴۰۳ می‌دهد."""
    limit = quota_limit(db, user, kind)
    if limit is None:
        return
    if limit <= 0:
        if kind == "ai":
            raise HTTPException(403, "دسترسی چت با هوش مصنوعی فقط برای مدیر فعال است (یا باید مدیر سهمیه روزانه برایت تنظیم کند).")
        raise HTTPException(403, "انجام این کار برای حساب تو بسته شده است.")
    day = today().isoformat()
    db.execute("INSERT OR IGNORE INTO daily_usage (user_id, day, kind, n) VALUES (?, ?, ?, 0)", (user["id"], day, kind))
    cur = db.execute("UPDATE daily_usage SET n = n + 1 WHERE user_id = ? AND day = ? AND kind = ? AND n < ?",
                     (user["id"], day, kind, limit))
    if cur.rowcount == 0:
        raise HTTPException(429, QUOTA_MSG[kind].format(n=to_fa(limit)))


def quota_out(db: sqlite3.Connection, user: sqlite3.Row) -> dict:
    used = {r["kind"]: r["n"] for r in db.execute(
        "SELECT kind, n FROM daily_usage WHERE user_id = ? AND day = ?", (user["id"], today().isoformat()))}
    return {
        k: {"used": used.get(k, 0), "limit": quota_limit(db, user, k)}
        for k in ("homework", "question", "answer", "ai")
    }


def touch_ip_and_device(db: sqlite3.Connection, uid: int, ip: str, dev: str) -> None:
    """هر IP و شناسه دستگاهی که یک حساب با آن کار کرده را ثبت می‌کند."""
    now = now_ms()
    changed = False
    if ip and ip != "unknown":
        cur = db.execute("UPDATE user_ips SET last_seen = ?, hits = hits + 1 WHERE user_id = ? AND ip = ? AND last_seen < ?",
                         (now, uid, ip, now - 300_000))
        if cur.rowcount > 0:
            changed = True
        else:
            cur = db.execute("INSERT OR IGNORE INTO user_ips (user_id, ip, first_seen, last_seen, hits) VALUES (?, ?, ?, ?, 1)",
                             (uid, ip, now, now))
            if cur.rowcount > 0:
                changed = True
                db.execute("DELETE FROM user_ips WHERE user_id = ? AND ip NOT IN "
                           "(SELECT ip FROM user_ips WHERE user_id = ? ORDER BY last_seen DESC LIMIT 20)", (uid, uid))
    if dev:
        cur = db.execute("UPDATE user_devices SET last_seen = ?, hits = hits + 1 WHERE user_id = ? AND device_id = ? AND last_seen < ?",
                         (now, uid, dev, now - 300_000))
        if cur.rowcount > 0:
            changed = True
        else:
            cur = db.execute("INSERT OR IGNORE INTO user_devices (user_id, device_id, first_seen, last_seen, hits) VALUES (?, ?, ?, ?, 1)",
                             (uid, dev, now, now))
            if cur.rowcount > 0:
                changed = True
                db.execute("DELETE FROM user_devices WHERE user_id = ? AND device_id NOT IN "
                           "(SELECT device_id FROM user_devices WHERE user_id = ? ORDER BY last_seen DESC LIMIT 10)", (uid, uid))
    if changed:
        db.commit()


def js_weekday(d: date) -> int:
    return (d.weekday() + 1) % 7


HW_SELECT = (
    "SELECT h.id, h.date, h.subject, h.text, h.created_at, h.status, h.ai_note, h.author_id, "
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
        "status": r["status"] if "status" in r.keys() else "approved",
        "aiNote": r["ai_note"] if "ai_note" in r.keys() else "",
        "author": r["name"],
        "authorRole": r["role"],
        "authorSubject": r["author_subject"],
        "authorId": r["username"],
        "createdAt": r["created_at"],
        "qCount": r["q_count"],
    }


EXAM_SELECT = (
    "SELECT e.id, e.date, e.subject, e.text, e.created_at, e.author_id, "
    "u.username, u.name, u.role, u.subject AS author_subject "
    "FROM exams e JOIN users u ON u.id = e.author_id"
)


def exam_out(r: sqlite3.Row) -> dict:
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
    }


def etag_json(request: Request, payload) -> Response:
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode()
    tag = '"' + hashlib.sha1(body).hexdigest()[:24] + '"'
    headers = {"ETag": tag, "Cache-Control": "no-cache"}
    if request.headers.get("if-none-match") == tag:
        return Response(status_code=304, headers=headers)
    return Response(body, media_type="application/json", headers=headers)


bearer = HTTPBearer(auto_error=False)


def optional_user(
    request: Request,
    cred: Optional[HTTPAuthorizationCredentials] = Depends(bearer),
    db: sqlite3.Connection = Depends(get_db),
) -> Optional[sqlite3.Row]:
    if cred is None:
        return None
    uid = security.decode_token(cred.credentials)
    row = db.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone() if uid else None
    if row is None:
        return None
    if active_ban(db, "user", row["username"]):
        return None
    touch_ip_and_device(db, row["id"], client_ip(request), client_device(request))
    return row


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
    dev = client_device(request)
    if dev:
        dban = active_ban(db, "device", dev)
        if dban and row["role"] != "admin":
            raise HTTPException(403, ban_message(dban, "این دستگاه"))
    if request.method not in ("GET", "HEAD", "OPTIONS"):
        key = f"uw:{row['id']}"
        check_limit(key, USER_WRITE_LIMIT, 60, "درخواست‌های تو زیاد است. کمی صبر کن.")
        add_hit(key, 60)
    touch_ip_and_device(db, row["id"], client_ip(request), dev)
    return row


def teacher_only(user: sqlite3.Row = Depends(current_user)) -> sqlite3.Row:
    if user["role"] not in STAFF_ROLES:
        raise HTTPException(403, "فقط معلم یا مدیر می‌تواند این کار را انجام دهد.")
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
        raise HTTPException(400, "نمی‌شود برای تاریخ گذشته ثبت کرد.")
    if d > t + timedelta(days=MAX_AHEAD_DAYS):
        raise HTTPException(400, "این تاریخ بیش از حد دور است.")
    return d.isoformat()


def push_notification(
    db: sqlite3.Connection,
    user_id: Optional[int],
    kind: str,
    title: str,
    body: str = "",
    link: str = "",
    broadcast: bool = False,
) -> None:
    db.execute(
        "INSERT INTO notifications (user_id, kind, title, body, link, broadcast, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)",
        (None if broadcast else user_id, kind, title[:160], body[:600], link[:80], 1 if broadcast else 0, now_ms()),
    )


# ---------------------------------------------------------------- مسیرها
@app.get("/api/health")
def health():
    return {"ok": True, "aiEnabled": bool(ATRIA_API_KEY and AI_MODERATION_ENABLED)}


@app.post("/api/auth/register")
def register(body: RegisterIn, request: Request, db: sqlite3.Connection = Depends(get_db)):
    ip = client_ip(request)
    dev = client_device(request)
    ip_key = f"reg:{ip}"
    check_limit(ip_key, limit=6, window=3600)

    if dev and active_ban(db, "device", dev):
        raise HTTPException(403, "دسترسی این دستگاه برای ساخت حساب جدید مسدود شده است.")
    if active_ban(db, "ip", ip):
        raise HTTPException(403, "دسترسی این شبکه مسدود شده است.")
    # اگر هر حسابی که قبلاً با این دستگاه یا IP وارد شده الان مسدود باشد، اجازه ساخت اکانت جدید نده!
    if dev:
        banned_linked = db.execute(
            "SELECT 1 FROM user_devices ud JOIN users u ON u.id = ud.user_id "
            "JOIN bans b ON b.kind = 'user' AND b.value = u.username "
            "WHERE ud.device_id = ? AND (b.expires_at IS NULL OR b.expires_at > ?)",
            (dev, now_ms()),
        ).fetchone()
        if banned_linked:
            raise HTTPException(403, "حساب قبلی این دستگاه مسدود شده است و امکان ساخت حساب جدید وجود ندارد.")

    raw_name = one_line(body.name, 5, 40, "نام و نام‌خانوادگی باید ۵ تا ۴۰ حرف باشد.")
    email = body.email.strip().lower()
    if len(email) > 254 or not EMAIL_RE.match(email):
        raise HTTPException(400, "ایمیل معتبر نیست.")
    username = body.username.strip().lower()
    if not USERNAME_RE.match(username):
        raise HTTPException(400, "نام کاربری ۳ تا ۲۰ حرف انگلیسی، عدد یا _ باشد.")
    if username in RESERVED_USERNAMES:
        raise HTTPException(400, "این نام کاربری مجاز نیست.")
    check_password(body.password, username, email)

    # ۱. اعتبارسنجی ساختار نام فارسی، یکتا بودن نام و عدم شباهت به آقای مرادی / معلم‌ها
    name = validate_student_identity(db, raw_name, username, email)

    if db.execute("SELECT 1 FROM users WHERE username = ?", (username,)).fetchone():
        raise HTTPException(409, "این نام کاربری قبلاً گرفته شده است.")
    if db.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        raise HTTPException(409, "با این ایمیل قبلاً ثبت‌نام شده است.")

    # ۲. تایید هوشمند نام و نام کاربری با هوش مصنوعی Atria-Dawn
    ai_verify_registration(db, name, username, email, ip, dev)

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
    touch_ip_and_device(db, row["id"], ip, dev)
    return {"token": security.create_token(row["id"]), "user": user_out(row)}


@app.post("/api/auth/login")
def login(body: LoginIn, request: Request, db: sqlite3.Connection = Depends(get_db)):
    ident = body.username.strip().lower()[:254]
    ip = client_ip(request)
    dev = client_device(request)
    ip_key, id_key = f"login-ip:{ip}", f"login:{ip}:{ident}"
    any_key = f"login-id:{ident}"
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
    if dev and row["role"] != "admin":
        dban = active_ban(db, "device", dev)
        if dban:
            raise HTTPException(403, ban_message(dban, "این دستگاه"))

    _hits.pop(id_key, None)
    touch_ip_and_device(db, row["id"], ip, dev)
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


# ---------------------------------------------------------------- تکالیف (با تایید ترکیبی AI + مدیر/معلم)
@app.get("/api/homework")
def list_homework(
    request: Request,
    user: Optional[sqlite3.Row] = Depends(optional_user),
    db: sqlite3.Connection = Depends(get_db),
):
    rows = db.execute(HW_SELECT + " ORDER BY h.date, h.created_at").fetchall()
    is_staff = bool(user and user["role"] in STAFF_ROLES)
    uid = user["id"] if user else None
    visible = [
        hw_out(r)
        for r in rows
        if r["status"] == "approved" or is_staff or (uid is not None and r["author_id"] == uid)
    ]
    if is_staff or uid is not None:
        return JSONResponse(visible, headers={"Cache-Control": "no-store"})
    return etag_json(request, visible)


@app.post("/api/homework", status_code=201)
def add_homework(
    body: HomeworkIn,
    request: Request,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    d = parse_date(body.date)
    subject = one_line(body.subject, 2, 30, "نام درس باید ۲ تا ۳۰ حرف باشد.")
    text = clean(body.text, 3, 600, "توضیح تکلیف باید ۳ تا ۶۰۰ حرف باشد.")
    check_blocked(subject)
    check_blocked(text)

    # دانش‌آموز فقط می‌تواند برای درس‌های مجاز مدرسه تکلیف ثبت کند
    if user["role"] not in STAFF_ROLES:
        allowed_norm = {_norm(s): s for s in get_allowed_subjects(db)}
        sn = _norm(subject)
        if sn not in allowed_norm:
            raise HTTPException(400, "نام درس معتبر نیست؛ لطفاً یکی از درس‌های برنامه کلاسی را انتخاب کن.")
        subject = allowed_norm[sn]

    # بررسی هوشمند با Atria-Dawn پیش از کسر سهمیه یا ثبت
    status, ai_note = ai_moderate_homework(db, user, subject, text, d, client_ip(request), client_device(request))

    consume(db, user, "homework")

    hid = uuid.uuid4().hex
    db.execute(
        "INSERT INTO homework (id, date, subject, text, author_id, created_at, status, ai_note) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        (hid, d, subject, text, user["id"], now_ms(), status, ai_note),
    )
    purge_old(db)
    row = db.execute(HW_SELECT + " WHERE h.id = ?", (hid,)).fetchone()
    return hw_out(row)


def _own_or_teacher(db: sqlite3.Connection, hid: str, user: sqlite3.Row) -> sqlite3.Row:
    row = db.execute("SELECT id, date, subject, author_id, status FROM homework WHERE id = ?", (hid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این تکلیف پیدا نشد.")
    if user["role"] not in STAFF_ROLES and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط ثبت‌کننده یا معلم می‌تواند این تکلیف را تغییر دهد.")
    return row


@app.put("/api/homework/{hid}")
def update_homework(
    hid: str,
    body: HomeworkIn,
    request: Request,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    existing = _own_or_teacher(db, hid, user)
    d = parse_date(body.date, allow_past_equal=existing["date"])
    subject = one_line(body.subject, 2, 30, "نام درس باید ۲ تا ۳۰ حرف باشد.")
    text = clean(body.text, 3, 600, "توضیح تکلیف باید ۳ تا ۶۰۰ حرف باشد.")
    check_blocked(subject)
    check_blocked(text)

    if user["role"] not in STAFF_ROLES:
        allowed_norm = {_norm(s): s for s in get_allowed_subjects(db)}
        sn = _norm(subject)
        if sn not in allowed_norm:
            raise HTTPException(400, "نام درس معتبر نیست؛ لطفاً یکی از درس‌های برنامه کلاسی را انتخاب کن.")
        subject = allowed_norm[sn]

    status, ai_note = ai_moderate_homework(db, user, subject, text, d, client_ip(request), client_device(request))
    db.execute(
        "UPDATE homework SET date = ?, subject = ?, text = ?, status = ?, ai_note = ? WHERE id = ?",
        (d, subject, text, status, ai_note, hid),
    )
    db.commit()
    return hw_out(db.execute(HW_SELECT + " WHERE h.id = ?", (hid,)).fetchone())


@app.post("/api/homework/{hid}/approve")
def approve_homework(
    hid: str,
    _: sqlite3.Row = Depends(teacher_only),
    db: sqlite3.Connection = Depends(get_db),
):
    row = db.execute("SELECT id, subject, author_id, status FROM homework WHERE id = ?", (hid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این تکلیف پیدا نشد.")
    db.execute("UPDATE homework SET status = 'approved', ai_note = '' WHERE id = ?", (hid,))
    if row["status"] != "approved":
        push_notification(
            db,
            row["author_id"],
            "answer",
            f"تکلیف «{row['subject']}» تایید و منتشر شد",
            "تکلیفی که ثبت کرده بودی توسط معلم/مدیر تایید شد و اکنون برای همه قابل مشاهده است.",
            link=f"hw:{hid}",
        )
    db.commit()
    return hw_out(db.execute(HW_SELECT + " WHERE h.id = ?", (hid,)).fetchone())


@app.delete("/api/homework/{hid}", status_code=204)
def delete_homework(
    hid: str,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    existing = _own_or_teacher(db, hid, user)
    if existing["author_id"] != user["id"]:
        push_notification(
            db,
            existing["author_id"],
            "removed",
            f"تکلیف «{existing['subject']}» حذف شد",
            f"تکلیفی که برای تاریخ {existing['date']} ثبت کرده بودی توسط معلم یا مدیر حذف شد.",
        )
    db.execute("DELETE FROM answers WHERE question_id IN (SELECT id FROM questions WHERE homework_id = ?)", (hid,))
    db.execute("DELETE FROM questions WHERE homework_id = ?", (hid,))
    db.execute("DELETE FROM homework WHERE id = ?", (hid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- امتحان‌ها (فقط معلم و مدیر می‌توانند ثبت/ویرایش/حذف کنند!)
@app.get("/api/exams")
def list_exams(request: Request, db: sqlite3.Connection = Depends(get_db)):
    rows = db.execute(EXAM_SELECT + " ORDER BY e.date, e.created_at").fetchall()
    return etag_json(request, [exam_out(r) for r in rows])


@app.post("/api/exams", status_code=201)
def add_exam(
    body: ExamIn,
    user: sqlite3.Row = Depends(teacher_only),   # دانش‌آموز مطلقاً حق ثبت امتحان ندارد!
    db: sqlite3.Connection = Depends(get_db),
):
    d = parse_date(body.date)
    subject = one_line(body.subject, 2, 30, "نام درس باید ۲ تا ۳۰ حرف باشد.")
    text = clean(body.text, 0, 600, "توضیحات امتحان حداکثر ۶۰۰ حرف باشد.") if body.text.strip() else ""
    eid = uuid.uuid4().hex
    db.execute(
        "INSERT INTO exams (id, date, subject, text, author_id, created_at) VALUES (?, ?, ?, ?, ?, ?)",
        (eid, d, subject, text, user["id"], now_ms()),
    )
    push_notification(
        db,
        None,
        "exam",
        f"امتحان جدید: {subject} ({d})",
        text or f"امتحان درس {subject} توسط {user['name']} ثبت شد.",
        link=f"exam:{eid}",
        broadcast=True,
    )
    db.commit()
    row = db.execute(EXAM_SELECT + " WHERE e.id = ?", (eid,)).fetchone()
    return exam_out(row)


@app.put("/api/exams/{eid}")
def update_exam(
    eid: str,
    body: ExamIn,
    _: sqlite3.Row = Depends(teacher_only),
    db: sqlite3.Connection = Depends(get_db),
):
    existing = db.execute("SELECT id, date FROM exams WHERE id = ?", (eid,)).fetchone()
    if existing is None:
        raise HTTPException(404, "این امتحان پیدا نشد.")
    d = parse_date(body.date, allow_past_equal=existing["date"])
    subject = one_line(body.subject, 2, 30, "نام درس باید ۲ تا ۳۰ حرف باشد.")
    text = clean(body.text, 0, 600, "توضیحات امتحان حداکثر ۶۰۰ حرف باشد.") if body.text.strip() else ""
    db.execute("UPDATE exams SET date = ?, subject = ?, text = ? WHERE id = ?", (d, subject, text, eid))
    db.commit()
    return exam_out(db.execute(EXAM_SELECT + " WHERE e.id = ?", (eid,)).fetchone())


@app.delete("/api/exams/{eid}", status_code=204)
def delete_exam(
    eid: str,
    _: sqlite3.Row = Depends(teacher_only),
    db: sqlite3.Connection = Depends(get_db),
):
    if not db.execute("SELECT 1 FROM exams WHERE id = ?", (eid,)).fetchone():
        raise HTTPException(404, "این امتحان پیدا نشد.")
    db.execute("DELETE FROM exams WHERE id = ?", (eid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- اعلان‌ها و اطلاعیه‌ها
@app.get("/api/notifications")
def get_notifications(user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    r_read = db.execute("SELECT last_read_at FROM notif_reads WHERE user_id = ?", (user["id"],)).fetchone()
    last_read = r_read["last_read_at"] if r_read else 0
    rows = db.execute(
        "SELECT id, kind, title, body, link, broadcast, created_at FROM notifications "
        "WHERE broadcast = 1 OR user_id = ? ORDER BY created_at DESC LIMIT 60",
        (user["id"],),
    ).fetchall()
    items = []
    unread = 0
    for r in rows:
        is_unread = r["created_at"] > last_read and r["created_at"] >= user["created_at"]
        if is_unread:
            unread += 1
        items.append({
            "id": r["id"],
            "kind": r["kind"],
            "title": r["title"],
            "body": r["body"],
            "link": r["link"],
            "broadcast": bool(r["broadcast"]),
            "createdAt": r["created_at"],
            "unread": is_unread,
        })
    return JSONResponse({"items": items, "unread": unread}, headers=NO_STORE)


@app.post("/api/notifications/read")
def read_notifications(user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    now = now_ms()
    db.execute(
        "INSERT INTO notif_reads (user_id, last_read_at) VALUES (?, ?) "
        "ON CONFLICT(user_id) DO UPDATE SET last_read_at = excluded.last_read_at",
        (user["id"], now),
    )
    db.commit()
    return {"ok": True}


@app.post("/api/admin/announcements", status_code=201)
def create_announcement(
    body: AnnouncementIn,
    _: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    title = one_line(body.title, 3, 80, "عنوان اطلاعیه باید ۳ تا ۸۰ حرف باشد.")
    text = clean(body.body, 0, 400, "متن اطلاعیه حداکثر ۴۰۰ حرف باشد.") if body.body.strip() else ""
    push_notification(db, None, "announcement", title, text, broadcast=True)
    db.commit()
    return {"ok": True}


@app.delete("/api/admin/announcements/{nid}", status_code=204)
def delete_announcement(nid: int, _: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    db.execute("DELETE FROM notifications WHERE id = ? AND broadcast = 1", (nid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- چت با هوش مصنوعی (فقط مدیر یا دانش‌آموز دارای سهمیه)
@app.post("/api/ai/chat")
def ai_chat(
    body: AiChatIn,
    user: sqlite3.Row = Depends(current_user),
    db: sqlite3.Connection = Depends(get_db),
):
    if not ATRIA_API_KEY:
        raise HTTPException(503, "کلید هوش مصنوعی (ATRIA_API_KEY) هنوز روی سرور تنظیم نشده است.")

    # بررسی و مصرف سهمیه چت روزانه (برای دانش‌آموزان پیش‌فرض ۰ است؛ برای ادمین نامحدود)
    consume(db, user, "ai")
    db.commit()

    cleaned_msgs = []
    for m in body.messages[-10:]:
        role = "assistant" if m.role == "assistant" else "user"
        txt = clean(m.content, 1, 2000, "پیام باید بین ۱ تا ۲۰۰۰ حرف باشد.")
        check_blocked(txt)
        cleaned_msgs.append({"role": role, "content": txt})
    if not cleaned_msgs or cleaned_msgs[-1]["role"] != "user":
        raise HTTPException(400, "پیام کاربر یافت نشد.")

    sys_prompt = (
        f"تو دستیار هوشمند درسی کلاس ۹۰۱ دبیرستان شهید بهشتی (پایه نهم) هستی. "
        f"نام کاربر فعلی «{user['name']}» است. به زبان فارسی روان، دقیق، علمی و صمیمی پاسخ بده. "
        "به دانش‌آموزان در یادگیری مفاهیم درسی (ریاضی، علوم، فیزیک، شیمی، زیست، ادبیات، عربی، زبان و ...)، "
        "حل گام‌به‌گام تمرین‌ها و برنامه‌ریزی مطالعه برای امتحانات کمک کن."
    )
    payload = {
        "model": ATRIA_MODEL,
        "messages": [{"role": "system", "content": sys_prompt}, *cleaned_msgs],
        "stream": False,
        "temperature": 0.3,
        "max_tokens": 1200,
    }
    req = urllib.request.Request(
        f"{ATRIA_BASE_URL}/chat/completions",
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {ATRIA_API_KEY}",
            "Content-Type": "application/json",
            "User-Agent": "TaklifSchoolApp/2.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=45) as resp:
            raw = json.loads(resp.read().decode("utf-8"))
        reply = (raw.get("choices") or [{}])[0].get("message", {}).get("content", "")
        reply = re.sub(r"<think>[\s\S]*?</think>", "", reply or "").strip()
        if not reply:
            reply = "پاسخی دریافت نشد. دوباره تلاش کن."
    except urllib.error.HTTPError as e:
        log.error("Atria chat HTTP error %s", e.code)
        raise HTTPException(502, "سرویس هوش مصنوعی در حال حاضر شلوغ است. چند لحظه بعد دوباره امتحان کن.")
    except Exception as e:
        log.error("Atria chat error: %s", e)
        raise HTTPException(502, "ارتباط با سرویس هوش مصنوعی برقرار نشد. دوباره تلاش کن.")

    return JSONResponse({"reply": reply, "quota": quota_out(db, user)}, headers=NO_STORE)


# ---------------------------------------------------------------- مدیریت معلم‌ها (فقط مدیر)
@app.get("/api/admin/teachers")
def list_teachers(_: sqlite3.Row = Depends(admin_only), db: sqlite3.Connection = Depends(get_db)):
    rows = db.execute(
        "SELECT username, name, subject, created_at FROM users WHERE role = 'teacher' ORDER BY created_at, id"
    ).fetchall()
    return JSONResponse([teacher_out(r) for r in rows], headers=NO_STORE)


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
    db.execute("DELETE FROM users WHERE id = ?", (row["id"],))
    db.execute("DELETE FROM bans WHERE kind = 'user' AND value = ?", (row["username"],))
    purge_orphans(db)
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- سهمیه‌ی امروز
@app.get("/api/quota")
def my_quota(user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    return JSONResponse(quota_out(db, user), headers=NO_STORE)


# ---------------------------------------------------------------- پرسش و پاسخ زیر هر تکلیف
def qa_out(r: sqlite3.Row) -> dict:
    return {
        "id": r["id"], "text": r["text"], "createdAt": r["created_at"],
        "author": r["name"], "authorId": r["username"],
        "authorRole": r["role"], "authorSubject": r["subject"],
    }


def _hw_row(db: sqlite3.Connection, hid: str) -> sqlite3.Row:
    if not HID_RE.match(hid):
        raise HTTPException(404, "این تکلیف پیدا نشد.")
    row = db.execute("SELECT id, subject, text, author_id FROM homework WHERE id = ?", (hid,)).fetchone()
    if not row:
        raise HTTPException(404, "این تکلیف پیدا نشد.")
    return row


def _is_staff(user: sqlite3.Row) -> bool:
    return user["role"] in STAFF_ROLES


@app.get("/api/homework/{hid}/questions")
def list_questions(hid: str, db: sqlite3.Connection = Depends(get_db)):
    _hw_row(db, hid)
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
    return JSONResponse(out, headers=NO_STORE)


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
    hw = _hw_row(db, hid)
    text = clean(body.text, 3, 300, "سؤال باید ۳ تا ۳۰۰ حرف باشد.")
    check_blocked(text)
    if _recent_duplicate(db, "questions", user["id"], text):
        raise HTTPException(409, "این سؤال را همین الان پرسیده‌ای.")
    if db.execute("SELECT COUNT(*) FROM questions WHERE homework_id = ?", (hid,)).fetchone()[0] >= MAX_QUESTIONS_PER_HW:
        raise HTTPException(400, "زیر این تکلیف تعداد سؤال‌ها به سقف رسیده است.")

    ai_moderate_qa(
        db, user, "سؤال", f"{hw['subject']}: {hw['text']}", text, client_ip(request), client_device(request)
    )
    consume(db, user, "question")
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
    qrow = db.execute("SELECT id, homework_id, author_id, text FROM questions WHERE id = ?", (qid,)).fetchone()
    if not qrow:
        raise HTTPException(404, "این سؤال پیدا نشد.")
    text = clean(body.text, 1, 500, "پاسخ باید ۱ تا ۵۰۰ حرف باشد.")
    check_blocked(text)
    if _recent_duplicate(db, "answers", user["id"], text):
        raise HTTPException(409, "این پاسخ را همین الان فرستاده‌ای.")
    if db.execute("SELECT COUNT(*) FROM answers WHERE question_id = ?", (qid,)).fetchone()[0] >= MAX_ANSWERS_PER_Q:
        raise HTTPException(400, "زیر این سؤال تعداد پاسخ‌ها به سقف رسیده است.")

    ai_moderate_qa(db, user, "پاسخ", qrow["text"], text, client_ip(request), client_device(request))
    consume(db, user, "answer")
    cur = db.execute(
        "INSERT INTO answers (question_id, author_id, text, ip, created_at) VALUES (?, ?, ?, ?, ?)",
        (qid, user["id"], text, client_ip(request), now_ms()),
    )
    if qrow["author_id"] != user["id"]:
        push_notification(
            db,
            qrow["author_id"],
            "answer",
            f"پاسخ جدید از {user['name']}",
            text[:160],
            link=f"hw:{qrow['homework_id']}",
        )
    db.commit()
    row = db.execute(
        "SELECT a.id, a.text, a.created_at, u.username, u.name, u.role, u.subject "
        "FROM answers a JOIN users u ON u.id = a.author_id WHERE a.id = ?", (cur.lastrowid,),
    ).fetchone()
    return qa_out(row)


@app.delete("/api/questions/{qid}", status_code=204)
def delete_question(qid: int, user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    row = db.execute("SELECT id, author_id, text FROM questions WHERE id = ?", (qid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این سؤال پیدا نشد.")
    if not _is_staff(user) and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط پرسنده یا معلم می‌تواند این سؤال را حذف کند.")
    if row["author_id"] != user["id"]:
        push_notification(db, row["author_id"], "removed", "سؤال تو توسط معلم/مدیر حذف شد", row["text"][:140])
    db.execute("DELETE FROM answers WHERE question_id = ?", (qid,))
    db.execute("DELETE FROM questions WHERE id = ?", (qid,))
    db.commit()
    return Response(status_code=204)


@app.delete("/api/answers/{aid}", status_code=204)
def delete_answer(aid: int, user: sqlite3.Row = Depends(current_user), db: sqlite3.Connection = Depends(get_db)):
    row = db.execute("SELECT id, author_id, text FROM answers WHERE id = ?", (aid,)).fetchone()
    if row is None:
        raise HTTPException(404, "این پاسخ پیدا نشد.")
    if not _is_staff(user) and row["author_id"] != user["id"]:
        raise HTTPException(403, "فقط پاسخ‌دهنده یا معلم می‌تواند این پاسخ را حذف کند.")
    if row["author_id"] != user["id"]:
        push_notification(db, row["author_id"], "removed", "پاسخ تو توسط معلم/مدیر حذف شد", row["text"][:140])
    db.execute("DELETE FROM answers WHERE id = ?", (aid,))
    db.commit()
    return Response(status_code=204)


# ---------------------------------------------------------------- پنل مدیر: حساب‌ها، سهمیه‌ها، IPها، مسدودی‌ها
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
            "limits": user_limits_info(db, r["id"], r["role"]),
        })
    return JSONResponse(out, headers=NO_STORE)


@app.put("/api/admin/users/{username}/limits")
def set_user_limits(
    username: str,
    body: LimitsIn,
    _: sqlite3.Row = Depends(admin_only),
    db: sqlite3.Connection = Depends(get_db),
):
    u = db.execute("SELECT id, role FROM users WHERE username = ?", (username.strip().lower(),)).fetchone()
    if not u:
        raise HTTPException(404, "این کاربر پیدا نشد.")
    for val in (body.homework, body.question, body.answer, body.ai):
        if val is not None and not (0 <= val <= 200):
            raise HTTPException(400, "هر سهمیه باید عددی بین ۰ تا ۲۰۰ باشد.")
    db.execute(
        "INSERT INTO user_limits (user_id, hw_limit, q_limit, a_limit, ai_chat_limit) VALUES (?, ?, ?, ?, ?) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "hw_limit = excluded.hw_limit, q_limit = excluded.q_limit, "
        "a_limit = excluded.a_limit, ai_chat_limit = excluded.ai_chat_limit",
        (u["id"], body.homework, body.question, body.answer, body.ai),
    )
    db.commit()
    return JSONResponse(user_limits_info(db, u["id"], u["role"]), headers=NO_STORE)


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
        # مسدودسازی خودکار تمام شناسه‌های دستگاه (Device ID) مرتبط با این کاربر تا نتواند اکانت جدید بسازد!
        admin_devs = {
            r["device_id"]
            for r in db.execute(
                "SELECT ud.device_id FROM user_devices ud JOIN users u ON u.id = ud.user_id WHERE u.role = 'admin'"
            )
        }
        for r in db.execute("SELECT device_id FROM user_devices WHERE user_id = ?", (target["id"],)):
            dev_id = r["device_id"]
            if dev_id and dev_id not in admin_devs:
                db.execute("DELETE FROM bans WHERE kind = 'device' AND value = ?", (dev_id,))
                db.execute(
                    "INSERT INTO bans (kind, value, reason, created_at, expires_at, created_by) VALUES ('device', ?, ?, ?, ?, ?)",
                    (dev_id, f"دستگاه مرتبط با {value}" + (f" ({reason})" if reason else ""), now_ms(), expires, admin["username"]),
                )
    elif kind == "ip":
        try:
            value = str(ipaddress.ip_address(body.value.strip()))
        except ValueError:
            raise HTTPException(400, "آدرس IP معتبر نیست.")
        if value == client_ip(request) or db.execute(
            "SELECT 1 FROM user_ips ui JOIN users u ON u.id = ui.user_id WHERE ui.ip = ? AND u.role = 'admin'", (value,)
        ).fetchone():
            raise HTTPException(400, "این IP متعلق به مدیر است؛ مسدودکردنش خودت را بیرون می‌اندازد.")
    elif kind == "device":
        value = body.value.strip()
        if not DEVICE_ID_RE.match(value):
            raise HTTPException(400, "شناسه دستگاه معتبر نیست.")
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
    row = db.execute("SELECT id, kind, value FROM bans WHERE id = ?", (bid,)).fetchone()
    if not row:
        raise HTTPException(404, "این مسدودی پیدا نشد.")
    # اگر مسدودی کاربر برداشته شد، مسدودی دستگاه‌های مرتبط با او را هم پاک کن
    if row["kind"] == "user":
        u = db.execute("SELECT id FROM users WHERE username = ?", (row["value"],)).fetchone()
        if u:
            db.execute(
                "DELETE FROM bans WHERE kind = 'device' AND value IN (SELECT device_id FROM user_devices WHERE user_id = ?)",
                (u["id"],),
            )
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
