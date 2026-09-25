"""
ALERT-TRIGGERED auto clicker + POPUP CLOSER + STRICT MOUSE LOCK + STOP KEY
STASH -> WAR -> RANDOM TELEPORT -> USE

Install:   python -m pip install pyautogui opencv-python numpy mss pygetwindow
Run:       python auto_click.py

How it works now:
  1) The script just WATCHES the game window (mouse is completely free, no delay).
  2) The instant an attack alert shows up it LOCKS the physical mouse and runs the
     STASH -> WAR -> RANDOM TELEPORT -> USE sequence immediately.
  3) Alert detection (any one of these triggers it, colors/background don't matter):
       a) red glowing frame around the screen (strict "alert red" colour on at
          least 2 of the 4 edges - not just any warm/reddish pixel)
       b) the real red warning triangle icon on the right side, matched against
          images/alert_triangle.png (a picture of the actual icon, not a
          shape/colour guess - this stops it firing on other red HUD elements
          like gold badges, flags, skulls, or resource gems)
       c) the window title starting with "INCOMING ATTACK"
     The border and triangle checks must both repeat for CONFIRM_FRAMES
     consecutive checks before they're trusted (title text is exact, so it
     fires immediately). This filters out one-off false reads.
  4) When the sequence ends the mouse is released. The script re-arms only after the
     alert has disappeared, so it never burns extra teleports on the same attack.

Strict mouse lock (Windows), 3 layers:
  1) low-level mouse hook  -> blocks EVERY mouse move / click / wheel event except
                              the script's own clicks
  2) ClipCursor            -> pointer is pinned to a 1-pixel box
  3) enforcer thread       -> every 10 ms puts the pointer back if it moved
The keyboard is NEVER locked. Press the STOP KEY (default F8) to stop everything
instantly (works while the mouse is locked, and the mouse-corner failsafe is off,
so ONLY the keyboard can stop the script).
"""
import os
import json
import time
import atexit
import ctypes
import queue
import threading
from datetime import datetime

import cv2
import mss
import numpy as np
import pyautogui
import tkinter as tk
from tkinter import ttk

# ---------------- SETTINGS ----------------
HERE = os.path.dirname(os.path.abspath(__file__))
IMG = os.path.join(HERE, "images")

STOP_KEY = "f8"          # f1-f12, esc, pause, space, a-z, 0-9
BLOCK_MOUSE = True       # lock the physical mouse when an alert is detected
CLIP_CURSOR = True       # layers 2+3: pin the pointer and enforce it
MAX_BLOCK_SECONDS = 30   # safety: lock releases itself after this long

CONFIDENCE = 0.80
TIMEOUT = 3
POLL = 0.0
CACHE_PAD = 40

USE_OFFSET = (310, 203)

# ----- alert detection -----
WATCH_INTERVAL = 0.02    # seconds between screen checks (~10 ms per check itself)
DETECT_BORDER = True     # red glowing frame around the screen
DETECT_TRIANGLE = True   # the actual attack-alert triangle icon (template match)
DETECT_TITLE = True      # window title contains TITLE_TRIGGER (needs pygetwindow)
TITLE_TRIGGER = "INCOMING ATTACK"

# The border/triangle checks are colour-based and any UI can *look* reddish
# (gold badges, flags, skull icons, resource gems, etc. are all "reddish" too).
# To avoid false positives we now require:
#   - a tight, saturated "alert red" hue band (not just R > G/B) for the border
#   - the real triangle ICON matched by its picture (alert_triangle.png), not
#     just "a reddish triangle-ish blob"
#   - CONFIRM_FRAMES consecutive detections in a row before it's trusted
#     (title-bar text is exact, so it never needs confirming)
RED_HUE_LOW = 8          # OpenCV hue 0-179: red wraps around 0/180
RED_HUE_HIGH = 172
RED_SAT_MIN = 70         # HSV saturation (0-255) - excludes washed-out/gold/tan UI
RED_VAL_MIN = 50         # HSV value (0-255) - excludes near-black noise
LINE_FRAC = 0.60         # share of an edge line that must be "alert red"
SIDES_NEEDED = 2         # how many of the 4 edges must show the red frame
                         # (kept low on purpose: the top edge is very often the
                         # OS window title bar, not game content, so it rarely
                         # lights up even during a real alert - 2 real sides is
                         # already a much stronger signal than the old "any
                         # warm-toned pixel counts as red" check ever needed)
BORDER_THICKNESS_FRAC = 0.012   # how thick (fraction of min(h,w)) the glow band is

TRIANGLE_TEMPLATE = "alert_triangle.png"   # crop of the real icon, see images/
TRIANGLE_CONFIDENCE = 0.55                 # shape-match floor (just locates the icon's
                                            # spot - the structural check, below, is
                                            # what actually decides real vs. false)
TRIANGLE_ZONE = (0.80, 1.00, 0.30, 0.90)   # (x0, x1, y0, y1) fraction of screen to search
TRIANGLE_STRUCT_CORR_MIN = 0.6   # mean-subtracted correlation, at the template's fill
                                  # pixels, between template and the matched spot.
                                  # This is what rejects a uniform red field (team
                                  # territory colour, a red rank/star badge, etc.) that
                                  # happens to sit inside the icon's silhouette, and
                                  # also rejects yellow/green versions of the same icon.
                                  # Tested: real icon (any background) ~1.0; red-territory
                                  # false positive 0.05; yellow/green variants 0.12-0.30.

CONFIRM_FRAMES = 2       # consecutive watch-loop hits needed for border/triangle

# ----- after a run -----
SEQUENCE_TRIES = 3       # attempts at the sequence per alert
RETRY_DELAY = 2.0        # if the sequence failed, re-arm after this many seconds
REARM_MIN = 3.0          # minimum seconds before re-arming after a successful run
CLEAR_SECONDS = 1.5      # alert must be gone this long before re-arming (it pulses)

# ----- popup closing -----
CLOSE_POPUPS = True
QUICK_CHECK = 0.3
CLOSE_WAIT = 1.2
MAX_CLOSE_TRIES = 3
GAME_TITLE = "WAR PLANET"
FIXED_CLICK = None       # e.g. (0.05, 0.60); None = auto pick

# ----- leaving Provinces/Globe mode -----
# If the player is on the Provinces/Globe strategic map (no STASH button
# there at all - it's replaced by RENEGADES in that mode), clicking outside
# to "close a popup" will never bring STASH back. The MAP nav button (bottom
# right) is present and in the same spot in every mode, so it's used as a
# universal "go back to the normal base/map view" recovery step.
AUTO_EXIT_PROVINCES_MODE = True
MAP_BUTTON_TEMPLATE = "map_button.png"
MAP_BUTTON_CONFIDENCE = 0.70   # a bit below the default CONFIDENCE: this button's
                                # match score dips slightly while on the Provinces
                                # map itself (tested ~0.76 there vs ~1.0 elsewhere)
MAP_RECOVERY_WAIT = 1.2        # settle time after clicking MAP before re-checking
MAX_MAP_RECOVERY_TRIES = 2

# Clicking the MAP nav button still means finding it on screen first
# (template search), which costs time. Tapping anywhere on the map itself
# does the same thing while on the Provinces/Globe view (it switches back
# to the normal map view there) with no search needed at all - just a
# straight click - so it's tried FIRST, before the slower popup-closing
# loop and before the MAP-button search fallback.
CENTER_CLICK_RECOVERY = True
CENTER_CLICK_WAIT = 2.0        # fixed settle time after the click before
                                # re-checking for STASH (not randomized)

pyautogui.PAUSE = 0
pyautogui.FAILSAFE = False   # keyboard-only stop (STOP_KEY)
# ------------------------------------------

IS_WIN = os.name == "nt"

try:  # real pixel coordinates on scaled Windows displays
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    pass

MSS = getattr(mss, "MSS", None) or mss.mss

ZONES = {
    "left":   (0.025, 0.085, 0.25, 0.95),
    "right":  (0.915, 0.975, 0.25, 0.95),
    "bottom": (0.150, 0.850, 0.925, 0.975),
}
PATCH = 41


# =====================================================================
#  Stop key + cooperative cancel
# =====================================================================
class StopRequested(Exception):
    pass


STOP = threading.Event()
DONE = threading.Event()

# =====================================================================
#  History log (feeds the dashboard UI, and survives closing the app)
# =====================================================================
EVENT_QUEUE = queue.Queue()

LOG_DIR = os.path.join(HERE, "logs")          # one file per day: logs/history_2026-09-25.jsonl
LOG_LOCK = threading.Lock()
LOG_KEEP_DAYS = 30                             # older daily log files are pruned on startup


def log_file_path(dt=None):
    dt = dt or datetime.now()
    return os.path.join(LOG_DIR, f"history_{dt.strftime('%Y-%m-%d')}.jsonl")


def log_event(kind, **fields):
    """Push an event for the dashboard to display, and - for real attack/dodge
    events - append it to today's log file so the history survives a restart.
    kind: 'status' | 'lock' | 'unlock' | 'alert' (attack seen) | 'dodge' (sequence finished)."""
    fields["kind"] = kind
    fields["time"] = datetime.now().strftime("%H:%M:%S")
    EVENT_QUEUE.put(fields)
    if kind in ("alert", "dodge"):
        try:
            os.makedirs(LOG_DIR, exist_ok=True)
            with LOG_LOCK, open(log_file_path(), "a", encoding="utf-8") as fh:
                fh.write(json.dumps(fields) + "\n")
        except Exception as e:
            print(f"Could not write history log: {e}")


def load_today_events():
    """Read back today's log file (if any) so the dashboard can show a full
    day's history even after the app was closed and reopened."""
    path = log_file_path()
    if not os.path.exists(path):
        return []
    events = []
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    events.append(json.loads(line))
                except Exception:
                    continue
    except Exception as e:
        print(f"Could not read history log: {e}")
    return events


def prune_old_logs():
    """Delete daily log files older than LOG_KEEP_DAYS so logs/ doesn't grow forever."""
    if not os.path.isdir(LOG_DIR):
        return
    cutoff = time.time() - LOG_KEEP_DAYS * 86400
    for name in os.listdir(LOG_DIR):
        if name.startswith("history_") and name.endswith(".jsonl"):
            p = os.path.join(LOG_DIR, name)
            try:
                if os.path.getmtime(p) < cutoff:
                    os.remove(p)
            except Exception:
                pass


def check_stop():
    if STOP.is_set():
        raise StopRequested()


def sleep(sec):
    """Sleep, but react to the stop key within 50 ms."""
    end = time.time() + sec
    while True:
        check_stop()
        left = end - time.time()
        if left <= 0:
            return
        time.sleep(min(left, 0.05))


def vk_code(name):
    n = name.strip().lower()
    special = {"esc": 0x1B, "escape": 0x1B, "pause": 0x13, "space": 0x20,
               "enter": 0x0D, "tab": 0x09, "backspace": 0x08, "delete": 0x2E,
               "home": 0x24, "end": 0x23, "insert": 0x2D, "caps": 0x14}
    if n in special:
        return special[n]
    if n.startswith("f") and n[1:].isdigit() and 1 <= int(n[1:]) <= 24:
        return 0x70 + int(n[1:]) - 1
    if len(n) == 1 and n.isalnum():
        return ord(n.upper())
    raise ValueError(f"Unknown STOP_KEY: {name!r}")


def _watch_stop_key(vk):
    while not DONE.is_set():
        if ctypes.windll.user32.GetAsyncKeyState(vk) & 0x8000:
            STOP.set()
            return
        time.sleep(0.01)


# =====================================================================
#  Strict physical mouse lock
# =====================================================================
if IS_WIN:
    from ctypes import wintypes

    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    LRESULT = ctypes.c_ssize_t
    HOOKPROC = ctypes.WINFUNCTYPE(LRESULT, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)

    user32.SetWindowsHookExW.argtypes = [ctypes.c_int, HOOKPROC, wintypes.HINSTANCE, wintypes.DWORD]
    user32.SetWindowsHookExW.restype = wintypes.HHOOK
    user32.CallNextHookEx.argtypes = [wintypes.HHOOK, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM]
    user32.CallNextHookEx.restype = LRESULT
    user32.UnhookWindowsHookEx.argtypes = [wintypes.HHOOK]
    user32.GetMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT]
    user32.GetMessageW.restype = ctypes.c_int
    user32.PeekMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT,
                                    wintypes.UINT, wintypes.UINT]
    user32.PostThreadMessageW.argtypes = [wintypes.DWORD, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
    user32.GetCursorPos.argtypes = [ctypes.POINTER(wintypes.POINT)]
    user32.SetCursorPos.argtypes = [ctypes.c_int, ctypes.c_int]
    user32.ClipCursor.argtypes = [ctypes.POINTER(wintypes.RECT)]
    kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
    kernel32.GetModuleHandleW.restype = wintypes.HMODULE
    kernel32.GetCurrentThreadId.restype = wintypes.DWORD


class MouseBlocker:
    """The hook is installed once at startup but only blocks while `engaged`."""
    WH_MOUSE_LL = 14
    WM_QUIT = 0x0012

    def __init__(self):
        self.allow = False       # True only while the script itself is clicking
        self.engaged = False     # True while the physical mouse is locked
        self.lock = threading.RLock()   # held by the script while it clicks
        self.deadline = None
        self.blocked = 0
        self.seen = 0
        self.pin = None
        self.hook_ok = False
        self._gen = 0
        self._tid = None
        self._hook = None
        self._proc = None
        self._thread = None
        self._ready = threading.Event()

    # ----- install once / shut down -----
    def install(self):
        if not IS_WIN or self._thread:
            return self.hook_ok
        self._ready.clear()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        self._ready.wait(3)
        self.hook_ok = bool(self._hook)
        return self.hook_ok

    def shutdown(self):
        self.release()
        if self._tid and self.hook_ok:
            user32.PostThreadMessageW(self._tid, self.WM_QUIT, 0, 0)
        if self._thread:
            self._thread.join(2)

    # ----- lock / unlock (instant) -----
    def engage(self, max_seconds=None):
        if not IS_WIN or self.engaged:
            return
        self.deadline = time.time() + max_seconds if max_seconds else None
        self.engaged = True              # hook starts swallowing mouse events NOW
        if CLIP_CURSOR:
            self.pin_here()
            self._gen += 1
            threading.Thread(target=self._enforce, args=(self._gen,), daemon=True).start()

    def release(self):
        if not self.engaged:
            return
        self.engaged = False
        self.unclip()

    # ----- layer 1: hook -----
    def _callback(self, nCode, wParam, lParam):
        if nCode >= 0:
            self.seen += 1
            if self.engaged and not self.allow:
                expired = self.deadline is not None and time.time() > self.deadline
                if not expired:
                    self.blocked += 1
                    return 1
        return user32.CallNextHookEx(None, nCode, wParam, lParam)

    def _run(self):
        self._tid = kernel32.GetCurrentThreadId()
        msg = wintypes.MSG()
        user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 0)   # create message queue
        self._proc = HOOKPROC(self._callback)                   # keep a reference
        self._hook = user32.SetWindowsHookExW(self.WH_MOUSE_LL, self._proc,
                                              kernel32.GetModuleHandleW(None), 0)
        self._ready.set()
        if not self._hook:
            return
        while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
            pass
        user32.UnhookWindowsHookEx(self._hook)
        self._hook = None

    # ----- layers 2 + 3 -----
    def _apply_clip(self):
        if self.pin:
            x, y = self.pin
            rect = wintypes.RECT(x, y, x + 1, y + 1)
            user32.ClipCursor(ctypes.byref(rect))

    def pin_here(self):
        if not (IS_WIN and CLIP_CURSOR and self.engaged):
            return
        pt = wintypes.POINT()
        if user32.GetCursorPos(ctypes.byref(pt)):
            self.pin = (pt.x, pt.y)
            self._apply_clip()

    def unclip(self):
        if IS_WIN:
            user32.ClipCursor(None)

    def _enforce(self, gen):
        while self.engaged and self._gen == gen:
            if self.deadline is not None and time.time() > self.deadline:
                self.release()           # safety timeout
                return
            if self.pin and self.lock.acquire(blocking=False):
                try:
                    if not self.allow:
                        pt = wintypes.POINT()
                        if user32.GetCursorPos(ctypes.byref(pt)) and (pt.x, pt.y) != self.pin:
                            user32.SetCursorPos(*self.pin)
                        self._apply_clip()
                finally:
                    self.lock.release()
            time.sleep(0.01)


BLOCKER = MouseBlocker()
atexit.register(BLOCKER.shutdown)


def click(x, y):
    """Script click: the only mouse input that passes the lock."""
    check_stop()
    with BLOCKER.lock:
        BLOCKER.allow = True
        BLOCKER.unclip()
        try:
            pyautogui.click(x, y)
            time.sleep(0.01)           # let the click events finish passing the hook
        finally:
            BLOCKER.pin_here()
            BLOCKER.allow = False


# =====================================================================
#  Popup-safe spot picking
# =====================================================================
def safe_spots(gray):
    h, w = gray.shape
    blur = cv2.GaussianBlur(gray, (3, 3), 0)
    lap = np.abs(cv2.Laplacian(blur, cv2.CV_32F))
    energy = cv2.boxFilter(lap, -1, (PATCH, PATCH))
    spots = []
    for x0, x1, y0, y1 in ZONES.values():
        xa, xb = int(x0 * w), int(x1 * w)
        ya, yb = int(y0 * h), int(y1 * h)
        if xb - xa < 2 or yb - ya < 2:
            continue
        sub = energy[ya:yb, xa:xb]
        iy, ix = np.unravel_index(np.argmin(sub), sub.shape)
        spots.append((float(sub[iy, ix]), xa + ix, ya + iy))
    spots.sort()
    return spots


# =====================================================================
#  Alert detection
#  - border: strict "alert red" hue/sat/val mask (not just R>G/B), so gold
#    badges, orange timers, maroon icons etc. no longer count as "red".
#  - triangle: matched against the real icon picture (alert_triangle.png)
#    instead of a generic red-triangle-shaped-blob guess, which is what was
#    catching every other reddish icon on the HUD.
# =====================================================================
def alert_red_mask(bgr):
    """Pixels that are specifically the saturated 'alert red' colour, not any
    reddish colour (excludes gold/orange badges, dull maroon icons, pink
    gems, etc. which all pass a plain R > G/B test)."""
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV)
    h, s, v = hsv[..., 0], hsv[..., 1], hsv[..., 2]
    return ((h <= RED_HUE_LOW) | (h >= RED_HUE_HIGH)) & (s >= RED_SAT_MIN) & (v >= RED_VAL_MIN)


def border_alert(bgr):
    """Red glowing frame: the outermost lines of the screen are mostly alert-red."""
    h, w = bgr.shape[:2]
    d = max(6, int(min(h, w) * BORDER_THICKNESS_FRAC))
    red = alert_red_mask(bgr)
    sides = (red[:d].mean(axis=1).max(),
             red[h - d:].mean(axis=1).max(),
             red[:, :d].mean(axis=0).max(),
             red[:, w - d:].mean(axis=0).max())
    return sum(v >= LINE_FRAC for v in sides) >= SIDES_NEEDED


class TriangleMatcher:
    """Template-matches the actual attack-alert triangle icon by SHAPE first
    (restricted to the corner of the HUD it lives in), then double-checks the
    actual PATTERN at that spot before accepting it.

    Three different false-positive traps, all fixed here:
      1) Background behind the icon's translucent panel changes (different
         terrain/map colours underneath it). Fix: the shape match that picks
         the CANDIDATE LOCATION is masked to only the icon's own red-fill
         pixels, so whatever is behind the panel never affects the score.
      2) A large solid-red area elsewhere on screen (e.g. a red-team-owned
         province on the map, or a red star/rank badge sitting on red
         territory) can score deceptively high on that same masked match,
         because a uniform red field trivially looks "red enough" everywhere
         within the icon's silhouette - there's no actual glyph there, just
         uniform colour. Fix: once a candidate location is found, we compute
         a mean-subtracted structural correlation (Pearson correlation)
         between the template and the candidate, using ONLY the fill-mask
         pixel positions. A uniform red field has essentially no structure
         at those positions relative to the template's own pattern, so it
         scores near zero, while the real icon (regardless of background)
         reproduces the template's brightness pattern almost exactly.
      3) A yellow/green version of the identical icon shape also fails this
         structural check, since its pixel values at the mask positions no
         longer vary the way the red template's do.
    Tested against a real alert screenshot, the same icon composited onto an
    unrelated background, a red province/rank-badge false positive, and
    simulated yellow/green variants: real cases score ~1.0, every false case
    scores well under 0.3.
    """

    def __init__(self):
        self._tpl = None
        self._icon_mask3 = None
        self._fill_mask = None

    def _template(self):
        if self._tpl is None:
            path = os.path.join(IMG, TRIANGLE_TEMPLATE)
            tpl = cv2.imread(path, cv2.IMREAD_COLOR)
            if tpl is None:
                raise FileNotFoundError(
                    f"{path} not found - put a cropped screenshot of the real "
                    f"alert triangle icon there (see images/{TRIANGLE_TEMPLATE})."
                )
            self._tpl = tpl
            self._fill_mask = alert_red_mask(tpl)             # the red fill only
            mask_u8 = self._fill_mask.astype(np.uint8) * 255
            self._icon_mask3 = cv2.merge([mask_u8, mask_u8, mask_u8])
        return self._tpl

    def _structural_corr(self, candidate):
        """Mean-subtracted correlation between template and candidate,
        evaluated only at the template's own fill-mask pixels."""
        m = self._fill_mask
        tpl = self._tpl
        corrs = []
        for c in range(3):
            t = tpl[..., c][m].astype(np.float64)
            v = candidate[..., c][m].astype(np.float64)
            t = t - t.mean()
            v = v - v.mean()
            denom = np.linalg.norm(t) * np.linalg.norm(v)
            corrs.append(0.0 if denom == 0 else float(np.dot(t, v) / denom))
        return sum(corrs) / len(corrs)

    def hit(self, bgr):
        tpl = self._template()
        th, tw = tpl.shape[:2]
        h, w = bgr.shape[:2]
        x0, x1 = int(w * TRIANGLE_ZONE[0]), int(w * TRIANGLE_ZONE[1])
        y0, y1 = int(h * TRIANGLE_ZONE[2]), int(h * TRIANGLE_ZONE[3])
        sub = bgr[y0:y1, x0:x1]
        if sub.shape[0] < th or sub.shape[1] < tw:
            return False
        # step 1: find the best candidate spot, ignoring whatever background
        # is behind the icon (masked to the icon's own pixels only)
        res = cv2.matchTemplate(sub, tpl, cv2.TM_CCORR_NORMED, mask=self._icon_mask3)
        _, score, _, loc = cv2.minMaxLoc(res)
        if score < TRIANGLE_CONFIDENCE:
            return False
        mx, my = loc
        candidate = sub[my:my + th, mx:mx + tw]
        if candidate.shape[:2] != (th, tw):
            return False
        # step 2: confirm it's the real glyph pattern, not just "red here"
        # (rejects uniform red fields - team territory, red badges, etc. -
        # and rejects yellow/green versions of the same icon shape)
        return self._structural_corr(candidate) >= TRIANGLE_STRUCT_CORR_MIN


TRIANGLE = TriangleMatcher()


# =====================================================================
#  Screen finder
# =====================================================================
class Finder:
    def __init__(self):
        self.sct = MSS()
        self.mon = self.sct.monitors[0]
        self.templates = {}
        self.cache = {}
        self._region = None
        self._region_t = 0.0

    def template(self, name):
        if name not in self.templates:
            path = os.path.join(IMG, name)
            img = cv2.imread(path, cv2.IMREAD_GRAYSCALE)
            if img is None:
                raise FileNotFoundError(path)
            self.templates[name] = img
        return self.templates[name]

    def _match(self, name, region, confidence=None):
        tpl = self.template(name)
        th, tw = tpl.shape
        left, top, w, h = region
        if w < tw or h < th:
            return None
        shot = self.sct.grab({"left": left, "top": top, "width": w, "height": h})
        gray = cv2.cvtColor(np.asarray(shot), cv2.COLOR_BGRA2GRAY)
        res = cv2.matchTemplate(gray, tpl, cv2.TM_CCOEFF_NORMED)
        _, score, _, loc = cv2.minMaxLoc(res)
        if score >= (CONFIDENCE if confidence is None else confidence):
            return left + loc[0], top + loc[1]
        return None

    def find(self, name, timeout=TIMEOUT, confidence=None):
        tpl = self.template(name)
        th, tw = tpl.shape
        m = self.mon
        full = (m["left"], m["top"], m["width"], m["height"])
        end = time.time() + timeout
        while True:
            check_stop()
            pos = None
            if name in self.cache:
                cx, cy = self.cache[name]
                l = max(m["left"], cx - CACHE_PAD)
                t = max(m["top"], cy - CACHE_PAD)
                r = min(m["left"] + m["width"], cx + tw + CACHE_PAD)
                b = min(m["top"] + m["height"], cy + th + CACHE_PAD)
                pos = self._match(name, (l, t, r - l, b - t), confidence)
            if pos is None:
                pos = self._match(name, full, confidence)
            if pos:
                self.cache[name] = pos
                return pos[0], pos[1], tw, th
            if time.time() >= end:
                return None
            if POLL:
                sleep(POLL)

    def _window(self):
        try:
            import pygetwindow as gw
            for win in gw.getWindowsWithTitle(GAME_TITLE):
                if win.width > 300 and win.height > 300 and not win.isMinimized:
                    return win
        except Exception:
            pass
        return None

    def game_region(self, max_age=0.0):
        now = time.time()
        if max_age and self._region and now - self._region_t < max_age:
            return self._region
        m = self.mon
        region = (m["left"], m["top"], m["width"], m["height"])
        win = self._window()
        if win:
            l = max(m["left"], win.left)
            t = max(m["top"], win.top)
            r = min(m["left"] + m["width"], win.left + win.width)
            b = min(m["top"] + m["height"], win.top + win.height)
            if r - l > 300 and b - t > 300:
                region = (l, t, r - l, b - t)
        self._region, self._region_t = region, now
        return region

    def alert_reason(self):
        """Return a short text if an attack alert is visible right now, else None."""
        if DETECT_TITLE:
            win = self._window()
            if win and TITLE_TRIGGER.upper() in (win.title or "").upper():
                return "window title"
        l, t, w, h = self.game_region(max_age=1.0)
        shot = self.sct.grab({"left": l, "top": t, "width": w, "height": h})
        bgr = np.asarray(shot)[..., :3]
        if DETECT_BORDER and border_alert(bgr):
            return "red screen border"
        if DETECT_TRIANGLE and TRIANGLE.hit(bgr):
            return "red warning triangle"
        return None

    def outside_click_point(self, attempt):
        l, t, w, h = self.game_region()
        if FIXED_CLICK:
            return int(l + FIXED_CLICK[0] * w), int(t + FIXED_CLICK[1] * h)
        shot = self.sct.grab({"left": l, "top": t, "width": w, "height": h})
        gray = cv2.cvtColor(np.asarray(shot), cv2.COLOR_BGRA2GRAY)
        spots = safe_spots(gray)
        _, x, y = spots[attempt % len(spots)]
        return l + x, t + y

    def find_map_button(self, timeout=TIMEOUT):
        return self.find(MAP_BUTTON_TEMPLATE, timeout=timeout, confidence=MAP_BUTTON_CONFIDENCE)

    def click_center_screen(self):
        """Tap dead-center of the game window. On the Provinces/Globe view
        this alone switches back to the normal map view (where STASH lives)
        - no template search needed, so it's effectively instant."""
        l, t, w, h = self.game_region()
        cx, cy = l + w // 2, t + h // 2
        click(cx, cy)
        print(f"Provinces mode -> tapped center at ({cx}, {cy})")

    def exit_to_map_mode(self):
        """Click the MAP nav button to leave Provinces/Globe (or any other
        mode) and return to the normal base/map view where STASH lives.
        Returns True if the button was found and clicked."""
        btn = self.find_map_button(timeout=QUICK_CHECK)
        if not btn:
            return False
        x, y, bw, bh = btn
        cx, cy = x + bw // 2, y + bh // 2
        click(cx, cy)
        print(f"Not on the normal map view -> clicked MAP at ({cx}, {cy})")
        return True

    def find_stash(self):
        hit = self.find("stash.png", timeout=QUICK_CHECK if CLOSE_POPUPS else TIMEOUT)
        if hit or not CLOSE_POPUPS:
            return hit
        # Try the fast path FIRST: if we're on the Provinces/Globe strategic
        # map, a single tap anywhere on the map flips it straight back to
        # the normal map view where STASH lives - no search, no popup-close
        # loop needed. Only fall back to the slower popup-closing loop and
        # the MAP-button search if this doesn't turn up STASH.
        if CENTER_CLICK_RECOVERY:
            self.click_center_screen()
            sleep(CENTER_CLICK_WAIT)
            hit = self.find("stash.png", timeout=QUICK_CHECK)
            if hit:
                return hit
        for attempt in range(MAX_CLOSE_TRIES):
            x, y = self.outside_click_point(attempt)
            click(x, y)
            print(f"Popup open -> clicked outside at ({x}, {y})")
            hit = self.find("stash.png", timeout=CLOSE_WAIT)
            if hit:
                return hit
        # Still no STASH - the MAP nav button is present and in the same
        # spot in every mode, so it's used as a last-resort universal
        # "go back to the normal base/map view" recovery step.
        if AUTO_EXIT_PROVINCES_MODE:
            for _ in range(MAX_MAP_RECOVERY_TRIES):
                if not self.exit_to_map_mode():
                    break
                hit = self.find("stash.png", timeout=MAP_RECOVERY_WAIT)
                if hit:
                    return hit
        return None


# =====================================================================
#  Main sequence
# =====================================================================
def run_once(f):
    """Run one STASH -> WAR -> RANDOM TELEPORT -> USE attempt.
    Returns (success, note); note names the step it stopped at, or a
    short summary of what ran, for the dashboard's history table."""
    hit = f.find_stash()
    if not hit:
        print("STASH not found.")
        return False, "stopped at STASH (not found)"
    click(hit[0] + hit[2] // 2, hit[1] + hit[3] // 2)
    print("Clicked STASH")

    hit = f.find("war.png")
    if not hit:
        print("WAR not found.")
        return False, "stopped at WAR (not found)"
    click(hit[0] + hit[2] // 2, hit[1] + hit[3] // 2)
    print("Clicked WAR")

    hit = f.find("random_teleport_title.png")
    if not hit:
        print("RANDOM TELEPORT not found.")
        return False, "stopped at RANDOM TELEPORT (not found)"
    click(hit[0] + USE_OFFSET[0], hit[1] + USE_OFFSET[1])
    print("Clicked USE")
    return True, "STASH -> WAR -> TELEPORT -> USE"


def wait_for_clear(f, ok):
    """Re-arm only after the alert is gone (or shortly after a failed attempt)."""
    if not ok:
        sleep(RETRY_DELAY)
        return
    t0 = time.time()
    clear_since = None
    told = False
    while True:
        check_stop()
        now = time.time()
        if f.alert_reason():
            clear_since = None
            if not told and now - t0 > 1:
                print("Waiting for the alert to clear before re-arming...")
                told = True
        elif clear_since is None:
            clear_since = now
        if clear_since is not None and now - clear_since >= CLEAR_SECONDS and now - t0 >= REARM_MIN:
            return
        time.sleep(WATCH_INTERVAL)


def watch_loop():
    """The original watch/detect/dodge loop, now running on a background
    thread and reporting each step through log_event() for the dashboard."""
    if IS_WIN:
        threading.Thread(target=_watch_stop_key, args=(vk_code(STOP_KEY),),
                         daemon=True).start()
        print(f"Press {STOP_KEY.upper()} at any time to stop.")
    else:
        print("Not Windows: stop key and mouse lock are disabled (use Ctrl+C).")

    try:
        if BLOCK_MOUSE and IS_WIN and not BLOCKER.install():
            print("WARNING: mouse hook failed; only the pointer pin will be used.")
            log_event("status", text="WARNING: mouse hook failed")
        f = Finder()
        print("Armed. Watching for the attack alert (mouse is free until it appears)...")
        log_event("status", text="Armed \u2013 watching for attacks")

        pending_reason = None
        pending_count = 0

        while True:
            check_stop()
            raw_reason = f.alert_reason()

            # Title text is an exact string match - trust it immediately.
            # Colour-based signals (border / triangle) must repeat for
            # CONFIRM_FRAMES consecutive checks before we act on them, so a
            # single stray/compressed frame can't fire a false alarm.
            if raw_reason == "window title":
                reason = raw_reason
                pending_reason, pending_count = None, 0
            elif raw_reason and raw_reason == pending_reason:
                pending_count += 1
                reason = raw_reason if pending_count >= CONFIRM_FRAMES else None
            elif raw_reason:
                pending_reason, pending_count = raw_reason, 1
                reason = None
            else:
                pending_reason, pending_count = None, 0
                reason = None

            if reason:
                if BLOCK_MOUSE:
                    BLOCKER.engage(MAX_BLOCK_SECONDS)   # lock FIRST, before anything else
                print(f"ALERT detected ({reason}) -> mouse locked, running now.")
                log_event("alert", reason=reason)
                log_event("lock")   # tell the UI to show the "don't touch the mouse" warning

                ok, note, tries_used = False, "", 0
                t_start = time.time()
                try:
                    for attempt in range(SEQUENCE_TRIES):
                        tries_used = attempt + 1
                        t0 = time.time()
                        ok, note = run_once(f)
                        print(f"Sequence took {time.time() - t0:.2f}s")
                        if ok:
                            break
                finally:
                    BLOCKER.release()
                    print("Mouse unlocked.")
                    log_event("unlock")   # tell the UI to hide the warning

                duration = time.time() - t_start
                log_event("dodge", reason=reason, result="dodged" if ok else "failed",
                           tries=tries_used, duration=f"{duration:.1f}s", note=note)

                wait_for_clear(f, ok)
                print("Re-armed.")
                log_event("status", text="Re-armed \u2013 watching for attacks")
            else:
                time.sleep(WATCH_INTERVAL)
    except StopRequested:
        print(f"Stopped ({STOP_KEY.upper()} pressed).")
        log_event("status", text=f"Stopped ({STOP_KEY.upper()} pressed)")
    except KeyboardInterrupt:
        print("Stopped (Ctrl+C).")
        log_event("status", text="Stopped (Ctrl+C)")
    except Exception as e:
        print(f"Watch loop crashed: {e}")
        log_event("status", text=f"Crashed: {e}")
    finally:
        DONE.set()
        blocked = BLOCKER.blocked
        BLOCKER.shutdown()
        print(f"Mouse unlocked. Physical mouse events blocked: {blocked}")


# =====================================================================
#  Dashboard UI - shows attack/dodge history while watch_loop runs
# =====================================================================
class Dashboard:
    def __init__(self, root):
        self.root = root
        self.counts = {"alerts": 0, "dodged": 0, "failed": 0}
        self.warning_win = None

        root.title("War Planet Auto-Dodge \u2013 Dashboard")
        root.geometry("780x480")
        root.minsize(620, 360)
        root.configure(bg="#12181f")
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Treeview", background="#1b2430", fieldbackground="#1b2430",
                         foreground="#e6ecf3", rowheight=24, borderwidth=0)
        style.configure("Treeview.Heading", background="#0d141c", foreground="#9fb4c9",
                         relief="flat")
        style.map("Treeview", background=[("selected", "#2a5599")])

        # ---- status bar ----
        top = tk.Frame(root, bg="#12181f")
        top.pack(fill="x", padx=12, pady=(10, 4))
        self.status_var = tk.StringVar(value="Starting...")
        tk.Label(top, textvariable=self.status_var, bg="#12181f", fg="#7fd77f",
                 font=("Segoe UI", 11, "bold")).pack(side="left")
        tk.Button(top, text=f"Stop ({STOP_KEY.upper()})", command=self.stop, bg="#a33333",
                  fg="white", relief="flat", padx=10, pady=2).pack(side="right")

        # ---- summary stats ----
        stats = tk.Frame(root, bg="#12181f")
        stats.pack(fill="x", padx=12, pady=(0, 8))
        self.stat_vars = {
            "alerts": tk.StringVar(value="Attacks seen: 0"),
            "dodged": tk.StringVar(value="Dodged: 0"),
            "failed": tk.StringVar(value="Failed: 0"),
        }
        for key in ("alerts", "dodged", "failed"):
            tk.Label(stats, textvariable=self.stat_vars[key], bg="#12181f", fg="#cdd7e1",
                     font=("Segoe UI", 10)).pack(side="left", padx=(0, 18))

        # ---- history table ----
        cols = ("time", "event", "reason", "result", "tries", "duration", "note")
        headers = {"time": "Time", "event": "Event", "reason": "Trigger", "result": "Result",
                   "tries": "Tries", "duration": "Duration", "note": "Detail"}
        widths = {"time": 70, "event": 60, "reason": 140, "result": 70,
                  "tries": 50, "duration": 70, "note": 240}

        self.tree = ttk.Treeview(root, columns=cols, show="headings", height=16)
        for c in cols:
            self.tree.heading(c, text=headers[c])
            self.tree.column(c, width=widths[c], anchor="w")
        self.tree.tag_configure("dodged", foreground="#7fd77f")
        self.tree.tag_configure("failed", foreground="#e26666")
        self.tree.tag_configure("alert", foreground="#f0c96a")
        self.tree.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        self.load_today()
        self.poll()

    def load_today(self):
        """Repopulate the table from today's log file, so history from
        before the app was last closed still shows up."""
        events = load_today_events()
        for ev in events:
            kind = ev.get("kind")
            if kind == "alert":
                self.counts["alerts"] += 1
                self.tree.insert("", 0, values=(ev.get("time", ""), "Attack", ev.get("reason", ""),
                                                 "-", "-", "-", "incoming"), tags=("alert",))
            elif kind == "dodge":
                ok = ev.get("result") == "dodged"
                self.counts["dodged" if ok else "failed"] += 1
                self.tree.insert("", 0, values=(ev.get("time", ""), "Dodge", ev.get("reason", ""),
                                                 ev.get("result", ""), ev.get("tries", ""),
                                                 ev.get("duration", ""), ev.get("note", "")),
                                  tags=("dodged" if ok else "failed",))
        if events:
            self.stat_vars["alerts"].set(f"Attacks seen: {self.counts['alerts']}")
            self.stat_vars["dodged"].set(f"Dodged: {self.counts['dodged']}")
            self.stat_vars["failed"].set(f"Failed: {self.counts['failed']}")
            self.status_var.set(f"Loaded {len(events)} events from today")

    def stop(self):
        STOP.set()
        self.status_var.set("Stopping...")

    def on_close(self):
        self.stop()
        self.hide_warning()
        self.root.after(300, self.root.destroy)

    # ---- always-on-top "don't touch the mouse" banner ----
    def show_warning(self):
        if self.warning_win is not None:
            return
        w = tk.Toplevel(self.root)
        w.overrideredirect(True)          # no title bar / borders
        w.attributes("-topmost", True)    # stays above the game and every other window
        try:
            w.attributes("-alpha", 0.96)
        except Exception:
            pass
        ww, wh = 620, 60
        sw = w.winfo_screenwidth()
        x = (sw - ww) // 2
        y = 25
        w.geometry(f"{ww}x{wh}+{x}+{y}")
        w.configure(bg="#e53935")
        label = tk.Label(w, text="\u26A0  AUTO-DODGE RUNNING \u2013 DO NOT TOUCH THE MOUSE  \u26A0",
                          bg="#e53935", fg="white", font=("Segoe UI", 14, "bold"))
        label.pack(expand=True, fill="both")
        w.update_idletasks()   # force it on screen immediately, no animation/fade
        self.warning_win = w

    def hide_warning(self):
        if self.warning_win is not None:
            try:
                self.warning_win.destroy()
            except Exception:
                pass
            self.warning_win = None

    def poll(self):
        try:
            while True:
                ev = EVENT_QUEUE.get_nowait()
                self.handle_event(ev)
        except queue.Empty:
            pass
        if DONE.is_set():
            self.status_var.set("Stopped")
            self.hide_warning()
            self.root.after(500, self.root.destroy)
            return
        self.root.after(15, self.poll)

    def handle_event(self, ev):
        kind = ev.get("kind")
        if kind == "status":
            self.status_var.set(ev.get("text", ""))
        elif kind == "alert":
            self.counts["alerts"] += 1
            self.stat_vars["alerts"].set(f"Attacks seen: {self.counts['alerts']}")
            self.status_var.set(f"Attack detected ({ev.get('reason', '?')}) \u2013 dodging...")
            self.tree.insert("", 0, values=(ev["time"], "Attack", ev.get("reason", ""),
                                             "-", "-", "-", "incoming"), tags=("alert",))
        elif kind == "lock":
            self.show_warning()
        elif kind == "unlock":
            self.hide_warning()
        elif kind == "dodge":
            ok = ev.get("result") == "dodged"
            self.counts["dodged" if ok else "failed"] += 1
            self.stat_vars["dodged"].set(f"Dodged: {self.counts['dodged']}")
            self.stat_vars["failed"].set(f"Failed: {self.counts['failed']}")
            self.status_var.set("Armed \u2013 watching for attacks")
            self.tree.insert("", 0, values=(ev["time"], "Dodge", ev.get("reason", ""),
                                             ev.get("result", ""), ev.get("tries", ""),
                                             ev.get("duration", ""), ev.get("note", "")),
                              tags=("dodged" if ok else "failed",))
        # cap table size so it doesn't grow forever during a long session
        children = self.tree.get_children()
        if len(children) > 300:
            for item in children[300:]:
                self.tree.delete(item)


def main():
    prune_old_logs()
    threading.Thread(target=watch_loop, daemon=True).start()
    root = tk.Tk()
    Dashboard(root)
    root.mainloop()


if __name__ == "__main__":
    main()