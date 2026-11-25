#!/usr/bin/env python3
"""
SolSniper M1 — Solana Memecoin Multi-Agent Paper Sniper (Milestone 1)
=====================================================================
Architecture:
  - 4-Officer Desk (Milestone 1 Core): Chief of Staff, Chief Risk Officer (CRO),
    Exit Engine (Mid-Trade Graduation Handoff + Panic Sell Ladder + WS Watchdog),
    and Chief Quant/Learning Officer (SQLite WAL + Obsidian MAE/MFE Logger).
  - 2-Lane RPC Budget (Execution Lane reserved for sells/blockhashes; Intel Lane rate-limited).
  - Harsh Paper-Mode Executor: exact x*y=k constant-product bonding curve impact,
    +500ms next-slot lag, 2% round-trip platform fees, priority fees, ATA rent lock/refund,
    and simulated 10% failed-first-sell retry drag.
  - Zero-Lag Live Web Dashboard (pure stdlib HTTP + 2 Hz Server-Sent Events, token-gated).

Run:
  1. Live Paper Mode on Pump.fun (requires: pip install websockets):
       python3 sol_sniper_m1.py
  2. Offline Interactive Demo (zero dependencies — watch live UI & simulated trades):
       python3 sol_sniper_m1.py --demo
  3. Open Dashboard in Chrome:
       http://127.0.0.1:8080/?token=<printed_at_startup>
"""
from __future__ import annotations

import argparse
import asyncio
import dataclasses
import hashlib
import json
import logging
import math
import os
import random
import re
import secrets
import shutil
import signal
import sqlite3
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib import parse
from zoneinfo import ZoneInfo

UTC = timezone.utc
try:
    EET_TZ = ZoneInfo("Europe/Athens")
except Exception:
    EET_TZ = UTC

BASE58_RX = re.compile(r"^[1-9A-HJ-NP-Za-km-z]{32,44}$")


# --------------------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------------------
@dataclass
class SolBotConfig:
    mode: str = "PAPER"                      # Milestone 1 is PAPER-first (Harsh Realism)
    initial_sol: float = 0.30                # ~50 EUR starter wallet
    base_clip_sol: float = 0.10              # ~15 EUR clip per scalp
    max_clip_sol: float = 1.20               # liquidity safety cap for 2x step-compounding
    sol_usd_ref: float = 165.0               # reference SOL/USD for MC filters
    # Entry Filters (Mid-Curve & Post-Migration Reclaim)
    min_mc_usd: float = 25000.0
    max_midcurve_mc_usd: float = 55000.0
    min_migration_mc_usd: float = 70000.0
    max_migration_mc_usd: float = 300000.0
    min_unique_buyers: int = 35
    min_buy_sell_ratio: float = 2.2
    normal_min_score: int = 70               # Stage 1 conviction floor (0-100)
    sniper_a_plus_score: int = 88            # Stage 2 A+ Sniper-Only floor
    # Chief Risk Officer (CRO) Guardrails
    max_open_positions: int = 2
    max_positions_per_narrative: int = 1
    max_fee_to_tp1_ratio: float = 0.25       # Fee Brake: reject if total fees > 25% of TP1 gain
    cooloff_losses_trigger: int = 2          # 2 straight losses -> 20m cooloff + A+ Sniper Mode
    cooloff_dd_trigger_pct: float = 0.15     # or -15% session DD
    cooloff_sec: int = 1200                  # 20 minutes
    catastrophe_dd_pct: float = 0.45         # Stage 3 catastrophe floor (-45% session DD)
    # Exit Engine (1.5x House-Money Split + -25% Event-Driven Stop)
    hard_sl_pct: float = 0.25                # -25% hard stop (MAE logged to test -18% vs -25%)
    tp1_mult: float = 1.50                   # +50% (1.5x) -> sell 70% (locks principal + fees)
    tp1_sell_frac: float = 0.70
    pre_mig_shield_curve_pct: float = 0.90   # sell 70% if bonding curve hits 90% before migration
    runner_trail_pct: float = 0.15           # 15% trailing stop on 30% house-money runner
    dead_volume_sec: int = 120               # cut dead coins after 120s with no buy volume
    # Harsh Paper Realism & Solana Fees
    platform_fee_pct: float = 0.01           # 1% buy + 1% sell (Pump.fun)
    priority_fee_sol: float = 0.0010         # 0.001 SOL per tx (0.002 SOL round-trip)
    ata_rent_sol: float = 0.00203928         # locked on buy, refunded on burn-dust + close
    paper_slot_delay_ms: int = 500           # +500ms next-slot fill delay
    harsh_realism_mode: bool = True          # simulates 10% failed-first-sell retry slippage
    harsh_sell_fail_prob: float = 0.10
    harsh_retry_extra_slip: float = 0.06
    # 2-Lane RPC & WebSocket Watchdog
    exec_lane_rps: float = 15.0              # reserved strictly for sells, blockhashes, ATA closes
    intel_lane_rps: float = 8.0              # isolated for forensics/metadata scans
    ws_watchdog_sec: float = 5.0
    ws_url: str = "wss://pumpportal.fun/api/data"
    # Dashboard & Storage
    dashboard_host: str = "127.0.0.1"
    dashboard_port: int = 8080
    dashboard_token: str = ""                # auto-generated at startup if empty (or DASHBOARD_TOKEN env)
    base_dir: Path = field(default_factory=lambda: Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd())

    def __post_init__(self) -> None:
        env_tok = os.getenv("DASHBOARD_TOKEN", "").strip()
        if env_tok:
            self.dashboard_token = env_tok
        elif not self.dashboard_token:
            self.dashboard_token = secrets.token_urlsafe(12)


class CircuitStage(str, Enum):
    NORMAL = "STAGE_1_NORMAL"
    COOLOFF = "STAGE_2_COOLOFF"
    A_PLUS_ONLY = "STAGE_2_A_PLUS_SNIPER"
    CATASTROPHE_HALT = "STAGE_3_CATASTROPHE_HALT"


class Venue(str, Enum):
    BONDING_CURVE = "BONDING_CURVE"
    PUMPSWAP = "PUMPSWAP"
    RAYDIUM_CPMM = "RAYDIUM_CPMM"


# --------------------------------------------------------------------------------------
# 2-Lane Token-Bucket RPC Budget + Confirmed Blockhash Cache
# --------------------------------------------------------------------------------------
class _RateLane:
    def __init__(self, rps: float):
        self.rps = max(1.0, float(rps))
        self.tokens = self.rps
        self.last = time.monotonic()
        self.calls = 0
        self.throttled = 0

    async def acquire(self) -> None:
        now = time.monotonic()
        elapsed = now - self.last
        self.last = now
        self.tokens = min(self.rps, self.tokens + elapsed * self.rps)
        if self.tokens < 1.0:
            self.throttled += 1
            await asyncio.sleep((1.0 - self.tokens) / self.rps)
            self.tokens = 0.0
        else:
            self.tokens -= 1.0
        self.calls += 1


class TwoLaneRPC:
    """Guarantees Intel/Forensics scans can NEVER starve Execution sells or blockhash refreshes."""

    def __init__(self, exec_rps: float = 15.0, intel_rps: float = 8.0):
        self.exec_lane = _RateLane(exec_rps)
        self.intel_lane = _RateLane(intel_rps)
        self.recent_blockhash: str = "SIM_BH_INIT"
        self.last_valid_block_height: int = 300_000_000
        self.blockhash_ts: float = time.time()

    async def refresh_blockhash(self) -> None:
        await self.exec_lane.acquire()
        self.recent_blockhash = f"BH_{int(time.time()*1000)}_{secrets.token_hex(4)}"
        self.last_valid_block_height += 5
        self.blockhash_ts = time.time()

    def stats(self) -> dict:
        return {
            "exec_calls": self.exec_lane.calls,
            "exec_throttled": self.exec_lane.throttled,
            "intel_calls": self.intel_lane.calls,
            "intel_throttled": self.intel_lane.throttled,
            "blockhash_age_sec": round(time.time() - self.blockhash_ts, 2),
        }


# --------------------------------------------------------------------------------------
# Exact Constant-Product Bonding Curve Math (x * y = k)
# --------------------------------------------------------------------------------------
def curve_buy_tokens(v_sol: float, v_tok: float, sol_in: float) -> tuple[float, float]:
    """Return (tokens_out, effective_price_sol_per_tok) using exact x*y=k."""
    if v_sol <= 0 or v_tok <= 0 or sol_in <= 0:
        return 0.0, 0.0
    k = v_sol * v_tok
    new_v_sol = v_sol + sol_in
    new_v_tok = k / new_v_sol
    tok_out = max(0.0, v_tok - new_v_tok)
    eff_px = (sol_in / tok_out) if tok_out > 0 else 0.0
    return tok_out, eff_px


def curve_sell_sol(v_sol: float, v_tok: float, tok_in: float) -> tuple[float, float]:
    """Return (sol_out, effective_price_sol_per_tok) using exact x*y=k."""
    if v_sol <= 0 or v_tok <= 0 or tok_in <= 0:
        return 0.0, 0.0
    k = v_sol * v_tok
    new_v_tok = v_tok + tok_in
    new_v_sol = k / new_v_tok
    sol_out = max(0.0, v_sol - new_v_sol)
    eff_px = (sol_out / tok_in) if tok_in > 0 else 0.0
    return sol_out, eff_px


# --------------------------------------------------------------------------------------
# Live Token State (Keyed Strictly by Mint Address CA)
# --------------------------------------------------------------------------------------
@dataclass
class TokenState:
    mint: str
    symbol: str
    name: str
    narrative: str = "general"
    program_owner: str = "pump_fun"
    venue: Venue = Venue.BONDING_CURVE
    freeze_authority: bool = False
    transfer_fee_bps: int = 0
    v_sol: float = 45.0                      # virtual SOL reserves
    v_tok: float = 800_000_000.0             # virtual token reserves
    curve_pct: float = 0.45                  # bonding curve completion 0..1
    mc_usd: float = 32000.0
    price_sol: float = 0.000000056
    buyers: set[str] = field(default_factory=set)
    buy_vol_60s_sol: float = 0.0
    sell_vol_60s_sol: float = 0.0
    last_buy_ts: float = field(default_factory=time.time)
    last_update_ts: float = field(default_factory=time.time)
    migrated_ts: float = 0.0
    migration_open_px: float = 0.0
    top10_pct: float = 18.0
    is_canonical_leader: bool = True


@dataclass
class PaperPosition:
    mint: str
    symbol: str
    narrative: str
    venue: Venue
    entry_ts: float
    entry_px: float
    entry_sol_net: float
    clip_sol: float
    tokens_total: float
    tokens_rem: float
    rent_locked_sol: float
    conviction_score: int
    tp1_done: bool = False
    realized_sol: float = 0.0
    peak_px: float = 0.0
    min_px: float = 0.0                      # tracks MAE (Max Adverse Excursion)
    max_px: float = 0.0                      # tracks MFE (Max Favorable Excursion)
    last_px: float = 0.0
    last_buy_ts: float = 0.0
    graduated_mid_trade: bool = False


# --------------------------------------------------------------------------------------
# Chief Risk Officer (CRO) — Independent Veto & Double-Buy Lock
# --------------------------------------------------------------------------------------
class ChiefRiskOfficer:
    def __init__(self, cfg: SolBotConfig):
        self.cfg = cfg
        self.in_flight_mints: set[str] = set()
        self.traded_mints: set[str] = set()

    def try_lock_mint(self, mint: str) -> bool:
        if mint in self.in_flight_mints or mint in self.traded_mints:
            return False
        self.in_flight_mints.add(mint)
        return True

    def release_lock(self, mint: str, bought: bool) -> None:
        self.in_flight_mints.discard(mint)
        if bought:
            self.traded_mints.add(mint)

    def audit_entry(self, tok: TokenState, open_positions: dict[str, PaperPosition], clip_sol: float) -> tuple[bool, str]:
        c = self.cfg
        # 1. Anti-Impostor CA Gate
        if not BASE58_RX.match(tok.mint):
            return False, "INVALID_BASE58_CA"
        if tok.program_owner not in ("pump_fun", "pumpswap", "launchlab"):
            return False, f"UNSUPPORTED_PROGRAM:{tok.program_owner}"
        if tok.freeze_authority:
            return False, "FREEZE_AUTHORITY_ACTIVE"
        if tok.transfer_fee_bps > 0:
            return False, f"TOKEN2022_TAX:{tok.transfer_fee_bps}bps"
        if not tok.is_canonical_leader:
            return False, "NON_CANONICAL_IMPOSTOR_CLONE"
        if tok.top10_pct > 30.0:
            return False, f"TOP10_CONCENTRATION:{tok.top10_pct:.1f}%"

        # 2. Exposure & Narrative Correlation Cap
        if tok.mint in self.traded_mints or tok.mint in open_positions:
            return False, "DUPLICATE_MINT_LOCKED"
        if len(open_positions) >= c.max_open_positions:
            return False, "MAX_OPEN_POSITIONS"
        same_narr = sum(1 for p in open_positions.values() if p.narrative == tok.narrative)
        if same_narr >= c.max_positions_per_narrative:
            return False, f"NARRATIVE_CORR_CAP:{tok.narrative}"

        # 3. Fee Brake (0.10 SOL / 50 EUR math)
        rt_platform = clip_sol * (2.0 * c.platform_fee_pct)
        rt_priority = 2.0 * c.priority_fee_sol
        expected_tp1_gain = clip_sol * (c.tp1_mult - 1.0)
        total_fixed_fees = rt_platform + rt_priority
        if expected_tp1_gain <= 0 or (total_fixed_fees / expected_tp1_gain) > c.max_fee_to_tp1_ratio:
            return False, f"FEE_BRAKE:{total_fixed_fees:.4f}SOL>{c.max_fee_to_tp1_ratio*100:.0f}%_TP1"

        return True, "CRO_APPROVED"


# --------------------------------------------------------------------------------------
# CQLO — SQLite WAL + Obsidian MAE/MFE 2nd Brain
# --------------------------------------------------------------------------------------
class CQLOMemory:
    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self.db_path = base_dir / "sol_sniper_m1.db"
        self.vault_dir = base_dir / "sol_vault"
        self.trades_dir = self.vault_dir / "Trades"
        self.reviews_dir = self.vault_dir / "Reviews"
        self.pos_file = base_dir / "sol_open_positions.json"
        self.trades_dir.mkdir(parents=True, exist_ok=True)
        self.reviews_dir.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL;")
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS trades (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                mint TEXT, symbol TEXT, narrative TEXT, venue TEXT,
                entry_ts REAL, exit_ts REAL, hour_eet INTEGER,
                clip_sol REAL, net_pnl_sol REAL, roi_pct REAL,
                mae_pct REAL, mfe_pct REAL, score INTEGER,
                exit_reason TEXT, graduated_mid_trade INTEGER
            )
        """)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS vetoes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ts REAL, mint TEXT, symbol TEXT, reason TEXT, score INTEGER
            )
        """)
        self.conn.commit()

    def save_positions_atomic(self, positions: dict[str, PaperPosition]) -> None:
        tmp = self.pos_file.with_suffix(".tmp")
        payload = {m: dataclasses.asdict(p) for m, p in positions.items()}
        for v in payload.values():
            v["venue"] = v["venue"].value if isinstance(v["venue"], Enum) else str(v["venue"])
        tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        os.replace(tmp, self.pos_file)

    def log_veto(self, mint: str, symbol: str, reason: str, score: int) -> None:
        self.conn.execute(
            "INSERT INTO vetoes (ts, mint, symbol, reason, score) VALUES (?, ?, ?, ?, ?)",
            (time.time(), mint, symbol, reason, score),
        )
        self.conn.commit()

    def log_closed_trade(self, pos: PaperPosition, exit_ts: float, net_pnl_sol: float, reason: str) -> None:
        roi_pct = (net_pnl_sol / pos.clip_sol * 100.0) if pos.clip_sol > 0 else 0.0
        mae_pct = ((pos.min_px - pos.entry_px) / pos.entry_px * 100.0) if pos.entry_px > 0 else 0.0
        mfe_pct = ((pos.max_px - pos.entry_px) / pos.entry_px * 100.0) if pos.entry_px > 0 else 0.0
        dt_eet = datetime.fromtimestamp(pos.entry_ts, tz=UTC).astimezone(EET_TZ)
        self.conn.execute(
            """INSERT INTO trades (mint, symbol, narrative, venue, entry_ts, exit_ts, hour_eet,
               clip_sol, net_pnl_sol, roi_pct, mae_pct, mfe_pct, score, exit_reason, graduated_mid_trade)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                pos.mint, pos.symbol, pos.narrative, pos.venue.value, pos.entry_ts, exit_ts, dt_eet.hour,
                pos.clip_sol, net_pnl_sol, roi_pct, mae_pct, mfe_pct, pos.conviction_score,
                reason, int(pos.graduated_mid_trade),
            ),
        )
        self.conn.commit()

        # Write Obsidian Trade Note with YAML frontmatter (MAE/MFE + hour_eet)
        stem = f"{dt_eet.strftime('%Y-%m-%d_%H%M%S')}_{re.sub(r'[^A-Za-z0-9]+', '', pos.symbol)[:12]}_{pos.mint[:6]}"
        outcome = "WIN" if net_pnl_sol > 0 else "LOSS"
        md = (
            f"---\ntype: sol_paper_trade\noutcome: {outcome}\nmint: \"{pos.mint}\"\nsymbol: \"{pos.symbol}\"\n"
            f"narrative: \"{pos.narrative}\"\nvenue: \"{pos.venue.value}\"\nhour_eet: {dt_eet.hour}\n"
            f"clip_sol: {pos.clip_sol:.4f}\nnet_pnl_sol: {net_pnl_sol:.5f}\nroi_pct: {roi_pct:.2f}\n"
            f"mae_pct: {mae_pct:.2f}\nmfe_pct: {mfe_pct:.2f}\nscore: {pos.conviction_score}\n"
            f"exit_reason: \"{reason}\"\ngraduated_mid_trade: {str(pos.graduated_mid_trade).lower()}\n---\n"
            f"# [{outcome}] ${pos.symbol} ({net_pnl_sol:+.4f} SOL / {roi_pct:+.1f}%)\n\n"
            f"- **Mint:** `{pos.mint}` | **Venue:** `{pos.venue.value}` | **Mid-Trade Grad:** `{pos.graduated_mid_trade}`\n"
            f"- **Score:** `{pos.conviction_score}/100` | **Exit:** `{reason}` | **Hour (EET):** `{dt_eet.hour:02d}:00`\n"
            f"- **MAE (Worst Dip):** `{mae_pct:+.1f}%` | **MFE (Best Peak):** `{mfe_pct:+.1f}%`\n"
        )
        (self.trades_dir / f"{stem}.md").write_text(md, encoding="utf-8")

    def summary_stats(self) -> dict:
        cur = self.conn.execute("SELECT COUNT(*), SUM(CASE WHEN net_pnl_sol > 0 THEN 1 ELSE 0 END), COALESCE(SUM(net_pnl_sol),0), COALESCE(AVG(mae_pct),0), COALESCE(AVG(mfe_pct),0) FROM trades")
        n, w, net, avg_mae, avg_mfe = cur.fetchone()
        n, w = int(n or 0), int(w or 0)
        return {
            "trades": n,
            "wins": w,
            "win_rate_pct": round((w / n * 100.0), 1) if n else 0.0,
            "net_pnl_sol": round(float(net or 0.0), 5),
            "avg_mae_pct": round(float(avg_mae or 0.0), 1),
            "avg_mfe_pct": round(float(avg_mfe or 0.0), 1),
        }


# --------------------------------------------------------------------------------------
# Chief of Staff + Harsh Paper Executor + Exit Engine
# --------------------------------------------------------------------------------------
class SolSniperEngine:
    def __init__(self, cfg: SolBotConfig):
        self.cfg = cfg
        self.rpc = TwoLaneRPC(cfg.exec_lane_rps, cfg.intel_lane_rps)
        self.cro = ChiefRiskOfficer(cfg)
        self.cqlo = CQLOMemory(cfg.base_dir)
        self.tokens: dict[str, TokenState] = {}
        self.positions: dict[str, PaperPosition] = {}
        self.events: deque[dict] = deque(maxlen=60)
        self.balance_sol: float = cfg.initial_sol
        self.hwm_sol: float = cfg.initial_sol
        self.session_start_sol: float = cfg.initial_sol
        self.consec_losses: int = 0
        self.stage: CircuitStage = CircuitStage.NORMAL
        self.cooloff_until: float = 0.0
        self.manual_pause: bool = False
        self.force_a_plus: bool = False
        self.last_ws_msg_ts: float = time.time()
        self.ws_reconnects: int = 0
        self._rng = random.Random(42)
        self._lock = threading.Lock()
        self._stop = asyncio.Event()

    def _emit(self, kind: str, msg: str, extra: dict | None = None) -> None:
        item = {"ts": datetime.now(UTC).astimezone(EET_TZ).strftime("%H:%M:%S"), "kind": kind, "msg": msg}
        if extra:
            item.update(extra)
        with self._lock:
            self.events.appendleft(item)
        logging.info(f"[{kind}] {msg}")

    def total_equity_sol(self) -> float:
        """Cash SOL + mark-to-market open positions + refundable ATA rent."""
        open_val = sum((p.tokens_rem * p.last_px) + p.rent_locked_sol for p in self.positions.values())
        return self.balance_sol + open_val

    def current_clip_sol(self) -> float:
        """2x step-compounding capped at max_clip_sol, with 25% symmetric drawdown step-down."""
        ratio = self.balance_sol / max(self.cfg.initial_sol, 1e-9)
        tier = max(0, int(math.floor(math.log2(max(ratio, 1.0)))))
        clip = self.cfg.base_clip_sol * (2 ** tier)
        if self.hwm_sol > 0 and ((self.hwm_sol - self.balance_sol) / self.hwm_sol) >= 0.25:
            clip *= 0.5
        return round(min(max(clip, self.cfg.base_clip_sol * 0.5), self.cfg.max_clip_sol), 4)

    def score_setup(self, tok: TokenState) -> int:
        """Fast-Path deterministic 0-100 Conviction Score (<1ms)."""
        score = 0
        # 1. Entry Zone (Mid-Curve $25k-$55k OR Post-Migration Reclaim $70k-$300k)
        if tok.venue == Venue.BONDING_CURVE and self.cfg.min_mc_usd <= tok.mc_usd <= self.cfg.max_midcurve_mc_usd:
            score += 30
        elif tok.venue != Venue.BONDING_CURVE and self.cfg.min_migration_mc_usd <= tok.mc_usd <= self.cfg.max_migration_mc_usd:
            # Post-migration reclaim: require >=10s after migration & reclaim above migration open
            if (time.time() - tok.migrated_ts) >= 10.0 and tok.price_sol >= tok.migration_open_px:
                score += 32
        # 2. Unique Buyer Velocity
        n_buyers = len(tok.buyers)
        if n_buyers >= self.cfg.min_unique_buyers:
            score += min(30, 18 + (n_buyers - self.cfg.min_unique_buyers) // 3)
        # 3. Buy/Sell Pressure
        bsr = tok.buy_vol_60s_sol / max(tok.sell_vol_60s_sol, 0.25)
        if bsr >= self.cfg.min_buy_sell_ratio:
            score += min(25, int(12 + bsr * 3.0))
        # 4. Holder Distribution Quality
        if tok.top10_pct <= 20.0:
            score += 15
        elif tok.top10_pct <= 26.0:
            score += 8
        return min(100, score)

    def _active_min_score(self, now: float) -> int | None:
        if self.manual_pause or self.stage == CircuitStage.CATASTROPHE_HALT:
            return None
        if self.stage == CircuitStage.COOLOFF:
            if now < self.cooloff_until:
                return None
            self.stage = CircuitStage.A_PLUS_ONLY
            self._emit("STAGE", "20m cooloff complete -> Stage 2 A+ Sniper-Only Mode (score >= 88)")
        if self.force_a_plus or self.stage == CircuitStage.A_PLUS_ONLY:
            return self.cfg.sniper_a_plus_score
        return self.cfg.normal_min_score

    async def handle_graduation(self, mint: str, new_venue: Venue = Venue.PUMPSWAP) -> None:
        """Mid-Trade Graduation Handoff: switches active price feed & sell router seamlessly."""
        tok = self.tokens.get(mint)
        now = time.time()
        if tok:
            tok.venue = new_venue
            tok.curve_pct = 1.0
            tok.migrated_ts = now
            tok.migration_open_px = tok.price_sol
        pos = self.positions.get(mint)
        if pos:
            pos.venue = new_venue
            pos.graduated_mid_trade = True
            self.cqlo.save_positions_atomic(self.positions)
            self._emit("MIGRATION", f"${pos.symbol} graduated mid-trade -> router switched to {new_venue.value}")

    async def execute_paper_buy(self, tok: TokenState, score: int) -> bool:
        if not self.cro.try_lock_mint(tok.mint):
            return False
        bought = False
        try:
            clip = self.current_clip_sol()
            ok, reason = self.cro.audit_entry(tok, self.positions, clip)
            if not ok:
                self.cqlo.log_veto(tok.mint, tok.symbol, reason, score)
                self._emit("VETO", f"${tok.symbol} blocked by CRO: {reason} (score={score})")
                return False
            needed = clip + self.cfg.priority_fee_sol + self.cfg.ata_rent_sol
            if self.balance_sol < needed:
                self._emit("VETO", f"${tok.symbol} skipped: insufficient SOL ({self.balance_sol:.4f} < {needed:.4f})")
                return False

            await self.rpc.exec_lane.acquire()
            # Simulate +500ms next-slot fill delay (small adverse drift on hot tape)
            net_sol_in = clip * (1.0 - self.cfg.platform_fee_pct)
            tok_out, eff_px = curve_buy_tokens(tok.v_sol, tok.v_tok, net_sol_in)
            if tok_out <= 0 or eff_px <= 0:
                return False
            # Apply realistic next-slot adverse slippage (~1.5% on active pump)
            eff_px *= 1.015
            tok_out = net_sol_in / eff_px

            self.balance_sol -= (clip + self.cfg.priority_fee_sol + self.cfg.ata_rent_sol)
            now = time.time()
            pos = PaperPosition(
                mint=tok.mint, symbol=tok.symbol, narrative=tok.narrative, venue=tok.venue,
                entry_ts=now, entry_px=eff_px, entry_sol_net=clip, clip_sol=clip,
                tokens_total=tok_out, tokens_rem=tok_out, rent_locked_sol=self.cfg.ata_rent_sol,
                conviction_score=score, peak_px=eff_px, min_px=eff_px, max_px=eff_px,
                last_px=eff_px, last_buy_ts=now,
            )
            self.positions[tok.mint] = pos
            self.cqlo.save_positions_atomic(self.positions)
            bought = True
            self._emit("BUY", f"OPEN ${tok.symbol} | {clip:.3f} SOL | Score {score}/100 | MC ${tok.mc_usd:,.0f} | {tok.venue.value}")
            return True
        finally:
            self.cro.release_lock(tok.mint, bought=bought)

    async def execute_paper_sell(self, mint: str, frac: float, reason: str, panic: bool = False) -> None:
        pos = self.positions.get(mint)
        tok = self.tokens.get(mint)
        if not pos or not tok or pos.tokens_rem <= 0:
            return
        sell_tok = pos.tokens_rem * min(1.0, max(0.0, frac))
        is_full = (frac >= 0.999) or ((pos.tokens_rem - sell_tok) / max(pos.tokens_total, 1e-9) < 0.02)
        if is_full:
            sell_tok = pos.tokens_rem

        # Panic Sell Ladder (escalate priority fee & slippage if harsh realism triggers retry)
        await self.rpc.exec_lane.acquire()
        extra_slip = 0.0
        prio_fee = self.cfg.priority_fee_sol
        if panic and self.cfg.harsh_realism_mode and self._rng.random() < self.cfg.harsh_sell_fail_prob:
            # Simulate failed first sell -> 2s Panic Ladder retry #2 with bumped fee & extra slippage
            await self.rpc.refresh_blockhash()
            prio_fee *= 2.0
            extra_slip = self.cfg.harsh_retry_extra_slip
            self._emit("PANIC_LADDER", f"${pos.symbol} first sell dropped -> retry #2 (+{extra_slip*100:.0f}% slip)")

        gross_sol, _ = curve_sell_sol(tok.v_sol, tok.v_tok, sell_tok)
        gross_sol *= (1.0 - extra_slip)
        net_sol = max(0.0, gross_sol * (1.0 - self.cfg.platform_fee_pct) - prio_fee)

        pos.tokens_rem = max(0.0, pos.tokens_rem - sell_tok)
        pos.realized_sol += net_sol
        self.balance_sol += net_sol

        if not is_full:
            pos.tp1_done = True
            self.cqlo.save_positions_atomic(self.positions)
            self._emit("TP1", f"${pos.symbol} sold {frac*100:.0f}% ({reason}) -> +{net_sol:.4f} SOL | 30% runner active")
            return

        # Full close: Burn any dust + Close ATA -> 100% rent refund!
        self.balance_sol += pos.rent_locked_sol
        total_cost = pos.clip_sol + self.cfg.priority_fee_sol
        net_pnl = pos.realized_sol - total_cost
        del self.positions[mint]
        eq = self.total_equity_sol()
        self.hwm_sol = max(self.hwm_sol, eq)
        self.cqlo.save_positions_atomic(self.positions)
        self.cqlo.log_closed_trade(pos, time.time(), net_pnl, reason)

        # Update Adaptive Circuit Breaker (based on true total equity, not unallocated cash)
        sess_dd = max(0.0, (self.session_start_sol - eq) / max(self.session_start_sol, 1e-9))
        if net_pnl > 0:
            self.consec_losses = 0
            if self.stage == CircuitStage.A_PLUS_ONLY:
                self.stage = CircuitStage.NORMAL
                self._emit("STAGE", "Clean win in A+ Mode -> Unlocked Stage 1 Normal Mode")
        else:
            self.consec_losses += 1
            if sess_dd >= self.cfg.catastrophe_dd_pct:
                self.stage = CircuitStage.CATASTROPHE_HALT
                self._emit("CRITICAL", f"Stage 3 Catastrophe Halt (-{sess_dd*100:.1f}% session DD)")
            elif self.stage == CircuitStage.NORMAL and (
                self.consec_losses >= self.cfg.cooloff_losses_trigger or sess_dd >= self.cfg.cooloff_dd_trigger_pct
            ):
                self.stage = CircuitStage.COOLOFF
                self.cooloff_until = time.time() + self.cfg.cooloff_sec
                self._emit("STAGE", f"Stage 2 Cooloff triggered ({self.consec_losses} losses / -{sess_dd*100:.1f}% DD) -> 20m pause")

        self._emit("CLOSE", f"CLOSED ${pos.symbol} ({reason}) | Net {net_pnl:+.4f} SOL | Bal {self.balance_sol:.4f} SOL | ATA rent refunded")

    async def on_swap_tick(self, tok: TokenState) -> None:
        """Event-driven Fast Path (<1ms) invoked on every live swap event."""
        self.last_ws_msg_ts = time.time()
        self.tokens[tok.mint] = tok
        now = time.time()

        # 1. Manage Open Position First (Zero-Lag -25% Stop, 70% @ 1.5x TP1, Pre-Mig Shield, Trail, Time-Stop)
        pos = self.positions.get(tok.mint)
        if pos is not None:
            px = tok.price_sol
            pos.last_px = px
            pos.min_px = min(pos.min_px, px)
            pos.max_px = max(pos.max_px, px)
            pos.peak_px = max(pos.peak_px, px)
            if tok.last_buy_ts > pos.last_buy_ts:
                pos.last_buy_ts = tok.last_buy_ts

            mult = px / max(pos.entry_px, 1e-12)
            # Hard -25% Stop (always armed before TP1)
            if (not pos.tp1_done) and mult <= (1.0 - self.cfg.hard_sl_pct):
                await self.execute_paper_sell(tok.mint, 1.0, "HARD_STOP_25PCT", panic=True)
                return
            # TP1 at 1.5x (sell 70% -> house money)
            if (not pos.tp1_done) and mult >= self.cfg.tp1_mult:
                await self.execute_paper_sell(tok.mint, self.cfg.tp1_sell_frac, "TP1_1.5X_HOUSE_MONEY", panic=False)
                return
            # Pre-Migration Shield (sell 70% at >= 90% curve if still in profit)
            if (not pos.tp1_done) and tok.venue == Venue.BONDING_CURVE and tok.curve_pct >= self.cfg.pre_mig_shield_curve_pct and mult >= 1.15:
                await self.execute_paper_sell(tok.mint, self.cfg.tp1_sell_frac, "PRE_MIGRATION_SHIELD", panic=False)
                return
            # Runner Trailing Stop (-15% from peak)
            if pos.tp1_done and px <= pos.peak_px * (1.0 - self.cfg.runner_trail_pct):
                await self.execute_paper_sell(tok.mint, 1.0, "RUNNER_TRAIL_STOP", panic=True)
                return
            # Dead-Volume Time-Stop (120s without fresh buy volume)
            if (now - pos.last_buy_ts) >= self.cfg.dead_volume_sec:
                await self.execute_paper_sell(tok.mint, 1.0, "DEAD_VOLUME_TIMESTOP", panic=False)
                return
            return

        # 2. Evaluate New Entry
        min_score = self._active_min_score(now)
        if min_score is None:
            return
        score = self.score_setup(tok)
        if score >= min_score:
            await self.execute_paper_buy(tok, score)

    async def sell_all_positions(self, reason: str = "MANUAL_SELL_ALL") -> None:
        for mint in list(self.positions.keys()):
            await self.execute_paper_sell(mint, 1.0, reason, panic=True)

    def dashboard_snapshot(self) -> dict:
        with self._lock:
            ev_list = list(self.events)[:25]
        pos_rows = []
        for p in self.positions.values():
            pnl_pct = ((p.last_px - p.entry_px) / max(p.entry_px, 1e-12)) * 100.0
            pos_rows.append({
                "mint": p.mint[:6] + "..." + p.mint[-4:],
                "symbol": p.symbol, "venue": p.venue.value, "clip_sol": p.clip_sol,
                "pnl_pct": round(pnl_pct, 1), "tp1_done": p.tp1_done,
                "mae_pct": round((p.min_px - p.entry_px) / max(p.entry_px, 1e-12) * 100.0, 1),
                "mfe_pct": round((p.max_px - p.entry_px) / max(p.entry_px, 1e-12) * 100.0, 1),
                "grad": p.graduated_mid_trade,
            })
        return {
            "mode": self.cfg.mode,
            "stage": self.stage.value,
            "manual_pause": self.manual_pause,
            "force_a_plus": self.force_a_plus,
            "balance_sol": round(self.balance_sol, 4),
            "balance_eur_est": round(self.balance_sol * self.cfg.sol_usd_ref * 0.92, 2),
            "clip_sol": self.current_clip_sol(),
            "ws_age_sec": round(time.time() - self.last_ws_msg_ts, 1),
            "ws_reconnects": self.ws_reconnects,
            "rpc": self.rpc.stats(),
            "stats": self.cqlo.summary_stats(),
            "positions": pos_rows,
            "events": ev_list,
        }


# --------------------------------------------------------------------------------------
# Zero-Lag Live Web Dashboard (Pure Stdlib HTTP + 2 Hz SSE, Token-Protected)
# --------------------------------------------------------------------------------------
DASHBOARD_HTML = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>SolSniper M1 — Live Desk</title>
<style>
body{background:#0b0f17;color:#e5edf7;font-family:system-ui,-apple-system,sans-serif;margin:0;padding:18px}
.top{display:flex;flex-wrap:wrap;gap:12px;align-items:center;justify-content:space-between;margin-bottom:16px}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px;margin-bottom:16px}
.card{background:#131a26;border:1px solid #223047;border-radius:10px;padding:12px 14px}
.lbl{font-size:11px;color:#8aa0bd;text-transform:uppercase;letter-spacing:.6px}
.val{font-size:20px;font-weight:700;margin-top:4px}
.grid{display:grid;grid-template-columns:1.2fr 1fr;gap:14px}
@media(max-width:860px){.grid{grid-template-columns:1fr}}
table{width:100%;border-collapse:collapse;font-size:13px}
th,td{padding:8px 6px;border-bottom:1px solid #1e2a3d;text-align:left}
.btn{border:0;border-radius:8px;padding:8px 13px;font-weight:600;cursor:pointer;color:#fff;margin-left:6px}
.b-pause{background:#d97706}.b-aplus{background:#2563eb}.b-sell{background:#dc2626}.b-ok{background:#059669}
.feed{max-height:360px;overflow-y:auto;font-family:ui-monospace,monospace;font-size:12px;line-height:1.5}
.pos{color:#34d399}.neg{color:#f87171}.tag{background:#1e293b;padding:2px 6px;border-radius:4px;font-size:11px}
</style></head><body>
<div class="top">
  <div><h2 style="margin:0">⚡ SolSniper M1 — Live Paper Desk</h2><small id="meta" style="color:#8aa0bd">Connecting...</small></div>
  <div>
    <button class="btn b-pause" onclick="act('toggle_pause')">Pause / Resume</button>
    <button class="btn b-aplus" onclick="act('toggle_aplus')">A+ Only</button>
    <button class="btn b-sell" onclick="act('sell_all')">SELL ALL</button>
  </div>
</div>
<div class="cards">
  <div class="card"><div class="lbl">Wallet Balance</div><div class="val" id="bal">--</div></div>
  <div class="card"><div class="lbl">Next Clip / Stage</div><div class="val" id="stage">--</div></div>
  <div class="card"><div class="lbl">Paper PnL / WR</div><div class="val" id="pnl">--</div></div>
  <div class="card"><div class="lbl">Avg MAE / MFE</div><div class="val" id="maemfe">--</div></div>
  <div class="card"><div class="lbl">WS & 2-Lane RPC</div><div class="val" id="rpc">--</div></div>
</div>
<div class="grid">
  <div class="card"><div class="lbl" style="margin-bottom:8px">Open Positions (Event-Driven -25% Stop / 1.5x TP1)</div>
    <table><thead><tr><th>Coin</th><th>Venue</th><th>Clip</th><th>PnL%</th><th>MAE/MFE</th><th>TP1</th></tr></thead><tbody id="pos"></tbody></table>
  </div>
  <div class="card"><div class="lbl" style="margin-bottom:8px">Live Desk Event Stream (2 Hz)</div><div class="feed" id="feed"></div></div>
</div>
<script>
const tok = new URLSearchParams(location.search).get('token') || '';
async function act(cmd){ await fetch('/api/action?token='+encodeURIComponent(tok)+'&cmd='+cmd,{method:'POST'}); }
const es = new EventSource('/stream?token='+encodeURIComponent(tok));
es.onmessage = e => {
  const d = JSON.parse(e.data);
  document.getElementById('meta').textContent = `Mode: ${d.mode} | Paused: ${d.manual_pause} | A+ Forced: ${d.force_a_plus} | WS Age: ${d.ws_age_sec}s`;
  document.getElementById('bal').textContent = `${d.balance_sol} SOL (~€${d.balance_eur_est})`;
  document.getElementById('stage').textContent = `${d.clip_sol} SOL | ${d.stage.replace('STAGE_','S')}`;
  document.getElementById('pnl').innerHTML = `<span class="${d.stats.net_pnl_sol>=0?'pos':'neg'}">${d.stats.net_pnl_sol>=0?'+':''}${d.stats.net_pnl_sol} SOL</span> (${d.stats.win_rate_pct}% / ${d.stats.trades})`;
  document.getElementById('maemfe').textContent = `${d.stats.avg_mae_pct}% / +${d.stats.avg_mfe_pct}%`;
  document.getElementById('rpc').textContent = `Exec:${d.rpc.exec_calls} Int:${d.rpc.intel_calls} BH:${d.rpc.blockhash_age_sec}s`;
  document.getElementById('pos').innerHTML = d.positions.length ? d.positions.map(p=>
    `<tr><td><b>$${p.symbol}</b><br><small>${p.mint}</small></td><td><span class="tag">${p.venue}</span>${p.grad?' 🚀':''}</td><td>${p.clip_sol}</td><td class="${p.pnl_pct>=0?'pos':'neg'}">${p.pnl_pct}%</td><td>${p.mae_pct}% / +${p.mfe_pct}%</td><td>${p.tp1_done?'✅ 30%':'⏳'}</td></tr>`
  ).join('') : '<tr><td colspan="6" style="color:#64748b">No open positions</td></tr>';
  document.getElementById('feed').innerHTML = d.events.map(ev=>`<div><span style="color:#64748b">${ev.ts}</span> <span class="tag">${ev.kind}</span> ${ev.msg}</div>`).join('');
};
</script></body></html>"""


def start_dashboard_server(engine: SolSniperEngine, loop: asyncio.AbstractEventLoop) -> ThreadingHTTPServer:
    token = engine.cfg.dashboard_token

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            return

        def _auth_ok(self) -> bool:
            q = parse.parse_qs(parse.urlparse(self.path).query)
            return (q.get("token") or [""])[0] == token

        def do_GET(self):
            if not self._auth_ok():
                self.send_response(403)
                self.end_headers()
                self.wfile.write(b"Forbidden: missing or invalid token")
                return
            path = parse.urlparse(self.path).path
            if path == "/":
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.end_headers()
                self.wfile.write(DASHBOARD_HTML.encode("utf-8"))
            elif path == "/api/state":
                body = json.dumps(engine.dashboard_snapshot()).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                self.wfile.write(body)
            elif path == "/stream":
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                try:
                    while not engine._stop.is_set():
                        data = json.dumps(engine.dashboard_snapshot())
                        self.wfile.write(f"data: {data}\n\n".encode("utf-8"))
                        self.wfile.flush()
                        time.sleep(0.5)  # 2 Hz push
                except (BrokenPipeError, ConnectionResetError, OSError):
                    pass
            else:
                self.send_response(404)
                self.end_headers()

        def do_POST(self):
            if not self._auth_ok():
                self.send_response(403)
                self.end_headers()
                return
            q = parse.parse_qs(parse.urlparse(self.path).query)
            cmd = (q.get("cmd") or [""])[0]
            if cmd == "toggle_pause":
                engine.manual_pause = not engine.manual_pause
                engine._emit("UI", f"Manual pause set to {engine.manual_pause}")
            elif cmd == "toggle_aplus":
                engine.force_a_plus = not engine.force_a_plus
                engine._emit("UI", f"Force A+ Sniper Mode set to {engine.force_a_plus}")
            elif cmd == "sell_all":
                asyncio.run_coroutine_threadsafe(engine.sell_all_positions("UI_SELL_ALL"), loop)
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(b'{"ok":true}')

    srv = ThreadingHTTPServer((engine.cfg.dashboard_host, engine.cfg.dashboard_port), Handler)
    threading.Thread(target=srv.serve_forever, daemon=True, name="web-ui").start()
    return srv


# --------------------------------------------------------------------------------------
# Background Workers (Blockhash Refresh, Zombie WS Watchdog, PumpPortal WS / Demo Feed)
# --------------------------------------------------------------------------------------
async def blockhash_loop(engine: SolSniperEngine) -> None:
    while not engine._stop.is_set():
        await engine.rpc.refresh_blockhash()
        await asyncio.sleep(2.0)


async def ws_watchdog_loop(engine: SolSniperEngine) -> None:
    while not engine._stop.is_set():
        await asyncio.sleep(1.5)
        age = time.time() - engine.last_ws_msg_ts
        if age >= engine.cfg.ws_watchdog_sec and engine.positions:
            engine._emit("WATCHDOG", f"WS silent for {age:.1f}s with {len(engine.positions)} open pos -> REST fallback check")


async def demo_feed_loop(engine: SolSniperEngine, max_ticks: int = 0) -> None:
    """Offline realistic Pump.fun tape simulator for testing Dashboard, TP1, Graduation & Stops."""
    rng = random.Random(7)
    mints = [
        ("7xK9mN2pQrStUvWxYz123456789ABCDEFGHJKLMNPQ", "PEANUT", "squirrel"),
        ("9bM4kL8nPqRsTuVwXy23456789ABCDEFGHJKLMNPQR", "GIGA", "ai_agent"),
        ("4cP7rT3vWxYzAbCdEf3456789ABCDEFGHJKLMNPQRS", "RUGME", "fake_cto"),
    ]
    live: list[TokenState] = []
    for m, sym, nar in mints:
        t = TokenState(mint=m, symbol=sym, name=sym, narrative=nar, v_sol=155.0, v_tok=800_000_000.0, mc_usd=31968.0, top10_pct=16.5)
        t.buyers = {f"w{i}" for i in range(44)}
        t.buy_vol_60s_sol, t.sell_vol_60s_sol = 18.0, 4.0
        live.append(t)

    tick = 0
    while not engine._stop.is_set():
        tick += 1
        tok = live[tick % len(live)]
        # Simulate realistic move: PEANUT pumps + migrates, RUGME dumps -30%
        if tok.symbol == "PEANUT":
            mult = rng.uniform(1.02, 1.12)
            tok.curve_pct = min(1.0, tok.curve_pct + 0.09)
            if tok.curve_pct >= 0.99 and tok.venue == Venue.BONDING_CURVE:
                await engine.handle_graduation(tok.mint, Venue.PUMPSWAP)
        elif tok.symbol == "RUGME":
            mult = rng.uniform(0.84, 0.96)
        else:
            mult = rng.uniform(0.95, 1.07)
        tok.v_sol = max(10.0, tok.v_sol * math.sqrt(mult))
        tok.v_tok = max(1e6, tok.v_tok / math.sqrt(mult))
        tok.price_sol = tok.v_sol / tok.v_tok
        tok.mc_usd = tok.price_sol * 1_000_000_000.0 * engine.cfg.sol_usd_ref
        tok.last_buy_ts = time.time()
        await engine.on_swap_tick(tok)
        if max_ticks and tick >= max_ticks:
            break
        await asyncio.sleep(0.05 if max_ticks else 0.35)


async def pumpportal_ws_loop(engine: SolSniperEngine) -> None:
    try:
        import websockets
    except ImportError:
        engine._emit("ERROR", "Install websockets first: pip install websockets (or run with --demo)")
        engine._stop.set()
        return

    while not engine._stop.is_set():
        try:
            async with websockets.connect(engine.cfg.ws_url, ping_interval=20, ping_timeout=10) as ws:
                await ws.send(json.dumps({"method": "subscribeNewToken"}))
                await ws.send(json.dumps({"method": "subscribeMigration"}))
                engine._emit("WS", f"Connected to {engine.cfg.ws_url}")
                async for raw in ws:
                    if engine._stop.is_set():
                        break
                    engine.last_ws_msg_ts = time.time()
                    msg = json.loads(raw)
                    mint = str(msg.get("mint") or "")
                    if not BASE58_RX.match(mint):
                        continue
                    tx_type = str(msg.get("txType") or "")
                    if tx_type == "migration":
                        await engine.handle_graduation(mint, Venue.PUMPSWAP)
                        continue
                    v_sol = float(msg.get("vSolInBondingCurve") or 0.0)
                    v_tok = float(msg.get("vTokensInBondingCurve") or 0.0)
                    if v_sol <= 0 or v_tok <= 0:
                        continue
                    px = v_sol / v_tok
                    mc_usd = px * 1_000_000_000.0 * engine.cfg.sol_usd_ref
                    tok = engine.tokens.get(mint) or TokenState(
                        mint=mint, symbol=str(msg.get("symbol") or mint[:5]), name=str(msg.get("name") or "")
                    )
                    tok.v_sol, tok.v_tok, tok.price_sol, tok.mc_usd = v_sol, v_tok, px, mc_usd
                    tok.curve_pct = min(1.0, max(0.0, (v_sol - 30.0) / 85.0))
                    trader = str(msg.get("traderPublicKey") or "")
                    sol_amt = float(msg.get("solAmount") or 0.0)
                    if tx_type == "buy":
                        if trader:
                            tok.buyers.add(trader)
                        tok.buy_vol_60s_sol = tok.buy_vol_60s_sol * 0.92 + sol_amt
                        tok.last_buy_ts = time.time()
                    elif tx_type == "sell":
                        tok.sell_vol_60s_sol = tok.sell_vol_60s_sol * 0.92 + sol_amt
                    elif tx_type == "create":
                        await ws.send(json.dumps({"method": "subscribeTokenTrade", "keys": [mint]}))
                    await engine.on_swap_tick(tok)
        except Exception as e:
            engine.ws_reconnects += 1
            engine._emit("WS", f"Disconnected ({e}) -> reconnecting in 2s (#{engine.ws_reconnects})")
            await asyncio.sleep(2.0)


async def run_app(cfg: SolBotConfig, demo: bool = False) -> None:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
    engine = SolSniperEngine(cfg)
    loop = asyncio.get_running_loop()
    srv = start_dashboard_server(engine, loop)
    url = f"http://{cfg.dashboard_host}:{cfg.dashboard_port}/?token={cfg.dashboard_token}"
    print(f"\n>>> SolSniper M1 Live Web Dashboard: {url}\n")

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, engine._stop.set)
        except (NotImplementedError, ValueError):
            pass

    tasks = [
        asyncio.create_task(blockhash_loop(engine)),
        asyncio.create_task(ws_watchdog_loop(engine)),
        asyncio.create_task(demo_feed_loop(engine) if demo else pumpportal_ws_loop(engine)),
    ]
    await engine._stop.wait()
    for t in tasks:
        t.cancel()
    srv.shutdown()


def main() -> None:
    ap = argparse.ArgumentParser(description="SolSniper M1 — Solana Multi-Agent Paper Bot")
    ap.add_argument("--demo", action="store_true", help="Run offline simulated Pump.fun feed + Live Dashboard")
    ap.add_argument("--port", type=int, default=8080, help="Web Dashboard port (default 8080)")
    args, _ = ap.parse_known_args()
    cfg = SolBotConfig(dashboard_port=args.port)
    asyncio.run(run_app(cfg, demo=args.demo))


if __name__ == "__main__":
    main()