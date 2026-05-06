#!/usr/bin/env python3
"""Estimate the size of «微核源» (M4-甲's literal `List YiInstr` for the
self-hosting microkernel) **before** committing to path 甲 vs 乙.

Risk mitigated: 路径丙 § 风险 6 (M2 末文本量爆炸).

Output (printed):
    · Per-handler instruction count for each of 12 YiInstr cases
    · 12-way dispatch table size
    · fetch + decode + writeback overhead
    · Total estimated `List YiInstr` length
    · Estimated wenyan source line count (one instruction per line)
    · Estimated Cell192 encoding length (after ProgEnc.encProg)
    · Decision recommendation per the route-丙 thresholds

Decision thresholds (from plan):
    · text < 200 lines → 路径乙 (standalone) viable
    · text > 500 lines → 路径甲 (in-Lean reflection) preferred
    · 200 ≤ text ≤ 500 → measure native_decide cost, then decide

Run: python3 scripts/estimate_microkernel_size.py
"""
from __future__ import annotations

import sys
from dataclasses import dataclass


@dataclass
class HandlerEstimate:
    op: str
    instrs: int       # YiInstr count for this handler
    notes: str = ""


# Per-instruction handler estimates (rough; refine after spike).
# Each handler reads tag, decodes args (if any), executes, writes back state,
# and jumps back to the dispatch loop.
HANDLERS: list[HandlerEstimate] = [
    HandlerEstimate("nop",                instrs=4,  notes="just inc pc + writeback"),
    HandlerEstimate("setShi",             instrs=8,  notes="decode Shi (3-way) + state.cur.2 := s"),
    HandlerEstimate("flipYao",            instrs=12, notes="decode Fin 6 + flip nth yao"),
    HandlerEstimate("hu",                 instrs=10, notes="hu transformation on hexagram"),
    HandlerEstimate("cuo",                instrs=8,  notes="cuo transformation"),
    HandlerEstimate("zong",               instrs=10, notes="zong transformation"),
    HandlerEstimate("branchYaoEq",        instrs=20, notes="decode 2 Fin 6 + Nat + cmp + branch"),
    HandlerEstimate("branchShiEq",        instrs=15, notes="decode Shi + Nat + cmp + branch"),
    HandlerEstimate("jump",               instrs=8,  notes="decode Nat + set pc"),
    HandlerEstimate("push",               instrs=10, notes="state.history := cur :: history"),
    HandlerEstimate("pop",                instrs=12, notes="state.cur := history.head; tail"),
    HandlerEstimate("halt",               instrs=4,  notes="set halted = true"),
]

# Dispatch overhead: 12-way branchYaoEq tree to jump to handlers.
DISPATCH_TABLE_INSTRS = 12 * 7  # binary-tree dispatch on 4-bit tag (~7 instr per level)
FETCH_DECODE_INSTRS = 30        # fetch instr at pc, decode tag (12 cases)
EPILOG_INSTRS = 20              # writeback + loop back to fetch


def estimate_lines() -> tuple[int, int, int]:
    handler_total = sum(h.instrs for h in HANDLERS)
    overhead = DISPATCH_TABLE_INSTRS + FETCH_DECODE_INSTRS + EPILOG_INSTRS
    total_instrs = handler_total + overhead

    # Wenyan source: roughly one instruction per source line in baguaWen
    # (each instr emits one «verb» + args; ≈1 line)
    wen_lines = total_instrs

    # Cell192 encoding (per WenyanSelfInterp §3 encInstr):
    #  · nullary instr: 1 cell
    #  · setShi/flipYao: 2 cells
    #  · branchYaoEq:    3 + encNat(t)  (encNat ≈ ⌈log₁₉₂(t)⌉ cells, typically 1-2)
    #  · branchShiEq:    2 + encNat(t)  (likewise 1-2 cells)
    #  · jump:           1 + encNat(t)
    avg_cells_per_instr = 2.5
    cell_count = int(total_instrs * avg_cells_per_instr)

    return total_instrs, wen_lines, cell_count


def recommend(wen_lines: int) -> str:
    if wen_lines < 200:
        return "RECOMMEND: 路径乙 (standalone wen-runtime) viable."
    if wen_lines > 500:
        return "RECOMMEND: 路径甲 (in-Lean reflection) preferred — text is too large for human-readable .wen."
    return ("MEASURE: 200 ≤ text ≤ 500. Run a native_decide cost spike first; "
            "if < 5s on full chunk, prefer 甲; else 乙.")


def main() -> int:
    print("=" * 64)
    print("«微核源» size estimate · path 丙 decision-point pre-probe")
    print("=" * 64)
    print()
    print("Per-handler estimate:")
    print(f"  {'op':<14} {'instrs':>7}   notes")
    print(f"  {'-' * 14} {'-' * 7}   {'-' * 40}")
    for h in HANDLERS:
        print(f"  {h.op:<14} {h.instrs:>7}   {h.notes}")
    print(f"  {'-' * 14} {'-' * 7}")
    handler_total = sum(h.instrs for h in HANDLERS)
    print(f"  {'(handlers)':<14} {handler_total:>7}")
    print()
    print(f"Dispatch table:           {DISPATCH_TABLE_INSTRS:>7} instr")
    print(f"Fetch + decode:           {FETCH_DECODE_INSTRS:>7} instr")
    print(f"Epilog:                   {EPILOG_INSTRS:>7} instr")
    print()
    total_instrs, wen_lines, cell_count = estimate_lines()
    print(f"TOTAL List YiInstr:       {total_instrs:>7} instr")
    print(f"≈ Wenyan source lines:    {wen_lines:>7} lines")
    print(f"≈ Cell192 encoding:       {cell_count:>7} cells")
    print()
    print(recommend(wen_lines))
    print()
    print("Note: refine these estimates after the M2 spike — measure actual")
    print("instruction count for one handler (e.g. setShi) and rescale.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
