# Krenn–Gu Monochromatic Quantum Graphs in Lean 4 (`D ≤ N - 3` for all even `N ≥ 10`)

A standalone, pure-Mathlib Lean 4 (`v4.33.1`) formalization proving a general upper bound of **`D ≤ N - 3`** for **all even `N ≥ 10`** on the Krenn–Gu monochromatic quantum graph equation system (`EqSystemN N D W`) over every commutative integral domain `K` (including `ℂ` and `ℝ`).

## Honest Scope & Literature Context

- **What is proved:** For every even `N ≥ 10`, every `D ≥ N - 2`, and every commutative integral domain `K`, there is no weight assignment `W : WeightsN N D K` satisfying `EqSystemN N D W`. Equivalently, every solution over an integral domain satisfies `D ≤ N - 3`.
- **Comparison with prior bounds:** Strictly improves the global general bound `D ≤ N - 2` (`KitaKen1`, Formal Conjectures PR #4661) and uniformly resolves infinitely many previously open cases—including `(N = 12, D = 10)`, `(N = 14, D = 12)`, `(N = 16, D = 14)`, …—without any SAT/LRAT solver.
- **What remains open (NOT claimed solved):** This does **not** prove the full €3,000 Krenn–Gu conjecture, which asserts that no solution exists for `D ≥ 3` (i.e., `D ≤ 2`) for all even `N ≥ 6` over `ℂ`. Cases with `3 ≤ D ≤ N - 3` for `N ≥ 8` (starting at `(N = 8, D = 3)`) remain open.

## Verbatim Lean 4 Theorem Signatures

All public theorems live in `KrennGu/PPL007_WorldRecord.lean` (referencing `MonochromaticQuantumGraph.WeightsN` and `MonochromaticQuantumGraph.EqSystemN`, copied verbatim from `FormalConjectures/Paper/MonochromaticQuantumGraph.lean`) with **0** custom helper classes or hidden hypotheses in their signatures:

```lean
theorem ppl007_world_record_domain {K : Type} [CommRing K] [IsDomain K]
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D K, EqSystemN N D W

theorem ppl007_world_record_complex
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D ℂ, EqSystemN N D W

theorem ppl007_world_record_real
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D ℝ, EqSystemN N D W

theorem ppl007_no_solution_n12_d10_complex :
    ¬ ∃ W : WeightsN 12 10 ℂ, EqSystemN 12 10 W

theorem ppl007_no_solution_n14_d12_complex :
    ¬ ∃ W : WeightsN 14 12 ℂ, EqSystemN 14 12 W
```

## Verification Results

Audited in [`docs/audit_ppl007_worldrecord.md`](docs/audit_ppl007_worldrecord.md) on Lean `v4.33.1`:

- **Static zero-cheat scan:** PASS (`0` `sorry`, `0` `admit`, `0` `axiom`, `0` `opaque`, `0` `native_decide`, `0` `unsafe`, `0` `@[implemented_by]`/`@[extern]`)
- **Build & kernel verification:** `0` errors, `0` warnings (`18.02 sec`, `4468524 KB maxrss`); official `leanchecker` **PASS**
- **Axiom audit:** **704** constants, strictly `⊆ {propext, Classical.choice, Quot.sound}`

## Repository Layout

- `KrennGu/PPL007_WorldRecord.lean` — complete standalone formalization (`6,234` lines)
- `docs/audit_ppl007_worldrecord.md` — 4-gate red-team audit report
- `docs/ppl007_findings.md` — mathematical analysis, border-rank obstruction notes, and proof architecture
- `lakefile.toml` / `lean-toolchain` — pinned to `leanprover/lean4:v4.33.1` and `mathlib4` rev `0df444a360eaa60ab8c11dca51a86af692955474`

## Building

```bash
lake exe cache get
lake build KrennGu
```

## License & Attribution

Licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)). Includes definitions from `FormalConjectures/Paper/MonochromaticQuantumGraph.lean` (Copyright 2026 The Formal Conjectures Authors, Apache-2.0) and generalizes the `(N = 10, D = 8)` solver-free algebraic framework of `KitaKen1` (`monochromatic-quantum-graph-sharp-bound-lean` and `monochromatic-quantum-graph-n10-d8-lean`, Copyright 2026 The quantum-cr contributors, Apache-2.0).
