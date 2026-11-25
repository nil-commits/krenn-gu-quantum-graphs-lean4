# Red-Team Audit Report: `RHDirect/PPL007_WorldRecord.lean` (World-Record Partial Milestone)

- **Target:** `D:\Arithmetica4Prizeproblems - Kopie\prize_lean\RHDirect\PPL007_WorldRecord.lean`
- **Problem:** PPL 007 (Krenn–Gu Conjecture — Monochromatic Inherited Vertex Colorings, €3,000, OPEN)
- **Scope:** **General Bound Milestone ONLY (`D ≤ N - 3` for all even `N ≥ 10`)** — strictly improves `D ≤ N - 2`, does **NOT** prove the full €3,000 `D = 3` conjecture (`3 ≤ D ≤ N - 3` for `N ≥ 8` remains open).
- **Verdict:** **PASS (World-Record General Bound Milestone Scope)**

## Gate 1 — Static Zero-Cheat Scan: PASS
- `verify_prize.ps1 -Files RHDirect/PPL007_WorldRecord.lean`: `[GATE 1 PASS] Static zero-cheat scan: 0 hits (1 file(s))`
- Independent `Select-String` check confirmed 0 hits for `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `@[implemented_by]`, `@[extern]`, monolithic `import Mathlib`, or Tier C `RHDirect.*` imports (targeted Mathlib imports on lines 16–34 only).

## Gate 2 — Independent Remote Compile + `leanchecker`: PASS
- Compiled on `rh-lean-hub` (`35.209.66.55`): `[check_prize] RHDirect/PPL007_WorldRecord.lean: 18.02 sec (4468524 KB maxrss)`
- `0` errors, `0` warnings.
- Official `leanchecker`: `[check_prize] leanchecker RHDirect.PPL007_WorldRecord: PASS`

## Gate 3 — Exhaustive Axiom Audit: PASS
- `[check_prize] axioms RHDirect.PPL007_WorldRecord: PASS (704 constants, strictly <= {propext, Classical.choice, Quot.sound})`

## Gate 4 — Statement-Faithfulness & Scope Audit: PASS (General Bound Milestone)
- Audited `MonochromaticQuantumGraph` definitions (lines 82–205: `V`, `EdgeN`, `WeightsN`, `mkEdge`, `vertices`, `allEqualList`, `allEqual`, `pmSumListAux`, `pmSumList`, `pmSumN`, `EqSystemN`) verbatim against Krenn–Gu / `FormalConjectures/Paper/MonochromaticQuantumGraph.lean`:
  - `vertices N` is strictly increasing `[0, ..., N-1]` (`vertices_pairwise_lt`), `allEqual ι ↔ ∀ u v, ι u = ι v` (`allEqual_iff_forall_eq`), and `pmSumN N D W ι` sums over every perfect matching of `K_N` bijectively by pairing the minimum remaining vertex `v` with each later `u > v` and recursing on `vs.erase u`.
  - Over any field (e.g. `FractionRing K`, `ℂ`, `ℝ`), normalizing nonzero monochromatic values to `1` is without loss of generality (rescaling vertex `0` weights by `c_i⁻¹`).
- Public theorems (lines 6195–6234) contain 0 custom helper classes (`ValidDim` is internal) and 0 hidden hypotheses:
  - `ppl007_world_record_domain {K : Type} [CommRing K] [IsDomain K] (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) : ¬ ∃ W : WeightsN N D K, EqSystemN N D W`
  - `ppl007_world_record_complex`, `ppl007_world_record_real`
  - `ppl007_no_solution_n12_d10_complex`, `ppl007_no_solution_n14_d12_complex`
- Clearly and accurately labeled in docstrings and theorem names as a general bound milestone (`D ≤ N - 3` for all even `N ≥ 10`), not a full `D = 3` prize claim.
