/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Based on definitions from `FormalConjectures/Paper/MonochromaticQuantumGraph.lean`
(Copyright 2026 The Formal Conjectures Authors, Apache-2.0) and generalized from the
`(N = 10, D = 8)` solver-free algebraic framework of `KitaKen1`
(`monochromatic-quantum-graph-sharp-bound-lean` & `monochromatic-quantum-graph-n10-d8-lean`,
Copyright 2026 The quantum-cr contributors, Apache-2.0).

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false

/-!
# PPL 007 (Krenn–Gu Conjecture): New World-Record General Bound `D ≤ N - 3` (`∀ even N ≥ 10`)

## Scope & Honest Labeling
This file proves a **new world-record general upper bound** for the Krenn–Gu monochromatic quantum
graph equation system (`EqSystemN N D W`):

> **Main Theorem (`ppl007_world_record_domain` / `ppl007_world_record_complex`):**
> For **every** even `N ≥ 10`, **every** `D ≥ N - 2`, and **every** commutative integral domain `K`
> (in particular `ℂ` and `ℝ`), there is **no** weight assignment `W : WeightsN N D K` satisfying
> `EqSystemN N D W`.

Equivalently, every monochromatic quantum graph on an even number `N ≥ 10` of vertices over any
integral domain has at most **`D ≤ N - 3`** colors.

- **Status vs. Literature:** Strictly improves the 2026 global general bound `D ≤ N - 2`
  (`KitaKen1`, Formal Conjectures PR #4661) and generalizes the single-instance `(N = 10, D = 8)`
  result to **all even `N ≥ 10` and all `D ≥ N - 2`** simultaneously, resolving infinitely many
  previously open cases (`(12, 10)`, `(14, 12)`, `(16, 14)`, …) without any SAT solver.
- **NOT the full €3,000 Krenn–Gu conjecture:** The full conjecture asks for `D ≤ 2` (i.e. no
  solution for `D ≥ 3`) for all even `N ≥ 6` over `ℂ`; cases with `3 ≤ D ≤ N - 3` for `N ≥ 8`
  (starting at `(N = 8, D = 3)`) remain open.

## Key Original Generalizations in This File
1. Uniform parameterization of the full-column, unique-exception, slice/pair, pencil-classification,
   and bad-color accounting machinery for **arbitrary even `N = n + 2 ≥ 10`** (`D = n ≥ 8`),
   replacing hardcoded `(10, 8)` bounds with `3 * S.card ≤ 2 * n < 3 * (n - 2)` and
   `2 * Bset.card ≤ n + 2` (yielding `≥ n - (n + 2) / 2 ≥ 3` clean colors for every even `N ≥ 10`).
2. A **new, general, solver-free Bogdanov's Lemma (`exists_mixed_matching_general`) for ALL even
   `N ≥ 6`**, covering **both** `N ≡ 2 (mod 4)` (single parity-changing chord) and `N ≡ 0 (mod 4)`
   (minimal-chord interleaving pair on the Hamiltonian `R ∪ B` cycle).
3. Color restriction (`eqSystemN_restrict`) lifting `D = N - 2` to **all `D ≥ N - 2`**.
-/


/- ## Section: definitions copied from Formal Conjectures

The definitions below are copied unchanged from
`FormalConjectures/Paper/MonochromaticQuantumGraph.lean` of
https://github.com/google-deepmind/formal-conjectures (Apache License 2.0). -/

open scoped Matrix
open scoped NNReal

namespace MonochromaticQuantumGraph

/-- Vertices of $K_N$. -/
abbrev V (N : Nat) := Fin N

/-- Edge label for $K_N$ with endpoint indices in `Fin D`.

We *intend* to build edges only with `u < v` (so undirected edges are represented once),
and our enumeration always pairs the first vertex in an ordered list with a later vertex.
-/
structure EdgeN (N D : Nat) where
  u : V N
  v : V N
  i : Fin D
  j : Fin D
deriving DecidableEq

/-- Weights on edges. -/
abbrev WeightsN (N D : Nat) (α : Type) := EdgeN N D → α

/-- Helper: build an `EdgeN` from endpoints and endpoint indices. -/
def mkEdge {N D : Nat} (u v : V N) (i j : Fin D) : EdgeN N D :=
  ⟨u, v, i, j⟩

/-- Ordered vertex list $[0, 1, \ldots, N-1]$. -/
def vertices : (N : Nat) → List (V N)
  | 0 => []
  | N + 1 =>
      (0 : Fin (N + 1)) :: (vertices N).map Fin.succ

/-
## `allEqual`: "all indices are equal"

We package the property "all indices `ι v` are equal" as a chain condition along a vertex list.

Concretely, `allEqualList ι L` means that the relation `ι v = ι w` holds between adjacent elements
of `L`. We implement this with `List.IsChain`, which is convenient for later reasoning and provides
good simp/decidability support.
-/

/-- Chain-equality along a list of vertices. -/
def allEqualList {N D : Nat} (ι : V N → Fin D) (L : List (V N)) : Prop :=
  List.IsChain (fun v w => ι v = ι w) L

/-- All indices equal on `Fin N` (using the canonical ordered vertex list). -/
def allEqual {N D : Nat} (ι : V N → Fin D) : Prop :=
  allEqualList ι (vertices N)

/-- Instance: `allEqualList ι L` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) (L : List (V N)) :
    Decidable (allEqualList ι L) := by
  letI : DecidableRel (fun v w : V N => ι v = ι w) := fun v w => inferInstance
  unfold allEqualList
  infer_instance

/-- Instance: `allEqual ι` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) : Decidable (allEqual ι) := by
  unfold allEqual
  infer_instance

/-
## Perfect matching sum, general `N`

Fix a semiring `α`, a weight function `W : WeightsN N D α`, and an index assignment
`ι : V N → Fin D`. The next definitions compute the sum over perfect matchings of the complete graph
on `N` vertices, where each edge is selected with the endpoint indices given by `ι`.

We define an auxiliary function `pmSumListAux W ι n L` with a decreasing fuel parameter `n`
(used only for termination). In the intended use, we call it with `n = L.length`.

Intuition (when `n = L.length`):

* `n = 0` : the empty matching contributes `1` (empty product).
* `n = 1` : odd number of vertices, so no perfect matchings; value `0`.
* `n = n' + 2` and `L = v :: vs`:
  pair `v` with each `u ∈ vs`, multiply the edge weight by the recursive contribution on the
  remaining vertices `vs.erase u`, and sum over `u`.
-/

/-- Auxiliary perfect-matching sum on a vertex list, using a fuel parameter `n` for termination.

When called as `pmSumListAux W ι L.length L`, this computes the weighted sum over all perfect
matchings on the vertices in `L`. The recursion pairs the head vertex with each later vertex and
recurses on the remaining vertices.

For lists of odd length, there are no perfect matchings and the value is `0`. -/
def pmSumListAux {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) :
    Nat → List (V N) → α
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, [] => 1
  | _ + 2, [_] => 0
  | n + 2, v :: vs =>
      (vs.map (fun u =>
          W (mkEdge v u (ι v) (ι u)) *
            pmSumListAux W ι n (vs.erase u)
        )).sum

/-- Perfect-matching sum on a list: run `pmSumListAux` with `fuel = L.length`. -/
def pmSumList {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) (L : List (V N)) : α :=
  pmSumListAux W ι L.length L

/-- The perfect-matching sum for $K_N$: use the canonical ordered vertex list `vertices N`. -/
def pmSumN {α : Type} [Semiring α] (N D : Nat)
    (W : WeightsN N D α) (ι : V N → Fin D) : α :=
  pmSumList W ι (vertices N)

/-- The monochromatic quantum graph equation system for $K_N$.

For every index assignment $\iota : V_N \to \mathrm{Fin}\, D$, the perfect-matching sum equals $1$
if $\iota$ is constant (monochromatic inherited vertex colouring), and equals $0$ otherwise. -/
def EqSystemN {α : Type} [Semiring α] (N D : Nat) (W : WeightsN N D α) : Prop :=
  ∀ ι : V N → Fin D,
    pmSumN N D W ι =
      (if allEqual ι then (1 : α) else (0 : α))

/-- Instance: `EqSystemN N D W` is decidable when `α` has decidable equality. -/
instance instDecidableEqSystemN {N D : Nat} {α : Type} [Semiring α] [DecidableEq α]
    (W : WeightsN N D α) : Decidable (EqSystemN N D W) :=
  Fintype.decidableForallFintype

end MonochromaticQuantumGraph

/- ## Section: `QuantumCR.Vertices` -/

/-
# Canonical vertex-list facts

Facts connecting the chain-based `allEqual` predicate in Formal Conjectures
to the ordinary statement that a coloring is constant.
-/

open MonochromaticQuantumGraph

namespace QuantumCR

/-- Standard coordinate vector. -/
def coordinateVector {F : Type} [Zero F] [One F] {D : Nat}
    (c : Fin D) : Fin D → F :=
  fun d => if d = c then 1 else 0

@[simp]
theorem coordinateVector_apply_same {F : Type} [Zero F] [One F] {D : Nat}
    (c : Fin D) : coordinateVector (F := F) c c = 1 := by
  simp [coordinateVector]

@[simp]
theorem coordinateVector_apply_ne {F : Type} [Zero F] [One F] {D : Nat}
    {c d : Fin D} (h : d ≠ c) : coordinateVector (F := F) c d = 0 := by
  simp [coordinateVector, h]

@[simp]
theorem vertices_length : ∀ N : Nat, (vertices N).length = N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => simp [vertices, ih]

theorem vertices_nodup : ∀ N : Nat, (vertices N).Nodup := by
  intro N
  induction N with
  | zero => simp [vertices]
  | succ N ih =>
      simp only [vertices, List.nodup_cons]
      constructor
      · simp
      · exact ih.map (Fin.succ_injective N)

/-- The canonical vertex list is strictly increasing. -/
theorem vertices_pairwise_lt : ∀ N : Nat, (vertices N).Pairwise (· < ·) := by
  intro N
  induction N with
  | zero => simp [vertices]
  | succ N ih =>
      simp only [vertices, List.pairwise_cons]
      constructor
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simp
      · rw [List.pairwise_map]
        exact ih.imp (fun hab => Fin.succ_lt_succ_iff.mpr hab)

@[simp]
theorem mem_vertices {N : Nat} (v : V N) : v ∈ vertices N := by
  induction N with
  | zero => exact Fin.elim0 v
  | succ N ih =>
      by_cases hv : v = 0
      · subst v
        simp [vertices]
      · have hpos : 0 < v.val := Nat.pos_of_ne_zero (by
          intro hzero
          apply hv
          exact Fin.ext hzero)
        let w : Fin N := ⟨v.val - 1, by omega⟩
        have hvw : Fin.succ w = v := by
          apply Fin.ext
          simp [w]
          omega
        rw [← hvw]
        simp [vertices, ih w]

/-- The chain-based `allEqual` predicate is ordinary pointwise constancy. -/
theorem allEqual_iff_forall_eq {N D : Nat} (ι : V N → Fin D) :
    allEqual ι ↔ ∀ u v, ι u = ι v := by
  constructor
  · intro h u v
    let R : V N → V N → Prop := fun x y => ι x = ι y
    have : Std.Refl R := ⟨fun _ => rfl⟩
    let _ : Trans R R R := ⟨fun hxy hyz => hxy.trans hyz⟩
    have hPairwise : (vertices N).Pairwise R :=
      (show (vertices N).IsChain R from h).pairwise
    have hu := hPairwise.rel_head (mem_vertices u)
    have hv := hPairwise.rel_head (mem_vertices v)
    exact hu.symm.trans hv
  · intro h
    unfold allEqual allEqualList
    induction vertices N with
    | nil => simp
    | cons a L ih =>
        cases L with
        | nil => simp
        | cons b bs =>
            exact List.IsChain.cons_cons (h a b) ih

end QuantumCR

/- ## Section: `QuantumCR.Relabel` -/

/-
# Vertex relabeling over a general coefficient semiring

Formal Conjectures stores only the canonical endpoint orientation.  We first
make edge evaluation symmetric, prove that the recursive matching sum is
independent of list order, and then pull weights back along a vertex
permutation.
-/

open MonochromaticQuantumGraph

namespace QuantumCR

/-- Evaluate an undirected colored edge after sorting its endpoints. -/
def orderedWeight {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (u v : V N) (i j : Fin D) : K :=
  if u < v then W (mkEdge u v i j)
  else if v < u then W (mkEdge v u j i)
  else 0

@[simp]
theorem orderedWeight_of_lt {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (u v : V N) (i j : Fin D) (h : u < v) :
    orderedWeight W u v i j = W (mkEdge u v i j) := by
  simp [orderedWeight, h]

@[simp]
theorem orderedWeight_of_gt {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (u v : V N) (i j : Fin D) (h : v < u) :
    orderedWeight W u v i j = W (mkEdge v u j i) := by
  have hnot : ¬ u < v := not_lt_of_ge (le_of_lt h)
  simp [orderedWeight, h, hnot]

/-- Sorting endpoints is symmetric under swapping vertices and colors. -/
theorem orderedWeight_swap {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (u v : V N) (i j : Fin D) :
    orderedWeight W u v i j = orderedWeight W v u j i := by
  by_cases huv : u < v
  · have hvu : ¬ v < u := not_lt_of_ge (le_of_lt huv)
    simp [orderedWeight, huv, hvu]
  · by_cases hvu : v < u
    · simp [orderedWeight, huv, hvu]
    · have huvLe : u ≤ v := not_lt.mp hvu
      have hvuLe : v ≤ u := not_lt.mp huv
      have huvEq : u = v := le_antisymm huvLe hvuLe
      rw [huvEq]
      simp [orderedWeight]

/-- Symmetric wrapper around canonically oriented weights. -/
def orderedWeights {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) : WeightsN N D K :=
  fun e => orderedWeight W e.u e.v e.i e.j

theorem orderedWeights_sym {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (ι : V N → Fin D) (u v : V N) :
    orderedWeights W (mkEdge u v (ι u) (ι v)) =
      orderedWeights W (mkEdge v u (ι v) (ι u)) :=
  orderedWeight_swap W u v (ι u) (ι v)

/-- Fuel-free head expansion of the recursive matching sum. -/
theorem pmSumList_cons {K : Type} [Semiring K] {N D : Nat}
    (W : WeightsN N D K) (ι : V N → Fin D)
    (v : V N) (vs : List (V N)) :
    pmSumList W ι (v :: vs) =
      (vs.map (fun x => W (mkEdge v x (ι v) (ι x)) *
        pmSumList W ι (vs.erase x))).sum := by
  cases vs with
  | nil => rfl
  | cons u us =>
      simp only [pmSumList, List.length_cons, pmSumListAux]
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      have hLength : ((u :: us).erase x).length = us.length := by
        have hErase := List.length_erase_add_one hx
        simp only [List.length_cons] at hErase
        omega
      rw [hLength]

theorem mul_list_sum {K : Type} [Semiring K] (a : K) (L : List K) :
    a * L.sum = (L.map (fun x => a * x)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

theorem list_sum_map_add_distrib
    {K A : Type} [AddCommMonoid K] (F G : A → K) (L : List A) :
    (L.map (fun x => F x + G x)).sum = (L.map F).sum + (L.map G).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel

/-- Transpose the sum over ordered pairs of distinct elements. -/
theorem list_sum_erase_transpose
    {K A : Type} [AddCommMonoid K] [DecidableEq A]
    (F : A → A → K) : ∀ L : List A, L.Nodup →
      (L.map (fun x => ((L.erase x).map (fun y => F x y)).sum)).sum =
        (L.map (fun y => ((L.erase y).map (fun x => F x y)).sum)).sum := by
  intro L hL
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha : a ∉ L := (List.nodup_cons.mp hL).1
      have hTail : L.Nodup := (List.nodup_cons.mp hL).2
      have hErase : ∀ x ∈ L, (a :: L).erase x = a :: L.erase x := by
        intro x hx
        apply List.erase_cons_tail
        intro hbeq
        have hax : a = x := by simpa only [beq_iff_eq] using hbeq
        subst x
        exact ha hx
      have hLeft :
          (L.map (fun x => (((a :: L).erase x).map (fun y => F x y)).sum)).sum =
            (L.map (fun x => F x a + ((L.erase x).map (fun y => F x y)).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro x hx
        rw [hErase x hx]
        rfl
      have hRight :
          (L.map (fun y => (((a :: L).erase y).map (fun x => F x y)).sum)).sum =
            (L.map (fun y => F a y + ((L.erase y).map (fun x => F x y)).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y hy
        rw [hErase y hy]
        rfl
      simp only [List.map_cons, List.sum_cons, List.erase_cons_head]
      rw [hLeft, hRight, list_sum_map_add_distrib, list_sum_map_add_distrib, ih hTail]
      abel

/-- The symmetric wrapper agrees with original weights on an increasing list. -/
theorem pmSumList_orderedWeights_eq_of_pairwise_lt
    {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) (ι : V N → Fin D) :
    ∀ L : List (V N), L.Pairwise (· < ·) →
      pmSumList (orderedWeights W) ι L = pmSumList W ι L := by
  intro L
  generalize hn : L.length = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
      intro hPair
      cases L with
      | nil => rfl
      | cons v S =>
          rw [pmSumList_cons, pmSumList_cons]
          apply congrArg List.sum
          apply List.map_congr_left
          intro x hx
          have hvx : v < x := (List.pairwise_cons.mp hPair).1 x hx
          change orderedWeight W v x (ι v) (ι x) *
              pmSumList (orderedWeights W) ι (S.erase x) =
            W (mkEdge v x (ι v) (ι x)) * pmSumList W ι (S.erase x)
          rw [orderedWeight_of_lt W v x (ι v) (ι x) hvx]
          apply congrArg (fun z => W (mkEdge v x (ι v) (ι x)) * z)
          have hRestLength : (S.erase x).length < n := by
            have hErase := List.length_erase_add_one hx
            simp only [List.length_cons] at hn
            omega
          exact ih (S.erase x).length hRestLength (S.erase x) rfl
            ((List.pairwise_cons.mp hPair).2.erase x)

/-- Swapping the first two vertices preserves a symmetric matching sum. -/
theorem pmSumList_swap_head
    {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) (ι : V N → Fin D)
    (a b : V N) (L : List (V N)) (hFull : (a :: b :: L).Nodup)
    (hSym : ∀ u v, W (mkEdge u v (ι u) (ι v)) =
      W (mkEdge v u (ι v) (ι u))) :
    pmSumList W ι (a :: b :: L) = pmSumList W ι (b :: a :: L) := by
  have hL : L.Nodup := hFull.tail.tail
  have haL : a ∉ L := by
    intro ha
    exact (List.nodup_cons.mp hFull).1 (by simp [ha])
  have hbL : b ∉ L := (List.nodup_cons.mp hFull.tail).1
  have hEraseB : ∀ x ∈ L, (b :: L).erase x = b :: L.erase x := by
    intro x hx
    apply List.erase_cons_tail
    intro hbeq
    have hbx : b = x := by simpa only [beq_iff_eq] using hbeq
    subst x
    exact hbL hx
  have hEraseA : ∀ x ∈ L, (a :: L).erase x = a :: L.erase x := by
    intro x hx
    apply List.erase_cons_tail
    intro hbeq
    have hax : a = x := by simpa only [beq_iff_eq] using hbeq
    subst x
    exact haL hx
  have hExpandB : ∀ x ∈ L,
      pmSumList W ι (b :: L.erase x) =
        ((L.erase x).map (fun y => W (mkEdge b y (ι b) (ι y)) *
          pmSumList W ι ((L.erase x).erase y))).sum := by
    intro x hx
    exact pmSumList_cons W ι b (L.erase x)
  have hExpandA : ∀ y ∈ L,
      pmSumList W ι (a :: L.erase y) =
        ((L.erase y).map (fun x => W (mkEdge a x (ι a) (ι x)) *
          pmSumList W ι ((L.erase y).erase x))).sum := by
    intro y hy
    exact pmSumList_cons W ι a (L.erase y)
  have hDouble :
      (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
        ((L.erase x).map (fun y => W (mkEdge b y (ι b) (ι y)) *
          pmSumList W ι ((L.erase x).erase y))).sum)).sum =
      (L.map (fun y => W (mkEdge b y (ι b) (ι y)) *
        ((L.erase y).map (fun x => W (mkEdge a x (ι a) (ι x)) *
          pmSumList W ι ((L.erase y).erase x))).sum)).sum := by
    calc
      _ = (L.map (fun x => ((L.erase x).map (fun y =>
          W (mkEdge a x (ι a) (ι x)) *
            (W (mkEdge b y (ι b) (ι y)) *
              pmSumList W ι ((L.erase x).erase y)))).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro x hx
        rw [mul_list_sum]
        apply congrArg List.sum
        simp only [List.map_map, Function.comp_def]
      _ = (L.map (fun y => ((L.erase y).map (fun x =>
          W (mkEdge a x (ι a) (ι x)) *
            (W (mkEdge b y (ι b) (ι y)) *
              pmSumList W ι ((L.erase x).erase y)))).sum)).sum :=
        list_sum_erase_transpose _ L hL
      _ = _ := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y hy
        rw [mul_list_sum]
        apply congrArg List.sum
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro x hx
        rw [List.erase_comm]
        ac_rfl
  rw [pmSumList_cons, pmSumList_cons]
  simp only [List.map_cons, List.sum_cons, List.erase_cons_head]
  have hCleanA :
      (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
        pmSumList W ι ((b :: L).erase x))).sum =
      (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
        pmSumList W ι (b :: L.erase x))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    rw [hEraseB x hx]
  have hCleanB :
      (L.map (fun x => W (mkEdge b x (ι b) (ι x)) *
        pmSumList W ι ((a :: L).erase x))).sum =
      (L.map (fun x => W (mkEdge b x (ι b) (ι x)) *
        pmSumList W ι (a :: L.erase x))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    rw [hEraseA x hx]
  rw [hCleanA, hCleanB]
  have hExpandSumB :
      (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
        pmSumList W ι (b :: L.erase x))).sum =
      (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
        ((L.erase x).map (fun y => W (mkEdge b y (ι b) (ι y)) *
          pmSumList W ι ((L.erase x).erase y))).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    rw [hExpandB x hx]
  have hExpandSumA :
      (L.map (fun y => W (mkEdge b y (ι b) (ι y)) *
        pmSumList W ι (a :: L.erase y))).sum =
      (L.map (fun y => W (mkEdge b y (ι b) (ι y)) *
        ((L.erase y).map (fun x => W (mkEdge a x (ι a) (ι x)) *
          pmSumList W ι ((L.erase y).erase x))).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro y hy
    rw [hExpandA y hy]
  rw [hExpandSumB, hExpandSumA]
  rw [hDouble, hSym a b]

/-- A symmetric matching sum is invariant under list permutations. -/
theorem pmSumList_perm
    {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) (ι : V N → Fin D)
    (hSym : ∀ u v, W (mkEdge u v (ι u) (ι v)) =
      W (mkEdge v u (ι v) (ι u))) :
    ∀ L K' : List (V N), L.Nodup → L.Perm K' →
      pmSumList W ι L = pmSumList W ι K' := by
  intro L
  generalize hn : L.length = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
      intro K' hL hPerm
      induction hPerm with
      | nil => rfl
      | @cons a L K' hPerm ihPerm =>
          have hTailL : L.Nodup := hL.tail
          rw [pmSumList_cons, pmSumList_cons]
          let F : V N → K := fun x => W (mkEdge a x (ι a) (ι x)) *
            pmSumList W ι (K'.erase x)
          calc
            (L.map (fun x => W (mkEdge a x (ι a) (ι x)) *
              pmSumList W ι (L.erase x))).sum = (L.map F).sum := by
                apply congrArg List.sum
                apply List.map_congr_left
                intro x hx
                apply congrArg (fun z => W (mkEdge a x (ι a) (ι x)) * z)
                have hErasePerm : (L.erase x).Perm (K'.erase x) := hPerm.erase x
                have hEraseLength : (L.erase x).length < n := by
                  have hLength := List.length_erase_add_one hx
                  simp only [List.length_cons] at hn
                  omega
                exact ih (L.erase x).length hEraseLength (L.erase x) rfl
                  (K'.erase x) (hTailL.erase x) hErasePerm
            _ = (K'.map F).sum := (hPerm.map F).sum_eq
      | @swap a b L => exact pmSumList_swap_head W ι b a L hL hSym
      | @trans L K' M h₁ h₂ ih₁ ih₂ =>
          have hnK : K'.length = n := h₁.length_eq.symm.trans hn
          exact (ih₁ hn hL).trans (ih₂ hnK (h₁.nodup_iff.mp hL))

/-- Pull weights back along a vertex map. -/
def pullbackWeights {K : Type} {M N D : Nat}
    (W : WeightsN N D K) (f : V M → V N) : WeightsN M D K :=
  fun e => W (mkEdge (f e.u) (f e.v) e.i e.j)

/-- Matching sums commute with an injective relabeling of the vertex list. -/
theorem pmSumList_pullback
    {K : Type} [Semiring K] {M N D : Nat}
    (W : WeightsN N D K) (f : V M → V N) (hf : Function.Injective f)
    (ι : V M → Fin D) (κ : V N → Fin D)
    (hColor : ∀ u, κ (f u) = ι u) : ∀ L : List (V M),
      pmSumList (pullbackWeights W f) ι L = pmSumList W κ (L.map f) := by
  intro L
  generalize hn : L.length = m
  induction m using Nat.strong_induction_on generalizing L with
  | h m ih =>
      cases L with
      | nil => rfl
      | cons v S =>
          rw [pmSumList_cons]
          simp only [List.map_cons]
          rw [pmSumList_cons]
          simp only [List.map_map, Function.comp_def]
          apply congrArg List.sum
          apply List.map_congr_left
          intro x hx
          change W (mkEdge (f v) (f x) (ι v) (ι x)) *
              pmSumList (pullbackWeights W f) ι (S.erase x) =
            W (mkEdge (f v) (f x) (κ (f v)) (κ (f x))) *
              pmSumList W κ ((S.map f).erase (f x))
          rw [hColor v, hColor x, ← List.map_erase hf]
          apply congrArg (fun z => W (mkEdge (f v) (f x) (ι v) (ι x)) * z)
          have hRestLength : (S.erase x).length < m := by
            have hErase := List.length_erase_add_one hx
            simp only [List.length_cons] at hn
            omega
          exact ih (S.erase x).length hRestLength (S.erase x) rfl

/-- Pull weights back along a vertex permutation with canonical orientation. -/
def relabelWeights {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (σ : Equiv.Perm (V N)) : WeightsN N D K :=
  pullbackWeights (orderedWeights W) σ

theorem orderedWeight_relabelWeights
    {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (σ : Equiv.Perm (V N))
    (u v : V N) (i j : Fin D) :
    orderedWeight (relabelWeights W σ) u v i j =
      orderedWeight W (σ u) (σ v) i j := by
  rcases lt_trichotomy u v with huv | huv | huv
  · rw [orderedWeight_of_lt _ _ _ _ _ huv]
    rfl
  · subst v
    simp [orderedWeight]
  · rw [orderedWeight_of_gt _ _ _ _ _ huv]
    change orderedWeight W (σ v) (σ u) j i = _
    exact orderedWeight_swap W (σ v) (σ u) j i

theorem vertices_map_perm {N : Nat} (σ : Equiv.Perm (V N)) :
    ((vertices N).map σ).Perm (vertices N) := by
  apply (List.perm_ext_iff_of_nodup
    ((vertices_nodup N).map σ.injective) (vertices_nodup N)).2
  intro vertex
  simp only [List.mem_map, mem_vertices, iff_true]
  exact ⟨σ.symm vertex, by simp⟩

/-- Perfect-matching sums commute with an arbitrary vertex permutation. -/
theorem pmSumN_relabelWeights
    {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) (σ : Equiv.Perm (V N)) (ι : V N → Fin D) :
    pmSumN N D (relabelWeights W σ) ι =
      pmSumN N D W (fun vertex => ι (σ.symm vertex)) := by
  let κ : V N → Fin D := fun vertex => ι (σ.symm vertex)
  have hPull := pmSumList_pullback (orderedWeights W) σ σ.injective ι κ
    (fun vertex => by simp [κ]) (vertices N)
  have hPerm := pmSumList_perm (orderedWeights W) κ (orderedWeights_sym W κ)
    ((vertices N).map σ) (vertices N)
    ((vertices_nodup N).map σ.injective) (vertices_map_perm σ)
  have hCanonical := pmSumList_orderedWeights_eq_of_pairwise_lt
    W κ (vertices N) (vertices_pairwise_lt N)
  unfold pmSumN
  change pmSumList (pullbackWeights (orderedWeights W) σ) ι (vertices N) =
    pmSumList W κ (vertices N)
  exact hPull.trans (hPerm.trans hCanonical)

/-- Equation systems are invariant under arbitrary vertex relabeling. -/
theorem relabelWeights_eqSystem
    {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) (σ : Equiv.Perm (V N))
    (hW : EqSystemN N D W) : EqSystemN N D (relabelWeights W σ) := by
  intro ι
  let κ : V N → Fin D := fun vertex => ι (σ.symm vertex)
  rw [pmSumN_relabelWeights]
  rw [hW κ]
  have hMono : allEqual κ ↔ allEqual ι := by
    rw [allEqual_iff_forall_eq, allEqual_iff_forall_eq]
    constructor
    · intro h u v
      simpa [κ] using h (σ u) (σ v)
    · intro h u v
      exact h (σ.symm u) (σ.symm v)
  by_cases hι : allEqual ι
  · have hκ : allEqual κ := hMono.mpr hι
    simp [hι, hκ]
  · have hκ : ¬ allEqual κ := fun h => hι (hMono.mp h)
    simp [hι, hκ]

end QuantumCR

/- ## Section: `QuantumCR.MapWeights` -/

/-
# Mapping equation systems along semiring homomorphisms

Perfect-matching sums are polynomials in the edge weights, hence a solution
maps to a solution along every semiring homomorphism.  The full-column proof
uses this with the constant-polynomial map.
-/

open MonochromaticQuantumGraph

namespace QuantumCR

/-- Apply a semiring homomorphism pointwise to all edge weights. -/
def mapWeights {A B : Type} [Semiring A] [Semiring B]
    {N D : Nat} (f : A →+* B) (W : WeightsN N D A) : WeightsN N D B :=
  fun edge => f (W edge)

theorem pmSumListAux_mapWeights
    {A B : Type} [Semiring A] [Semiring B]
    {N D : Nat} (f : A →+* B) (W : WeightsN N D A)
    (ι : V N → Fin D) :
    ∀ fuel L,
      pmSumListAux (mapWeights f W) ι fuel L =
        f (pmSumListAux W ι fuel L) := by
  intro fuel
  induction fuel using Nat.twoStepInduction with
  | zero =>
      intro L
      simp [pmSumListAux]
  | one =>
      intro L
      simp [pmSumListAux]
  | more fuel ih _ =>
      intro L
      cases L with
      | nil => simp [pmSumListAux]
      | cons vertex rest =>
          cases rest with
          | nil => simp [pmSumListAux]
          | cons partner tail =>
              simp only [pmSumListAux, List.map_cons, List.sum_cons]
              rw [map_add, map_mul]
              rw [map_list_sum f]
              simp only [mapWeights, ih]
              congr 1
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro u hu
              simp [Function.comp_apply]

theorem pmSumList_mapWeights
    {A B : Type} [Semiring A] [Semiring B]
    {N D : Nat} (f : A →+* B) (W : WeightsN N D A)
    (ι : V N → Fin D) (L : List (V N)) :
    pmSumList (mapWeights f W) ι L = f (pmSumList W ι L) := by
  exact pmSumListAux_mapWeights f W ι L.length L

theorem pmSumN_mapWeights
    {A B : Type} [Semiring A] [Semiring B]
    {N D : Nat} (f : A →+* B) (W : WeightsN N D A)
    (ι : V N → Fin D) :
    pmSumN N D (mapWeights f W) ι = f (pmSumN N D W ι) := by
  exact pmSumList_mapWeights f W ι (vertices N)

/-- Equation systems are preserved by every semiring homomorphism. -/
theorem EqSystemN.mapWeights
    {A B : Type} [Semiring A] [Semiring B]
    {N D : Nat} {W : WeightsN N D A}
    (hW : EqSystemN N D W) (f : A →+* B) :
    EqSystemN N D (mapWeights f W) := by
  intro ι
  rw [pmSumN_mapWeights, hW ι]
  by_cases hEqual : allEqual ι
  · simp [hEqual]
  · simp [hEqual]

end QuantumCR

/- ## Section: `QuantumCR.FiniteSums` -/

/-
# Finite-sum factorization

Reusable finite-sum lemmas for separating one or two coordinates of a
function.  These are purely algebraic and do not use characteristic two.
-/

open scoped BigOperators

namespace QuantumCR

/-- Split a finite sum over functions at one coordinate and factor a product
whose two factors depend on disjoint pieces of the function. -/
theorem sum_fun_splitAt_mul {R α β : Type} [CommSemiring R]
    [Fintype α] [DecidableEq α] [Fintype β]
    (v : α) (A : β → R) (G : ({x : α // x ≠ v} → β) → R) :
    (∑ f : α → β, A (f v) * G (fun x => f x)) =
      (∑ a : β, A a) * ∑ g : {x : α // x ≠ v} → β, G g := by
  rw [← (Equiv.funSplitAt v β).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply]
  have hrest :
      ∀ (a : β) (g : {x : α // x ≠ v} → β),
        (fun x : {x : α // x ≠ v} =>
          if h : (x : α) = v then a else g ⟨x, h⟩) = g := by
    intro a g
    funext x
    rw [dif_neg x.2]
  simp_rw [hrest]
  simp only [dif_pos trivial]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Two-coordinate version of `sum_fun_splitAt_mul`. -/
theorem sum_fun_splitAt_two_mul
    {R α β : Type} [CommSemiring R]
    [Fintype α] [DecidableEq α] [Fintype β]
    (v u : α) (hvu : u ≠ v) (A : β → β → R)
    (G : ({x : {y : α // y ≠ v} // x ≠ ⟨u, hvu⟩} → β) → R) :
    (∑ f : α → β,
      A (f v) (f u) * G (fun x => f x.1.1)) =
      (∑ a : β, ∑ b : β, A a b) *
        ∑ g : {x : {y : α // y ≠ v} // x ≠ ⟨u, hvu⟩} → β, G g := by
  rw [← (Equiv.funSplitAt v β).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply]
  simp only [dif_pos trivial]
  have hu :
      ∀ (a : β) (g : {x : α // x ≠ v} → β),
        (if h : u = v then a else g ⟨u, h⟩) = g ⟨u, hvu⟩ := by
    intro a g
    rw [dif_neg hvu]
  simp_rw [hu]
  have hrestTwo :
      ∀ (a : β) (g : {x : α // x ≠ v} → β),
        (fun x : {x : {y : α // y ≠ v} // x ≠ ⟨u, hvu⟩} =>
          if h : (x.1 : α) = v then a else g ⟨x.1, h⟩) =
            fun x => g x.1 := by
    intro a g
    funext x
    rw [dif_neg x.1.2]
  simp_rw [hrestTwo]
  have hinner :
      ∀ a : β,
        (∑ g : {x : α // x ≠ v} → β,
          A a (g ⟨u, hvu⟩) * G (fun x => g x)) =
          (∑ b : β, A a b) *
            ∑ g : {x : {y : α // y ≠ v} // x ≠ ⟨u, hvu⟩} → β, G g := by
    intro a
    exact sum_fun_splitAt_mul (⟨u, hvu⟩ : {x : α // x ≠ v}) (A a) G
  simp_rw [hinner]
  rw [← Finset.sum_mul]

/-- If a factor depends only on two coordinates and the other factor is
invariant under those coordinates, a zero two-coordinate sum kills the full
sum. -/
theorem sum_mul_eq_zero_of_invariant_two
    {R α β : Type} [CommSemiring R]
    [Fintype α] [DecidableEq α] [Fintype β] [Inhabited β]
    (v u : α) (hvu : u ≠ v) (A : β → β → R)
    (B : (α → β) → R)
    (hB : ∀ f κ : α → β,
      (∀ y, y ≠ v → y ≠ u → f y = κ y) → B f = B κ)
    (hA : (∑ a : β, ∑ b : β, A a b) = 0) :
    (∑ f : α → β, A (f v) (f u) * B f) = 0 := by
  let u' : {y : α // y ≠ v} := ⟨u, hvu⟩
  let extend :
      ({x : {y : α // y ≠ v} // x ≠ u'} → β) → α → β :=
    fun g =>
      (Equiv.funSplitAt v β).symm
        (default, (Equiv.funSplitAt u' β).symm (default, g))
  let restrict :
      (α → β) → ({x : {y : α // y ≠ v} // x ≠ u'} → β) :=
    fun f x => f x.1.1
  let G :
      ({x : {y : α // y ≠ v} // x ≠ u'} → β) → R :=
    fun g => B (extend g)
  have hExtend :
      ∀ (f : α → β) y, y ≠ v → y ≠ u →
        f y = extend (restrict f) y := by
    intro f y hyv hyu
    simp [extend, restrict, u', Equiv.funSplitAt_symm_apply, hyv, hyu]
  have hBG : ∀ f : α → β, B f = G (restrict f) := by
    intro f
    exact hB f (extend (restrict f)) (hExtend f)
  calc
    (∑ f : α → β, A (f v) (f u) * B f) =
        ∑ f : α → β, A (f v) (f u) * G (restrict f) := by
          apply Finset.sum_congr rfl
          intro f _
          rw [hBG f]
    _ = (∑ a : β, ∑ b : β, A a b) *
        ∑ g : {x : {y : α // y ≠ v} // x ≠ u'} → β, G g := by
          exact sum_fun_splitAt_two_mul v u hvu A G
    _ = 0 := by rw [hA, zero_mul]

/-- Commute a finite sum with a list sum. -/
theorem sum_list_map_sum_comm {R α β : Type} [AddCommMonoid R] [Fintype α]
    (F : α → β → R) (L : List β) :
    (∑ a : α, (L.map (F a)).sum) =
      (L.map (fun b => ∑ a : α, F a b)).sum := by
  induction L with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

end QuantumCR

/- ## Section: `QuantumCR.ProductContraction` -/

/-
# Product-vector contractions

This module starts the solver-free characteristic-zero argument.  It packages
the contraction of every inherited coloring against one vector at each vertex.
The first main identity rewrites the right-hand side of `EqSystemN` as the GHZ
contraction.
-/

open scoped BigOperators
open MonochromaticQuantumGraph

namespace QuantumCR

/-- A vector with one coordinate for every color, attached to every vertex. -/
abbrev VertexVectors (N D : Nat) (R : Type) := V N → Fin D → R

/-- Contract the perfect-matching amplitude against a product of vertex vectors. -/
def productAmplitude {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (z : VertexVectors N D R) : R :=
  ∑ ι : V N → Fin D, pmSumN N D W ι * ∏ v : V N, z v (ι v)

/-- Contract the diagonal (GHZ) tensor against the same product vector. -/
def ghzAmplitude {R : Type} [CommSemiring R] {N D : Nat}
    (z : VertexVectors N D R) : R :=
  ∑ c : Fin D, ∏ v : V N, z v c

/-- The constant coloring with value `c`. -/
def constantColor {N D : Nat} (c : Fin D) : V N → Fin D := fun _ => c

@[simp]
theorem allEqual_constantColor {N D : Nat} (c : Fin D) :
    allEqual (constantColor (N := N) c) := by
  rw [allEqual_iff_forall_eq]
  simp [constantColor]

/-- An all-equal coloring is the constant coloring determined at any chosen root. -/
theorem eq_constantColor_of_allEqual {N D : Nat} (ι : V N → Fin D)
    (root : V N) (hι : allEqual ι) :
    ι = constantColor (ι root) := by
  funext v
  exact (allEqual_iff_forall_eq ι).mp hι v root

/-- If a root vertex is available, colors are equivalent to all-equal colorings. -/
def constantColorEquiv {N D : Nat} (root : V N) :
    Fin D ≃ {ι : V N → Fin D // allEqual ι} where
  toFun c := ⟨constantColor c, allEqual_constantColor c⟩
  invFun ι := ι.1 root
  left_inv _ := rfl
  right_inv ι := by
    apply Subtype.ext
    exact (eq_constantColor_of_allEqual ι.1 root ι.2).symm

/-- Summing a function over all-equal colorings is the same as summing it
over the unique underlying color. -/
theorem sum_indicator_allEqual {R : Type} [CommSemiring R] {N D : Nat}
    (root : V N) (f : (V N → Fin D) → R) :
    (∑ ι : V N → Fin D, if allEqual ι then f ι else 0) =
      ∑ c : Fin D, f (constantColor c) := by
  classical
  calc
    (∑ ι : V N → Fin D, if allEqual ι then f ι else 0) =
        ∑ ι ∈ Finset.univ.filter allEqual, f ι := by
          rw [Finset.sum_filter]
    _ = ∑ ι : {ι : V N → Fin D // allEqual ι}, f ι.1 := by
      exact Finset.sum_subtype _ (by simp) f
    _ = ∑ c : Fin D, f (constantColor c) := by
      exact (Equiv.sum_comp (constantColorEquiv root) (fun ι => f ι.1)).symm

/-- Every solution of `EqSystemN`, when contracted against arbitrary vertex
vectors, gives exactly the corresponding GHZ contraction. -/
theorem productAmplitude_eq_ghz_of_eqSystem {R : Type} [CommSemiring R]
    {N D : Nat} (W : WeightsN N D R) (hW : EqSystemN N D W)
    (z : VertexVectors N D R) (root : V N) :
    productAmplitude W z = ghzAmplitude z := by
  unfold productAmplitude ghzAmplitude
  calc
    (∑ ι : V N → Fin D, pmSumN N D W ι * ∏ v : V N, z v (ι v)) =
        ∑ ι : V N → Fin D,
          (if allEqual ι then 1 else 0) * ∏ v : V N, z v (ι v) := by
            apply Finset.sum_congr rfl
            intro ι _
            rw [hW ι]
    _ = ∑ ι : V N → Fin D,
        if allEqual ι then (∏ v : V N, z v (ι v)) else 0 := by
          apply Finset.sum_congr rfl
          intro ι _
          split <;> simp_all
    _ = ∑ c : Fin D, ∏ v : V N, z v c :=
      sum_indicator_allEqual root (fun ι => ∏ v : V N, z v (ι v))

end QuantumCR

/- ## Section: `QuantumCR.MatchingContraction` -/

/-
# The matching side of a product-vector contraction

The lemmas here show that a vanishing contracted edge incident to a selected
root kills every matching term that uses that edge.  No decision procedure or
finite certificate is involved.
-/

open scoped BigOperators
open MonochromaticQuantumGraph

namespace QuantumCR

/-- The recursive matching sum depends only on colors of vertices in its
current list. -/
theorem pmSumListAux_coloring_congr {R : Type} [Semiring R] {N D : Nat}
    (W : WeightsN N D R) (ι κ : V N → Fin D) :
    ∀ n L, (∀ v ∈ L, ι v = κ v) →
      pmSumListAux W ι n L = pmSumListAux W κ n L := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L hColor
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              cases L with
              | nil => rfl
              | cons v vs =>
                  cases vs with
                  | nil => rfl
                  | cons u us =>
                      simp only [pmSumListAux]
                      apply congrArg List.sum
                      apply List.map_congr_left
                      intro x hx
                      rw [hColor v (by simp), hColor x (by simp [hx])]
                      congr 1
                      apply ih n (by omega)
                      intro y hy
                      apply hColor y
                      simp only [List.mem_cons]
                      right
                      simpa only [List.mem_cons] using List.mem_of_mem_erase hy

/-- Contract the two endpoint colors of an oriented edge. -/
def incidentContraction {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (z : VertexVectors N D R)
    (root neighbor : V N) : R :=
  ∑ a : Fin D, ∑ b : Fin D,
    z root a * W (mkEdge root neighbor a b) * z neighbor b

/-- Product of all vertex factors except the root and one selected neighbor. -/
def productExceptTwo {R : Type} [CommMonoid R] {N D : Nat}
    (z : VertexVectors N D R) (root neighbor : V N)
    (ι : V N → Fin D) : R :=
  ∏ v ∈ (Finset.univ.erase root).erase neighbor, z v (ι v)

/-- Split a full vertex product into the root, one neighbor, and all remaining
vertices. -/
theorem vertexProduct_eq_mul_productExceptTwo
    {R : Type} [CommMonoid R] {N D : Nat}
    (z : VertexVectors N D R) (root neighbor : V N)
    (hne : neighbor ≠ root) (ι : V N → Fin D) :
    (∏ v : V N, z v (ι v)) =
      z root (ι root) * z neighbor (ι neighbor) *
        productExceptTwo z root neighbor ι := by
  have hroot : root ∈ (Finset.univ : Finset (V N)) := Finset.mem_univ root
  have hneighbor : neighbor ∈ (Finset.univ.erase root : Finset (V N)) :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ neighbor⟩
  calc
    (∏ v : V N, z v (ι v)) =
        z root (ι root) *
          ∏ v ∈ (Finset.univ.erase root : Finset (V N)), z v (ι v) :=
      (Finset.mul_prod_erase Finset.univ (fun v => z v (ι v)) hroot).symm
    _ = z root (ι root) *
        (z neighbor (ι neighbor) *
          ∏ v ∈ (Finset.univ.erase root).erase neighbor, z v (ι v)) := by
      rw [Finset.mul_prod_erase (Finset.univ.erase root)
        (fun v => z v (ι v)) hneighbor]
    _ = z root (ι root) * z neighbor (ι neighbor) *
        productExceptTwo z root neighbor ι := by
      simp only [productExceptTwo, mul_assoc]

/-- The factor left after extracting an edge and its two endpoint vectors. -/
def residualMatchingFactor {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (z : VertexVectors N D R)
    (root neighbor : V N) (fuel : Nat) (L : List (V N))
    (ι : V N → Fin D) : R :=
  pmSumListAux W ι fuel L * productExceptTwo z root neighbor ι

/-- The residual matching factor is insensitive to the colors at the two
removed endpoints. -/
theorem residualMatchingFactor_invariant
    {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (z : VertexVectors N D R)
    (root neighbor : V N) (fuel : Nat) (L : List (V N))
    (hL : ∀ v ∈ L, v ≠ root ∧ v ≠ neighbor)
    (f κ : V N → Fin D)
    (hColor : ∀ y, y ≠ root → y ≠ neighbor → f y = κ y) :
    residualMatchingFactor W z root neighbor fuel L f =
      residualMatchingFactor W z root neighbor fuel L κ := by
  unfold residualMatchingFactor
  congr 1
  · apply pmSumListAux_coloring_congr W f κ fuel L
    intro v hv
    exact hColor v (hL v hv).1 (hL v hv).2
  · unfold productExceptTwo
    apply Finset.prod_congr rfl
    intro v hv
    have hvNeighbor : v ≠ neighbor := (Finset.mem_erase.mp hv).1
    have hvRoot : v ≠ root :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    rw [hColor v hvRoot hvNeighbor]

/-- A zero contracted edge makes the full color sum of the corresponding
matching term vanish. -/
theorem sum_edge_matching_term_eq_zero
    {R : Type} [CommSemiring R] {N D : Nat} [NeZero D]
    (W : WeightsN N D R) (z : VertexVectors N D R)
    (root neighbor : V N) (hne : neighbor ≠ root)
    (fuel : Nat) (L : List (V N))
    (hL : ∀ v ∈ L, v ≠ root ∧ v ≠ neighbor)
    (hEdge : incidentContraction W z root neighbor = 0) :
    (∑ ι : V N → Fin D,
      (z root (ι root) * W (mkEdge root neighbor (ι root) (ι neighbor)) *
        z neighbor (ι neighbor)) *
          residualMatchingFactor W z root neighbor fuel L ι) = 0 := by
  apply sum_mul_eq_zero_of_invariant_two root neighbor hne
    (fun a b => z root a * W (mkEdge root neighbor a b) * z neighbor b)
    (residualMatchingFactor W z root neighbor fuel L)
  · exact residualMatchingFactor_invariant W z root neighbor fuel L hL
  · exact hEdge

/-- If every edge from vertex `0` has zero product-vector contraction, then
the full perfect-matching contraction is zero.  This is the matching-side
identity needed by the full-column argument. -/
theorem productAmplitude_eq_zero_of_root_incident_zero
    {R : Type} [CommSemiring R] {n D : Nat} [NeZero D]
    (W : WeightsN (n + 2) D R) (z : VertexVectors (n + 2) D R)
    (hEdge : ∀ u : V (n + 2), u ≠ 0 → incidentContraction W z 0 u = 0) :
    productAmplitude W z = 0 := by
  let us : List (V (n + 2)) := (vertices (n + 1)).map Fin.succ
  have hVertices : vertices (n + 2) = (0 : V (n + 2)) :: us := by
    rfl
  have husLength : us.length = n + 1 := by
    simp [us, vertices_length]
  have husNodup : us.Nodup := by
    exact (vertices_nodup (n + 1)).map (Fin.succ_injective (n + 1))
  unfold productAmplitude pmSumN pmSumList
  rw [hVertices]
  rw [show ((0 : V (n + 2)) :: us).length = n + 2 by simp [husLength]]
  change (∑ ι : V (n + 2) → Fin D,
    (us.map (fun u =>
      W (mkEdge 0 u (ι 0) (ι u)) *
        pmSumListAux W ι n (us.erase u))).sum *
          ∏ v : V (n + 2), z v (ι v)) = 0
  have hDistribute : ∀ ι : V (n + 2) → Fin D,
      (us.map (fun u =>
        W (mkEdge 0 u (ι 0) (ι u)) *
          pmSumListAux W ι n (us.erase u))).sum *
            (∏ v : V (n + 2), z v (ι v)) =
        (us.map (fun u =>
          (W (mkEdge 0 u (ι 0) (ι u)) *
            pmSumListAux W ι n (us.erase u)) *
              ∏ v : V (n + 2), z v (ι v))).sum := by
    intro ι
    exact (List.sum_map_mul_right us
      (fun u => W (mkEdge 0 u (ι 0) (ι u)) *
        pmSumListAux W ι n (us.erase u))
      (∏ v : V (n + 2), z v (ι v))).symm
  simp_rw [hDistribute]
  rw [sum_list_map_sum_comm]
  apply List.sum_eq_zero
  intro term hterm
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hterm
  obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp (show u ∈ us from hu)
  let neighbor : V (n + 2) := Fin.succ q
  have hne : neighbor ≠ 0 := Fin.succ_ne_zero q
  have hL : ∀ v ∈ us.erase neighbor, v ≠ 0 ∧ v ≠ neighbor := by
    intro v hv
    have hvErase := husNodup.mem_erase_iff.mp hv
    constructor
    · obtain ⟨r, _hr, hvr⟩ := List.mem_map.mp hvErase.2
      subst v
      exact Fin.succ_ne_zero r
    · exact hvErase.1
  calc
    (∑ ι : V (n + 2) → Fin D,
      (W (mkEdge 0 neighbor (ι 0) (ι neighbor)) *
        pmSumListAux W ι n (us.erase neighbor)) *
          ∏ v : V (n + 2), z v (ι v)) =
        ∑ ι : V (n + 2) → Fin D,
          (z 0 (ι 0) * W (mkEdge 0 neighbor (ι 0) (ι neighbor)) *
            z neighbor (ι neighbor)) *
              residualMatchingFactor W z 0 neighbor n (us.erase neighbor) ι := by
                apply Finset.sum_congr rfl
                intro ι _
                rw [vertexProduct_eq_mul_productExceptTwo z 0 neighbor hne ι]
                unfold residualMatchingFactor
                ring
    _ = 0 := by
      exact sum_edge_matching_term_eq_zero W z 0 neighbor hne n
        (us.erase neighbor) hL (hEdge neighbor hne)

end QuantumCR

/- ## Section: `QuantumCR.FullColumn` -/

/-
# Full-column infrastructure

This module states the coefficient-level full-column property and connects the
two contraction identities.  The remaining research step is the polynomial
product-vector construction that forces a full column.
-/

open scoped BigOperators
open MonochromaticQuantumGraph

namespace QuantumCR

/-- At vertex `0`, the neighbor-side `output` column on edge `(0, neighbor)`
is nonzero and every other neighbor-side column is zero. -/
def FullColumnAtZero {K : Type} [Zero K] {N D : Nat} [NeZero N]
    (W : WeightsN N D K) (output : Fin D) (neighbor : V N) : Prop :=
  (∃ rootColor : Fin D,
      W (mkEdge 0 neighbor rootColor output) ≠ 0) ∧
    ∀ rootColor other : Fin D, other ≠ output →
      W (mkEdge 0 neighbor rootColor other) = 0

/-- Contract a neighbor-side column against a vector at the root. -/
def contractedColumn {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (rootVector : Fin D → R)
    (root neighbor : V N) (neighborColor : Fin D) : R :=
  ∑ rootColor : Fin D,
    rootVector rootColor * W (mkEdge root neighbor rootColor neighborColor)

/-- Edge contraction is the sum of contracted columns paired with the vector
at the neighboring vertex. -/
theorem incidentContraction_eq_sum_contractedColumn
    {R : Type} [CommSemiring R] {N D : Nat}
    (W : WeightsN N D R) (z : VertexVectors N D R)
    (root neighbor : V N) :
    incidentContraction W z root neighbor =
      ∑ neighborColor : Fin D,
        contractedColumn W (z root) root neighbor neighborColor *
          z neighbor neighborColor := by
  unfold incidentContraction contractedColumn
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Combining the equation-system contraction with the matching expansion:
if every edge incident to root `0` contracts to zero, then the GHZ
contraction is zero. -/
theorem ghzAmplitude_eq_zero_of_root_incident_zero
    {R : Type} [CommSemiring R] {n D : Nat} [NeZero D]
    (W : WeightsN (n + 2) D R) (hW : EqSystemN (n + 2) D W)
    (z : VertexVectors (n + 2) D R)
    (hEdge : ∀ u : V (n + 2), u ≠ 0 → incidentContraction W z 0 u = 0) :
    ghzAmplitude z = 0 := by
  rw [← productAmplitude_eq_ghz_of_eqSystem W hW z (0 : V (n + 2))]
  exact productAmplitude_eq_zero_of_root_incident_zero W z hEdge

end QuantumCR

/- ## Section: `QuantumCR.PolynomialKernel` -/

/-
# Polynomial moment columns and local kernel vectors

The root vector is `(1, X, X², ...)`.  Every neighbor-side column then becomes
a polynomial.  Any two columns have an explicit division-free kernel vector.
-/

open scoped BigOperators Polynomial
open MonochromaticQuantumGraph

namespace QuantumCR

/-- Lift coefficient weights to constant polynomials. -/
noncomputable def polynomialWeights {K : Type} [CommSemiring K] {N D : Nat}
    (W : WeightsN N D K) : WeightsN N D K[X] :=
  mapWeights Polynomial.C W

/-- Generic moment vector at the root. -/
noncomputable def rootMoment {K : Type} [CommSemiring K] {D : Nat}
    (color : Fin D) : K[X] :=
  Polynomial.X ^ color.val

/-- A neighbor-side column after contraction against the generic root moment. -/
noncomputable def momentColumn {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor : Fin D) : K[X] :=
  ∑ rootColor : Fin D,
    rootMoment rootColor *
      Polynomial.C (W (mkEdge 0 neighbor rootColor neighborColor))

/-- The coefficient of the generic moment column at a color degree is the
corresponding original edge weight. -/
theorem momentColumn_coeff
    {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor rootColor : Fin D) :
    (momentColumn W neighbor neighborColor).coeff rootColor.val =
      W (mkEdge 0 neighbor rootColor neighborColor) := by
  classical
  simp [momentColumn, rootMoment]
  rw [Finset.sum_eq_single rootColor]
  · simp
  · intro color _ hne
    have hval : color.val ≠ rootColor.val := by
      intro h
      exact hne (Fin.ext h)
    simp [Ne.symm hval]
  · simp

/-- A nonzero original coefficient gives a nonzero generic moment column. -/
theorem momentColumn_ne_zero_of_weight_ne_zero
    {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor rootColor : Fin D)
    (hWeight : W (mkEdge 0 neighbor rootColor neighborColor) ≠ 0) :
    momentColumn W neighbor neighborColor ≠ 0 := by
  intro hColumn
  have hCoeff := congrArg (fun p : K[X] => p.coeff rootColor.val) hColumn
  change (momentColumn W neighbor neighborColor).coeff rootColor.val = 0 at hCoeff
  rw [momentColumn_coeff] at hCoeff
  exact hWeight hCoeff

/-- Every nonzero generic moment column has a nonzero original coefficient. -/
theorem exists_weight_ne_zero_of_momentColumn_ne_zero
    {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor : Fin D)
    (hColumn : momentColumn W neighbor neighborColor ≠ 0) :
    ∃ rootColor : Fin D,
      W (mkEdge 0 neighbor rootColor neighborColor) ≠ 0 := by
  by_contra h
  apply hColumn
  simp only [momentColumn]
  apply Finset.sum_eq_zero
  intro rootColor _
  have hZero : W (mkEdge 0 neighbor rootColor neighborColor) = 0 :=
    not_ne_iff.mp (not_exists.mp h rootColor)
  rw [hZero, map_zero, mul_zero]

/-- A zero generic moment column means that all its original coefficients
vanish. -/
theorem weight_eq_zero_of_momentColumn_eq_zero
    {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor rootColor : Fin D)
    (hColumn : momentColumn W neighbor neighborColor = 0) :
    W (mkEdge 0 neighbor rootColor neighborColor) = 0 := by
  have hCoeff := congrArg (fun p : K[X] => p.coeff rootColor.val) hColumn
  simpa only [momentColumn_coeff, Polynomial.coeff_zero] using hCoeff

@[simp]
theorem contractedColumn_polynomialWeights_rootMoment
    {K : Type} [CommSemiring K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (neighborColor : Fin D) :
    contractedColumn (polynomialWeights W) rootMoment 0 neighbor neighborColor =
      momentColumn W neighbor neighborColor := by
  rfl

/-- Division-free kernel vector supported on two chosen neighbor-side
columns. -/
noncomputable def twoColumnKernel {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (a b : Fin D) (color : Fin D) : K[X] :=
  if color = a then momentColumn W neighbor b
  else if color = b then -momentColumn W neighbor a
  else 0

/-- The two-column vector lies in the kernel of the contracted edge. -/
theorem momentColumn_dot_twoColumnKernel_eq_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (a b : Fin D) (hba : b ≠ a) :
    (∑ color : Fin D,
      momentColumn W neighbor color *
        twoColumnKernel W neighbor a b color) = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ a]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨b, hba⟩]
  simp [twoColumnKernel, hba, mul_comm]
  apply Finset.sum_eq_zero
  intro color _
  have hca : color.1.1 ≠ a := color.1.2
  have hcb : color.1.1 ≠ b := by
    intro h
    apply color.2
    apply Subtype.ext
    exact h
  simp [hca, hcb]

/-- A vertex-vector family whose root is the generic moment and whose chosen
neighbor carries the two-column kernel has zero contraction on that edge. -/
theorem incidentContraction_twoColumnKernel_eq_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (a b : Fin D) (hba : b ≠ a)
    (z : VertexVectors (n + 2) D K[X])
    (hRoot : z 0 = rootMoment)
    (hNeighbor : z neighbor = twoColumnKernel W neighbor a b) :
    incidentContraction (polynomialWeights W) z 0 neighbor = 0 := by
  rw [incidentContraction_eq_sum_contractedColumn]
  rw [hRoot, hNeighbor]
  simp_rw [contractedColumn_polynomialWeights_rootMoment]
  exact momentColumn_dot_twoColumnKernel_eq_zero W neighbor a b hba

/-- Pairing a generic moment column with its standard coordinate vector
recovers that column. -/
theorem incidentContraction_coordinateVector_eq_momentColumn
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (neighbor : V (n + 2))
    (a : Fin D) (z : VertexVectors (n + 2) D K[X])
    (hRoot : z 0 = rootMoment)
    (hNeighbor : z neighbor = coordinateVector a) :
    incidentContraction (polynomialWeights W) z 0 neighbor =
      momentColumn W neighbor a := by
  rw [incidentContraction_eq_sum_contractedColumn]
  rw [hRoot, hNeighbor]
  simp_rw [contractedColumn_polynomialWeights_rootMoment]
  classical
  simp [coordinateVector]

end QuantumCR

/- ## Section: `QuantumCR.VaryingFullColumn` -/

/-
# Varying-column full-column argument

The generic root moment permits an independent external-column choice at
every neighboring vertex.  A nonconstant choice leaves exactly one nonzero
GHZ coordinate, contradicting the equation system.  This is the central
solver-free step in the full-column theorem.
-/

open scoped BigOperators Polynomial
open MonochromaticQuantumGraph

namespace QuantumCR

/-- If a selected column is nonzero but is not a full column, some different
column on the same edge is also nonzero after generic contraction. -/
theorem exists_external_momentColumn_ne_zero_of_not_fullColumn
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (neighbor : V (n + 2))
    (hColumn : momentColumn W neighbor a ≠ 0)
    (hNotFull : ¬ FullColumnAtZero W a neighbor) :
    ∃ b : Fin D, b ≠ a ∧ momentColumn W neighbor b ≠ 0 := by
  obtain ⟨rootColor, hWeight⟩ :=
    exists_weight_ne_zero_of_momentColumn_ne_zero W neighbor a hColumn
  have hNotZeroOutside :
      ¬ ∀ rootColor other : Fin D, other ≠ a →
        W (mkEdge 0 neighbor rootColor other) = 0 := by
    intro hZeroOutside
    exact hNotFull ⟨⟨rootColor, hWeight⟩, hZeroOutside⟩
  push Not at hNotZeroOutside
  obtain ⟨otherRoot, b, hba, hOtherWeight⟩ := hNotZeroOutside
  exact ⟨b, hba,
    momentColumn_ne_zero_of_weight_ne_zero W neighbor b otherRoot hOtherWeight⟩

/-- In the preliminary contradiction, a zero `a` column receives the standard
coordinate vector and a nonzero `a` column receives a chosen two-column
kernel. -/
noncomputable def preliminaryKernelVectors
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D) : VertexVectors (n + 2) D K[X] := by
  classical
  exact fun v =>
    if v = 0 then rootMoment
    else if momentColumn W v a = 0 then coordinateVector a
    else twoColumnKernel W v a (b v)

@[simp]
theorem preliminaryKernelVectors_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D) :
    preliminaryKernelVectors W a b 0 = rootMoment := by
  simp [preliminaryKernelVectors]

/-- Under failure of the full-column property, the target moment column is
nonzero on every edge incident to vertex zero. -/
theorem momentColumn_ne_zero_of_no_fullColumn
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (a : Fin D)
    (hNoFull : ∀ v : V (n + 2), v ≠ 0 → ¬ FullColumnAtZero W a v) :
    ∀ v : V (n + 2), v ≠ 0 → momentColumn W v a ≠ 0 := by
  intro u hu hUa
  have hExistsChoice : ∀ v : V (n + 2),
      ∃ b : Fin D, v ≠ 0 → momentColumn W v a ≠ 0 →
        b ≠ a ∧ momentColumn W v b ≠ 0 := by
    intro v
    by_cases hv : v = 0
    · exact ⟨a, fun h => (h hv).elim⟩
    · by_cases hA : momentColumn W v a = 0
      · exact ⟨a, fun _ h => (h hA).elim⟩
      · obtain ⟨b, hba, hb⟩ :=
          exists_external_momentColumn_ne_zero_of_not_fullColumn
            W a v hA (hNoFull v hv)
        exact ⟨b, fun _ _ => ⟨hba, hb⟩⟩
  choose b hb using hExistsChoice
  let z : VertexVectors (n + 2) D K[X] := preliminaryKernelVectors W a b
  have hEdge : ∀ w : V (n + 2), w ≠ 0 →
      incidentContraction (polynomialWeights W) z 0 w = 0 := by
    intro w hw
    by_cases hA : momentColumn W w a = 0
    · rw [incidentContraction_coordinateVector_eq_momentColumn W w a z]
      · exact hA
      · exact preliminaryKernelVectors_zero W a b
      · simp [z, preliminaryKernelVectors, hw, hA]
    · apply incidentContraction_twoColumnKernel_eq_zero W w a (b w)
        (hb w hw hA).1 z
      · exact preliminaryKernelVectors_zero W a b
      · simp [z, preliminaryKernelVectors, hw, hA]
  have hMapped : EqSystemN (n + 2) D (polynomialWeights W) :=
    QuantumCR.EqSystemN.mapWeights hW Polynomial.C
  have : NeZero D := ⟨by
    intro hD
    subst D
    exact Fin.elim0 a⟩
  have hZero : ghzAmplitude z = 0 :=
    ghzAmplitude_eq_zero_of_root_incident_zero (polynomialWeights W) hMapped z hEdge
  have hSingle : ghzAmplitude z = ∏ w : V (n + 2), z w a := by
    unfold ghzAmplitude
    rw [Fintype.sum_eq_single a]
    intro c hca
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp [z, preliminaryKernelVectors, hu, hUa, coordinateVector, hca]
  have hNonzero : (∏ w : V (n + 2), z w a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    by_cases hw : w = 0
    · subst w
      simp [z, rootMoment]
    · by_cases hA : momentColumn W w a = 0
      · simp [z, preliminaryKernelVectors, hw, hA, coordinateVector]
      · simpa [z, preliminaryKernelVectors, hw, hA, twoColumnKernel,
          (hb w hw hA).1] using (hb w hw hA).2
  exact hNonzero (hSingle ▸ hZero)

/-- Root moment at vertex zero and a two-column kernel at every other vertex. -/
noncomputable def varyingKernelVectors
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D) : VertexVectors (n + 2) D K[X] :=
  fun v => if v = 0 then rootMoment else twoColumnKernel W v a (b v)

@[simp]
theorem varyingKernelVectors_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D) :
    varyingKernelVectors W a b 0 = rootMoment := by
  simp [varyingKernelVectors]

@[simp]
theorem varyingKernelVectors_ne_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D) (v : V (n + 2)) (hv : v ≠ 0) :
    varyingKernelVectors W a b v = twoColumnKernel W v a (b v) := by
  simp [varyingKernelVectors, hv]

/-- The selected vector has a nonzero `a` coordinate at every vertex when
all selected external moment columns are nonzero. -/
theorem varyingKernelVectors_apply_a_ne_zero
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D)
    (_hba : ∀ v, v ≠ 0 → b v ≠ a)
    (hColumn : ∀ v, v ≠ 0 → momentColumn W v (b v) ≠ 0) :
    ∀ v : V (n + 2), varyingKernelVectors W a b v a ≠ 0 := by
  intro v
  by_cases hv : v = 0
  · subst v
    simp [varyingKernelVectors, rootMoment]
  · simp [varyingKernelVectors, hv, twoColumnKernel, hColumn v hv]

/-- If two neighboring vertices select different external columns, then at
every coordinate other than `a` one of those two vertex vectors vanishes. -/
theorem varyingKernelVectors_other_coordinate_zero
    {K : Type} [CommRing K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (a : Fin D)
    (b : V (n + 2) → Fin D)
    {u v : V (n + 2)} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : b u ≠ b v) {c : Fin D} (hca : c ≠ a) :
    ∃ w : V (n + 2), varyingKernelVectors W a b w c = 0 := by
  by_cases hcu : c = b u
  · refine ⟨v, ?_⟩
    have hcv : c ≠ b v := by simpa [hcu] using huv
    simp [varyingKernelVectors, hv, twoColumnKernel, hca, hcv]
  · refine ⟨u, ?_⟩
    simp [varyingKernelVectors, hu, twoColumnKernel, hca, hcu]

/-- A nonconstant choice of nonzero external columns is incompatible with an
equation-system solution. -/
theorem externalColumnChoice_constant
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (a : Fin D) (b : V (n + 2) → Fin D)
    (hba : ∀ v, v ≠ 0 → b v ≠ a)
    (hColumn : ∀ v, v ≠ 0 → momentColumn W v (b v) ≠ 0) :
    ∀ u v : V (n + 2), u ≠ 0 → v ≠ 0 → b u = b v := by
  intro u v hu hv
  by_contra huv
  let z : VertexVectors (n + 2) D K[X] := varyingKernelVectors W a b
  have hEdge : ∀ w : V (n + 2), w ≠ 0 →
      incidentContraction (polynomialWeights W) z 0 w = 0 := by
    intro w hw
    apply incidentContraction_twoColumnKernel_eq_zero W w a (b w) (hba w hw) z
    · exact varyingKernelVectors_zero W a b
    · exact varyingKernelVectors_ne_zero W a b w hw
  have hMapped : EqSystemN (n + 2) D (polynomialWeights W) :=
    QuantumCR.EqSystemN.mapWeights hW Polynomial.C
  have : NeZero D := ⟨by
    intro hD
    subst D
    exact Fin.elim0 a⟩
  have hZero : ghzAmplitude z = 0 :=
    ghzAmplitude_eq_zero_of_root_incident_zero (polynomialWeights W) hMapped z hEdge
  have hSingle : ghzAmplitude z = ∏ w : V (n + 2), z w a := by
    unfold ghzAmplitude
    rw [Fintype.sum_eq_single a]
    intro c hca
    obtain ⟨w, hw⟩ :=
      varyingKernelVectors_other_coordinate_zero W a b hu hv huv hca
    exact Finset.prod_eq_zero (Finset.mem_univ w) hw
  have hNonzero : (∏ w : V (n + 2), z w a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    exact varyingKernelVectors_apply_a_ne_zero W a b hba hColumn w
  exact hNonzero (hSingle ▸ hZero)

/-- Root moment at vertex zero and the same coordinate vector at every
neighboring vertex. -/
noncomputable def singleColorKernelVectors
    {K : Type} [CommRing K] {n D : Nat} (q : Fin D) :
    VertexVectors (n + 2) D K[X] :=
  fun v => if v = 0 then rootMoment else coordinateVector q

/-- For every color, at least one edge incident to vertex zero has a nonzero
generic moment column. -/
theorem exists_incident_momentColumn_ne_zero
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (q : Fin D) :
    ∃ v : V (n + 2), v ≠ 0 ∧ momentColumn W v q ≠ 0 := by
  by_contra hExists
  push Not at hExists
  let z : VertexVectors (n + 2) D K[X] := singleColorKernelVectors q
  have hEdge : ∀ v : V (n + 2), v ≠ 0 →
      incidentContraction (polynomialWeights W) z 0 v = 0 := by
    intro v hv
    rw [incidentContraction_coordinateVector_eq_momentColumn W v q z]
    · exact hExists v hv
    · simp [z, singleColorKernelVectors]
    · simp [z, singleColorKernelVectors, hv]
  have hMapped : EqSystemN (n + 2) D (polynomialWeights W) :=
    QuantumCR.EqSystemN.mapWeights hW Polynomial.C
  have : NeZero D := ⟨by
    intro hD
    subst D
    exact Fin.elim0 q⟩
  have hZero : ghzAmplitude z = 0 :=
    ghzAmplitude_eq_zero_of_root_incident_zero (polynomialWeights W) hMapped z hEdge
  have hOne : (1 : V (n + 2)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num at hval
  have hSingle : ghzAmplitude z = ∏ v : V (n + 2), z v q := by
    unfold ghzAmplitude
    rw [Fintype.sum_eq_single q]
    intro c hcq
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : V (n + 2)))
    simp [z, singleColorKernelVectors, hOne, coordinateVector, hcq]
  have hNonzero : (∏ v : V (n + 2), z v q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    by_cases hv : v = 0
    · subst v
      simp [z, singleColorKernelVectors, rootMoment]
    · simp [z, singleColorKernelVectors, hv, coordinateVector]
  exact hNonzero (hSingle ▸ hZero)

/-- Solver-free full-column theorem at vertex zero over every integral
domain.  The graph has `n+2` vertices; `2 ≤ n` supplies at least three
neighbors of the root, while `3 ≤ D` supplies a third color. -/
theorem exists_fullColumnAtZero_domain
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (hn : 2 ≤ n) (hD : 3 ≤ D)
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (a : Fin D) :
    ∃ v : V (n + 2), v ≠ 0 ∧ FullColumnAtZero W a v := by
  by_contra hFull
  push Not at hFull
  have hA : ∀ v : V (n + 2), v ≠ 0 → momentColumn W v a ≠ 0 :=
    momentColumn_ne_zero_of_no_fullColumn W hW a hFull
  have hExistsChoice : ∀ v : V (n + 2),
      ∃ b : Fin D, v ≠ 0 → b ≠ a ∧ momentColumn W v b ≠ 0 := by
    intro v
    by_cases hv : v = 0
    · exact ⟨a, fun h => (h hv).elim⟩
    · obtain ⟨b, hba, hb⟩ :=
        exists_external_momentColumn_ne_zero_of_not_fullColumn
          W a v (hA v hv) (hFull v hv)
      exact ⟨b, fun _ => ⟨hba, hb⟩⟩
  choose b hb using hExistsChoice
  have hba : ∀ v : V (n + 2), v ≠ 0 → b v ≠ a :=
    fun v hv => (hb v hv).1
  have hbNonzero : ∀ v : V (n + 2), v ≠ 0 →
      momentColumn W v (b v) ≠ 0 :=
    fun v hv => (hb v hv).2
  have hConstant := externalColumnChoice_constant W hW a b hba hbNonzero
  have hOne : (1 : V (n + 2)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num at hval
  obtain ⟨q, hqa, hqb⟩ :=
    Fin.exists_ne_and_ne_of_two_lt a (b (1 : V (n + 2))) (by omega : 2 < D)
  have hQZero : ∀ v : V (n + 2), v ≠ 0 → momentColumn W v q = 0 := by
    intro v hv
    by_contra hQ
    obtain ⟨t, htZero, htv⟩ :=
      Fin.exists_ne_and_ne_of_two_lt (0 : V (n + 2)) v (by omega : 2 < n + 2)
    let b' : V (n + 2) → Fin D := fun w => if w = v then q else b w
    have hb'a : ∀ w : V (n + 2), w ≠ 0 → b' w ≠ a := by
      intro w hw
      by_cases hwv : w = v
      · simp [b', hwv, hqa]
      · simp [b', hwv, hba w hw]
    have hb'Nonzero : ∀ w : V (n + 2), w ≠ 0 →
        momentColumn W w (b' w) ≠ 0 := by
      intro w hw
      by_cases hwv : w = v
      · subst w
        simpa [b'] using hQ
      · simpa [b', hwv] using hbNonzero w hw
    have hEqual :=
      externalColumnChoice_constant W hW a b' hb'a hb'Nonzero v t hv htZero
    have hqt : q = b t := by
      simpa [b', htv] using hEqual
    have htOne : b t = b (1 : V (n + 2)) :=
      hConstant t 1 htZero hOne
    exact hqb (hqt.trans htOne)
  obtain ⟨v, hv, hqNonzero⟩ := exists_incident_momentColumn_ne_zero W hW q
  exact hqNonzero (hQZero v hv)

end QuantumCR

/- ## Section: `QuantumCR.FullColumnRelabel` -/

/-
# Full columns at an arbitrary root

The raw Formal Conjectures weight type is canonically oriented.  Thus the
root-independent statement uses `orderedWeight`, and follows by swapping the
chosen root with vertex zero.
-/

open MonochromaticQuantumGraph

namespace QuantumCR

/-- From `root`, the `output` column on the edge to `neighbor` is nonzero and
all other neighbor-side columns vanish. -/
def FullColumnAt {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root : V N) (output : Fin D)
    (neighbor : V N) : Prop :=
  (∃ rootColor : Fin D,
      orderedWeight W root neighbor rootColor output ≠ 0) ∧
    ∀ rootColor other : Fin D, other ≠ output →
      orderedWeight W root neighbor rootColor other = 0

/-- Solver-free full-column theorem at every root over every integral domain. -/
theorem exists_fullColumnAt_domain
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (hn : 2 ≤ n) (hD : 3 ≤ D)
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (root : V (n + 2)) (output : Fin D) :
    ∃ neighbor : V (n + 2), neighbor ≠ root ∧
      FullColumnAt W root output neighbor := by
  let σ : Equiv.Perm (V (n + 2)) := Equiv.swap 0 root
  have hσ0 : σ 0 = root := by simp [σ]
  have hRelabeled : EqSystemN (n + 2) D (relabelWeights W σ) :=
    relabelWeights_eqSystem W σ hW
  obtain ⟨v, hv, hFull⟩ :=
    exists_fullColumnAtZero_domain hn hD (relabelWeights W σ) hRelabeled output
  have h0v : (0 : V (n + 2)) < v := Fin.pos_iff_ne_zero.mpr hv
  refine ⟨σ v, ?_, ?_⟩
  · intro hEqual
    apply hv
    apply σ.injective
    rw [hσ0]
    exact hEqual
  · constructor
    · obtain ⟨rootColor, hNonzero⟩ := hFull.1
      refine ⟨rootColor, ?_⟩
      rw [← hσ0, ← orderedWeight_relabelWeights]
      rw [orderedWeight_of_lt _ _ _ _ _ h0v]
      exact hNonzero
    · intro rootColor other hOther
      rw [← hσ0, ← orderedWeight_relabelWeights]
      rw [orderedWeight_of_lt _ _ _ _ _ h0v]
      exact hFull.2 rootColor other hOther

end QuantumCR

/- ## Section: `QuantumCR.BoundaryAnchors` -/

/-
# Anchor bijections in the boundary case

When `D = N - 1`, full columns identify the colors bijectively with the
neighbors of every root vertex.
-/

open MonochromaticQuantumGraph

namespace QuantumCR

def FullColumnsAt {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root : V N) : Prop :=
  ∀ output : Fin D, ∃ neighbor : V N, neighbor ≠ root ∧
    FullColumnAt W root output neighbor

theorem fullColumnsAt_of_eqSystem_domain
    {K : Type} [CommRing K] [IsDomain K] {n D : Nat}
    (hn : 2 ≤ n) (hD : 3 ≤ D)
    (W : WeightsN (n + 2) D K) (hW : EqSystemN (n + 2) D W)
    (root : V (n + 2)) : FullColumnsAt W root := by
  intro output
  exact exists_fullColumnAt_domain hn hD W hW root output

/-- Two full columns at the same oriented edge have the same output color. -/
theorem fullColumnAt_outputs_eq_of_same_neighbor
    {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root neighbor : V N)
    (a b : Fin D) (ha : FullColumnAt W root a neighbor)
    (hb : FullColumnAt W root b neighbor) : a = b := by
  by_contra hab
  obtain ⟨rootColor, hNonzero⟩ := ha.1
  exact hNonzero (hb.2 rootColor a hab)

noncomputable def fullColumnNeighborAt
    {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root : V N)
    (hFull : FullColumnsAt W root) (output : Fin D) :
    {neighbor : V N // neighbor ≠ root} :=
  ⟨Classical.choose (hFull output),
    (Classical.choose_spec (hFull output)).1⟩

theorem fullColumnNeighborAt_spec
    {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root : V N)
    (hFull : FullColumnsAt W root) (output : Fin D) :
    FullColumnAt W root output (fullColumnNeighborAt W root hFull output).1 :=
  (Classical.choose_spec (hFull output)).2

theorem fullColumnNeighborAt_injective
    {K : Type} [Zero K] {N D : Nat}
    (W : WeightsN N D K) (root : V N)
    (hFull : FullColumnsAt W root) :
    Function.Injective (fullColumnNeighborAt W root hFull) := by
  intro a b hab
  have hNeighbor :
      (fullColumnNeighborAt W root hFull a).1 =
        (fullColumnNeighborAt W root hFull b).1 := congrArg Subtype.val hab
  apply fullColumnAt_outputs_eq_of_same_neighbor W root
    (fullColumnNeighborAt W root hFull a).1 a b
  · exact fullColumnNeighborAt_spec W root hFull a
  · rw [hNeighbor]
    exact fullColumnNeighborAt_spec W root hFull b

/-- At the boundary `D = N-1`, every neighbor is the unique anchor of a
color. -/
theorem fullColumnNeighborAt_surjective
    {K : Type} [Zero K] {n D : Nat}
    (hBoundary : D = n + 1)
    (W : WeightsN (n + 2) D K) (root : V (n + 2))
    (hFull : FullColumnsAt W root) :
    Function.Surjective (fullColumnNeighborAt W root hFull) := by
  have hCard :
      Fintype.card (Fin D) =
        Fintype.card {neighbor : V (n + 2) // neighbor ≠ root} := by
    simp only [Fintype.card_fin,
      Fintype.card_congr (finSuccAboveEquiv root).symm]
    exact hBoundary
  exact ((Fintype.bijective_iff_injective_and_card
    (fullColumnNeighborAt W root hFull)).2
      ⟨fullColumnNeighborAt_injective W root hFull, hCard⟩).2

/-- The output color attached to an oriented adjacent pair in the boundary
case. -/
noncomputable def boundaryOutputColor
    {K : Type} [Zero K] {n D : Nat}
    (hBoundary : D = n + 1)
    (W : WeightsN (n + 2) D K) (root neighbor : V (n + 2))
    (hne : neighbor ≠ root) (hFull : FullColumnsAt W root) : Fin D :=
  Classical.choose (fullColumnNeighborAt_surjective hBoundary W root hFull
    ⟨neighbor, hne⟩)

theorem boundaryOutputColor_neighbor
    {K : Type} [Zero K] {n D : Nat}
    (hBoundary : D = n + 1)
    (W : WeightsN (n + 2) D K) (root neighbor : V (n + 2))
    (hne : neighbor ≠ root) (hFull : FullColumnsAt W root) :
    (fullColumnNeighborAt W root hFull
      (boundaryOutputColor hBoundary W root neighbor hne hFull)).1 = neighbor := by
  exact congrArg Subtype.val (Classical.choose_spec
    (fullColumnNeighborAt_surjective hBoundary W root hFull
      ⟨neighbor, hne⟩))

theorem boundaryOutputColor_fullColumn
    {K : Type} [Zero K] {n D : Nat}
    (hBoundary : D = n + 1)
    (W : WeightsN (n + 2) D K) (root neighbor : V (n + 2))
    (hne : neighbor ≠ root) (hFull : FullColumnsAt W root) :
    FullColumnAt W root
      (boundaryOutputColor hBoundary W root neighbor hne hFull) neighbor := by
  let output := boundaryOutputColor hBoundary W root neighbor hne hFull
  have hSpec : FullColumnAt W root output
      (fullColumnNeighborAt W root hFull output).1 :=
    fullColumnNeighborAt_spec W root hFull output
  have hNeighbor :
      (fullColumnNeighborAt W root hFull output).1 = neighbor := by
    exact boundaryOutputColor_neighbor hBoundary W root neighbor hne hFull
  rw [hNeighbor] at hSpec
  exact hSpec

end QuantumCR

/- ## Section: `PPL007General.MatchingSum` -/

/-
# Matching sums over vertex subsets

The Formal Conjectures matching sum is a recursion along an ordered list.  With
the symmetrized weights `orderedWeights W` the recursion is independent of the
list order, so it defines a matching sum `msum W ι S` over any finite vertex
set `S`.  This file provides the expansion at an arbitrary vertex, the
forced-partner factorization, coloring congruence, and a nonvanishing criterion
for a coloring whose support is a single perfect matching.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General

variable {K : Type} [CommRing K] {N D : Nat}

/-- Canonical increasing list of the vertices in `S`. -/
def vlist (S : Finset (V N)) : List (V N) :=
  (vertices N).filter (fun v => decide (v ∈ S))

theorem vlist_nodup (S : Finset (V N)) : (vlist S).Nodup :=
  (vertices_nodup N).filter _

theorem mem_vlist {S : Finset (V N)} {v : V N} : v ∈ vlist S ↔ v ∈ S := by
  simp [vlist]

theorem vlist_toFinset (S : Finset (V N)) : (vlist S).toFinset = S := by
  ext v
  simp [mem_vlist]

/-- Matching sum over the vertex set `S`, computed with symmetrized weights. -/
def msum (W : WeightsN N D K) (ι : V N → Fin D) (S : Finset (V N)) : K :=
  pmSumList (orderedWeights W) ι (vlist S)

theorem pmSumList_orderedWeights_eq_msum (W : WeightsN N D K) (ι : V N → Fin D)
    (L : List (V N)) (hL : L.Nodup) (S : Finset (V N)) (hS : L.toFinset = S) :
    pmSumList (orderedWeights W) ι L = msum W ι S := by
  unfold msum
  apply pmSumList_perm (orderedWeights W) ι (orderedWeights_sym W ι) L (vlist S) hL
  apply List.perm_of_nodup_nodup_toFinset_eq hL (vlist_nodup S)
  rw [hS, vlist_toFinset]

/-- The Formal Conjectures matching sum is the matching sum over all vertices. -/
theorem pmSumN_eq_msum (W : WeightsN N D K) (ι : V N → Fin D) :
    pmSumN N D W ι = msum W ι Finset.univ := by
  unfold pmSumN
  rw [← pmSumList_orderedWeights_eq_of_pairwise_lt W ι (vertices N)
    (vertices_pairwise_lt N)]
  apply pmSumList_orderedWeights_eq_msum W ι _ (vertices_nodup N)
  ext v
  simp

@[simp]
theorem msum_empty (W : WeightsN N D K) (ι : V N → Fin D) :
    msum W ι ∅ = 1 := by
  simp [msum, vlist, pmSumList, pmSumListAux]

/-- Only the colors on `S` matter. -/
theorem msum_congr (W : WeightsN N D K) {ι κ : V N → Fin D} (S : Finset (V N))
    (h : ∀ v ∈ S, ι v = κ v) : msum W ι S = msum W κ S := by
  unfold msum pmSumList
  exact pmSumListAux_coloring_congr (orderedWeights W) ι κ _ _
    (fun v hv => h v (mem_vlist.mp hv))

/-- Expansion of the matching sum at an arbitrary vertex `w ∈ S`. -/
theorem msum_expand (W : WeightsN N D K) (ι : V N → Fin D) (S : Finset (V N))
    {w : V N} (hw : w ∈ S) :
    msum W ι S = ∑ x ∈ S.erase w,
      orderedWeight W w x (ι w) (ι x) * msum W ι ((S.erase w).erase x) := by
  classical
  have hL : (w :: vlist (S.erase w)).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, vlist_nodup _⟩
    simp [mem_vlist]
  have hT : (w :: vlist (S.erase w)).toFinset = S := by
    ext v
    by_cases hv : v = w
    · subst hv
      simp [hw]
    · simp [mem_vlist, hv]
  rw [← pmSumList_orderedWeights_eq_msum W ι _ hL S hT, pmSumList_cons]
  rw [← List.sum_toFinset _ (vlist_nodup (S.erase w)), vlist_toFinset]
  apply Finset.sum_congr rfl
  intro x hx
  have hxL : x ∈ vlist (S.erase w) := mem_vlist.mpr hx
  change orderedWeight W w x (ι w) (ι x) *
      pmSumList (orderedWeights W) ι ((vlist (S.erase w)).erase x) = _
  congr 1
  apply pmSumList_orderedWeights_eq_msum W ι _ ((vlist_nodup _).erase x)
  ext v
  rw [List.mem_toFinset, (vlist_nodup (S.erase w)).mem_erase_iff, mem_vlist]
  simp [Finset.mem_erase]

/-- If every edge from `w` inside `S` except the one to `x` vanishes, the
matching sum factors through the edge `wx`. -/
theorem msum_forced (W : WeightsN N D K) (ι : V N → Fin D) (S : Finset (V N))
    {w x : V N} (hw : w ∈ S) (hx : x ∈ S) (hxw : x ≠ w)
    (h0 : ∀ y ∈ S, y ≠ w → y ≠ x → orderedWeight W w y (ι w) (ι y) = 0) :
    msum W ι S = orderedWeight W w x (ι w) (ι x) *
      msum W ι ((S.erase w).erase x) := by
  rw [msum_expand W ι S hw]
  apply Finset.sum_eq_single_of_mem x (Finset.mem_erase.mpr ⟨hxw, hx⟩)
  intro y hy hyx
  rw [h0 y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy) hyx, zero_mul]

/-- If every edge from `w` inside `S` vanishes, the matching sum vanishes. -/
theorem msum_eq_zero_of_isolated (W : WeightsN N D K) (ι : V N → Fin D)
    (S : Finset (V N)) {w : V N} (hw : w ∈ S)
    (h0 : ∀ y ∈ S, y ≠ w → orderedWeight W w y (ι w) (ι y) = 0) :
    msum W ι S = 0 := by
  rw [msum_expand W ι S hw]
  apply Finset.sum_eq_zero
  intro y hy
  rw [h0 y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy), zero_mul]

/-- A coloring whose only supported edges form one perfect matching `m` has a
nonzero matching sum on every `m`-closed vertex set. -/
theorem msum_ne_zero_of_involution [IsDomain K] (W : WeightsN N D K)
    (ι : V N → Fin D) (m : V N → V N)
    (hm : ∀ v, m (m v) = v) (hfix : ∀ v, m v ≠ v)
    (hne : ∀ v, orderedWeight W v (m v) (ι v) (ι (m v)) ≠ 0)
    (hzero : ∀ v y, y ≠ v → y ≠ m v → orderedWeight W v y (ι v) (ι y) = 0) :
    ∀ S : Finset (V N), (∀ v ∈ S, m v ∈ S) → msum W ι S ≠ 0 := by
  classical
  intro S
  induction hS : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hclosed
    rcases S.eq_empty_or_nonempty with hempty | ⟨w, hw⟩
    · subst hempty
      simp
    · have hmw : m w ∈ S := hclosed w hw
      rw [msum_forced W ι S hw hmw (hfix w)
        (fun y _ hyw hym => hzero w y hyw hym)]
      apply mul_ne_zero (hne w)
      have hmwS : m w ∈ S.erase w := Finset.mem_erase.mpr ⟨hfix w, hmw⟩
      have hcard : ((S.erase w).erase (m w)).card < n := by
        rw [Finset.card_erase_of_mem hmwS, Finset.card_erase_of_mem hw]
        have := Finset.card_pos.mpr ⟨w, hw⟩
        omega
      apply ih _ hcard _ rfl
      intro v hv
      have hvw : v ≠ w := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
      have hvmw : v ≠ m w := Finset.ne_of_mem_erase hv
      have hvS : v ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hclosed v hvS⟩⟩
      · intro h
        apply hvw
        rw [← hm v, h, hm w]
      · intro h
        apply hvmw
        rw [← h, hm v]

end PPL007General

/- ## Section: `QuantumTenEight.Selection` -/

/-
# Priority-selected full columns and the exception map at `(N, D) = (10, 8)`

For every root `u` and color `c` the full-column theorem supplies neighbors
whose edge matrix from `u` has only the column `c`.  Among them we select, in
this priority order, a neighbor whose column is a multiple of `e_c`, then one
with a nonzero diagonal entry, then any.  The selected neighbors `anchor u c`
are distinct, so exactly one neighbor `exc u` of `u` is not selected.
-/


open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General

set_option linter.unusedSectionVars false

/-- Internal dimension witness for even `N = n + 2 ≥ 10` (so `n ≥ 8` is even).
Not exposed in any public theorem statement. -/
class ValidDim (n : Nat) : Prop where
  ge_eight : 8 ≤ n
  even : Even n

instance (n : Nat) [ValidDim n] : NeZero n :=
  ⟨by have := ValidDim.ge_eight (n := n); omega⟩

variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]


theorem ow_swap (W : WeightsN (n + 2) n K) (u v : Fin (n + 2)) (i j : Fin n) :
    orderedWeight W u v i j = orderedWeight W v u j i :=
  orderedWeight_swap W u v i j

@[simp]
theorem ow_self (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (i j : Fin n) :
    orderedWeight W u u i j = 0 := by
  simp [orderedWeight]

/-- `x` is a full-column neighbor of `u` for the output color `c`. -/
def Cand (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (c : Fin n) (x : Fin (n + 2)) : Prop :=
  x ≠ u ∧ FullColumnAt W u c x

/-- A vector is supported at the single coordinate `c`. -/
def PureAt (a : Fin n → K) (c : Fin n) : Prop :=
  ∀ i, i ≠ c → a i = 0

/-- Priority score of a candidate: pure column `0`, nonzero diagonal `1`,
otherwise `2`. -/
noncomputable def score (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (c : Fin n)
    (x : Fin (n + 2)) : ℕ := by
  classical
  exact if PureAt (fun i => orderedWeight W u x i c) c then 0
    else if orderedWeight W u x c c ≠ 0 then 1 else 2

theorem score_eq_zero_iff (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (c : Fin n) (x : Fin (n + 2)) :
    score W u c x = 0 ↔ PureAt (fun i => orderedWeight W u x i c) c := by
  classical
  unfold score
  by_cases hp : PureAt (fun i => orderedWeight W u x i c) c
  · simp [hp]
  · by_cases hd : orderedWeight W u x c c ≠ 0 <;> simp [hp, hd]

theorem score_le_one_iff (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (c : Fin n) (x : Fin (n + 2)) :
    score W u c x ≤ 1 ↔
      PureAt (fun i => orderedWeight W u x i c) c ∨ orderedWeight W u x c c ≠ 0 := by
  classical
  unfold score
  by_cases hp : PureAt (fun i => orderedWeight W u x i c) c
  · simp [hp]
  · by_cases hd : orderedWeight W u x c c ≠ 0 <;> simp [hp, hd]

section Selection

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

theorem exists_cand (u : Fin (n + 2)) (c : Fin n) : ∃ x, Cand W u c x := by
  obtain ⟨x, hx, hfull⟩ :=
    exists_fullColumnAt_domain (K := K) (n := n) (D := n)
      (by have := ValidDim.ge_eight (n := n); omega)
      (by have := ValidDim.ge_eight (n := n); omega)
      W hW u c
  exact ⟨x, hx, hfull⟩

theorem exists_best (u : Fin (n + 2)) (c : Fin n) :
    ∃ x, Cand W u c x ∧ ∀ y, Cand W u c y →
      score W u c x * (n + 2) + x.val ≤ score W u c y * (n + 2) + y.val := by
  classical
  obtain ⟨x0, hx0⟩ := exists_cand W hW u c
  have hne : (Finset.univ.filter (Cand W u c)).Nonempty := ⟨x0, by simpa using hx0⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image _ (fun y => score W u c y * (n + 2) + y.val) hne
  refine ⟨x, (Finset.mem_filter.mp hx).2, fun y hy => hmin y ?_⟩
  simpa using hy

/-- The priority-selected full-column neighbor of `u` for the color `c`. -/
noncomputable def anchor (u : Fin (n + 2)) (c : Fin n) : Fin (n + 2) :=
  Classical.choose (exists_best W hW u c)

theorem anchor_cand (u : Fin (n + 2)) (c : Fin n) : Cand W u c (anchor W hW u c) :=
  (Classical.choose_spec (exists_best W hW u c)).1

theorem anchor_ne (u : Fin (n + 2)) (c : Fin n) : anchor W hW u c ≠ u :=
  (anchor_cand W hW u c).1

theorem anchor_full (u : Fin (n + 2)) (c : Fin n) : FullColumnAt W u c (anchor W hW u c) :=
  (anchor_cand W hW u c).2

theorem anchor_score_le (u : Fin (n + 2)) (c : Fin n) (y : Fin (n + 2)) (hy : Cand W u c y) :
    score W u c (anchor W hW u c) ≤ score W u c y := by
  have h := (Classical.choose_spec (exists_best W hW u c)).2 y hy
  have h1 := (Classical.choose (exists_best W hW u c)).isLt
  have h2 := y.isLt
  show score W u c (Classical.choose (exists_best W hW u c)) ≤ score W u c y
  nlinarith

/-- The selected column vector (colors at `u`). -/
noncomputable def colA (u : Fin (n + 2)) (c : Fin n) : Fin n → K :=
  fun i => orderedWeight W u (anchor W hW u c) i c

theorem anchor_col_zero (u : Fin (n + 2)) (c i j : Fin n) (hj : j ≠ c) :
    orderedWeight W u (anchor W hW u c) i j = 0 :=
  (anchor_full W hW u c).2 i j hj

theorem colA_ne_zero (u : Fin (n + 2)) (c : Fin n) : ∃ i, colA W hW u c i ≠ 0 :=
  (anchor_full W hW u c).1

theorem anchor_injective (u : Fin (n + 2)) : Function.Injective (anchor W hW u) := by
  intro c d h
  apply fullColumnAt_outputs_eq_of_same_neighbor W u (anchor W hW u c) c d
    (anchor_full W hW u c)
  rw [h]
  exact anchor_full W hW u d

/-- Priority one: a pure candidate forces a pure selected column. -/
theorem colA_pure_of_pure_cand (u : Fin (n + 2)) (c : Fin n) (y : Fin (n + 2))
    (hy : Cand W u c y) (hpure : PureAt (fun i => orderedWeight W u y i c) c) :
    PureAt (colA W hW u c) c := by
  have h0 : score W u c y = 0 := (score_eq_zero_iff W u c y).mpr hpure
  have hle := anchor_score_le W hW u c y hy
  have hz : score W u c (anchor W hW u c) = 0 := by omega
  exact (score_eq_zero_iff W u c _).mp hz

theorem colA_self_ne_zero_of_pure (u : Fin (n + 2)) (c : Fin n)
    (hpure : PureAt (colA W hW u c) c) : colA W hW u c c ≠ 0 := by
  obtain ⟨i, hi⟩ := colA_ne_zero W hW u c
  by_cases hic : i = c
  · subst hic
    exact hi
  · exact absurd (hpure i hic) hi

/-- Priority two: a candidate with nonzero diagonal forces a nonzero
diagonal entry of the selected column. -/
theorem colA_diag_of_diag_cand (u : Fin (n + 2)) (c : Fin n) (y : Fin (n + 2))
    (hy : Cand W u c y) (hdiag : orderedWeight W u y c c ≠ 0) : colA W hW u c c ≠ 0 := by
  have h1 : score W u c y ≤ 1 := (score_le_one_iff W u c y).mpr (Or.inr hdiag)
  have hle := anchor_score_le W hW u c y hy
  have h2 : score W u c (anchor W hW u c) ≤ 1 := le_trans hle h1
  rcases (score_le_one_iff W u c _).mp h2 with hp | hd
  · exact colA_self_ne_zero_of_pure W hW u c hp
  · exact hd

theorem exists_exc (u : Fin (n + 2)) : ∃ x, x ≠ u ∧ ∀ c, anchor W hW u c ≠ x := by
  classical
  by_contra h
  push Not at h
  have hsub : Finset.univ.erase u ⊆ Finset.univ.image (anchor W hW u) := by
    intro x hx
    obtain ⟨c, hc⟩ := h x (Finset.ne_of_mem_erase hx)
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image (anchor W hW u)).card ≤ n := by
    calc (Finset.univ.image (anchor W hW u)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  rw [Finset.card_erase_of_mem (Finset.mem_univ u)] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- The unique non-selected neighbor of `u`. -/
noncomputable def exc (u : Fin (n + 2)) : Fin (n + 2) :=
  Classical.choose (exists_exc W hW u)

theorem exc_ne (u : Fin (n + 2)) : exc W hW u ≠ u :=
  (Classical.choose_spec (exists_exc W hW u)).1

theorem anchor_ne_exc (u : Fin (n + 2)) (c : Fin n) : anchor W hW u c ≠ exc W hW u :=
  (Classical.choose_spec (exists_exc W hW u)).2 c

/-- Every neighbor other than the exception is selected. -/
theorem exists_anchor_eq (u x : Fin (n + 2)) (hxu : x ≠ u) (hxe : x ≠ exc W hW u) :
    ∃ c, anchor W hW u c = x := by
  classical
  by_contra h
  push Not at h
  set T := Finset.univ.image (anchor W hW u) with hT
  have hTcard : T.card = n := by
    rw [hT, Finset.card_image_of_injective _ (anchor_injective W hW u)]
    simp
  have hexcT : exc W hW u ∉ T := by
    rw [hT]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact anchor_ne_exc W hW u
  have hxT : x ∉ insert (exc W hW u) T := by
    rw [Finset.mem_insert, hT]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    exact ⟨hxe, h⟩
  have hsub : insert x (insert (exc W hW u) T) ⊆ Finset.univ.erase u := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, hT] at hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | rfl | ⟨c, rfl⟩
    · exact Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨exc_ne W hW u, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨anchor_ne W hW u c, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxT, Finset.card_insert_of_notMem hexcT, hTcard,
    Finset.card_erase_of_mem (Finset.mem_univ u)] at hcard
  simp at hcard

/-- `u` and its exception form a mutual exception pair. -/
def Paired (u : Fin (n + 2)) : Prop :=
  exc W hW (exc W hW u) = u

theorem exists_rr (u : Fin (n + 2)) (hu : ¬ Paired W hW u) :
    ∃ r, anchor W hW (exc W hW u) r = u :=
  exists_anchor_eq W hW (exc W hW u) u (exc_ne W hW u).symm (Ne.symm hu)

open Classical in
/-- For an unpaired root, the color with which its exception selects it. -/
noncomputable def rr (u : Fin (n + 2)) : Fin n :=
  if h : ∃ r, anchor W hW (exc W hW u) r = u then Classical.choose h else 0

theorem anchor_exc_rr (u : Fin (n + 2)) (hu : ¬ Paired W hW u) :
    anchor W hW (exc W hW u) (rr W hW u) = u := by
  have h := exists_rr W hW u hu
  unfold rr
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- If `x` selects `u` with the color `d`, the edge matrix from `u` has only
the row `d`. -/
theorem ow_row_zero_of_anchor_eq {x u : Fin (n + 2)} {d : Fin n}
    (h : anchor W hW x d = u) (i j : Fin n) (hi : i ≠ d) : orderedWeight W u x i j = 0 := by
  rw [ow_swap]
  have := anchor_col_zero W hW x d j i hi
  rw [h] at this
  exact this

theorem exists_ow_row_ne_zero_of_anchor_eq {x u : Fin (n + 2)} {d : Fin n}
    (h : anchor W hW x d = u) : ∃ j, orderedWeight W u x d j ≠ 0 := by
  obtain ⟨j, hj⟩ := colA_ne_zero W hW x d
  refine ⟨j, ?_⟩
  rw [ow_swap]
  unfold colA at hj
  rw [h] at hj
  exact hj

theorem paired_exc (u : Fin (n + 2)) (hu : Paired W hW u) : Paired W hW (exc W hW u) := by
  unfold Paired at *
  rw [hu]

/-- An anchor of `u` which does not select `u` back has `u` as exception. -/
theorem exc_eq_of_not_selects (x u : Fin (n + 2)) (hxu : x ≠ u)
    (h : ∀ d, anchor W hW x d ≠ u) : exc W hW x = u := by
  by_contra hne
  obtain ⟨d, hd⟩ := exists_anchor_eq W hW x u (Ne.symm hxu) (Ne.symm hne)
  exact h d hd

end Selection

end PPL007General

/- ## Section: `PPL007General.Slice` -/

/-
# Slice equations

Color every vertex other than a root `u` and its exception `v = exc u` by one
color `c`.  Only the edge `uv` and the selected edge of color `c` at `u` can
carry weight, which gives the slice equation

`M i j * s_c + A_c i * R_c j = [i = c ∧ j = c]`

with `M` the exceptional edge matrix and `A_c` the selected column.  For a
mutual exception pair the residual `R_c` factors once more through the
selected edge of color `c` at `v`.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

/-- Constant coloring. -/
def cst (c : Fin n) : Fin (n + 2) → Fin n := fun _ => c

@[simp]
theorem cst_apply (c : Fin n) (v : Fin (n + 2)) : cst c v = c := rfl

theorem exists_third (a b : Fin (n + 2)) : ∃ z : Fin (n + 2), z ≠ a ∧ z ≠ b := by
  have hge := ValidDim.ge_eight (n := n)
  have h1 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin (n + 2))).erase a) (a := b)
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at h1
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase a).erase b).card)
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
  exact ⟨z, hz.2, hz.1⟩

section Slice

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

theorem msum_univ_of_const (ι : Fin (n + 2) → Fin n) (h : ∀ a b, ι a = ι b) :
    msum W ι Finset.univ = 1 := by
  rw [← pmSumN_eq_msum, hW ι, if_pos ((allEqual_iff_forall_eq ι).mpr h)]

theorem msum_univ_of_not_const (ι : Fin (n + 2) → Fin n) (h : ¬ ∀ a b, ι a = ι b) :
    msum W ι Finset.univ = 0 := by
  rw [← pmSumN_eq_msum, hW ι, if_neg (fun h' => h ((allEqual_iff_forall_eq ι).mp h'))]

theorem msum_univ_ne_zero_const (ι : Fin (n + 2) → Fin n) (h : msum W ι Finset.univ ≠ 0) :
    ∀ a b, ι a = ι b := by
  by_contra hc
  exact h (msum_univ_of_not_const W hW ι hc)

/-- Residual of the exception term in the slice. -/
noncomputable def sS (u : Fin (n + 2)) (c : Fin n) : K :=
  msum W (cst c) ((Finset.univ.erase u).erase (exc W hW u))

/-- Residual of the selected term in the slice. -/
noncomputable def sR (u : Fin (n + 2)) (c j : Fin n) : K :=
  msum W (Function.update (cst c) (exc W hW u) j)
    ((Finset.univ.erase u).erase (anchor W hW u c))

/-- The slice equation at an arbitrary root. -/
theorem slice_eq (u : Fin (n + 2)) (c i j : Fin n) :
    orderedWeight W u (exc W hW u) i j * sS W hW u c + colA W hW u c i * sR W hW u c j =
      if i = c ∧ j = c then 1 else 0 := by
  classical
  set v := exc W hW u with hv
  set x := anchor W hW u c with hx
  have hvu : v ≠ u := exc_ne W hW u
  have hxu : x ≠ u := anchor_ne W hW u c
  have hxv : x ≠ v := anchor_ne_exc W hW u c
  set ι : Fin (n + 2) → Fin n := Function.update (Function.update (cst c) u i) v j with hι
  have hιu : ι u = i := by simp [ι, hvu.symm]
  have hιv : ι v = j := by simp [ι]
  have hιo : ∀ z, z ≠ u → z ≠ v → ι z = c := by
    intro z hzu hzv
    simp [ι, hzu, hzv]
  have hval : msum W ι Finset.univ = if i = c ∧ j = c then 1 else 0 := by
    by_cases hij : i = c ∧ j = c
    · rw [if_pos hij]
      apply msum_univ_of_const W hW
      have hall : ∀ z, ι z = c := by
        intro z
        by_cases hzu : z = u
        · rw [hzu, hιu, hij.1]
        · by_cases hzv : z = v
          · rw [hzv, hιv, hij.2]
          · exact hιo z hzu hzv
      intro a b
      rw [hall a, hall b]
    · rw [if_neg hij]
      apply msum_univ_of_not_const W hW
      intro hall
      apply hij
      obtain ⟨z, hzu, hzv⟩ := exists_third u v
      exact ⟨by rw [← hιu, hall u z, hιo z hzu hzv],
        by rw [← hιv, hall v z, hιo z hzu hzv]⟩
  rw [← hval, msum_expand W ι Finset.univ (Finset.mem_univ u)]
  rw [Finset.sum_eq_add_of_mem v x (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩)
    (Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩) (Ne.symm hxv)]
  · congr 1
    · rw [hιu, hιv]
      congr 1
      unfold sS
      rw [← hv]
      apply msum_congr
      intro z hz
      have hzv : z ≠ v := Finset.ne_of_mem_erase hz
      have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
      rw [hιo z hzu hzv]
      rfl
    · rw [hιu, hιo x hxu hxv]
      congr 1
      unfold sR
      rw [← hv, ← hx]
      apply msum_congr
      intro z hz
      have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
      by_cases hzv : z = v
      · rw [hzv, hιv]
        simp
      · rw [hιo z hzu hzv]
        simp [hzv]
  · intro z hz hzvx
    have hzu : z ≠ u := Finset.ne_of_mem_erase hz
    obtain ⟨d, hd⟩ := exists_anchor_eq W hW u z hzu hzvx.1
    have hdc : d ≠ c := by
      intro hdc
      apply hzvx.2
      rw [← hd, hdc]
    rw [hιu, hιo z hzu hzvx.1, ← hd, anchor_col_zero W hW u d i c (Ne.symm hdc), zero_mul]

/-- Residual of a mutual exception pair. -/
noncomputable def tT (u : Fin (n + 2)) (c : Fin n) : K :=
  msum W (cst c) ((((Finset.univ.erase u).erase (anchor W hW u c)).erase (exc W hW u)).erase
    (anchor W hW (exc W hW u) c))

/-- For a mutual exception pair the slice residual factors through the
selected edge of color `c` at the partner. -/
theorem sR_of_paired (u : Fin (n + 2)) (hu : Paired W hW u) (c j : Fin n) :
    sR W hW u c j = if anchor W hW (exc W hW u) c = anchor W hW u c then 0 else
      colA W hW (exc W hW u) c j * tT W hW u c := by
  classical
  set v := exc W hW u with hv
  set x := anchor W hW u c with hx
  set y := anchor W hW v c with hy
  have hexcv : exc W hW v = u := hu
  have hvu : v ≠ u := exc_ne W hW u
  have hxu : x ≠ u := anchor_ne W hW u c
  have hxv : x ≠ v := anchor_ne_exc W hW u c
  have hyv : y ≠ v := anchor_ne W hW v c
  have hyu : y ≠ u := by
    have := anchor_ne_exc W hW v c
    rw [hexcv] at this
    exact this
  set ι : Fin (n + 2) → Fin n := Function.update (cst c) v j with hι
  have hιv : ι v = j := by simp [ι]
  have hιo : ∀ z, z ≠ v → ι z = c := by
    intro z hzv
    simp [ι, hzv]
  set S := (Finset.univ.erase u).erase x with hS
  have hvS : v ∈ S := Finset.mem_erase.mpr ⟨Ne.symm hxv, Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩⟩
  have hzero : ∀ z ∈ S, z ≠ v → z ≠ y → orderedWeight W v z (ι v) (ι z) = 0 := by
    intro z hz hzv hzy
    have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
    obtain ⟨d, hd⟩ := exists_anchor_eq W hW v z hzv (by rw [hexcv]; exact hzu)
    have hdc : d ≠ c := by
      intro hdc
      apply hzy
      rw [← hd, hdc]
    rw [hιv, hιo z hzv, ← hd]
    exact anchor_col_zero W hW v d j c (Ne.symm hdc)
  unfold sR
  change msum W ι S = _
  by_cases hyx : y = x
  · rw [if_pos hyx]
    apply msum_eq_zero_of_isolated W ι S hvS
    intro z hz hzv
    by_cases hzy : z = y
    · exfalso
      rw [hzy, hyx] at hz
      exact Finset.ne_of_mem_erase hz rfl
    · exact hzero z hz hzv hzy
  · rw [if_neg hyx]
    have hyS : y ∈ S := Finset.mem_erase.mpr ⟨hyx, Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩
    rw [msum_forced W ι S hvS hyS hyv (fun z hz hzv hzy => hzero z hz hzv hzy)]
    rw [hιv, hιo y hyv]
    congr 1
    unfold tT
    apply msum_congr
    intro z hz
    have hzv : z ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
    rw [hιo z hzv]
    rfl

/-- The pair equation for a mutual exception pair. -/
theorem pair_eq (u : Fin (n + 2)) (hu : Paired W hW u) (c i j : Fin n) :
    orderedWeight W u (exc W hW u) i j * sS W hW u c +
        colA W hW u c i * ((if anchor W hW (exc W hW u) c = anchor W hW u c then 0 else
          tT W hW u c) * colA W hW (exc W hW u) c j) =
      if i = c ∧ j = c then 1 else 0 := by
  rw [← slice_eq W hW u c i j, sR_of_paired W hW u hu c j]
  split_ifs <;> ring

end Slice

end PPL007General

/- ## Section: `PPL007General.NonPaired` -/

/-
# Local structure at a root whose exception is not mutual

Let `u` be a root with `exc (exc u) ≠ u`.  The exception `v = exc u` selects
`u` with the color `r = rr u`, so the exceptional matrix has only the row `r`.
The slice equation then shows:

* no selected column at `u` is a single off-diagonal coordinate;
* an impure selected column has support exactly `{c, r}` and the exceptional
  matrix is a multiple of the matrix unit `(r, c)`;
* every color other than `r` is isolated at `u`: its row has exactly one
  nonzero entry, the diagonal entry on the selected edge.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

/-- The color `c` is isolated at `u` with partner `x`. -/
def Iso (W : WeightsN (n + 2) n K) (u : Fin (n + 2)) (c : Fin n) (x : Fin (n + 2)) : Prop :=
  orderedWeight W u x c c ≠ 0 ∧
    ∀ y, y ≠ u → ∀ j, orderedWeight W u y c j ≠ 0 → y = x ∧ j = c

section NonPaired

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

/-- If the slice residual vanishes identically, the exceptional edge is a pure
full column and the selected column is pure. -/
theorem colA_pure_of_sR_zero (u : Fin (n + 2)) (c : Fin n)
    (hF : ∀ j, sR W hW u c j = 0) : PureAt (colA W hW u c) c := by
  have hs : ∀ i j, orderedWeight W u (exc W hW u) i j * sS W hW u c =
      if i = c ∧ j = c then 1 else 0 := by
    intro i j
    have := slice_eq W hW u c i j
    rw [hF j, mul_zero, add_zero] at this
    exact this
  have hcc := hs c c
  rw [if_pos ⟨rfl, rfl⟩] at hcc
  have hs0 : sS W hW u c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcc
    exact zero_ne_one hcc
  have hM : ∀ i j, ¬ (i = c ∧ j = c) → orderedWeight W u (exc W hW u) i j = 0 := by
    intro i j hij
    have := hs i j
    rw [if_neg hij] at this
    exact (mul_eq_zero.mp this).resolve_right hs0
  apply colA_pure_of_pure_cand W hW u c (exc W hW u)
  · refine ⟨exc_ne W hW u, ⟨c, ?_⟩, ?_⟩
    · intro h
      rw [h, zero_mul] at hcc
      exact zero_ne_one hcc
    · intro i j hj
      exact hM i j (fun h => hj h.2)
  · intro i hi
    exact hM i c (fun h => hi h.1)

/-- The exceptional matrix of an unpaired root has only the row `rr u`. -/
theorem exc_row_zero (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (i j : Fin n)
    (hi : i ≠ rr W hW u) : orderedWeight W u (exc W hW u) i j = 0 :=
  ow_row_zero_of_anchor_eq W hW (anchor_exc_rr W hW u hu) i j hi

/-- An unpaired root has no selected column supported at a single
off-diagonal coordinate. -/
theorem np_no_single (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c i₀ : Fin n)
    (hi₀ : i₀ ≠ c) (hsingle : ∀ i, i ≠ i₀ → colA W hW u c i = 0) : False := by
  have hA0 : colA W hW u c i₀ ≠ 0 := by
    obtain ⟨i, hi⟩ := colA_ne_zero W hW u c
    by_cases h : i = i₀
    · rw [← h]
      exact hi
    · exact absurd (hsingle i h) hi
  have hAc : colA W hW u c c = 0 := hsingle c (Ne.symm hi₀)
  have hcc := slice_eq W hW u c c c
  rw [hAc, zero_mul, add_zero, if_pos ⟨rfl, rfl⟩] at hcc
  have hMcc : orderedWeight W u (exc W hW u) c c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcc
    exact zero_ne_one hcc
  have hcr : c = rr W hW u := by
    by_contra h
    exact hMcc (exc_row_zero W hW u hu c c h)
  have hF : ∀ j, sR W hW u c j = 0 := by
    intro j
    have := slice_eq W hW u c i₀ j
    rw [exc_row_zero W hW u hu i₀ j (by rw [← hcr]; exact hi₀), zero_mul, zero_add,
      if_neg (fun h => hi₀ h.1)] at this
    exact (mul_eq_zero.mp this).resolve_left hA0
  exact hA0 (colA_pure_of_sR_zero W hW u c hF i₀ hi₀)

/-- Structure of an impure selected column at an unpaired root. -/
theorem np_impure (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c : Fin n)
    (himp : ¬ PureAt (colA W hW u c) c) :
    rr W hW u ≠ c ∧ colA W hW u c c ≠ 0 ∧ colA W hW u c (rr W hW u) ≠ 0 ∧
      (∀ i, i ≠ c → i ≠ rr W hW u → colA W hW u c i = 0) ∧
      orderedWeight W u (exc W hW u) (rr W hW u) c ≠ 0 ∧
      (∀ i j, ¬ (i = rr W hW u ∧ j = c) → orderedWeight W u (exc W hW u) i j = 0) := by
  set r := rr W hW u with hr
  set A := colA W hW u c with hA
  set s := sS W hW u c with hs
  set M := fun i j => orderedWeight W u (exc W hW u) i j with hM
  have hsl : ∀ i j, M i j * s + A i * sR W hW u c j = if i = c ∧ j = c then 1 else 0 :=
    fun i j => slice_eq W hW u c i j
  have hMrow : ∀ i j, i ≠ r → M i j = 0 := fun i j hi => exc_row_zero W hW u hu i j hi
  obtain ⟨i₀, hi₀c, hi₀⟩ : ∃ i₀, i₀ ≠ c ∧ A i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact himp (fun i hi => h i hi)
  have hFne : ¬ ∀ j, sR W hW u c j = 0 := fun hF => himp (colA_pure_of_sR_zero W hW u c hF)
  have hrc : r ≠ c := by
    intro hrc
    apply hFne
    intro j
    have := hsl i₀ j
    rw [hMrow i₀ j (by rw [hrc]; exact hi₀c), zero_mul, zero_add,
      if_neg (fun h => hi₀c h.1)] at this
    exact (mul_eq_zero.mp this).resolve_left hi₀
  -- row c
  have hrowc : ∀ j, A c * sR W hW u c j = if j = c then 1 else 0 := by
    intro j
    have := hsl c j
    rw [hMrow c j (Ne.symm hrc), zero_mul, zero_add] at this
    rw [this]
    by_cases hj : j = c <;> simp [hj]
  have hAcF : A c * sR W hW u c c = 1 := by
    rw [hrowc c, if_pos rfl]
  have hAc : A c ≠ 0 := left_ne_zero_of_mul_eq_one hAcF
  have hFc : sR W hW u c c ≠ 0 := right_ne_zero_of_mul_eq_one hAcF
  have hFoff : ∀ j, j ≠ c → sR W hW u c j = 0 := by
    intro j hj
    have := hrowc j
    rw [if_neg hj] at this
    exact (mul_eq_zero.mp this).resolve_left hAc
  -- other rows
  have hAoff : ∀ i, i ≠ c → i ≠ r → A i = 0 := by
    intro i hic hir
    have := hsl i c
    rw [hMrow i c hir, zero_mul, zero_add, if_neg (fun h => hic h.1)] at this
    exact (mul_eq_zero.mp this).resolve_right hFc
  have hi₀r : i₀ = r := by
    by_contra h
    exact hi₀ (hAoff i₀ hi₀c h)
  have hAr : A r ≠ 0 := by rw [← hi₀r]; exact hi₀
  -- row r
  have hrowr : ∀ j, M r j * s + A r * sR W hW u c j = 0 := by
    intro j
    have := hsl r j
    rw [if_neg (fun h => hrc h.1)] at this
    exact this
  have hMrc : M r c * s ≠ 0 := by
    have := hrowr c
    intro h
    rw [h, zero_add] at this
    exact mul_ne_zero hAr hFc this
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hMrc
  refine ⟨hrc, hAc, hAr, hAoff, left_ne_zero_of_mul hMrc, ?_⟩
  intro i j hij
  by_cases hir : i = r
  · subst hir
    have hjc : j ≠ c := fun h => hij ⟨rfl, h⟩
    have := hrowr j
    rw [hFoff j hjc, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hs0
  · exact hMrow i j hir

/-- Every color other than `rr u` is isolated at an unpaired root `u`. -/
theorem np_iso (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c : Fin n) (hc : c ≠ rr W hW u) :
    Iso W u c (anchor W hW u c) := by
  constructor
  · by_cases hp : PureAt (colA W hW u c) c
    · exact colA_self_ne_zero_of_pure W hW u c hp
    · exact (np_impure W hW u hu c hp).2.1
  · intro y hyu j hy
    by_cases hye : y = exc W hW u
    · exfalso
      rw [hye] at hy
      exact hy (exc_row_zero W hW u hu c j hc)
    · obtain ⟨d, hd⟩ := exists_anchor_eq W hW u y hyu hye
      have hjd : j = d := by
        by_contra hjd
        rw [← hd] at hy
        exact hy (anchor_col_zero W hW u d c j hjd)
      subst hjd
      have hcd : c = j := by
        by_contra hcd
        -- the column of color `j` at `u` is impure, with support `{j, rr u}`
        have hAc : colA W hW u j c ≠ 0 := by
          unfold colA
          rw [hd]
          exact hy
        have himp : ¬ PureAt (colA W hW u j) j := fun hp => hAc (hp c hcd)
        have := (np_impure W hW u hu j himp).2.2.2.1 c hcd hc
        exact hAc this
      subst hcd
      exact ⟨hd.symm, rfl⟩

/-- At most one impure selected column at an unpaired root. -/
theorem np_impure_unique (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c d : Fin n)
    (hc : ¬ PureAt (colA W hW u c) c) (hd : ¬ PureAt (colA W hW u d) d) : c = d := by
  have h1 := (np_impure W hW u hu c hc).2.2.2.2.1
  have h2 := (np_impure W hW u hu d hd).2.2.2.2.2
  by_contra hcd
  exact h1 (h2 _ c (fun h => hcd h.2))

end NonPaired

end PPL007General

/- ## Section: `PPL007General.PureDigraph` -/

/-
# A partial-injection digraph bound

Two injective maps `x, y` from a color set `S` into a vertex set `U` with
`x c ≠ y c` define a digraph with edges `x c → y c`.  If no edge has both an
incoming edge at its tail and an outgoing edge at its head, every component is
a path with at most two edges, so `3 |S| ≤ 2 |U|`.
-/

namespace PPL007General
variable {n : Nat} [ValidDim n]

theorem three_mul_card_le_of_chainFree {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (U : Finset α) (S : Finset ι) (x y : ι → α)
    (hx : ∀ c ∈ S, x c ∈ U) (hy : ∀ c ∈ S, y c ∈ U)
    (hxinj : ∀ c ∈ S, ∀ d ∈ S, x c = x d → c = d)
    (hyinj : ∀ c ∈ S, ∀ d ∈ S, y c = y d → c = d)
    (hchain : ∀ c ∈ S, ∀ d ∈ S, ∀ f ∈ S, y c = x d → x c = y f → False) :
    3 * S.card ≤ 2 * U.card := by
  -- Let `X = S.image x`, `Y = S.image y`.  Then `|X| = |Y| = |S|` and `X ∪ Y ⊆ U`, so
  -- `|U| ≥ |X ∪ Y| = 2 |S| - |X ∩ Y|`; it remains to show `2 |X ∩ Y| ≤ |S|`.
  have hXc : (S.image x).card = S.card :=
    Finset.card_image_of_injOn (fun c hc d hd h => hxinj c hc d hd h)
  have hYc : (S.image y).card = S.card :=
    Finset.card_image_of_injOn (fun c hc d hd h => hyinj c hc d hd h)
  have hUsub : S.image x ∪ S.image y ⊆ U := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      exact hx c hc
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      exact hy c hc
  have hU : (S.image x ∪ S.image y).card ≤ U.card := Finset.card_le_card hUsub
  have hui := Finset.card_union_add_card_inter (S.image x) (S.image y)
  -- Every point of `X ∩ Y` is the tail `x c` of a color `c` whose tail is a head ...
  have hT : (S.image x ∩ S.image y).card ≤
      (S.filter (fun c => ∃ f ∈ S, x c = y f)).card := by
    calc (S.image x ∩ S.image y).card
        ≤ ((S.filter (fun c => ∃ f ∈ S, x c = y f)).image x).card := by
          apply Finset.card_le_card
          intro a ha
          obtain ⟨haX, haY⟩ := Finset.mem_inter.1 ha
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 haX
          obtain ⟨f, hf, hfc⟩ := Finset.mem_image.1 haY
          exact Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hc, f, hf, hfc.symm⟩, rfl⟩
      _ ≤ (S.filter (fun c => ∃ f ∈ S, x c = y f)).card := Finset.card_image_le
  -- ... and the head `y c` of a color `c` whose head is a tail; by `hchain` such a color's
  -- tail is not a head.
  have hH : (S.image x ∩ S.image y).card ≤
      (S.filter (fun c => ¬ ∃ f ∈ S, x c = y f)).card := by
    calc (S.image x ∩ S.image y).card
        ≤ ((S.filter (fun c => ¬ ∃ f ∈ S, x c = y f)).image y).card := by
          apply Finset.card_le_card
          intro a ha
          obtain ⟨haX, haY⟩ := Finset.mem_inter.1 ha
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 haY
          obtain ⟨d, hd, hdc⟩ := Finset.mem_image.1 haX
          refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hc, ?_⟩, rfl⟩
          rintro ⟨f, hf, hcf⟩
          exact hchain c hc d hd f hf hdc.symm hcf
      _ ≤ (S.filter (fun c => ¬ ∃ f ∈ S, x c = y f)).card := Finset.card_image_le
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := S) (fun c => ∃ f ∈ S, x c = y f)
  omega

end PPL007General

/- ## Section: `PPL007General.IsoBound` -/

/-
# Common isolated colors of two roots

Let `S` be a set of colors isolated at two roots `u, v` with partners outside
`{u, v}`.  The monochromatic equations force the partners of a color to be
different, and a mixed coloring shows that no partner edge can be followed on
both sides by further partner edges.  The digraph bound then gives
`|S| ≤ 5` on ten vertices.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

theorem exists_not_mem_of_card_lt (T : Finset (Fin (n + 2))) (h : T.card < n + 2) :
    ∃ z, z ∉ T := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin (n + 2))) ⊆ T := fun z _ => hc z
  have := Finset.card_le_card hsub
  simp at this
  omega

theorem iso_ne (W : WeightsN (n + 2) n K) {u x : Fin (n + 2)} {c : Fin n} (h : Iso W u c x) :
    x ≠ u := by
  intro hxu
  apply h.1
  rw [hxu]
  simp [orderedWeight]

/-- Forced partner of an isolated color. -/
theorem msum_forced_iso (W : WeightsN (n + 2) n K) (ι : Fin (n + 2) → Fin n) (S : Finset (Fin (n + 2)))
    {u x : Fin (n + 2)} {c : Fin n} (hiso : Iso W u c x) (hu : u ∈ S) (hx : x ∈ S)
    (hιu : ι u = c) :
    msum W ι S = orderedWeight W u x c (ι x) * msum W ι ((S.erase u).erase x) := by
  rw [msum_forced W ι S hu hx (iso_ne W hiso), hιu]
  intro y _ hyu hyx
  by_contra hne
  rw [hιu] at hne
  exact hyx (hiso.2 y hyu (ι y) hne).1

theorem msum_zero_iso (W : WeightsN (n + 2) n K) (ι : Fin (n + 2) → Fin n) (S : Finset (Fin (n + 2)))
    {u x : Fin (n + 2)} {c : Fin n} (hiso : Iso W u c x) (hu : u ∈ S) (hx : x ∉ S)
    (hιu : ι u = c) : msum W ι S = 0 := by
  apply msum_eq_zero_of_isolated W ι S hu
  intro y hy hyu
  by_contra hne
  rw [hιu] at hne
  have := (hiso.2 y hyu (ι y) hne).1
  rw [this] at hy
  exact hx hy

section Iso

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

/-- Two isolated partners of the same color differ, and the residual of the
monochromatic equation is nonzero. -/
theorem iso_pair_mono (u v : Fin (n + 2)) (huv : u ≠ v) (c : Fin n) (x y : Fin (n + 2))
    (hx : Iso W u c x) (hy : Iso W v c y) (hxv : x ≠ v) (hyu : y ≠ u) :
    x ≠ y ∧ msum W (cst c) ((((Finset.univ.erase u).erase x).erase v).erase y) ≠ 0 := by
  have hxu := iso_ne W hx
  have hyv := iso_ne W hy
  have hmono := msum_univ_of_const W hW (cst c) (fun _ _ => rfl)
  rw [msum_forced_iso W (cst c) Finset.univ hx (Finset.mem_univ u) (Finset.mem_univ x) rfl]
    at hmono
  have hvT : v ∈ (Finset.univ.erase u).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxv, Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩⟩
  have hxy : x ≠ y := by
    intro hxy
    have hyT : y ∉ (Finset.univ.erase u).erase x := by
      rw [← hxy]
      exact fun h => Finset.ne_of_mem_erase h rfl
    rw [msum_zero_iso W (cst c) _ hy hvT hyT rfl, mul_zero] at hmono
    exact zero_ne_one hmono
  refine ⟨hxy, ?_⟩
  have hyT : y ∈ (Finset.univ.erase u).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩
  rw [msum_forced_iso W (cst c) _ hy hvT hyT rfl] at hmono
  intro h
  rw [h, mul_zero, mul_zero] at hmono
  exact zero_ne_one hmono

/-- Common isolated colors with external partners number at most five. -/
theorem iso_three_mul_card_le (u v : Fin (n + 2)) (huv : u ≠ v) (S : Finset (Fin n))
    (x y : Fin n → Fin (n + 2))
    (hxI : ∀ c ∈ S, Iso W u c (x c)) (hyI : ∀ c ∈ S, Iso W v c (y c))
    (hxv : ∀ c ∈ S, x c ≠ v) (hyu : ∀ c ∈ S, y c ≠ u)
    (hxinj : ∀ c ∈ S, ∀ d ∈ S, x c = x d → c = d)
    (hyinj : ∀ c ∈ S, ∀ d ∈ S, y c = y d → c = d) : 3 * S.card ≤ 2 * n := by
  classical
  set U := (Finset.univ.erase u).erase v with hU
  have hUcard : U.card = n := by
    rw [hU, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u)]
    simp
  have hxU : ∀ c ∈ S, x c ∈ U := fun c hc =>
    Finset.mem_erase.mpr ⟨hxv c hc, Finset.mem_erase.mpr ⟨iso_ne W (hxI c hc), Finset.mem_univ _⟩⟩
  have hyU : ∀ c ∈ S, y c ∈ U := fun c hc =>
    Finset.mem_erase.mpr ⟨iso_ne W (hyI c hc), Finset.mem_erase.mpr ⟨hyu c hc, Finset.mem_univ _⟩⟩
  have hxy : ∀ c ∈ S, x c ≠ y c := fun c hc =>
    (iso_pair_mono W hW u v huv c (x c) (y c) (hxI c hc) (hyI c hc) (hxv c hc) (hyu c hc)).1
  have hchain : ∀ c ∈ S, ∀ d ∈ S, ∀ f ∈ S, y c = x d → x c = y f → False := by
    intro c hc d hd f hf hycd hxcf
    have hxcu : x c ≠ u := iso_ne W (hxI c hc)
    have hycv : y c ≠ v := iso_ne W (hyI c hc)
    have hxyc := hxy c hc
    have hR := (iso_pair_mono W hW u v huv c (x c) (y c) (hxI c hc) (hyI c hc)
      (hxv c hc) (hyu c hc)).2
    have hdc : d ≠ c := by
      intro hdc
      rw [hdc] at hycd
      exact hxyc hycd.symm
    set η : Fin (n + 2) → Fin n := Function.update (Function.update (Function.update
      (Function.update (cst c) u d) (y c) d) v f) (x c) f with hη
    have hηu : η u = d := by
      simp [η, huv, Ne.symm (hyu c hc), hxcu.symm]
    have hηyc : η (y c) = d := by
      simp [η, hycv, Ne.symm hxyc]
    have hηv : η v = f := by
      simp [η, Ne.symm (hxv c hc)]
    have hηxc : η (x c) = f := by simp [η]
    have hηo : ∀ z, z ≠ u → z ≠ v → z ≠ x c → z ≠ y c → η z = c := by
      intro z hzu hzv hzx hzy
      simp [η, hzu, hzv, hzx, hzy]
    have hisoU : Iso W u d (y c) := by rw [hycd]; exact hxI d hd
    have hisoV : Iso W v f (x c) := by rw [hxcf]; exact hyI f hf
    have hsum : msum W η Finset.univ ≠ 0 := by
      rw [msum_forced_iso W η Finset.univ hisoU (Finset.mem_univ u) (Finset.mem_univ _) hηu]
      have hvT : v ∈ (Finset.univ.erase u).erase (y c) :=
        Finset.mem_erase.mpr ⟨Ne.symm hycv, Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩⟩
      have hxT : x c ∈ (Finset.univ.erase u).erase (y c) :=
        Finset.mem_erase.mpr ⟨hxyc, Finset.mem_erase.mpr ⟨hxcu, Finset.mem_univ _⟩⟩
      rw [msum_forced_iso W η _ hisoV hvT hxT hηv]
      rw [hηyc, hηxc]
      apply mul_ne_zero hisoU.1
      apply mul_ne_zero hisoV.1
      have hset : ((((Finset.univ.erase u).erase (y c)).erase v).erase (x c)) =
          ((((Finset.univ.erase u).erase (x c)).erase v).erase (y c)) := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        tauto
      rw [hset]
      rw [msum_congr W _ (fun z hz => by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
        exact hηo z hz.2.2.2 hz.2.1 hz.2.2.1 hz.1)]
      exact hR
    obtain ⟨z, hz⟩ := exists_not_mem_of_card_lt ({u, v, x c, y c} : Finset (Fin (n + 2)))
      (lt_of_le_of_lt Finset.card_le_four (by have := ValidDim.ge_eight (n := n); omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    have hconst := msum_univ_ne_zero_const W hW η hsum u z
    rw [hηu, hηo z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2] at hconst
    exact hdc hconst
  have := three_mul_card_le_of_chainFree U S x y hxU hyU hxinj hyinj hchain
  omega

end Iso

end PPL007General

/- ## Section: `PPL007General.NonPairedGlobal` -/

/-
# Unpaired roots on ten vertices

Two unpaired roots share at least six isolated colors, which the common
isolated-color bound excludes whenever all their partners are external.  Hence
every unpaired root points to a mutual exception pair, all its selected columns
are pure, and different unpaired roots have different exceptional rows.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

theorem sub_two_le_card_filter_ne_ne (a b : Fin n) :
    n - 2 ≤ (Finset.univ.filter (fun c => c ≠ a ∧ c ≠ b)).card := by
  have hsub : (Finset.univ.erase a).erase b ⊆ Finset.univ.filter (fun c => c ≠ a ∧ c ≠ b) := by
    intro c hc
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc
    simp [hc.1, hc.2]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.erase a) (a := b)
  rw [Finset.card_erase_of_mem (Finset.mem_univ a)] at h2
  simp at h2
  omega

section Global

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

/-- The exception of an unpaired root belongs to a mutual exception pair. -/
theorem np_exc_paired (u : Fin (n + 2)) (hu : ¬ Paired W hW u) :
    Paired W hW (exc W hW u) := by
  classical
  by_contra hv
  set v := exc W hW u with hvdef
  set S := Finset.univ.filter (fun c => c ≠ rr W hW u ∧ c ≠ rr W hW v) with hS
  have hge := ValidDim.ge_eight (n := n)
  have hcard : n - 2 ≤ S.card := sub_two_le_card_filter_ne_ne (rr W hW u) (rr W hW v)
  have huv : u ≠ v := (exc_ne W hW u).symm
  have hle : 3 * S.card ≤ 2 * n := by
    apply iso_three_mul_card_le W hW u v huv S (anchor W hW u) (anchor W hW v)
    · intro c hc
      exact np_iso W hW u hu c (Finset.mem_filter.mp hc).2.1
    · intro c hc
      exact np_iso W hW v hv c (Finset.mem_filter.mp hc).2.2
    · intro c _
      exact anchor_ne_exc W hW u c
    · intro c hc h
      apply (Finset.mem_filter.mp hc).2.1
      apply anchor_injective W hW v
      rw [h]
      exact (anchor_exc_rr W hW u hu).symm
    · intro c _ d _ h
      exact anchor_injective W hW u h
    · intro c _ d _ h
      exact anchor_injective W hW v h
  omega

/-- All selected columns at an unpaired root are pure. -/
theorem np_pure (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c : Fin n) :
    PureAt (colA W hW u c) c := by
  by_contra himp
  obtain ⟨hrc, hAc, hAr, _, _, _⟩ := np_impure W hW u hu c himp
  set x := anchor W hW u c with hx
  have hns : ∀ d, anchor W hW x d ≠ u := by
    intro d hd
    have h1 := ow_row_zero_of_anchor_eq W hW hd
    have hcd : c = d := by
      by_contra h
      exact hAc (h1 c c h)
    have hrd : rr W hW u = d := by
      by_contra h
      exact hAr (h1 _ c h)
    exact hrc (hrd.trans hcd.symm)
  have hexcx : exc W hW x = u := exc_eq_of_not_selects W hW x u (anchor_ne W hW u c) hns
  have hxnp : ¬ Paired W hW x := by
    unfold Paired
    rw [hexcx]
    exact (anchor_ne_exc W hW u c).symm
  have := np_exc_paired W hW x hxnp
  rw [hexcx] at this
  exact hu this

/-- Different unpaired roots have different exceptional rows. -/
theorem np_rr_ne (u v : Fin (n + 2)) (hu : ¬ Paired W hW u) (hv : ¬ Paired W hW v)
    (huv : u ≠ v) : rr W hW u ≠ rr W hW v := by
  classical
  intro hr
  have hve : v ≠ exc W hW u := fun h => hv (h ▸ np_exc_paired W hW u hu)
  have hue : u ≠ exc W hW v := fun h => hu (h ▸ np_exc_paired W hW v hv)
  obtain ⟨d, hd⟩ := exists_anchor_eq W hW u v (Ne.symm huv) hve
  obtain ⟨d', hd'⟩ := exists_anchor_eq W hW v u huv hue
  have hdd : orderedWeight W u v d d ≠ 0 := by
    have := colA_self_ne_zero_of_pure W hW u d (np_pure W hW u hu d)
    unfold colA at this
    rw [hd] at this
    exact this
  have hd'd : d' = d := by
    by_contra h
    exact hdd (ow_row_zero_of_anchor_eq W hW hd' d d (Ne.symm h))
  set S := Finset.univ.filter (fun c => c ≠ rr W hW u ∧ c ≠ d) with hS
  have hge := ValidDim.ge_eight (n := n)
  have hcard : n - 2 ≤ S.card := sub_two_le_card_filter_ne_ne (rr W hW u) d
  have hle : 3 * S.card ≤ 2 * n := by
    apply iso_three_mul_card_le W hW u v huv S (anchor W hW u) (anchor W hW v)
    · intro c hc
      exact np_iso W hW u hu c (Finset.mem_filter.mp hc).2.1
    · intro c hc
      exact np_iso W hW v hv c (by rw [← hr]; exact (Finset.mem_filter.mp hc).2.1)
    · intro c hc h
      apply (Finset.mem_filter.mp hc).2.2
      apply anchor_injective W hW u
      rw [h, hd]
    · intro c hc h
      apply (Finset.mem_filter.mp hc).2.2
      apply anchor_injective W hW v
      rw [h, ← hd', hd'd]
    · intro c _ d _ h
      exact anchor_injective W hW u h
    · intro c _ d _ h
      exact anchor_injective W hW v h
  omega

/-- An unpaired root selects its partner with pure diagonal columns; hence
every color other than `rr u` is isolated at `u` with its anchor. -/
theorem np_iso' (u : Fin (n + 2)) (hu : ¬ Paired W hW u) (c : Fin n) (hc : c ≠ rr W hW u) :
    Iso W u c (anchor W hW u c) :=
  np_iso W hW u hu c hc

end Global

end PPL007General

/- ## Section: `PPL007General.AllConsistent` -/

/-
# A mutual exception pair has an impure selected column

Let `u, v` be a mutual exception pair and suppose all selected columns at `u`
and `v` are pure.  Then `f = anchor u` and `g = anchor v` are bijections of the
colors onto the other eight vertices `U`, every selected edge is a diagonal
matrix unit, and for colors `i, j` at `u, v` and any coloring `κ` of `U`

`[i = j ∧ κ ≡ i on U] = M i j * h κ + [f i ≠ g j ∧ κ (f i) = i ∧ κ (g j) = j] α i β j h₂`,

where `h κ` is the matching sum on `U` and `h₂` the one on `U \ {f i, g j}`.
This is the coefficient form of the matching-polynomial identity of the paper
proof; the case analysis below derives a contradiction from it.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

theorem erase_erase_comm (S : Finset (Fin (n + 2))) (a b : Fin (n + 2)) :
    (S.erase a).erase b = (S.erase b).erase a :=
  Finset.erase_right_comm

section AllConsistent

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

theorem pure_entry_zero (u : Fin (n + 2)) (d : Fin n) (hp : PureAt (colA W hW u d) d)
    (i k : Fin n) (hi : i ≠ d) : orderedWeight W u (anchor W hW u d) i k = 0 := by
  by_cases hk : k = d
  · subst hk
    exact hp i hi
  · exact anchor_col_zero W hW u d i k hk

/-- The coefficient form of the pair identity. -/
theorem pair_expansion (u : Fin (n + 2)) (hu : Paired W hW u)
    (hA : ∀ c, PureAt (colA W hW u c) c) (hB : ∀ c, PureAt (colA W hW (exc W hW u) c) c)
    (κ : Fin (n + 2) → Fin n) (i j : Fin n) :
    msum W (Function.update (Function.update κ u i) (exc W hW u) j) Finset.univ =
      orderedWeight W u (exc W hW u) i j *
          msum W κ ((Finset.univ.erase u).erase (exc W hW u)) +
        (if anchor W hW u i ≠ anchor W hW (exc W hW u) j ∧ κ (anchor W hW u i) = i ∧
            κ (anchor W hW (exc W hW u) j) = j then
          colA W hW u i i * colA W hW (exc W hW u) j j *
            msum W κ ((((Finset.univ.erase u).erase (exc W hW u)).erase
              (anchor W hW u i)).erase (anchor W hW (exc W hW u) j))
        else 0) := by
  classical
  set v := exc W hW u with hv
  set ι := Function.update (Function.update κ u i) v j with hι
  have hvu : v ≠ u := exc_ne W hW u
  have hexcv : exc W hW v = u := hu
  have hιu : ι u = i := by simp [ι, Ne.symm hvu]
  have hιv : ι v = j := by simp [ι]
  have hιo : ∀ z, z ≠ u → z ≠ v → ι z = κ z := by
    intro z h1 h2
    simp [ι, h1, h2]
  set x := anchor W hW u i with hx
  set y := anchor W hW v j with hy
  have hxu : x ≠ u := anchor_ne W hW u i
  have hxv : x ≠ v := anchor_ne_exc W hW u i
  have hyv : y ≠ v := anchor_ne W hW v j
  have hyu : y ≠ u := by
    have := anchor_ne_exc W hW v j
    rw [hexcv] at this
    exact this
  rw [msum_expand W ι Finset.univ (Finset.mem_univ u)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩)]
  congr 1
  · rw [hιu, hιv]
    congr 1
    apply msum_congr
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    exact hιo z hz.2 hz.1
  · have hxU : x ∈ (Finset.univ.erase u).erase v :=
      Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ x⟩⟩
    rw [Finset.sum_eq_single_of_mem x hxU]
    · rw [hιu, hιo x hxu hxv]
      by_cases hκx : κ x = i
      · rw [hκx]
        have hvT : v ∈ (Finset.univ.erase u).erase x :=
          Finset.mem_erase.mpr ⟨Ne.symm hxv, Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩⟩
        rw [msum_expand W ι _ hvT, hιv]
        by_cases hxy : x = y
        · -- no admissible partner at `v`
          rw [if_neg (fun h => h.1 hxy)]
          rw [Finset.sum_eq_zero, mul_zero]
          intro z hz
          have hzv : z ≠ v := Finset.ne_of_mem_erase hz
          have hzx : z ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
          have hzu : z ≠ u :=
            Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
          obtain ⟨d, hd⟩ := exists_anchor_eq W hW v z hzv (by rw [hexcv]; exact hzu)
          have hdj : d ≠ j := by
            intro hdj
            apply hzx
            rw [← hd, hdj, ← hy, hxy]
          rw [← hd, pure_entry_zero W hW v d (hB d) j _ (Ne.symm hdj), zero_mul]
        · have hyT : y ∈ ((Finset.univ.erase u).erase x).erase v :=
            Finset.mem_erase.mpr ⟨hyv, Finset.mem_erase.mpr ⟨Ne.symm hxy,
              Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩⟩
          rw [Finset.sum_eq_single_of_mem y hyT]
          · rw [hιo y hyu hyv]
            by_cases hκy : κ y = j
            · rw [if_pos ⟨hxy, rfl, hκy⟩, hκy]
              have hset : ((((Finset.univ.erase u).erase x).erase v).erase y) =
                  ((((Finset.univ.erase u).erase v).erase x).erase y) := by
                rw [erase_erase_comm ((Finset.univ.erase u)) x v]
              rw [hset]
              have hcongr : msum W ι ((((Finset.univ.erase u).erase v).erase x).erase y) =
                  msum W κ ((((Finset.univ.erase u).erase v).erase x).erase y) := by
                apply msum_congr
                intro z hz
                simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
                exact hιo z hz.2.2.2 hz.2.2.1
              rw [hcongr]
              unfold colA
              ring
            · rw [if_neg (fun h => hκy h.2.2)]
              rw [anchor_col_zero W hW v j j (κ y) hκy, zero_mul, mul_zero]
          · intro z hz hzy
            have hzv : z ≠ v := Finset.ne_of_mem_erase hz
            have hzu : z ≠ u :=
              Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
            obtain ⟨d, hd⟩ := exists_anchor_eq W hW v z hzv (by rw [hexcv]; exact hzu)
            have hdj : d ≠ j := by
              intro hdj
              apply hzy
              rw [← hd, hdj]
            rw [← hd, pure_entry_zero W hW v d (hB d) j _ (Ne.symm hdj), zero_mul]
      · rw [if_neg (fun h => hκx h.2.1)]
        rw [anchor_col_zero W hW u i i (κ x) hκx, zero_mul]
    · intro z hz hzx
      have hzv : z ≠ v := Finset.ne_of_mem_erase hz
      have hzu : z ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
      obtain ⟨d, hd⟩ := exists_anchor_eq W hW u z hzu hzv
      have hdi : d ≠ i := by
        intro hdi
        apply hzx
        rw [← hd, hdi]
      rw [hιu, ← hd, pure_entry_zero W hW u d (hA d) i _ (Ne.symm hdi), zero_mul]

/-- The value of the equation system for the coloring used in
`pair_expansion`. -/
theorem pair_lhs (u : Fin (n + 2)) (κ : Fin (n + 2) → Fin n) (i j : Fin n) :
    msum W (Function.update (Function.update κ u i) (exc W hW u) j) Finset.univ =
      if i = j ∧ ∀ z ∈ (Finset.univ.erase u).erase (exc W hW u), κ z = i then 1 else 0 := by
  classical
  set v := exc W hW u with hv
  set ι := Function.update (Function.update κ u i) v j with hι
  have hvu : v ≠ u := exc_ne W hW u
  have hιu : ι u = i := by simp [ι, Ne.symm hvu]
  have hιv : ι v = j := by simp [ι]
  have hιo : ∀ z, z ≠ u → z ≠ v → ι z = κ z := by
    intro z h1 h2
    simp [ι, h1, h2]
  obtain ⟨z₀, hz₀u, hz₀v⟩ := exists_third u v
  by_cases hc : i = j ∧ ∀ z ∈ (Finset.univ.erase u).erase v, κ z = i
  · rw [if_pos hc]
    apply msum_univ_of_const W hW
    have hall : ∀ z, ι z = i := by
      intro z
      by_cases hzu : z = u
      · rw [hzu, hιu]
      · by_cases hzv : z = v
        · rw [hzv, hιv, hc.1]
        · rw [hιo z hzu hzv]
          exact hc.2 z (Finset.mem_erase.mpr ⟨hzv, Finset.mem_erase.mpr ⟨hzu, Finset.mem_univ z⟩⟩)
    intro a b
    rw [hall a, hall b]
  · rw [if_neg hc]
    apply msum_univ_of_not_const W hW
    intro hall
    apply hc
    refine ⟨by rw [← hιu, ← hιv]; exact hall u v, ?_⟩
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    rw [← hιo z hz.2 hz.1, ← hιu]
    exact hall z u

/-- Some selected column of a mutual exception pair is impure. -/
theorem pair_not_all_pure (u : Fin (n + 2)) (hu : Paired W hW u)
    (hA : ∀ c, PureAt (colA W hW u c) c) (hB : ∀ c, PureAt (colA W hW (exc W hW u) c) c) :
    False := by
  classical
  set v := exc W hW u with hv
  have hvu : v ≠ u := exc_ne W hW u
  have hexcv : exc W hW v = u := hu
  set U := (Finset.univ.erase u).erase v with hU
  have hUmem : ∀ z, z ∈ U ↔ z ≠ u ∧ z ≠ v := by
    intro z
    simp only [hU, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have hUcard : U.card = n := by
    rw [hU, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u)]
    simp
  set f := anchor W hW u with hf
  set g := anchor W hW v with hg
  have hfU : ∀ c, f c ∈ U := fun c =>
    (hUmem _).mpr ⟨anchor_ne W hW u c, anchor_ne_exc W hW u c⟩
  have hgU : ∀ c, g c ∈ U := by
    intro c
    refine (hUmem _).mpr ⟨?_, anchor_ne W hW v c⟩
    have := anchor_ne_exc W hW v c
    rw [hexcv] at this
    exact this
  have hfsurj : ∀ z ∈ U, ∃ d, f d = z := by
    intro z hz
    obtain ⟨hzu, hzv⟩ := (hUmem z).mp hz
    exact exists_anchor_eq W hW u z hzu hzv
  have hfinj := anchor_injective W hW u
  have hginj := anchor_injective W hW v
  set α := fun c => colA W hW u c c with hα
  set β := fun c => colA W hW v c c with hβ
  have hα0 : ∀ c, α c ≠ 0 := fun c => colA_self_ne_zero_of_pure W hW u c (hA c)
  have hβ0 : ∀ c, β c ≠ 0 := fun c => colA_self_ne_zero_of_pure W hW v c (hB c)
  set M := fun i j => orderedWeight W u v i j with hM
  set h := fun κ : Fin (n + 2) → Fin n => msum W κ U with hh
  set h2 := fun (a b : Fin (n + 2)) (κ : Fin (n + 2) → Fin n) => msum W κ ((U.erase a).erase b) with hh2
  -- the basic equation
  have E : ∀ κ i j, (if i = j ∧ ∀ z ∈ U, κ z = i then (1 : K) else 0) =
      M i j * h κ + (if f i ≠ g j ∧ κ (f i) = i ∧ κ (g j) = j then
        α i * β j * h2 (f i) (g j) κ else 0) := by
    intro κ i j
    rw [← pair_lhs W hW u κ i j, pair_expansion W hW u hu hA hB κ i j]
  have h2comm : ∀ a b κ, h2 a b κ = h2 b a κ := by
    intro a b κ
    simp only [hh2]
    rw [erase_erase_comm]
  have h2congr : ∀ a b κ κ', (∀ z ∈ U, z ≠ a → z ≠ b → κ z = κ' z) → h2 a b κ = h2 a b κ' := by
    intro a b κ κ' hk
    simp only [hh2]
    apply msum_congr
    intro z hz
    simp only [Finset.mem_erase] at hz
    exact hk z hz.2.2 hz.2.1 hz.1
  have hcongr : ∀ κ κ', (∀ z ∈ U, κ z = κ' z) → h κ = h κ' := by
    intro κ κ' hk
    simp only [hh]
    exact msum_congr W U hk
  -- a vertex of `U` outside two given vertices
  have hthird : ∀ a b : Fin (n + 2), ∃ z ∈ U, z ≠ a ∧ z ≠ b := by
    intro a b
    have hcard : ((U.erase a).erase b).card ≥ 6 := by
      have hge := ValidDim.ge_eight (n := n)
      have h1 := Finset.pred_card_le_card_erase (s := U.erase a) (a := b)
      have h2 := Finset.pred_card_le_card_erase (s := U) (a := a)
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((U.erase a).erase b).card)
    simp only [Finset.mem_erase] at hz
    exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
  -- Step 1: the monochromatic equations
  have hmono : ∀ c, (1 : K) = M c c * h (cst c) +
      (if f c ≠ g c then α c * β c * h2 (f c) (g c) (cst c) else 0) := by
    intro c
    have := E (cst c) c c
    rw [if_pos ⟨rfl, fun z _ => rfl⟩] at this
    rw [this]
    congr 1
    by_cases hfg : f c = g c
    · rw [if_neg (show ¬ (f c ≠ g c ∧ cst c (f c) = c ∧ cst c (g c) = c) from fun h => h.1 hfg),
        if_neg (show ¬ (f c ≠ g c) from fun h => h hfg)]
    · rw [if_pos (show f c ≠ g c ∧ cst c (f c) = c ∧ cst c (g c) = c from ⟨hfg, rfl, rfl⟩),
        if_pos (show f c ≠ g c from hfg)]
  -- The key mixed coloring for a color `c` with `f c ≠ g c`.
  -- `d` is the `f`-preimage of `g c`, `a` the `g`-preimage of `f c`.
  have hmixed : ∀ c, f c ≠ g c → ∀ d a, f d = g c → g a = f c →
      ∀ κ : Fin (n + 2) → Fin n, κ (g c) = d → κ (f c) = a →
        (∀ z ∈ U, z ≠ f c → z ≠ g c → κ z = c) →
        (0 : K) = M d a * h κ + α d * β a * h2 (f c) (g c) (cst c) := by
    intro c hfg d a hd ha κ hκy hκx hκo
    have hdc : d ≠ c := by
      intro hdc
      apply hfg
      rw [← hd, hdc]
    have := E κ d a
    rw [if_neg] at this
    · rw [this]
      congr 1
      rw [if_pos ⟨by rw [hd, ha]; exact Ne.symm hfg, by rw [hd]; exact hκy,
        by rw [ha]; exact hκx⟩]
      rw [hd, ha, h2comm]
      congr 1
      apply h2congr
      intro z hz hzx hzy
      exact hκo z hz hzx hzy
    · intro hc
      obtain ⟨z, hz, hzx, hzy⟩ := hthird (f c) (g c)
      have := hc.2 z hz
      rw [hκo z hz hzx hzy] at this
      exact hdc this.symm
  -- construction of the mixed coloring
  have hκstar : ∀ c, f c ≠ g c → ∀ d a : Fin n, ∃ κ : Fin (n + 2) → Fin n, κ (g c) = d ∧ κ (f c) = a ∧
      ∀ z, z ≠ f c → z ≠ g c → κ z = c := by
    intro c hfg d a
    refine ⟨Function.update (Function.update (cst c) (g c) d) (f c) a, ?_, ?_, ?_⟩
    · simp [Ne.symm hfg]
    · simp
    · intro z hzx hzy
      simp [hzx, hzy]
  have hpre_f : ∀ c, ∃ d, f d = g c := fun c => hfsurj (g c) (hgU c)
  have hpre_g : ∀ c, ∃ a, g a = f c := by
    intro c
    obtain ⟨hzu, hzv⟩ := (hUmem (f c)).mp (hfU c)
    exact exists_anchor_eq W hW v (f c) hzv (by rw [hexcv]; exact hzu)
  by_cases hcaseA : ∃ h₀, h (cst h₀) ≠ 0
  · -- Case A
    obtain ⟨h₀, hh₀⟩ := hcaseA
    have hMzero : ∀ i j, ¬ (i = h₀ ∧ j = h₀) → M i j = 0 := by
      intro i j hij
      have := E (cst h₀) i j
      have hL : ¬ (i = j ∧ ∀ z ∈ U, cst h₀ z = i) := by
        intro hc
        obtain ⟨z, hz, -, -⟩ := hthird u u
        have hz' : cst h₀ z = i := hc.2 z hz
        rw [cst_apply] at hz'
        exact hij ⟨hz'.symm, by rw [← hc.1]; exact hz'.symm⟩
      have hR : ¬ (f i ≠ g j ∧ cst h₀ (f i) = i ∧ cst h₀ (g j) = j) := by
        intro hc
        exact hij ⟨hc.2.1.symm, hc.2.2.symm⟩
      rw [if_neg hL, if_neg hR, add_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hh₀
    have hg_const : ∀ c, c ≠ h₀ → g c = f h₀ := by
      intro c hc
      have hm := hmono c
      rw [hMzero c c (fun h => hc h.1), zero_mul, zero_add] at hm
      have hfg : f c ≠ g c := by
        intro hfg
        rw [if_neg (fun h => h hfg)] at hm
        exact one_ne_zero hm
      rw [if_pos hfg] at hm
      have hh2ne : h2 (f c) (g c) (cst c) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hm
        exact one_ne_zero hm
      obtain ⟨d, hd⟩ := hpre_f c
      obtain ⟨a, ha⟩ := hpre_g c
      obtain ⟨κ, hκy, hκx, hκo⟩ := hκstar c hfg d a
      have h0 := hmixed c hfg d a hd ha κ hκy hκx (fun z _ hzx hzy => hκo z hzx hzy)
      have hda : d = h₀ ∧ a = h₀ := by
        by_contra hda
        rw [hMzero d a hda, zero_mul, zero_add] at h0
        exact mul_ne_zero (mul_ne_zero (hα0 d) (hβ0 a)) hh2ne h0.symm
      rw [← hd, hda.1]
    obtain ⟨c₁, hc₁⟩ : ∃ c : Fin n, c ≠ h₀ := by
      have hge := ValidDim.ge_eight (n := n)
      refine ⟨⟨(h₀.val + 1) % n, Nat.mod_lt _ (by omega)⟩, ?_⟩
      intro heq
      have hv : (h₀.val + 1) % n = h₀.val := congrArg Fin.val heq
      have hlt := h₀.isLt
      by_cases hlast : h₀.val + 1 = n
      · rw [hlast, Nat.mod_self] at hv; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
    obtain ⟨c₂, hc₂, hc₁₂⟩ : ∃ c : Fin n, c ≠ h₀ ∧ c ≠ c₁ := by
      by_contra hne
      push Not at hne
      have h3 : (Finset.univ : Finset (Fin n)) ⊆ {h₀, c₁} := by
        intro c _
        by_cases hc : c = h₀
        · simp [hc]
        · simp [hne c hc]
      have := Finset.card_le_card h3
      have hge := ValidDim.ge_eight (n := n)
      have h4 := Finset.card_le_two (a := h₀) (b := c₁)
      simp at this
      omega
    exact hc₁₂ (hginj ((hg_const c₂ hc₂).trans (hg_const c₁ hc₁).symm))
  · push Not at hcaseA
    -- Case B: every monochromatic matching sum on `U` vanishes.
    have hB0 : ∀ c, f c ≠ g c ∧ h2 (f c) (g c) (cst c) ≠ 0 := by
      intro c
      have hm := hmono c
      rw [hcaseA c, mul_zero, zero_add] at hm
      have hfg : f c ≠ g c := by
        intro hfg
        rw [if_neg (fun h => h hfg)] at hm
        exact one_ne_zero hm
      rw [if_pos hfg] at hm
      refine ⟨hfg, ?_⟩
      intro h0
      rw [h0, mul_zero] at hm
      exact one_ne_zero hm
    by_cases hcaseBi : ∀ κ, h κ = 0
    · -- Case B(i)
      obtain ⟨hfg, hh2⟩ := hB0 0
      obtain ⟨d, hd⟩ := hpre_f 0
      obtain ⟨a, ha⟩ := hpre_g 0
      obtain ⟨κ, hκy, hκx, hκo⟩ := hκstar 0 hfg d a
      have h0 := hmixed 0 hfg d a hd ha κ hκy hκx (fun z _ hzx hzy => hκo z hzx hzy)
      rw [hcaseBi κ, mul_zero, zero_add] at h0
      exact mul_ne_zero (mul_ne_zero (hα0 d) (hβ0 a)) hh2 h0.symm
    · -- Case B(ii)
      push Not at hcaseBi
      obtain ⟨κ₀, hκ₀⟩ := hcaseBi
      -- every color occurs at least twice on `U` under `κ₀`
      have htwice : ∀ b : Fin n, 2 ≤ (U.filter (fun z => κ₀ z = b)).card := by
        intro b
        by_cases hMb : M b b ≠ 0
        · have := E κ₀ b b
          rw [if_neg] at this
          · by_cases hcond : f b ≠ g b ∧ κ₀ (f b) = b ∧ κ₀ (g b) = b
            · have hsub : ({f b, g b} : Finset (Fin (n + 2))) ⊆ U.filter (fun z => κ₀ z = b) := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl
                · exact Finset.mem_filter.mpr ⟨hfU b, hcond.2.1⟩
                · exact Finset.mem_filter.mpr ⟨hgU b, hcond.2.2⟩
              have := Finset.card_le_card hsub
              rw [Finset.card_pair hcond.1] at this
              exact this
            · rw [if_neg hcond, add_zero] at this
              exact absurd this.symm (mul_ne_zero hMb hκ₀)
          · intro hc
            apply hκ₀
            rw [hcongr κ₀ (cst b) (fun z hz => hc.2 z hz)]
            exact hcaseA b
        · push Not at hMb
          obtain ⟨hfg, hh2⟩ := hB0 b
          obtain ⟨d, hd⟩ := hpre_f b
          obtain ⟨a, ha⟩ := hpre_g b
          have hdb : d ≠ b := by
            intro hdb
            apply hfg
            rw [← hd, hdb]
          -- support of `h2 (f b) (g b)` for colorings equal to `b` at `f b, g b`
          have hsupp : ∀ κ : Fin (n + 2) → Fin n, κ (f b) = b → κ (g b) = b →
              h2 (f b) (g b) κ ≠ 0 → ∀ z ∈ U, κ z = b := by
            intro κ hx hy hne
            have := E κ b b
            rw [hMb, zero_mul, zero_add,
              if_pos (show f b ≠ g b ∧ κ (f b) = b ∧ κ (g b) = b from ⟨hfg, hx, hy⟩)] at this
            by_contra hnot
            rw [if_neg (fun hc => hnot hc.2)] at this
            exact mul_ne_zero (mul_ne_zero (hα0 b) (hβ0 b)) hne this.symm
          by_cases hda : d = a
          · -- impossible
            exfalso
            subst hda
            have hm := hmono d
            rw [hcaseA d, mul_zero, zero_add] at hm
            have hfgd : f d ≠ g d := (hB0 d).1
            rw [if_pos hfgd] at hm
            -- `h2 (f d) (g d) (cst d) = 0`
            have hzero : h2 (f d) (g d) (cst d) = 0 := by
              rw [hd, ha, h2comm]
              by_contra hne
              obtain ⟨κ, hκx, hκy, hκo⟩ : ∃ κ : Fin (n + 2) → Fin n, κ (f b) = b ∧ κ (g b) = b ∧
                  ∀ z, z ≠ f b → z ≠ g b → κ z = d := by
                refine ⟨Function.update (Function.update (cst d) (f b) b) (g b) b, ?_, ?_, ?_⟩
                · simp [hfg]
                · simp
                · intro z hzx hzy
                  simp [hzx, hzy]
              have hne' : h2 (f b) (g b) κ ≠ 0 := by
                rw [h2congr (f b) (g b) κ (cst d) (fun z _ hzx hzy => hκo z hzx hzy)]
                exact hne
              obtain ⟨z, hz, hzx, hzy⟩ := hthird (f b) (g b)
              have := hsupp κ hκx hκy hne' z hz
              rw [hκo z hzx hzy] at this
              exact hdb this
            rw [hzero, mul_zero] at hm
            exact one_ne_zero hm
          · -- `h` is supported on the single coloring `κ*`
            have hdom : ∀ κ : Fin (n + 2) → Fin n, h κ ≠ 0 →
                κ (g b) = d ∧ κ (f b) = a ∧ ∀ z ∈ U, z ≠ f b → z ≠ g b → κ z = b := by
              intro κ hκ
              have := E κ d a
              rw [if_neg (fun hc => hda hc.1)] at this
              by_cases hcond : κ (g b) = d ∧ κ (f b) = a
              · refine ⟨hcond.1, hcond.2, ?_⟩
                rw [if_pos ⟨by rw [hd, ha]; exact Ne.symm hfg, by rw [hd]; exact hcond.1,
                  by rw [ha]; exact hcond.2⟩] at this
                rw [hd, ha] at this
                have hh2ne : h2 (g b) (f b) κ ≠ 0 := by
                  intro h0
                  rw [h0, mul_zero, add_zero] at this
                  -- then `M d a * h κ = 0`; show `M d a ≠ 0` from `κ*`
                  obtain ⟨κs, hκsy, hκsx, hκso⟩ := hκstar b hfg d a
                  have h0' := hmixed b hfg d a hd ha κs hκsy hκsx
                    (fun z _ hzx hzy => hκso z hzx hzy)
                  have hMda : M d a ≠ 0 := by
                    intro hM0
                    rw [hM0, zero_mul, zero_add] at h0'
                    exact mul_ne_zero (mul_ne_zero (hα0 d) (hβ0 a)) hh2 h0'.symm
                  exact mul_ne_zero hMda hκ this.symm
                -- recolor `f b, g b` by `b` and use `hsupp`
                obtain ⟨κ', hκ'x, hκ'y, hκ'o⟩ : ∃ κ' : Fin (n + 2) → Fin n, κ' (f b) = b ∧
                    κ' (g b) = b ∧ ∀ z, z ≠ f b → z ≠ g b → κ' z = κ z := by
                  refine ⟨Function.update (Function.update κ (f b) b) (g b) b, ?_, ?_, ?_⟩
                  · simp [hfg]
                  · simp
                  · intro z hzx hzy
                    simp [hzx, hzy]
                have hne' : h2 (f b) (g b) κ' ≠ 0 := by
                  rw [h2congr (f b) (g b) κ' κ (fun z _ hzx hzy => hκ'o z hzx hzy), h2comm]
                  exact hh2ne
                intro z hz hzx hzy
                have := hsupp κ' hκ'x hκ'y hne' z hz
                rw [hκ'o z hzx hzy] at this
                exact this
              · rw [if_neg (fun hc => hcond ⟨by rw [← hd]; exact hc.2.1,
                  by rw [← ha]; exact hc.2.2⟩), add_zero] at this
                exfalso
                obtain ⟨κs, hκsy, hκsx, hκso⟩ := hκstar b hfg d a
                have h0' := hmixed b hfg d a hd ha κs hκsy hκsx
                  (fun z _ hzx hzy => hκso z hzx hzy)
                have hMda : M d a ≠ 0 := by
                  intro hM0
                  rw [hM0, zero_mul, zero_add] at h0'
                  exact mul_ne_zero (mul_ne_zero (hα0 d) (hβ0 a)) hh2 h0'.symm
                exact mul_ne_zero hMda hκ this.symm
            obtain ⟨-, -, hκ₀o⟩ := hdom κ₀ hκ₀
            have hsub : (U.erase (f b)).erase (g b) ⊆ U.filter (fun z => κ₀ z = b) := by
              intro z hz
              simp only [Finset.mem_erase] at hz
              exact Finset.mem_filter.mpr ⟨hz.2.2, hκ₀o z hz.2.2 hz.2.1 hz.1⟩
            have h1 := Finset.card_le_card hsub
            have h2' := Finset.pred_card_le_card_erase (s := U.erase (f b)) (a := g b)
            have hge := ValidDim.ge_eight (n := n)
            have h3 := Finset.pred_card_le_card_erase (s := U) (a := f b)
            omega
      have hsum := Finset.card_eq_sum_card_fiberwise (s := U) (t := Finset.univ)
        (f := κ₀) (fun z _ => Finset.mem_univ (κ₀ z))
      have hge : ∑ b ∈ (Finset.univ : Finset (Fin n)), (U.filter (fun z => κ₀ z = b)).card ≥
          ∑ _b ∈ (Finset.univ : Finset (Fin n)), 2 :=
        Finset.sum_le_sum (fun b _ => htwice b)
      have hge8 := ValidDim.ge_eight (n := n)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hge
      omega

end AllConsistent

end PPL007General

/- ## Section: `PPL007General.PurePencil` -/

/-
# Rank-one pencils through coordinate matrices

`E c` is the matrix unit at `(c, c)`.  If `E c - h M` is a rank-one matrix
`a bᵀ` for two different colors, all four factors live on the two
coordinates.  Three colors force `M = 0`.  For two colors the two-by-two block
is classified into an exchange type and a type with a two-component factor in
each color.
-/

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K] {dim : Nat}

/-- Matrix unit at `(c, c)`, as a function of the entry. -/
def unitE (c i j : Fin dim) : K := if i = c ∧ j = c then 1 else 0

/- ### Auxiliary lemmas -/

theorem pencil_aux_unitE_self (c : Fin dim) : unitE c c c = (1 : K) := by
  simp [unitE]

theorem pencil_aux_unitE_of_ne_left {c i : Fin dim} (j : Fin dim) (h : i ≠ c) :
    unitE c i j = (0 : K) := by
  simp [unitE, h]

theorem pencil_aux_unitE_of_ne_right {c j : Fin dim} (i : Fin dim) (h : j ≠ c) :
    unitE c i j = (0 : K) := by
  simp [unitE, h]

/-- In `0 = h m + x y` with `h ≠ 0`, a nonzero `m` forces both factors to be nonzero. -/
theorem pencil_aux_ne_of_ne {h m x y : K} (e : (0 : K) = h * m + x * y) (h0 : h ≠ 0)
    (hm : m ≠ 0) : x ≠ 0 ∧ y ≠ 0 := by
  have hxy : x * y ≠ 0 := by
    intro hxy
    apply hm
    have hhm : h * m = 0 := by linear_combination -e - hxy
    exact (mul_eq_zero.1 hhm).resolve_left h0
  exact mul_ne_zero_iff.1 hxy

/-- In `0 = h m + x y` with `m = 0` and `x ≠ 0`, the factor `y` vanishes. -/
theorem pencil_aux_right_zero {h m x y : K} (e : (0 : K) = h * m + x * y) (hm : m = 0)
    (hx : x ≠ 0) : y = 0 := by
  have hxy : x * y = 0 := by linear_combination -e - h * hm
  exact (mul_eq_zero.1 hxy).resolve_left hx

/-- In `0 = h m + x y` with `m = 0` and `y ≠ 0`, the factor `x` vanishes. -/
theorem pencil_aux_left_zero {h m x y : K} (e : (0 : K) = h * m + x * y) (hm : m = 0)
    (hy : y ≠ 0) : x = 0 := by
  have hxy : x * y = 0 := by linear_combination -e - h * hm
  exact (mul_eq_zero.1 hxy).resolve_right hy

/-- In `0 = h m + x y` with `h ≠ 0` and `x y = 0`, the entry `m` vanishes. -/
theorem pencil_aux_m_zero {h m x y : K} (e : (0 : K) = h * m + x * y) (h0 : h ≠ 0)
    (hxy : x * y = 0) : m = 0 := by
  have hhm : h * m = 0 := by linear_combination -e - hxy
  exact (mul_eq_zero.1 hhm).resolve_left h0

/-- In `1 = h m + x y` with `m = 0`, both factors are nonzero. -/
theorem pencil_aux_one_ne {h m x y : K} (e : (1 : K) = h * m + x * y) (hm : m = 0) :
    x ≠ 0 ∧ y ≠ 0 := by
  have hxy : x * y = 1 := by linear_combination -e - h * hm
  refine mul_ne_zero_iff.1 ?_
  rw [hxy]
  exact one_ne_zero

/-- In `1 = h m + x y` with `x y = 0`, the entry `m` is nonzero. -/
theorem pencil_aux_one_m_ne {h m x y : K} (e : (1 : K) = h * m + x * y) (hxy : x * y = 0) :
    m ≠ 0 := by
  intro hm
  have h10 : (1 : K) = 0 := by linear_combination e + h * hm + hxy
  exact one_ne_zero h10

/-- An entry in a row where the left factor vanishes (outside the center) is zero. -/
theorem pencil_aux_M_zero_row (M : Fin dim → Fin dim → K) (c : Fin dim) (hc : K) (hc0 : hc ≠ 0)
    (ac bc : Fin dim → K) (Hc : ∀ i j, unitE c i j = hc * M i j + ac i * bc j)
    {i : Fin dim} (j : Fin dim) (hi : i ≠ c) (ha : ac i = 0) : M i j = 0 := by
  have e := Hc i j
  rw [pencil_aux_unitE_of_ne_left j hi, ha] at e
  have hm : hc * M i j = 0 := by linear_combination -e
  exact (mul_eq_zero.1 hm).resolve_left hc0

/-- An entry in a column where the right factor vanishes (outside the center) is zero. -/
theorem pencil_aux_M_zero_col (M : Fin dim → Fin dim → K) (c : Fin dim) (hc : K) (hc0 : hc ≠ 0)
    (ac bc : Fin dim → K) (Hc : ∀ i j, unitE c i j = hc * M i j + ac i * bc j)
    (i : Fin dim) {j : Fin dim} (hj : j ≠ c) (hb : bc j = 0) : M i j = 0 := by
  have e := Hc i j
  rw [pencil_aux_unitE_of_ne_right i hj, hb] at e
  have hm : hc * M i j = 0 := by linear_combination -e
  exact (mul_eq_zero.1 hm).resolve_left hc0

/-- If two factors vanish outside `{c, d}` and one of them is nonzero somewhere
off `c`, then one of them is nonzero at `d`. -/
theorem pencil_aux_bad {c d : Fin dim} (a b : Fin dim → K)
    (ha : ∀ i, i ≠ c → i ≠ d → a i = 0) (hb : ∀ j, j ≠ c → j ≠ d → b j = 0)
    (hbad : (∃ i, i ≠ c ∧ a i ≠ 0) ∨ (∃ j, j ≠ c ∧ b j ≠ 0)) : a d ≠ 0 ∨ b d ≠ 0 := by
  rcases hbad with ⟨i, hic, hi⟩ | ⟨j, hjc, hj⟩
  · left
    by_cases hid : i = d
    · rwa [hid] at hi
    · exact absurd (ha i hic hid) hi
  · right
    by_cases hjd : j = d
    · rwa [hjd] at hj
    · exact absurd (hb j hjc hjd) hj

/- ### Main statements -/

theorem pencil_two (M : Fin dim → Fin dim → K) (c d : Fin dim) (hcd : c ≠ d)
    (hc hd : K) (hc0 : hc ≠ 0) (hd0 : hd ≠ 0) (ac bc ad bd : Fin dim → K)
    (Hc : ∀ i j, unitE c i j = hc * M i j + ac i * bc j)
    (Hd : ∀ i j, unitE d i j = hd * M i j + ad i * bd j) :
    (∀ i, i ≠ c → i ≠ d → ac i = 0 ∧ ad i = 0) ∧
      (∀ j, j ≠ c → j ≠ d → bc j = 0 ∧ bd j = 0) := by
  have hdc : d ≠ c := hcd.symm
  -- Eliminating `M`: `hd E_c - hc E_d = hd ac bcᵀ - hc ad bdᵀ`.
  have H : ∀ i j, hd * unitE c i j - hc * unitE d i j
      = hd * ac i * bc j - hc * ad i * bd j := by
    intro i j
    linear_combination hd * Hc i j - hc * Hd i j
  -- The two-by-two block on `{c, d}`.
  have e11 : hd = hd * ac c * bc c - hc * ad c * bd c := by
    have h := H c c
    rw [pencil_aux_unitE_self, pencil_aux_unitE_of_ne_left c hcd] at h
    linear_combination h
  have e12 : (0 : K) = hd * ac c * bc d - hc * ad c * bd d := by
    have h := H c d
    rw [pencil_aux_unitE_of_ne_right c hdc, pencil_aux_unitE_of_ne_left d hcd] at h
    linear_combination h
  have e21 : (0 : K) = hd * ac d * bc c - hc * ad d * bd c := by
    have h := H d c
    rw [pencil_aux_unitE_of_ne_left c hdc, pencil_aux_unitE_of_ne_right d hcd] at h
    linear_combination h
  have e22 : -hc = hd * ac d * bc d - hc * ad d * bd d := by
    have h := H d d
    rw [pencil_aux_unitE_of_ne_left d hdc, pencil_aux_unitE_self] at h
    linear_combination h
  -- Taking determinants of the block: `det Y * det X = 1` up to the factor `hc hd`.
  have key : hc * hd * (ac c * ad d - ac d * ad c) * (bc c * bd d - bc d * bd c)
      = hc * hd := by
    linear_combination (hd * ac d * bc d - hc * ad d * bd d) * e11 + hd * e22
      - (hd * ac d * bc c - hc * ad d * bd c) * e12
  have hX : bc c * bd d - bc d * bd c ≠ 0 := by
    intro h0
    apply mul_ne_zero hc0 hd0
    linear_combination -key + hc * hd * (ac c * ad d - ac d * ad c) * h0
  have hY : ac c * ad d - ac d * ad c ≠ 0 := by
    intro h0
    apply mul_ne_zero hc0 hd0
    linear_combination -key + hc * hd * (bc c * bd d - bc d * bd c) * h0
  refine ⟨fun i hic hid => ?_, fun j hjc hjd => ?_⟩
  · -- Rows outside `{c, d}`.
    have f1 : (0 : K) = hd * ac i * bc c - hc * ad i * bd c := by
      have h := H i c
      rw [pencil_aux_unitE_of_ne_left c hic, pencil_aux_unitE_of_ne_left c hid] at h
      linear_combination h
    have f2 : (0 : K) = hd * ac i * bc d - hc * ad i * bd d := by
      have h := H i d
      rw [pencil_aux_unitE_of_ne_left d hic, pencil_aux_unitE_of_ne_left d hid] at h
      linear_combination h
    have g1 : hd * ac i * (bc c * bd d - bc d * bd c) = 0 := by
      linear_combination (-bd d) * f1 + bd c * f2
    have g2 : hc * ad i * (bc c * bd d - bc d * bd c) = 0 := by
      linear_combination (-bc d) * f1 + bc c * f2
    constructor
    · by_contra h
      exact mul_ne_zero (mul_ne_zero hd0 h) hX g1
    · by_contra h
      exact mul_ne_zero (mul_ne_zero hc0 h) hX g2
  · -- Columns outside `{c, d}`.
    have f1 : (0 : K) = hd * ac c * bc j - hc * ad c * bd j := by
      have h := H c j
      rw [pencil_aux_unitE_of_ne_right c hjc, pencil_aux_unitE_of_ne_right c hjd] at h
      linear_combination h
    have f2 : (0 : K) = hd * ac d * bc j - hc * ad d * bd j := by
      have h := H d j
      rw [pencil_aux_unitE_of_ne_right d hjc, pencil_aux_unitE_of_ne_right d hjd] at h
      linear_combination h
    have g1 : hd * bc j * (ac c * ad d - ac d * ad c) = 0 := by
      linear_combination (-ad d) * f1 + ad c * f2
    have g2 : hc * bd j * (ac c * ad d - ac d * ad c) = 0 := by
      linear_combination (-ac d) * f1 + ac c * f2
    constructor
    · by_contra h
      exact mul_ne_zero (mul_ne_zero hd0 h) hY g1
    · by_contra h
      exact mul_ne_zero (mul_ne_zero hc0 h) hY g2

theorem pencil_three (M : Fin dim → Fin dim → K) (c d f : Fin dim)
    (hcd : c ≠ d) (hcf : c ≠ f) (hdf : d ≠ f)
    (hc hd hf : K) (hc0 : hc ≠ 0) (hd0 : hd ≠ 0) (hf0 : hf ≠ 0)
    (ac bc ad bd af bf : Fin dim → K)
    (Hc : ∀ i j, unitE c i j = hc * M i j + ac i * bc j)
    (Hd : ∀ i j, unitE d i j = hd * M i j + ad i * bd j)
    (Hf : ∀ i j, unitE f i j = hf * M i j + af i * bf j) :
    ∀ i j, M i j = 0 := by
  obtain ⟨rcd, ccd⟩ := pencil_two M c d hcd hc hd hc0 hd0 ac bc ad bd Hc Hd
  obtain ⟨rcf, ccf⟩ := pencil_two M c f hcf hc hf hc0 hf0 ac bc af bf Hc Hf
  obtain ⟨rdf, -⟩ := pencil_two M d f hdf hd hf hd0 hf0 ad bd af bf Hd Hf
  -- The factors of color `c` live on `c` alone.
  have hac : ∀ i, i ≠ c → ac i = 0 := by
    intro i hic
    by_cases hid : i = d
    · rw [hid]
      exact (rcf d hcd.symm hdf).1
    · exact (rcd i hic hid).1
  have hbc : ∀ j, j ≠ c → bc j = 0 := by
    intro j hjc
    by_cases hjd : j = d
    · rw [hjd]
      exact (ccf d hcd.symm hdf).1
    · exact (ccd j hjc hjd).1
  -- The left factor of color `d` vanishes at `c`.
  have hadc : ad c = 0 := (rdf c hcd hcf).1
  intro i j
  by_cases hic : i = c
  · by_cases hjc : j = c
    · rw [hic, hjc]
      exact pencil_aux_M_zero_row M d hd hd0 ad bd Hd c hcd hadc
    · exact pencil_aux_M_zero_col M c hc hc0 ac bc Hc i hjc (hbc j hjc)
  · exact pencil_aux_M_zero_row M c hc hc0 ac bc Hc j hic (hac i hic)

/-- Classification of a pencil with exactly the two bad colors `c, d`.
Either both factors of color `c` vanish at `c` and both factors of color `d`
vanish at `d` (exchange type), or each color has a factor with two nonzero
coordinates. -/
theorem pencil_block_classification (M : Fin dim → Fin dim → K) (c d : Fin dim)
    (hcd : c ≠ d) (hc hd : K) (hc0 : hc ≠ 0) (hd0 : hd ≠ 0)
    (ac bc ad bd : Fin dim → K)
    (Hc : ∀ i j, unitE c i j = hc * M i j + ac i * bc j)
    (Hd : ∀ i j, unitE d i j = hd * M i j + ad i * bd j)
    (hcBad : (∃ i, i ≠ c ∧ ac i ≠ 0) ∨ (∃ j, j ≠ c ∧ bc j ≠ 0))
    (hdBad : (∃ i, i ≠ d ∧ ad i ≠ 0) ∨ (∃ j, j ≠ d ∧ bd j ≠ 0))
    (hcNotBoth : ¬ ((ac c ≠ 0 ∧ ac d ≠ 0) ∧ (bc c ≠ 0 ∧ bc d ≠ 0))) :
    (ac c = 0 ∧ bc c = 0 ∧ ad d = 0 ∧ bd d = 0) ∨
      (((ac c ≠ 0 ∧ ac d ≠ 0) ∨ (bc c ≠ 0 ∧ bc d ≠ 0)) ∧
        ((ad c ≠ 0 ∧ ad d ≠ 0) ∨ (bd c ≠ 0 ∧ bd d ≠ 0))) := by
  obtain ⟨hrow, hcol⟩ := pencil_two M c d hcd hc hd hc0 hd0 ac bc ad bd Hc Hd
  have hdc : d ≠ c := hcd.symm
  -- By `pencil_two`, badness of color `c` is seen at the coordinate `d`, and
  -- badness of color `d` at the coordinate `c`.
  have hcBad' : ac d ≠ 0 ∨ bc d ≠ 0 :=
    pencil_aux_bad ac bc (fun i hic hid => (hrow i hic hid).1)
      (fun j hjc hjd => (hcol j hjc hjd).1) hcBad
  have hdBad' : ad c ≠ 0 ∨ bd c ≠ 0 :=
    pencil_aux_bad ad bd (fun i hid hic => (hrow i hic hid).2)
      (fun j hjd hjc => (hcol j hjc hjd).2) hdBad
  -- The eight scalar equations of the two-by-two block.
  have c11 := Hc c c
  have c12 := Hc c d
  have c21 := Hc d c
  have c22 := Hc d d
  have d11 := Hd c c
  have d12 := Hd c d
  have d21 := Hd d c
  have d22 := Hd d d
  rw [pencil_aux_unitE_self] at c11
  rw [pencil_aux_unitE_of_ne_right c hdc] at c12
  rw [pencil_aux_unitE_of_ne_left c hdc] at c21
  rw [pencil_aux_unitE_of_ne_left d hdc] at c22
  rw [pencil_aux_unitE_of_ne_left c hcd] at d11
  rw [pencil_aux_unitE_of_ne_left d hcd] at d12
  rw [pencil_aux_unitE_of_ne_right d hcd] at d21
  rw [pencil_aux_unitE_self] at d22
  by_cases h12 : M c d = 0
  · by_cases h21 : M d c = 0
    · -- Diagonal block: exchange type.
      left
      have h11 : M c c ≠ 0 := by
        apply pencil_aux_one_m_ne c11
        rcases hcBad' with h | h
        · rw [pencil_aux_right_zero c21 h21 h, mul_zero]
        · rw [pencil_aux_left_zero c12 h12 h, zero_mul]
      have h22 : M d d ≠ 0 := by
        apply pencil_aux_one_m_ne d22
        rcases hdBad' with h | h
        · rw [pencil_aux_right_zero d12 h12 h, mul_zero]
        · rw [pencil_aux_left_zero d21 h21 h, zero_mul]
      obtain ⟨ha', hb'⟩ := pencil_aux_ne_of_ne c22 hc0 h22
      obtain ⟨hp, hq⟩ := pencil_aux_ne_of_ne d11 hd0 h11
      exact ⟨pencil_aux_left_zero c12 h12 hb', pencil_aux_right_zero c21 h21 ha',
        pencil_aux_left_zero d21 h21 hq, pencil_aux_right_zero d12 h12 hp⟩
    · -- Only the `(d, c)` entry is off the diagonal.
      right
      obtain ⟨ha', hb⟩ := pencil_aux_ne_of_ne c21 hc0 h21
      obtain ⟨hp', hq⟩ := pencil_aux_ne_of_ne d21 hd0 h21
      by_cases hb' : bc d = 0
      · have h22 : M d d = 0 := pencil_aux_m_zero c22 hc0 (by rw [hb', mul_zero])
        obtain ⟨-, hq'⟩ := pencil_aux_one_ne d22 h22
        have hp : ad c = 0 := pencil_aux_left_zero d12 h12 hq'
        have h11 : M c c = 0 := pencil_aux_m_zero d11 hd0 (by rw [hp, zero_mul])
        obtain ⟨ha, -⟩ := pencil_aux_one_ne c11 h11
        exact ⟨Or.inl ⟨ha, ha'⟩, Or.inr ⟨hq, hq'⟩⟩
      · have ha : ac c = 0 := pencil_aux_left_zero c12 h12 hb'
        have h11 : M c c ≠ 0 := pencil_aux_one_m_ne c11 (by rw [ha, zero_mul])
        obtain ⟨hp, -⟩ := pencil_aux_ne_of_ne d11 hd0 h11
        exact ⟨Or.inr ⟨hb, hb'⟩, Or.inl ⟨hp, hp'⟩⟩
  · by_cases h21 : M d c = 0
    · -- Only the `(c, d)` entry is off the diagonal.
      right
      obtain ⟨ha, hb'⟩ := pencil_aux_ne_of_ne c12 hc0 h12
      obtain ⟨hp, hq'⟩ := pencil_aux_ne_of_ne d12 hd0 h12
      by_cases ha' : ac d = 0
      · have h22 : M d d = 0 := pencil_aux_m_zero c22 hc0 (by rw [ha', zero_mul])
        obtain ⟨hp', -⟩ := pencil_aux_one_ne d22 h22
        have hq : bd c = 0 := pencil_aux_right_zero d21 h21 hp'
        have h11 : M c c = 0 := pencil_aux_m_zero d11 hd0 (by rw [hq, mul_zero])
        obtain ⟨-, hb⟩ := pencil_aux_one_ne c11 h11
        exact ⟨Or.inr ⟨hb, hb'⟩, Or.inl ⟨hp, hp'⟩⟩
      · have hb : bc c = 0 := pencil_aux_right_zero c21 h21 ha'
        have h11 : M c c ≠ 0 := pencil_aux_one_m_ne c11 (by rw [hb, mul_zero])
        obtain ⟨-, hq⟩ := pencil_aux_ne_of_ne d11 hd0 h11
        exact ⟨Or.inl ⟨ha, ha'⟩, Or.inr ⟨hq, hq'⟩⟩
    · -- Both off-diagonal entries nonzero: all four factors of color `c` are nonzero.
      exfalso
      obtain ⟨ha, hb'⟩ := pencil_aux_ne_of_ne c12 hc0 h12
      obtain ⟨ha', hb⟩ := pencil_aux_ne_of_ne c21 hc0 h21
      exact hcNotBoth ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩

end PPL007General

/- ## Section: `PPL007General.PairStructure` -/

/-
# Bad colors of a mutual exception pair

For a mutual exception pair `{u, v}` a color is *bad* if the selected column of
that color at `u` or at `v` is impure.  The pair equation writes
`E_c - s_c M` as a rank-one matrix, so the pencil lemmas give:

* at most two bad colors;
* an impure column supported at a single coordinate `k` confines the bad
  colors to `{c, k}`;
* a pair with two bad colors is of exchange type, or each bad color has a
  selected column with two nonzero coordinates.

A column with two nonzero coordinates is never selected back by its anchor, so
its anchor is an unpaired vertex pointing to the pair.
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

/-- A vector with two nonzero coordinates. -/
def Multi (a : Fin n → K) : Prop :=
  ∃ i i', i ≠ i' ∧ a i ≠ 0 ∧ a i' ≠ 0

theorem pure_of_rank_one (c : Fin n) (a b : Fin n → K)
    (h : ∀ i j, (unitE c i j : K) = a i * b j) : PureAt a c ∧ PureAt b c := by
  have hcc := h c c
  simp only [unitE, and_self, ite_true] at hcc
  have ha : a c ≠ 0 := left_ne_zero_of_mul (by rw [← hcc]; exact one_ne_zero)
  have hb : b c ≠ 0 := right_ne_zero_of_mul (by rw [← hcc]; exact one_ne_zero)
  constructor
  · intro i hi
    have := h i c
    simp only [unitE, hi, false_and, ite_false] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hb
  · intro j hj
    have := h c j
    simp only [unitE, hj, and_false, ite_false] at this
    exact (mul_eq_zero.mp this.symm).resolve_left ha

theorem multi_of_two (a : Fin n → K) (c d : Fin n) (hcd : c ≠ d) (hc : a c ≠ 0)
    (hd : a d ≠ 0) : Multi a :=
  ⟨c, d, hcd, hc, hd⟩

section Pair

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

/-- Bad colors of the pair of `u`. -/
noncomputable def badP (u : Fin (n + 2)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c =>
    ¬ PureAt (colA W hW u c) c ∨ ¬ PureAt (colA W hW (exc W hW u) c) c)

theorem mem_badP (u : Fin (n + 2)) (c : Fin n) :
    c ∈ badP W hW u ↔
      ¬ PureAt (colA W hW u c) c ∨ ¬ PureAt (colA W hW (exc W hW u) c) c := by
  classical
  unfold badP
  simp

theorem badP_exc (u : Fin (n + 2)) (hu : Paired W hW u) : badP W hW (exc W hW u) = badP W hW u := by
  ext c
  rw [mem_badP, mem_badP, hu]
  exact Or.comm

/-- The pair coefficient. -/
noncomputable def tP (u : Fin (n + 2)) (c : Fin n) : K := by
  classical
  exact if anchor W hW (exc W hW u) c = anchor W hW u c then 0 else tT W hW u c

/-- The pair equation in pencil form. -/
theorem pencil_eq (u : Fin (n + 2)) (hu : Paired W hW u) (c i j : Fin n) :
    (unitE c i j : K) = sS W hW u c * orderedWeight W u (exc W hW u) i j +
      (colA W hW u c i * tP W hW u c) * colA W hW (exc W hW u) c j := by
  classical
  have := pair_eq W hW u hu c i j
  unfold unitE
  rw [← this]
  unfold tP
  split_ifs <;> ring

theorem bad_sS_ne_zero (u : Fin (n + 2)) (hu : Paired W hW u) (c : Fin n)
    (hc : c ∈ badP W hW u) : sS W hW u c ≠ 0 := by
  intro hs
  have h : ∀ i j, (unitE c i j : K) =
      (colA W hW u c i * tP W hW u c) * colA W hW (exc W hW u) c j := by
    intro i j
    rw [pencil_eq W hW u hu c i j, hs, zero_mul, zero_add]
  obtain ⟨hA, hB⟩ := pure_of_rank_one c _ _ h
  rcases (mem_badP W hW u c).mp hc with hA' | hB'
  · apply hA'
    intro i hi
    have := hA i hi
    have htP : tP W hW u c ≠ 0 := by
      intro ht
      have hcc := h c c
      simp only [unitE, and_self, ite_true, ht, mul_zero, zero_mul] at hcc
      exact one_ne_zero hcc
    exact (mul_eq_zero.mp this).resolve_right htP
  · exact hB' hB

theorem bad_tP_ne_zero (u : Fin (n + 2)) (hu : Paired W hW u) (c : Fin n)
    (hc : c ∈ badP W hW u) : tP W hW u c ≠ 0 := by
  intro ht
  set v := exc W hW u with hv
  have hvu : v ≠ u := exc_ne W hW u
  have hexcv : exc W hW v = u := hu
  have h : ∀ i j, (unitE c i j : K) = sS W hW u c * orderedWeight W u v i j := by
    intro i j
    rw [pencil_eq W hW u hu c i j, ht, mul_zero, zero_mul, add_zero]
  have hs := bad_sS_ne_zero W hW u hu c hc
  have hMcc : orderedWeight W u v c c ≠ 0 := by
    intro h0
    have := h c c
    simp only [unitE, and_self, ite_true, h0, mul_zero] at this
    exact one_ne_zero this
  have hMz : ∀ i j, ¬ (i = c ∧ j = c) → orderedWeight W u v i j = 0 := by
    intro i j hij
    have := h i j
    simp only [unitE, if_neg hij] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hs
  have hApure : PureAt (colA W hW u c) c := by
    apply colA_pure_of_pure_cand W hW u c v
    · refine ⟨hvu, ⟨c, hMcc⟩, ?_⟩
      intro i j hj
      exact hMz i j (fun h => hj h.2)
    · intro i hi
      exact hMz i c (fun h => hi h.1)
  have hBpure : PureAt (colA W hW v c) c := by
    apply colA_pure_of_pure_cand W hW v c u
    · refine ⟨Ne.symm hvu, ⟨c, by rw [ow_swap]; exact hMcc⟩, ?_⟩
      intro i j hj
      rw [ow_swap]
      exact hMz j i (fun h => hj h.1)
    · intro i hi
      show orderedWeight W v u i c = 0
      rw [ow_swap]
      exact hMz c i (fun h => hi h.2)
  rcases (mem_badP W hW u c).mp hc with hA' | hB'
  · exact hA' hApure
  · exact hB' hBpure

/-- The factors of the pencil at a bad color. -/
theorem bad_pencil (u : Fin (n + 2)) (hu : Paired W hW u) (c : Fin n) :
    ∀ i j, (unitE c i j : K) = sS W hW u c * orderedWeight W u (exc W hW u) i j +
      (fun i => colA W hW u c i * tP W hW u c) i * colA W hW (exc W hW u) c j :=
  fun i j => pencil_eq W hW u hu c i j

theorem badP_card_le_two (u : Fin (n + 2)) (hu : Paired W hW u) : (badP W hW u).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, d, hd, f, hf, hcd, hcf, hdf⟩ := Finset.two_lt_card.mp hlt
  have hM := pencil_three (fun i j => orderedWeight W u (exc W hW u) i j) c d f hcd hcf hdf
    (sS W hW u c) (sS W hW u d) (sS W hW u f)
    (bad_sS_ne_zero W hW u hu c hc) (bad_sS_ne_zero W hW u hu d hd)
    (bad_sS_ne_zero W hW u hu f hf)
    _ _ _ _ _ _ (bad_pencil W hW u hu c) (bad_pencil W hW u hu d) (bad_pencil W hW u hu f)
  have h : ∀ i j, (unitE c i j : K) =
      (colA W hW u c i * tP W hW u c) * colA W hW (exc W hW u) c j := by
    intro i j
    rw [pencil_eq W hW u hu c i j]
    have := hM i j
    try simp only at this
    rw [this, mul_zero, zero_add]
  obtain ⟨hA, hB⟩ := pure_of_rank_one c _ _ h
  have htP := bad_tP_ne_zero W hW u hu c hc
  rcases (mem_badP W hW u c).mp hc with hA' | hB'
  · apply hA'
    intro i hi
    exact (mul_eq_zero.mp (hA i hi)).resolve_right htP
  · exact hB' hB

/-- Every pair has a bad color. -/
theorem badP_nonempty (u : Fin (n + 2)) (hu : Paired W hW u) : (badP W hW u).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply pair_not_all_pure W hW u hu
  · intro c
    by_contra h
    have : c ∈ badP W hW u := (mem_badP W hW u c).mpr (Or.inl h)
    rw [hne] at this
    exact Finset.notMem_empty c this
  · intro c
    by_contra h
    have : c ∈ badP W hW u := (mem_badP W hW u c).mpr (Or.inr h)
    rw [hne] at this
    exact Finset.notMem_empty c this

/-- The anchor of `u` for `c` does not select `u` back. -/
def NotRecip (u : Fin (n + 2)) (c : Fin n) : Prop :=
  ∀ d, anchor W hW (anchor W hW u c) d ≠ u

theorem notRecip_of_multi (u : Fin (n + 2)) (c : Fin n) (h : Multi (colA W hW u c)) :
    NotRecip W hW u c := by
  intro d hd
  obtain ⟨i, i', hii, hi, hi'⟩ := h
  have hrow := ow_row_zero_of_anchor_eq W hW hd
  have h1 : i = d := by
    by_contra h1
    exact hi (hrow i c h1)
  have h2 : i' = d := by
    by_contra h2
    exact hi' (hrow i' c h2)
  exact hii (h1.trans h2.symm)

/-- An unreciprocated anchor is an unpaired vertex pointing back. -/
theorem notRecip_np (u : Fin (n + 2)) (c : Fin n) (h : NotRecip W hW u c) :
    ¬ Paired W hW (anchor W hW u c) ∧ exc W hW (anchor W hW u c) = u ∧
      rr W hW (anchor W hW u c) = c := by
  have hexc : exc W hW (anchor W hW u c) = u :=
    exc_eq_of_not_selects W hW _ u (anchor_ne W hW u c) h
  have hnp : ¬ Paired W hW (anchor W hW u c) := by
    unfold Paired
    rw [hexc]
    exact (anchor_ne_exc W hW u c).symm
  refine ⟨hnp, hexc, ?_⟩
  have := anchor_exc_rr W hW _ hnp
  rw [hexc] at this
  exact anchor_injective W hW u this

theorem not_both_notRecip (u : Fin (n + 2)) (c : Fin n) :
    ¬ (NotRecip W hW u c ∧ NotRecip W hW (exc W hW u) c) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hnp1, hexc1, hrr1⟩ := notRecip_np W hW u c h1
  obtain ⟨hnp2, hexc2, hrr2⟩ := notRecip_np W hW _ c h2
  by_cases hxy : anchor W hW u c = anchor W hW (exc W hW u) c
  · rw [hxy, hexc2] at hexc1
    exact exc_ne W hW u hexc1
  · exact np_rr_ne W hW _ _ hnp1 hnp2 hxy (hrr1.trans hrr2.symm)

/-- A reciprocated anchor makes the selected column single-coordinate. -/
theorem colA_single_of_recip (u : Fin (n + 2)) (c k : Fin n)
    (hk : anchor W hW (anchor W hW u c) k = u) :
    ∀ i, i ≠ k → colA W hW u c i = 0 :=
  fun i hi => ow_row_zero_of_anchor_eq W hW hk i c hi

theorem colA_ne_zero_of_single (u : Fin (n + 2)) (c k : Fin n)
    (h : ∀ i, i ≠ k → colA W hW u c i = 0) : colA W hW u c k ≠ 0 := by
  obtain ⟨i, hi⟩ := colA_ne_zero W hW u c
  by_cases hik : i = k
  · rw [← hik]
    exact hi
  · exact absurd (h i hik) hi

/-- If the anchor of `u` for `c` selects `u` with a color `k ≠ c`, the anchor
is paired and `k` is one of its bad colors, supported at `c`. -/
theorem recip_offdiag (u : Fin (n + 2)) (c k : Fin n) (hck : k ≠ c)
    (hk : anchor W hW (anchor W hW u c) k = u) :
    Paired W hW (anchor W hW u c) ∧ k ∈ badP W hW (anchor W hW u c) ∧
      (∀ j, j ≠ c → colA W hW (anchor W hW u c) k j = 0) := by
  set x := anchor W hW u c with hx
  have hsingle := colA_single_of_recip W hW u c k hk
  have hne := colA_ne_zero_of_single W hW u c k hsingle
  have hcol : ∀ j, colA W hW x k j = orderedWeight W u x k j := by
    intro j
    unfold colA
    rw [hk, ow_swap]
  have hxsupp : ∀ j, j ≠ c → colA W hW x k j = 0 := by
    intro j hj
    rw [hcol j]
    exact anchor_col_zero W hW u c k j hj
  have himp : ¬ PureAt (colA W hW x k) k := by
    intro hp
    apply hne
    have := hp c (Ne.symm hck)
    rw [hcol c] at this
    exact this
  have hpaired : Paired W hW x := by
    by_contra hnp
    exact himp (np_pure W hW x hnp k)
  exact ⟨hpaired, (mem_badP W hW x k).mpr (Or.inl himp), hxsupp⟩

/-- A single-coordinate impure column at `c` supported at `k` confines the bad
colors to `{c, k}`. -/
theorem badP_subset_of_single (u : Fin (n + 2)) (hu : Paired W hW u) (c k : Fin n) (hkc : k ≠ c)
    (hsingle : ∀ i, i ≠ k → colA W hW u c i = 0) : badP W hW u ⊆ {c, k} := by
  intro f hf
  have hne := colA_ne_zero_of_single W hW u c k hsingle
  have hcbad : c ∈ badP W hW u := by
    rw [mem_badP]
    left
    intro hp
    exact hne (hp k hkc)
  by_cases hfc : f = c
  · simp [hfc]
  · have h := (pencil_two (fun i j => orderedWeight W u (exc W hW u) i j) c f (Ne.symm hfc)
      (sS W hW u c) (sS W hW u f) (bad_sS_ne_zero W hW u hu c hcbad)
      (bad_sS_ne_zero W hW u hu f hf) _ _ _ _ (bad_pencil W hW u hu c)
      (bad_pencil W hW u hu f)).1
    have hkf : k = f := by
      by_contra hkf
      have := (h k hkc hkf).1
      try simp only at this
      exact mul_ne_zero hne (bad_tP_ne_zero W hW u hu c hcbad) this
    simp [hkf]

/-- The supports of the four factors of a pair with the two bad colors `c, d`. -/
theorem bad_two_support (u : Fin (n + 2)) (hu : Paired W hW u) (c d : Fin n) (hcd : c ≠ d)
    (hc : c ∈ badP W hW u) (hd : d ∈ badP W hW u) :
    (∀ i, i ≠ c → i ≠ d → colA W hW u c i = 0 ∧ colA W hW u d i = 0) ∧
      (∀ j, j ≠ c → j ≠ d →
        colA W hW (exc W hW u) c j = 0 ∧ colA W hW (exc W hW u) d j = 0) := by
  have h := pencil_two (fun i j => orderedWeight W u (exc W hW u) i j) c d hcd
      (sS W hW u c) (sS W hW u d) (bad_sS_ne_zero W hW u hu c hc)
      (bad_sS_ne_zero W hW u hu d hd) _ _ _ _ (bad_pencil W hW u hu c)
      (bad_pencil W hW u hu d)
  have htc := bad_tP_ne_zero W hW u hu c hc
  have htd := bad_tP_ne_zero W hW u hu d hd
  refine ⟨fun i hic hid => ?_, h.2⟩
  obtain ⟨h1, h2⟩ := h.1 i hic hid
  exact ⟨(mul_eq_zero.mp h1).resolve_right htc, (mul_eq_zero.mp h2).resolve_right htd⟩

/-- Exchange type: both factors of each bad color vanish at that color. -/
def ExchP (u : Fin (n + 2)) : Prop :=
  ∀ e ∈ badP W hW u, colA W hW u e e = 0 ∧ colA W hW (exc W hW u) e e = 0

/-- Classification of a pair with two bad colors. -/
theorem pair_classification (u : Fin (n + 2)) (hu : Paired W hW u) (c d : Fin n) (hcd : c ≠ d)
    (hbad : badP W hW u = {c, d}) :
    ExchP W hW u ∨
      ((Multi (colA W hW u c) ∨ Multi (colA W hW (exc W hW u) c)) ∧
        (Multi (colA W hW u d) ∨ Multi (colA W hW (exc W hW u) d))) := by
  have hc : c ∈ badP W hW u := by rw [hbad]; simp
  have hd : d ∈ badP W hW u := by rw [hbad]; simp
  have htc := bad_tP_ne_zero W hW u hu c hc
  have htd := bad_tP_ne_zero W hW u hu d hd
  set v := exc W hW u with hv
  have hsupp := bad_two_support W hW u hu c d hcd hc hd
  have hcBad : (∃ i, i ≠ c ∧ (fun i => colA W hW u c i * tP W hW u c) i ≠ 0) ∨
      (∃ j, j ≠ c ∧ colA W hW v c j ≠ 0) := by
    rcases (mem_badP W hW u c).mp hc with hA | hB
    · left
      unfold PureAt at hA
      push Not at hA
      obtain ⟨i, hi, hne⟩ := hA
      exact ⟨i, hi, mul_ne_zero hne htc⟩
    · right
      unfold PureAt at hB
      push Not at hB
      exact hB
  have hdBad : (∃ i, i ≠ d ∧ (fun i => colA W hW u d i * tP W hW u d) i ≠ 0) ∨
      (∃ j, j ≠ d ∧ colA W hW v d j ≠ 0) := by
    rcases (mem_badP W hW u d).mp hd with hA | hB
    · left
      unfold PureAt at hA
      push Not at hA
      obtain ⟨i, hi, hne⟩ := hA
      exact ⟨i, hi, mul_ne_zero hne htd⟩
    · right
      unfold PureAt at hB
      push Not at hB
      exact hB
  have hNotBoth : ∀ e, ¬ (Multi (colA W hW u e) ∧ Multi (colA W hW v e)) := by
    rintro e ⟨h1, h2⟩
    exact not_both_notRecip W hW u e
      ⟨notRecip_of_multi W hW u e h1, notRecip_of_multi W hW v e h2⟩
  have hcNotBoth : ¬ (((fun i => colA W hW u c i * tP W hW u c) c ≠ 0 ∧
      (fun i => colA W hW u c i * tP W hW u c) d ≠ 0) ∧
      (colA W hW v c c ≠ 0 ∧ colA W hW v c d ≠ 0)) := by
    rintro ⟨⟨h1, h2⟩, h3, h4⟩
    simp only at h1 h2
    exact hNotBoth c ⟨multi_of_two _ c d hcd (left_ne_zero_of_mul h1) (left_ne_zero_of_mul h2),
      multi_of_two _ c d hcd h3 h4⟩
  have hdNotBoth : ¬ (((fun i => colA W hW u d i * tP W hW u d) c ≠ 0 ∧
      (fun i => colA W hW u d i * tP W hW u d) d ≠ 0) ∧
      (colA W hW v d c ≠ 0 ∧ colA W hW v d d ≠ 0)) := by
    rintro ⟨⟨h1, h2⟩, h3, h4⟩
    simp only at h1 h2
    exact hNotBoth d ⟨multi_of_two _ c d hcd (left_ne_zero_of_mul h1) (left_ne_zero_of_mul h2),
      multi_of_two _ c d hcd h3 h4⟩
  rcases pencil_block_classification (fun i j => orderedWeight W u v i j) c d hcd
      (sS W hW u c) (sS W hW u d) (bad_sS_ne_zero W hW u hu c hc)
      (bad_sS_ne_zero W hW u hu d hd) _ _ _ _ (bad_pencil W hW u hu c)
      (bad_pencil W hW u hu d) hcBad hdBad hcNotBoth with h | h
  · left
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro e he
    rw [hbad] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨(mul_eq_zero.mp h1).resolve_right htc, h2⟩
    · exact ⟨(mul_eq_zero.mp h3).resolve_right htd, h4⟩
  · right
    obtain ⟨h1, h2⟩ := h
    constructor
    · rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · exact Or.inl (multi_of_two _ c d hcd (left_ne_zero_of_mul h1)
          (left_ne_zero_of_mul h1'))
      · exact Or.inr (multi_of_two _ c d hcd h1 h1')
    · rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
      · exact Or.inl (multi_of_two _ c d hcd (left_ne_zero_of_mul h2)
          (left_ne_zero_of_mul h2'))
      · exact Or.inr (multi_of_two _ c d hcd h2 h2')

/-- In an exchange pair with bad colors `{c, d}`, the color `d` is a bad color
of another pair whose bad colors lie in `{c, d}`. -/
theorem exch_witness (u : Fin (n + 2)) (hu : Paired W hW u) (c d : Fin n) (hcd : c ≠ d)
    (hbad : badP W hW u = {c, d}) (hexch : ExchP W hW u) :
    ∃ w, Paired W hW w ∧ w ≠ u ∧ w ≠ exc W hW u ∧ d ∈ badP W hW w ∧
      badP W hW w ⊆ {c, d} := by
  have hc : c ∈ badP W hW u := by rw [hbad]; simp
  have hd : d ∈ badP W hW u := by rw [hbad]; simp
  obtain ⟨hAc, hBc⟩ := hexch c hc
  have hsupp := bad_two_support W hW u hu c d hcd hc hd
  -- both selected columns of color `c` are supported at `d`
  have hAsingle : ∀ i, i ≠ d → colA W hW u c i = 0 := by
    intro i hid
    by_cases hic : i = c
    · rw [hic]
      exact hAc
    · exact (hsupp.1 i hic hid).1
  have hBsingle : ∀ i, i ≠ d → colA W hW (exc W hW u) c i = 0 := by
    intro i hid
    by_cases hic : i = c
    · rw [hic]
      exact hBc
    · exact (hsupp.2 i hic hid).1
  -- one of the two edges is reciprocated
  have hrecip : ¬ NotRecip W hW u c ∨ ¬ NotRecip W hW (exc W hW u) c := by
    by_contra h
    push Not at h
    exact not_both_notRecip W hW u c h
  -- treat a root `w` of the pair whose `c`-edge is reciprocated
  have key : ∀ w, (w = u ∨ w = exc W hW u) → ¬ NotRecip W hW w c →
      (∀ i, i ≠ d → colA W hW w c i = 0) →
      ∃ x, Paired W hW x ∧ x ≠ u ∧ x ≠ exc W hW u ∧ d ∈ badP W hW x ∧
        badP W hW x ⊆ {c, d} := by
    intro w hw hnr hsingle
    unfold NotRecip at hnr
    push Not at hnr
    obtain ⟨k, hk⟩ := hnr
    have hkd : k = d := by
      by_contra hkd
      have := colA_ne_zero_of_single W hW w c d hsingle
      exact this (colA_single_of_recip W hW w c k hk d (Ne.symm hkd))
    rw [hkd] at hk
    obtain ⟨hpx, hdx, hxsupp⟩ := recip_offdiag W hW w c d (Ne.symm hcd) hk
    set x := anchor W hW w c with hx
    have hxw : x ≠ w := anchor_ne W hW w c
    have hxe : x ≠ exc W hW w := anchor_ne_exc W hW w c
    refine ⟨x, hpx, ?_, ?_, hdx, ?_⟩
    · rcases hw with rfl | rfl
      · exact hxw
      · rw [hu] at hxe
        exact hxe
    · rcases hw with rfl | rfl
      · exact hxe
      · exact hxw
    · have := badP_subset_of_single W hW x hpx d c hcd hxsupp
      intro e he
      have := this he
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
  rcases hrecip with h | h
  · exact key u (Or.inl rfl) h hAsingle
  · exact key (exc W hW u) (Or.inr rfl) h hBsingle

end Pair

end PPL007General

/- ## Section: `PPL007General.PureAccounting` -/

/-
# The bad-color accounting

Each pair carries at most two bad colors.  A two-color pair of exchange type
whose colors also appear as bad colors of other pairs with smaller or equal
bad sets, and a two-color pair of non-exchange type owns two unpaired vertices.
Then the union of bad colors has at most `|P| + |Q| / 2` elements.
-/

namespace PPL007General
variable {n : Nat} [ValidDim n]

/-- A family of sets of size at most two, indexed by `S`, in which every set is
attained by at least two distinct indices, has a union of size at most `#S`. -/
theorem acct_card_biUnion_le_of_paired {α γ : Type} [DecidableEq γ]
    (S : Finset α) (bad : α → Finset γ)
    (h2 : ∀ p ∈ S, (bad p).card ≤ 2)
    (hpair : ∀ p ∈ S, ∃ p' ∈ S, p' ≠ p ∧ bad p' = bad p) :
    (S.biUnion bad).card ≤ S.card := by
  have hsub : S.biUnion bad ⊆ (S.image bad).biUnion id := by
    intro c hc
    obtain ⟨p, hp, hcp⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨bad p, Finset.mem_image_of_mem bad hp, hcp⟩
  have h3 : ((S.image bad).biUnion id).card ≤ (S.image bad).card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    exact h2 p hp
  have h4 : 2 * (S.image bad).card ≤ S.card := by
    apply Finset.mul_card_image_le_card
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨p', hp', hne, heq⟩ := hpair p hp
    have h5 : 1 < (S.filter (fun a => bad a = bad p)).card :=
      Finset.one_lt_card.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, p', Finset.mem_filter.mpr ⟨hp', heq⟩, hne.symm⟩
    exact h5
  have h6 := Finset.card_le_card hsub
  omega

/-- If every element of `S` owns two distinct elements of `Q`, then
`2 * #S ≤ #Q`. -/
theorem acct_two_mul_card_le_of_owns {α β : Type} [DecidableEq α]
    (S : Finset α) (Q : Finset β) (owner : β → α)
    (hown : ∀ p ∈ S, ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ owner x = p ∧ owner y = p) :
    2 * S.card ≤ Q.card := by
  have h1 : 2 * S.card ≤ (Q.filter (fun x => owner x ∈ S)).card := by
    apply Finset.mul_card_image_le_card_of_maps_to (f := owner)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro p hp
      obtain ⟨x, hx, y, hy, hne, hxp, hyp⟩ := hown p hp
      have hx' : x ∈ (Q.filter (fun x => owner x ∈ S)).filter (fun a => owner a = p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx, by rw [hxp]; exact hp⟩, hxp⟩
      have hy' : y ∈ (Q.filter (fun x => owner x ∈ S)).filter (fun a => owner a = p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hy, by rw [hyp]; exact hp⟩, hyp⟩
      have h5 : 1 < ((Q.filter (fun x => owner x ∈ S)).filter (fun a => owner a = p)).card :=
        Finset.one_lt_card.mpr ⟨x, hx', y, hy', hne⟩
      exact h5
  exact h1.trans (Finset.card_filter_le _ _)

theorem two_mul_card_biUnion_le {α β γ : Type} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ]
    (P : Finset α) (bad : α → Finset γ) (Q : Finset β) (owner : β → α)
    (exch : α → Prop)
    (h2 : ∀ p ∈ P, (bad p).card ≤ 2)
    (hex : ∀ p ∈ P, (bad p).card = 2 → exch p →
      ∀ c ∈ bad p, ∃ p' ∈ P, p' ≠ p ∧ c ∈ bad p' ∧ bad p' ⊆ bad p)
    (hnex : ∀ p ∈ P, (bad p).card = 2 → ¬ exch p →
      ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ owner x = p ∧ owner y = p) :
    2 * (P.biUnion bad).card ≤ 2 * P.card + Q.card := by
  classical
  -- Split `P` into: at most one bad color (`P1`); two bad colors (`R`), the
  -- latter split into shared two-sets (`Qa`) and unshared ones (`R'`); the
  -- unshared ones of non-exchange type form `Qc`.
  obtain ⟨P1, hP1⟩ : ∃ s : Finset α, s = P.filter (fun p => (bad p).card ≤ 1) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ s : Finset α, s = P.filter (fun p => ¬ (bad p).card ≤ 1) := ⟨_, rfl⟩
  obtain ⟨Qa, hQa⟩ : ∃ s : Finset α,
      s = R.filter (fun p => ∃ p' ∈ P, p' ≠ p ∧ bad p' = bad p) := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ s : Finset α,
      s = R.filter (fun p => ¬ ∃ p' ∈ P, p' ≠ p ∧ bad p' = bad p) := ⟨_, rfl⟩
  obtain ⟨Qc, hQc⟩ : ∃ s : Finset α, s = R'.filter (fun p => ¬ exch p) := ⟨_, rfl⟩
  have mP1 : ∀ p, p ∈ P1 ↔ p ∈ P ∧ (bad p).card ≤ 1 := fun p => by
    rw [hP1, Finset.mem_filter]
  have mR : ∀ p, p ∈ R ↔ p ∈ P ∧ ¬ (bad p).card ≤ 1 := fun p => by
    rw [hR, Finset.mem_filter]
  have mQa : ∀ p, p ∈ Qa ↔ p ∈ R ∧ ∃ p' ∈ P, p' ≠ p ∧ bad p' = bad p := fun p => by
    rw [hQa, Finset.mem_filter]
  have mR' : ∀ p, p ∈ R' ↔ p ∈ R ∧ ¬ ∃ p' ∈ P, p' ≠ p ∧ bad p' = bad p := fun p => by
    rw [hR', Finset.mem_filter]
  have mQc : ∀ p, p ∈ Qc ↔ p ∈ R' ∧ ¬ exch p := fun p => by
    rw [hQc, Finset.mem_filter]
  -- Cardinalities of the parts.
  have cP : P1.card + R.card = P.card := by
    rw [hP1, hR]
    exact Finset.card_filter_add_card_filter_not _
  have cR : Qa.card + R'.card = R.card := by
    rw [hQa, hR']
    exact Finset.card_filter_add_card_filter_not _
  have cR' : Qc.card ≤ R'.card := by
    rw [hQc]
    exact Finset.card_filter_le _ _
  -- Every bad color is a bad color of `P1`, `Qa` or `Qc`; the unshared
  -- exchange-type pairs contribute nothing new.
  have hcover : P.biUnion bad ⊆ (P1.biUnion bad ∪ Qa.biUnion bad) ∪ Qc.biUnion bad := by
    intro c hc
    obtain ⟨p, hp, hcp⟩ := Finset.mem_biUnion.mp hc
    by_cases h1 : (bad p).card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨p, (mP1 p).mpr ⟨hp, h1⟩, hcp⟩))
    · have hcard : (bad p).card = 2 := by
        have := h2 p hp
        omega
      have hpR : p ∈ R := (mR p).mpr ⟨hp, h1⟩
      by_cases hsh : ∃ p' ∈ P, p' ≠ p ∧ bad p' = bad p
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨p, (mQa p).mpr ⟨hpR, hsh⟩, hcp⟩))
      · by_cases hx : exch p
        · obtain ⟨p', hp', hne, hcp', hsub⟩ := hex p hp hcard hx c hcp
          have h1' : (bad p').card ≤ 1 := by
            by_contra h1''
            have hcard' : (bad p').card = 2 := by
              have := h2 p' hp'
              omega
            exact hsh ⟨p', hp', hne, Finset.eq_of_subset_of_card_le hsub (by omega)⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨p', (mP1 p').mpr ⟨hp', h1'⟩, hcp'⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨p, (mQc p).mpr ⟨(mR' p).mpr ⟨hpR, hsh⟩, hx⟩, hcp⟩)
  -- Bounds on the three pieces.
  have b1 : (P1.biUnion bad).card ≤ P1.card * 1 := by
    apply Finset.card_biUnion_le_card_mul
    intro p hp
    exact ((mP1 p).mp hp).2
  have b2 : (Qa.biUnion bad).card ≤ Qa.card := by
    apply acct_card_biUnion_le_of_paired
    · intro p hp
      exact h2 p ((mR p).mp ((mQa p).mp hp).1).1
    · intro p hp
      obtain ⟨hpR, p', hp', hne, heq⟩ := (mQa p).mp hp
      have hpR2 := (mR p).mp hpR
      have hp'R : p' ∈ R := by
        refine (mR p').mpr ⟨hp', ?_⟩
        rw [heq]
        exact hpR2.2
      exact ⟨p', (mQa p').mpr ⟨hp'R, p, hpR2.1, hne.symm, heq.symm⟩, hne, heq⟩
  have b3 : (Qc.biUnion bad).card ≤ Qc.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro p hp
    exact h2 p ((mR p).mp ((mR' p).mp ((mQc p).mp hp).1).1).1
  have b4 : 2 * Qc.card ≤ Q.card := by
    apply acct_two_mul_card_le_of_owns Qc Q owner
    intro p hp
    have hpc := (mQc p).mp hp
    have hpR' := (mR' p).mp hpc.1
    have hpP := (mR p).mp hpR'.1
    have hcard : (bad p).card = 2 := by
      have := h2 p hpP.1
      omega
    exact hnex p hpP.1 hcard hpc.2
  have hU := Finset.card_le_card hcover
  have hU1 := Finset.card_union_le (P1.biUnion bad ∪ Qa.biUnion bad) (Qc.biUnion bad)
  have hU2 := Finset.card_union_le (P1.biUnion bad) (Qa.biUnion bad)
  omega

end PPL007General

/- ## Section: `PPL007General.PureInvolution` -/

/-
# Fixed-point-free involutions have even support
-/

namespace PPL007General
variable {n : Nat} [ValidDim n]

theorem card_eq_two_mul_of_involution {α : Type} [LinearOrder α] (T : Finset α)
    (f : α → α) (hmem : ∀ x ∈ T, f x ∈ T) (hinv : ∀ x ∈ T, f (f x) = x)
    (hfix : ∀ x ∈ T, f x ≠ x) :
    T.card = 2 * (T.filter (fun x => x < f x)).card := by
  -- `T` splits into `{x | x < f x}` and `{x | ¬ x < f x}`, and `f` swaps the two parts.
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun x => x < f x)
  have hbij : (T.filter (fun x => x < f x)).card = (T.filter (fun x => ¬ x < f x)).card := by
    refine Finset.card_nbij' f f ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      refine ⟨hmem a ha.1, ?_⟩
      rw [hinv a ha.1]
      exact not_lt.2 ha.2.le
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      refine ⟨hmem a ha.1, ?_⟩
      rw [hinv a ha.1]
      exact lt_of_le_of_ne (not_lt.1 ha.2) (hfix a ha.1)
    · intro a ha
      exact hinv a (Finset.mem_filter.1 ha).1
    · intro a ha
      exact hinv a (Finset.mem_filter.1 ha).1
  omega

theorem even_card_of_involution {α : Type} [LinearOrder α] (T : Finset α)
    (f : α → α) (hmem : ∀ x ∈ T, f x ∈ T) (hinv : ∀ x ∈ T, f (f x) = x)
    (hfix : ∀ x ∈ T, f x ≠ x) : Even T.card := by
  rw [card_eq_two_mul_of_involution T f hmem hinv hfix]
  exact even_two_mul _

end PPL007General

/- ## Section: `PPL007General.Global` -/

/-
# Global accounting and the clean colors

The union `B` of the bad colors of all mutual exception pairs has at most
`q + k / 2 = 5` elements, where `q` is the number of pairs and `k` the number
of unpaired vertices.  Every color outside `B` is *clean*:

* pair edges vanish on clean colors;
* a nonzero entry between clean colors is diagonal;
* for a clean color `c`, the selected edge of color `c` is the only edge at a
  vertex with a nonzero `(c, c)` entry (a parity argument rules out the
  exceptional edge of an unpaired vertex).
-/

open MonochromaticQuantumGraph QuantumCR
open scoped BigOperators

namespace PPL007General
variable {n : Nat} [ValidDim n]

variable {K : Type} [Field K]

section Global

variable (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W)
include hW

/-- Representative of the pair of `u`. -/
noncomputable def rep (u : Fin (n + 2)) : Fin (n + 2) := by
  classical
  exact if u < exc W hW u then u else exc W hW u

/-- Mutual exception pairs, indexed by their smaller vertex. -/
noncomputable def Pairs : Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter (fun u => Paired W hW u ∧ u < exc W hW u)

/-- Unpaired vertices. -/
noncomputable def NP : Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter (fun u => ¬ Paired W hW u)

/-- All bad colors. -/
noncomputable def Bset : Finset (Fin n) := by
  classical
  exact (Pairs W hW).biUnion (badP W hW)

theorem mem_Pairs (u : Fin (n + 2)) : u ∈ Pairs W hW ↔ Paired W hW u ∧ u < exc W hW u := by
  classical
  unfold Pairs
  simp

theorem mem_NP (u : Fin (n + 2)) : u ∈ NP W hW ↔ ¬ Paired W hW u := by
  classical
  unfold NP
  simp

theorem rep_spec (u : Fin (n + 2)) (hu : Paired W hW u) :
    rep W hW u ∈ Pairs W hW ∧ (rep W hW u = u ∨ rep W hW u = exc W hW u) ∧
      badP W hW (rep W hW u) = badP W hW u := by
  classical
  unfold rep
  by_cases hlt : u < exc W hW u
  · rw [if_pos hlt]
    exact ⟨(mem_Pairs W hW u).mpr ⟨hu, hlt⟩, Or.inl rfl, rfl⟩
  · rw [if_neg hlt]
    have hne : exc W hW u ≠ u := exc_ne W hW u
    have hlt' : exc W hW u < u := lt_of_le_of_ne (not_lt.mp hlt) hne
    refine ⟨(mem_Pairs W hW _).mpr ⟨paired_exc W hW u hu, ?_⟩, Or.inr rfl,
      badP_exc W hW u hu⟩
    rw [hu]
    exact hlt'

theorem badP_subset_Bset (u : Fin (n + 2)) (hu : Paired W hW u) : badP W hW u ⊆ Bset W hW := by
  classical
  intro c hc
  obtain ⟨hmem, -, hbad⟩ := rep_spec W hW u hu
  unfold Bset
  rw [Finset.mem_biUnion]
  exact ⟨rep W hW u, hmem, by rw [hbad]; exact hc⟩

theorem card_pairs_np : 2 * (Pairs W hW).card + (NP W hW).card = n + 2 := by
  classical
  set PV := Finset.univ.filter (fun u => Paired W hW u) with hPV
  have h1 : PV.card = 2 * (PV.filter (fun x => x < exc W hW x)).card := by
    apply card_eq_two_mul_of_involution PV (exc W hW)
    · intro x hx
      simp only [hPV, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact paired_exc W hW x hx
    · intro x hx
      simp only [hPV, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    · intro x _
      exact exc_ne W hW x
  have h2 : PV.filter (fun x => x < exc W hW x) = Pairs W hW := by
    ext x
    rw [mem_Pairs]
    simp [hPV]
  have h3 : PV.card + (NP W hW).card = n + 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (n + 2))))
      (p := fun u => Paired W hW u)
    have hNP : NP W hW = Finset.univ.filter (fun u => ¬ Paired W hW u) := by
      ext x
      rw [mem_NP]
      simp
    rw [hNP, hPV]
    simpa using this
  rw [h2] at h1
  omega

theorem two_mul_Bset_card_le : 2 * (Bset W hW).card ≤ n + 2 := by
  classical
  have key := two_mul_card_biUnion_le (Pairs W hW) (badP W hW) (NP W hW)
    (fun x => rep W hW (exc W hW x)) (ExchP W hW)
    (fun p hp => badP_card_le_two W hW p ((mem_Pairs W hW p).mp hp).1)
    ?hex ?hnex
  · have := card_pairs_np W hW
    have hB : (Bset W hW).card = ((Pairs W hW).biUnion (badP W hW)).card := by
      unfold Bset
      rfl
    omega
  case hex =>
    intro p hp hcard hexch e he
    have hpp := ((mem_Pairs W hW p).mp hp).1
    obtain ⟨c₁, c₂, h12, hbad⟩ := Finset.card_eq_two.mp hcard
    have hfind : ∀ c d : Fin n, c ≠ d → badP W hW p = {c, d} →
        ∃ p' ∈ Pairs W hW, p' ≠ p ∧ d ∈ badP W hW p' ∧ badP W hW p' ⊆ badP W hW p := by
      intro c d hcd hcdbad
      obtain ⟨w, hwp, hw1, hw2, hdw, hsub⟩ := exch_witness W hW p hpp c d hcd hcdbad hexch
      obtain ⟨hmem, hrep, hbadrep⟩ := rep_spec W hW w hwp
      refine ⟨rep W hW w, hmem, ?_, by rw [hbadrep]; exact hdw,
        by rw [hbadrep, hcdbad]; exact hsub⟩
      rcases hrep with h | h
      · rw [h]
        exact hw1
      · rw [h]
        intro hwe
        apply hw2
        rw [← hwe, hwp]
    rw [hbad] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hfind c₂ e (Ne.symm h12) (by rw [hbad, Finset.pair_comm])
    · exact hfind c₁ e h12 hbad
  case hnex =>
    intro p hp hcard hexch
    have hpp := ((mem_Pairs W hW p).mp hp).1
    have hplt := ((mem_Pairs W hW p).mp hp).2
    obtain ⟨c₁, c₂, h12, hbad⟩ := Finset.card_eq_two.mp hcard
    rcases pair_classification W hW p hpp c₁ c₂ h12 hbad with hex | ⟨h1, h2⟩
    · exact absurd hex hexch
    · -- a `Multi` column at a root of the pair gives an unpaired witness
      have hwit : ∀ c : Fin n, (Multi (colA W hW p c) ∨ Multi (colA W hW (exc W hW p) c)) →
          ∃ x ∈ NP W hW, rep W hW (exc W hW x) = p ∧ rr W hW x = c := by
        intro c hmulti
        have hrep_p : rep W hW p = p := by
          unfold rep
          rw [if_pos hplt]
        have hrep_e : rep W hW (exc W hW p) = p := by
          unfold rep
          rw [hpp, if_neg (not_lt.mpr (le_of_lt hplt))]
        rcases hmulti with hm | hm
        · obtain ⟨hnp, hexc, hrr⟩ := notRecip_np W hW p c (notRecip_of_multi W hW p c hm)
          exact ⟨anchor W hW p c, (mem_NP W hW _).mpr hnp, by rw [hexc, hrep_p], hrr⟩
        · obtain ⟨hnp, hexc, hrr⟩ :=
            notRecip_np W hW (exc W hW p) c (notRecip_of_multi W hW (exc W hW p) c hm)
          exact ⟨anchor W hW (exc W hW p) c, (mem_NP W hW _).mpr hnp,
            by rw [hexc, hrep_e], hrr⟩
      obtain ⟨x, hx, hxo, hxr⟩ := hwit c₁ h1
      obtain ⟨y, hy, hyo, hyr⟩ := hwit c₂ h2
      refine ⟨x, hx, y, hy, ?_, hxo, hyo⟩
      intro hxy
      apply h12
      rw [← hxr, ← hyr, hxy]

/-- Pair edges vanish on colors outside `Bset`. -/
theorem pair_edge_zero (u : Fin (n + 2)) (hu : Paired W hW u) (i j : Fin n)
    (hi : i ∉ Bset W hW) (hj : j ∉ Bset W hW) : orderedWeight W u (exc W hW u) i j = 0 := by
  obtain ⟨c, hc⟩ := badP_nonempty W hW u hu
  have hcB : c ∈ Bset W hW := badP_subset_Bset W hW u hu hc
  have hic : i ≠ c := fun h => hi (h ▸ hcB)
  have heq := pencil_eq W hW u hu c i j
  simp only [unitE, hic, false_and, ite_false] at heq
  -- a reciprocated edge of color `c` at a root `w` of the pair has its
  -- support inside `Bset`
  have hrecB : ∀ w, Paired W hW w → badP W hW w ⊆ Bset W hW → ∀ k,
      anchor W hW (anchor W hW w c) k = w → c ∈ Bset W hW → k ∈ Bset W hW := by
    intro w _ _ k hk hc'
    by_cases hkc : k = c
    · rw [hkc]
      exact hc'
    · obtain ⟨hpx, hkx, -⟩ := recip_offdiag W hW w c k hkc hk
      exact badP_subset_Bset W hW _ hpx hkx
  have hprod : (colA W hW u c i * tP W hW u c) * colA W hW (exc W hW u) c j = 0 := by
    rcases not_and_or.mp (not_both_notRecip W hW u c) with h | h
    · unfold NotRecip at h
      push Not at h
      obtain ⟨k, hk⟩ := h
      have hkB := hrecB u hu (badP_subset_Bset W hW u hu) k hk hcB
      have hik : i ≠ k := fun h => hi (h ▸ hkB)
      rw [colA_single_of_recip W hW u c k hk i hik]
      ring
    · unfold NotRecip at h
      push Not at h
      obtain ⟨k, hk⟩ := h
      have hv := paired_exc W hW u hu
      have hkB := hrecB (exc W hW u) hv (badP_subset_Bset W hW _ hv) k hk hcB
      have hjk : j ≠ k := fun h => hj (h ▸ hkB)
      rw [colA_single_of_recip W hW (exc W hW u) c k hk j hjk]
      ring
  rw [hprod, add_zero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (bad_sS_ne_zero W hW u hu c hc)

/-- A clean column is pure, so its diagonal entry is nonzero. -/
theorem clean_pure (w : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW) :
    PureAt (colA W hW w c) c := by
  by_cases hw : Paired W hW w
  · by_contra himp
    exact hc (badP_subset_Bset W hW w hw ((mem_badP W hW w c).mpr (Or.inl himp)))
  · exact np_pure W hW w hw c

theorem clean_edge_ne_zero (w : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW) :
    orderedWeight W w (anchor W hW w c) c c ≠ 0 :=
  colA_self_ne_zero_of_pure W hW w c (clean_pure W hW w c hc)

/-- Directed version of diagonality on clean colors. -/
theorem clean_diag_of_anchor (u : Fin (n + 2)) (d i j : Fin n)
    (hj : j ∉ Bset W hW) (hne : orderedWeight W u (anchor W hW u d) i j ≠ 0) : i = j := by
  set y := anchor W hW u d with hy
  have hjd : j = d := by
    by_contra h
    exact hne (anchor_col_zero W hW u d i j h)
  subst hjd
  by_cases hrec : ∃ k, anchor W hW y k = u
  · obtain ⟨k, hk⟩ := hrec
    have hik : i = k := by
      by_contra h
      exact hne (ow_row_zero_of_anchor_eq W hW hk i j h)
    subst hik
    by_contra hij
    obtain ⟨hpy, hiy, -⟩ := recip_offdiag W hW u j i hij hk
    -- the column of color `j` at `u` is impure: `u` is paired and `j` is bad
    have hsingle := colA_single_of_recip W hW u j i hk
    have hne' := colA_ne_zero_of_single W hW u j i hsingle
    have himp : ¬ PureAt (colA W hW u j) j := fun hp => hne' (hp i hij)
    have hup : Paired W hW u := by
      by_contra hnp
      exact himp (np_pure W hW u hnp j)
    exact hj (badP_subset_Bset W hW u hup ((mem_badP W hW u j).mpr (Or.inl himp)))
  · push Not at hrec
    obtain ⟨hnp, hexc, hrr⟩ := notRecip_np W hW u j hrec
    have hup : Paired W hW u := by
      have := np_exc_paired W hW y hnp
      rw [hexc] at this
      exact this
    have hpure : PureAt (colA W hW u j) j := by
      by_contra himp
      exact hj (badP_subset_Bset W hW u hup ((mem_badP W hW u j).mpr (Or.inl himp)))
    by_contra hij
    exact hne (hpure i hij)

/-- A nonzero entry between clean colors is diagonal. -/
theorem clean_diag (u y : Fin (n + 2)) (i j : Fin n) (hi : i ∉ Bset W hW) (hj : j ∉ Bset W hW)
    (hne : orderedWeight W u y i j ≠ 0) : i = j := by
  have hyu : y ≠ u := by
    intro h
    rw [h] at hne
    exact hne (ow_self W u i j)
  by_cases hye : y = exc W hW u
  · by_cases hue : u = exc W hW y
    · exfalso
      have hp : Paired W hW u := by
        unfold Paired
        rw [← hye, ← hue]
      rw [hye] at hne
      exact hne (pair_edge_zero W hW u hp i j hi hj)
    · obtain ⟨d, hd⟩ := exists_anchor_eq W hW y u (Ne.symm hyu) hue
      rw [ow_swap, ← hd] at hne
      exact (clean_diag_of_anchor W hW y d j i hi hne).symm
  · obtain ⟨d, hd⟩ := exists_anchor_eq W hW u y hyu hye
    rw [← hd] at hne
    exact clean_diag_of_anchor W hW u d i j hj hne

/-- The `(c, c)`-neighbors of a vertex for a clean color `c`. -/
theorem clean_neighbors (w y : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW)
    (hne : orderedWeight W w y c c ≠ 0) :
    y = anchor W hW w c ∨ (¬ Paired W hW w ∧ rr W hW w = c ∧ y = exc W hW w) := by
  have hyw : y ≠ w := by
    intro h
    rw [h] at hne
    exact hne (ow_self W w c c)
  by_cases hye : y = exc W hW w
  · by_cases hw : Paired W hW w
    · exfalso
      rw [hye] at hne
      exact hne (pair_edge_zero W hW w hw c c hc hc)
    · right
      refine ⟨hw, ?_, hye⟩
      by_contra hr
      rw [hye] at hne
      exact hne (exc_row_zero W hW w hw c c (Ne.symm hr))
  · left
    obtain ⟨d, hd⟩ := exists_anchor_eq W hW w y hyw hye
    have hdc : d = c := by
      by_contra h
      rw [← hd] at hne
      exact hne (anchor_col_zero W hW w d c c (Ne.symm h))
    rw [← hd, hdc]

/-- Parity: the exceptional edge of an unpaired vertex never carries a clean
diagonal entry. -/
theorem clean_no_loop (w₀ : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW)
    (hw₀ : ¬ Paired W hW w₀) (hne : orderedWeight W w₀ (exc W hW w₀) c c ≠ 0) : False := by
  classical
  have hrr : rr W hW w₀ = c := by
    by_contra hr
    exact hne (exc_row_zero W hW w₀ hw₀ c c (Ne.symm hr))
  set a := anchor W hW w₀ c with ha
  set b := exc W hW w₀ with hb
  have haw : a ≠ w₀ := anchor_ne W hW w₀ c
  have hbw : b ≠ w₀ := exc_ne W hW w₀
  have hab : a ≠ b := anchor_ne_exc W hW w₀ c
  -- vertices other than `w₀` have a unique `(c, c)`-neighbor
  have huniq : ∀ z y, z ≠ w₀ → orderedWeight W z y c c ≠ 0 → y = anchor W hW z c := by
    intro z y hz hzy
    rcases clean_neighbors W hW z y c hc hzy with h | ⟨hnp, hrz, -⟩
    · exact h
    · exfalso
      exact np_rr_ne W hW z w₀ hnp hw₀ hz (hrz.trans hrr.symm)
  have hsym : ∀ z y, orderedWeight W z y c c ≠ 0 → orderedWeight W y z c c ≠ 0 := by
    intro z y h
    rw [ow_swap]
    exact h
  set T := ((Finset.univ.erase w₀).erase a).erase b with hT
  have hTmem : ∀ z, z ∈ T ↔ z ≠ w₀ ∧ z ≠ a ∧ z ≠ b := by
    intro z
    simp only [hT, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have hTcard : T.card = n - 1 := by
    have hge := ValidDim.ge_eight (n := n)
    rw [hT, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
    · simp only [Finset.card_univ, Fintype.card_fin]
      omega
    · exact Finset.mem_univ _
    · exact Finset.mem_erase.mpr ⟨haw, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_erase.mpr ⟨hbw, Finset.mem_univ _⟩⟩
  set f := fun z => anchor W hW z c with hf
  have hedge : ∀ z, orderedWeight W z (f z) c c ≠ 0 := fun z => clean_edge_ne_zero W hW z c hc
  have hmem : ∀ z ∈ T, f z ∈ T := by
    intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := (hTmem z).mp hz
    refine (hTmem _).mpr ⟨?_, ?_, ?_⟩
    · intro h
      have h1 := hsym z (f z) (hedge z)
      rw [h] at h1
      rcases clean_neighbors W hW w₀ z c hc h1 with h2 | ⟨-, -, h2⟩
      · exact hz2 h2
      · exact hz3 h2
    · intro h
      have h1 := hsym z (f z) (hedge z)
      rw [h] at h1
      have h2 := huniq a z haw h1
      have h3 := huniq a w₀ haw (hsym w₀ a (hedge w₀))
      exact hz1 (h2.trans h3.symm)
    · intro h
      have h1 := hsym z (f z) (hedge z)
      rw [h] at h1
      have h2 := huniq b z hbw h1
      have h3 := huniq b w₀ hbw (hsym w₀ b hne)
      exact hz1 (h2.trans h3.symm)
  have hinv : ∀ z ∈ T, f (f z) = z := by
    intro z hz
    have hfz : f z ∈ T := hmem z hz
    exact (huniq (f z) z ((hTmem _).mp hfz).1 (hsym z (f z) (hedge z))).symm
  have hfix : ∀ z ∈ T, f z ≠ z := fun z _ => anchor_ne W hW z c
  have heven := even_card_of_involution T f hmem hinv hfix
  rw [hTcard] at heven
  have hge := ValidDim.ge_eight (n := n)
  rcases ValidDim.even (n := n) with ⟨k, hk⟩
  rcases heven with ⟨j, hj⟩
  omega

/-- For a clean color the selected edge is the unique `(c, c)`-edge. -/
theorem clean_unique (w y : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW)
    (hne : orderedWeight W w y c c ≠ 0) : y = anchor W hW w c := by
  rcases clean_neighbors W hW w y c hc hne with h | ⟨hnp, -, hy⟩
  · exact h
  · exfalso
    rw [hy] at hne
    exact clean_no_loop W hW w c hc hnp hne

theorem clean_involutive (w : Fin (n + 2)) (c : Fin n) (hc : c ∉ Bset W hW) :
    anchor W hW (anchor W hW w c) c = w := by
  have h := clean_edge_ne_zero W hW w c hc
  rw [ow_swap] at h
  exact (clean_unique W hW _ w c hc h).symm

end Global

end PPL007General


/-!
## Section: General Bogdanov's Lemma for ALL Even `N ≥ 6`

For any even `N ≥ 6` (covering **both** `N ≡ 2 (mod 4)` and `N ≡ 0 (mod 4)`!) and any
three pairwise disjoint fixed-point-free involutions `R, B, G` on `Fin N`, there exists a
non-constant coloring `τ : Fin N → Fin 3` that is invariant under `v ↦ m (τ v) v`.
-/

namespace PPL007General

section GeneralBogdanov

private def bg_s {N : Nat} (R B : Fin N → Fin N) (v : Fin N) : Fin N := B (R v)

private theorem bg_s_inj {N : Nat} (R B : Fin N → Fin N)
    (hR : ∀ v, R (R v) = v) (hB : ∀ v, B (B v) = v) :
    Function.Injective (bg_s R B) := by
  intro a b h
  have h1 : B (B (R a)) = B (B (R b)) := congrArg B h
  rw [hB, hB] at h1
  have h2 : R (R a) = R (R b) := congrArg R h1
  rwa [hR, hR] at h2

private theorem bg_iter_conj {N : Nat} (R B : Fin N → Fin N)
    (hR : ∀ v, R (R v) = v) (hB : ∀ v, B (B v) = v) :
    ∀ k v, (bg_s R B)^[k] (R ((bg_s R B)^[k] v)) = R v := by
  intro k
  induction k with
  | zero => intro v; rfl
  | succ k ih =>
    intro v
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    have hstep : bg_s R B (R (bg_s R B ((bg_s R B)^[k] v))) = R ((bg_s R B)^[k] v) := by
      simp only [bg_s, hR, hB]
    rw [hstep]
    exact ih v

private theorem bg_orbit_disj {N : Nat} (R B : Fin N → Fin N)
    (hR : ∀ v, R (R v) = v) (hB : ∀ v, B (B v) = v)
    (hRne : ∀ v, R v ≠ v) (hBne : ∀ v, B v ≠ v)
    (v0 : Fin N) (i j : Nat) :
    (bg_s R B)^[i] v0 ≠ R ((bg_s R B)^[j] v0) := by
  intro h
  have hs := bg_s_inj R B hR hB
  have h1 : (bg_s R B)^[j + i] v0 = R v0 := by
    rw [Function.iterate_add_apply, h, bg_iter_conj R B hR hB j v0]
  rcases Nat.even_or_odd (j + i) with ⟨q, hq⟩ | ⟨q, hq⟩
  · have h2 : (bg_s R B)^[q] ((bg_s R B)^[q] v0) = (bg_s R B)^[q] (R ((bg_s R B)^[q] v0)) := by
      rw [← Function.iterate_add_apply, ← hq, h1, bg_iter_conj R B hR hB q v0]
    exact hRne _ (hs.iterate q h2).symm
  · have h2 : (bg_s R B)^[q] (bg_s R B ((bg_s R B)^[q] v0)) =
        (bg_s R B)^[q] (R ((bg_s R B)^[q] v0)) := by
      rw [← Function.iterate_succ_apply' (bg_s R B) q v0, ← Function.iterate_add_apply]
      have hq' : q + (q + 1) = j + i := by omega
      rw [hq', h1, bg_iter_conj R B hR hB q v0]
    have h3 : B (R ((bg_s R B)^[q] v0)) = R ((bg_s R B)^[q] v0) := hs.iterate q h2
    exact hBne _ h3

private theorem bg_period {N : Nat} (f : Fin N → Fin N) (hf : Function.Injective f) (v0 : Fin N) :
    ∃ c, 0 < c ∧ f^[c] v0 = v0 ∧ ∀ k, 0 < k → k < c → f^[k] v0 ≠ v0 := by
  classical
  have hex : ∃ k, 0 < k ∧ f^[k] v0 = v0 := by
    have hcard : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by simp
    obtain ⟨a, b, hab, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (N + 1) => f^[i.val] v0) hcard
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · refine ⟨b.val - a.val, by omega, ?_⟩
      apply hf.iterate a.val
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt)]
      exact heq.symm
    · refine ⟨a.val - b.val, by omega, ?_⟩
      apply hf.iterate b.val
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hgt)]
      exact heq
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro k hkpos hklt hfk
  exact Nat.find_min hex hklt ⟨hkpos, hfk⟩

private theorem bg_iter_mod {α : Type*} (f : α → α) (v0 : α) (c : Nat) (hfc : f^[c] v0 = v0) :
    ∀ k, f^[k % c] v0 = f^[k] v0 := by
  intro k
  have hmul : ∀ q, f^[c * q + k % c] v0 = f^[k % c] v0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have : c * (q + 1) + k % c = (c * q + k % c) + c := by ring
      rw [this, Function.iterate_add_apply, hfc, ih]
  conv_rhs => rw [← Nat.div_add_mod k c]
  exact (hmul (k / c)).symm

private def bg_r0 (N : Nat) (hNeven : Even N) (p : Fin N) : Fin N :=
  ⟨if p.val % 2 = 0 then p.val + 1 else p.val - 1, by
    rcases hNeven with ⟨m, hm⟩
    have hp := p.isLt
    split_ifs <;> omega⟩

private def bg_b0 (N : Nat) (hN : 2 ≤ N) (p : Fin N) : Fin N :=
  ⟨if p.val % 2 = 1 then (p.val + 1) % N else (p.val + N - 1) % N, by
    split_ifs <;> exact Nat.mod_lt _ (by omega)⟩

private theorem bg_r0_inv (N : Nat) (hNeven : Even N) (p : Fin N) :
    bg_r0 N hNeven (bg_r0 N hNeven p) = p := by
  ext
  simp only [bg_r0]
  rcases hNeven with ⟨m, hm⟩
  have hp := p.isLt
  split_ifs <;> omega

private theorem bg_b0_inv (N : Nat) (hN : 2 ≤ N) (hNeven : Even N) (p : Fin N) :
    bg_b0 N hN (bg_b0 N hN p) = p := by
  ext
  simp only [bg_b0]
  rcases hNeven with ⟨m, hm⟩
  have hp := p.isLt
  by_cases h1 : p.val % 2 = 1
  · simp only [h1, ↓reduceIte]
    by_cases hlast : p.val + 1 = N
    · have hmod0 : (p.val + 1) % N = 0 := by rw [hlast, Nat.mod_self]
      rw [hmod0]
      simp only [Nat.zero_mod, zero_ne_one, ↓reduceIte, zero_add]
      have hmodN1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmodN1]; omega
    · have hmodp1 : (p.val + 1) % N = p.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmodp1]
      have h2 : (p.val + 1) % 2 ≠ 1 := by omega
      simp only [h2, ↓reduceIte]
      have : p.val + 1 + N - 1 = p.val + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  · simp only [h1, ↓reduceIte]
    by_cases h0 : p.val = 0
    · rw [h0, zero_add]
      have hmodN1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmodN1]
      have h2 : (N - 1) % 2 = 1 := by omega
      simp only [h2, ↓reduceIte]
      have : N - 1 + 1 = N := by omega
      rw [this, Nat.mod_self]
    · have hmodpm1 : (p.val + N - 1) % N = p.val - 1 := by
        have e1 : p.val + N - 1 = (p.val - 1) + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmodpm1]
      have h2 : (p.val - 1) % 2 = 1 := by omega
      simp only [h2, ↓reduceIte]
      have h3 : p.val - 1 + 1 = p.val := by omega
      rw [h3, Nat.mod_eq_of_lt hp]

private def bg_fwd {N : Nat} (u v : Fin N) : Nat := (v.val + N - u.val) % N

private theorem bg_fwd_lt {N : Nat} (hN : 0 < N) (u v : Fin N) : bg_fwd u v < N :=
  Nat.mod_lt _ hN

private theorem bg_fwd_eq_zero_iff {N : Nat} (u v : Fin N) : bg_fwd u v = 0 ↔ u = v := by
  constructor
  · intro h
    ext
    unfold bg_fwd at h
    have hu := u.isLt; have hv := v.isLt
    by_cases hle : u.val ≤ v.val
    · have e1 : (v.val + N - u.val) % N = v.val - u.val := by
        have : v.val + N - u.val = (v.val - u.val) + N := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have e1 : (v.val + N - u.val) % N = v.val + N - u.val := Nat.mod_eq_of_lt (by omega)
      omega
  · rintro rfl
    unfold bg_fwd
    have hu := u.isLt
    have : u.val + N - u.val = N := by omega
    rw [this, Nat.mod_self]

private theorem bg_fwd_inj {N : Nat} (p u v : Fin N) (h : bg_fwd p u = bg_fwd p v) : u = v := by
  ext
  unfold bg_fwd at h
  have hp := p.isLt; have hu := u.isLt; have hv := v.isLt
  have eu : (u.val + N - p.val) % N = if p.val ≤ u.val then u.val - p.val else u.val + N - p.val := by
    split_ifs with hle
    · have : u.val + N - p.val = (u.val - p.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have ev : (v.val + N - p.val) % N = if p.val ≤ v.val then v.val - p.val else v.val + N - p.val := by
    split_ifs with hle
    · have : v.val + N - p.val = (v.val - p.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [eu, ev] at h
  split_ifs at h <;> omega

private theorem bg_fwd_add_symm {N : Nat} (u v : Fin N) (huv : u ≠ v) :
    bg_fwd u v + bg_fwd v u = N := by
  have hval : u.val ≠ v.val := Fin.val_ne_of_ne huv
  have hu := u.isLt; have hv := v.isLt
  unfold bg_fwd
  by_cases hlt : u.val < v.val
  · have e1 : (v.val + N - u.val) % N = v.val - u.val := by
      have : v.val + N - u.val = (v.val - u.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (u.val + N - v.val) % N = u.val + N - v.val := Nat.mod_eq_of_lt (by omega)
    omega
  · have e1 : (v.val + N - u.val) % N = v.val + N - u.val := Nat.mod_eq_of_lt (by omega)
    have e2 : (u.val + N - v.val) % N = u.val - v.val := by
      have : u.val + N - v.val = (u.val - v.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem bg_fwd_mod_two {N : Nat} (hNeven : Even N) (u v : Fin N) :
    bg_fwd u v % 2 = (v.val + u.val) % 2 := by
  rcases hNeven with ⟨m, hm⟩
  have hu := u.isLt; have hv := v.isLt
  unfold bg_fwd
  by_cases hle : u.val ≤ v.val
  · have e1 : (v.val + N - u.val) % N = v.val - u.val := by
      have : v.val + N - u.val = (v.val - u.val) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1]; omega
  · have e1 : (v.val + N - u.val) % N = v.val + N - u.val := Nat.mod_eq_of_lt (by omega)
    rw [e1]; omega

private theorem bg_fwd_val {N : Nat} (u v : Fin N) :
    bg_fwd u v = if u.val ≤ v.val then v.val - u.val else v.val + N - u.val := by
  have hu := u.isLt; have hv := v.isLt
  unfold bg_fwd
  split_ifs with hle
  · have : v.val + N - u.val = (v.val - u.val) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem bg_fwd_succ_mod {N : Nat} (hN : 2 ≤ N) (p q : Fin N) :
    bg_fwd p ⟨(q.val + 1) % N, Nat.mod_lt _ (by omega)⟩ = (bg_fwd p q + 1) % N := by
  have hp := p.isLt; have hq := q.isLt
  have hL := bg_fwd_val p ⟨(q.val + 1) % N, Nat.mod_lt _ (by omega)⟩
  have hR := bg_fwd_val p q
  rw [hL, hR]; dsimp only
  by_cases hq1 : q.val + 1 = N
  · have hmod0 : (q.val + 1) % N = 0 := by rw [hq1, Nat.mod_self]
    simp only [hmod0]
    by_cases hp0 : p.val = 0
    · simp only [hp0, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
      rw [hq1, Nat.mod_self]
    · have hle : p.val ≤ q.val := by omega
      have hnle : ¬ p.val ≤ 0 := by omega
      simp only [hle, hnle, ↓reduceIte]
      have e1 : q.val - p.val + 1 = N - p.val := by omega
      rw [e1, Nat.mod_eq_of_lt (by omega)]; omega
  · have hmodq1 : (q.val + 1) % N = q.val + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hmodq1]
    by_cases hle : p.val ≤ q.val
    · have hle1 : p.val ≤ q.val + 1 := by omega
      simp only [hle, hle1, ↓reduceIte]
      have e1 : q.val - p.val + 1 = q.val + 1 - p.val := by omega
      rw [e1, Nat.mod_eq_of_lt (by omega)]
    · by_cases hpeq : q.val + 1 = p.val
      · have hle1 : p.val ≤ q.val + 1 := by omega
        simp only [hle, hle1, ↓reduceIte]
        have e1 : q.val + N - p.val + 1 = N := by omega
        rw [e1, Nat.mod_self]; omega
      · have hnle1 : ¬ p.val ≤ q.val + 1 := by omega
        simp only [hle, hnle1, ↓reduceIte]
        have e1 : q.val + N - p.val + 1 = q.val + 1 + N - p.val := by omega
        rw [e1, Nat.mod_eq_of_lt (by omega)]

private theorem bg_fwd_pred_mod {N : Nat} (hN : 2 ≤ N) (p q : Fin N) :
    bg_fwd p ⟨(q.val + N - 1) % N, Nat.mod_lt _ (by omega)⟩ = (bg_fwd p q + N - 1) % N := by
  have hp := p.isLt; have hq := q.isLt
  have hL := bg_fwd_val p ⟨(q.val + N - 1) % N, Nat.mod_lt _ (by omega)⟩
  have hR := bg_fwd_val p q
  rw [hL, hR]; dsimp only
  by_cases hq0 : q.val = 0
  · have hmodN1 : (q.val + N - 1) % N = N - 1 := by
      rw [hq0, zero_add]; exact Nat.mod_eq_of_lt (by omega)
    simp only [hmodN1]
    have hle1 : p.val ≤ N - 1 := by omega
    by_cases hp0 : p.val = 0
    · have hle0 : p.val ≤ q.val := by omega
      rw [if_pos hle1, if_pos hle0, hq0, hp0, Nat.sub_zero, Nat.sub_zero, zero_add]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · have hnle0 : ¬ p.val ≤ q.val := by omega
      rw [if_pos hle1, if_neg hnle0, hq0, zero_add]
      have e1 : N - p.val + N - 1 = (N - 1 - p.val) + N := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have hmodqm1 : (q.val + N - 1) % N = q.val - 1 := by
      have e1 : q.val + N - 1 = (q.val - 1) + N := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [hmodqm1]
    by_cases hle : p.val ≤ q.val - 1
    · have hle0 : p.val ≤ q.val := by omega
      rw [if_pos hle, if_pos hle0]
      have e1 : q.val - p.val + N - 1 = (q.val - 1 - p.val) + N := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · by_cases hpeq : p.val = q.val
      · have hle0 : p.val ≤ q.val := by omega
        rw [if_neg hle, if_pos hle0, hpeq, Nat.sub_self, zero_add]
        have e1 : q.val - 1 + N - q.val = N - 1 := by omega
        rw [e1, Nat.mod_eq_of_lt (by omega)]
      · have hnle0 : ¬ p.val ≤ q.val := by omega
        rw [if_neg hle, if_neg hnle0]
        have e1 : q.val + N - p.val + N - 1 = (q.val - 1 + N - p.val) + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem bg_fwd_from_succ {N : Nat} (hN : 2 ≤ N) (p w : Fin N)
    (h1 : 1 ≤ bg_fwd p w) :
    bg_fwd ⟨(p.val + 1) % N, Nat.mod_lt _ (by omega)⟩ w = bg_fwd p w - 1 := by
  have hp := p.isLt; have hw := w.isLt
  have hL := bg_fwd_val ⟨(p.val + 1) % N, Nat.mod_lt _ (by omega)⟩ w
  have hR := bg_fwd_val p w
  rw [hR] at h1
  rw [hL, hR]; dsimp only
  by_cases hp1 : p.val + 1 = N
  · have hmod0 : (p.val + 1) % N = 0 := by rw [hp1, Nat.mod_self]
    simp only [hmod0]
    split_ifs at h1 ⊢ <;> omega
  · have hmodp1 : (p.val + 1) % N = p.val + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hmodp1]
    split_ifs at h1 ⊢ <;> omega

/-- **General Bogdanov's Lemma (all even `N ≥ 6`)**:
Three pairwise disjoint fixed-point-free involutions on `Fin N` (`6 ≤ N`, `Even N`)
always admit a non-constant 3-coloring `τ` invariant under `v ↦ m (τ v) v`. -/
theorem exists_mixed_matching_general {N : Nat} (hN6 : 6 ≤ N) (hNeven : Even N)
    (m : Fin 3 → Fin N → Fin N)
    (hinv : ∀ k v, m k (m k v) = v)
    (hfix : ∀ k v, m k v ≠ v)
    (hdisj : ∀ k l v, k ≠ l → m k v ≠ m l v) :
    ∃ τ : Fin N → Fin 3,
      (∀ v, τ (m (τ v) v) = τ v) ∧ ∃ v₁ v₂, τ v₁ ≠ τ v₂ := by
  classical
  set R := m 0 with hRdef
  set B := m 1 with hBdef
  set G := m 2 with hGdef
  have hR : ∀ v, R (R v) = v := hinv 0
  have hB : ∀ v, B (B v) = v := hinv 1
  have hG : ∀ v, G (G v) = v := hinv 2
  have hRne : ∀ v, R v ≠ v := hfix 0
  have hBne : ∀ v, B v ≠ v := hfix 1
  have hGne : ∀ v, G v ≠ v := hfix 2
  have hRB : ∀ v, R v ≠ B v := fun v => hdisj 0 1 v (by decide)
  have hRG : ∀ v, R v ≠ G v := fun v => hdisj 0 2 v (by decide)
  have hBG : ∀ v, B v ≠ G v := fun v => hdisj 1 2 v (by decide)
  set s := bg_s R B with hsdef
  have hs_inj : Function.Injective s := bg_s_inj R B hR hB
  set v0 : Fin N := ⟨0, by omega⟩
  obtain ⟨c, hcpos, hsc, hcmin⟩ := bg_period s hs_inj v0
  have hsinj_lt : ∀ i < c, ∀ j < c, s^[i] v0 = s^[j] v0 → i = j := by
    intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h0 : s^[j - i] v0 = v0 := by
        apply hs_inj.iterate i
        rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt)]
        exact heq.symm
      exact hcmin (j - i) (by omega) (by omega) h0
    · have h0 : s^[i - j] v0 = v0 := by
        apply hs_inj.iterate j
        rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hgt)]
        exact heq
      exact hcmin (i - j) (by omega) (by omega) h0
  set O : Finset (Fin N) := (Finset.range c).image (fun k => s^[k] v0) with hOdef
  set H : Finset (Fin N) := O ∪ O.image R with hHdef
  have hO_mem : ∀ v, v ∈ O ↔ ∃ k < c, s^[k] v0 = v := by
    intro v; simp [hOdef]
  have hH_R : ∀ v ∈ H, R v ∈ H := by
    intro v hv
    simp only [hHdef, Finset.mem_union, Finset.mem_image] at hv ⊢
    rcases hv with hO | ⟨u, hu, rfl⟩
    · exact Or.inr ⟨v, hO, rfl⟩
    · rw [hR]; exact Or.inl hu
  have hH_B : ∀ v ∈ H, B v ∈ H := by
    intro v hv
    simp only [hHdef, Finset.mem_union, Finset.mem_image] at hv ⊢
    rcases hv with hO | ⟨u, hu, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := (hO_mem _).mp hO
      refine Or.inr ⟨s^[(k + c - 1) % c] v0, (hO_mem _).mpr ⟨(k + c - 1) % c, Nat.mod_lt _ hcpos, rfl⟩, ?_⟩
      have h1 : B (R (s^[(k + c - 1) % c] v0)) = s^[k] v0 := by
        show s (s^[(k + c - 1) % c] v0) = s^[k] v0
        rw [← Function.iterate_succ_apply' s ((k + c - 1) % c) v0,
          ← bg_iter_mod s v0 c hsc ((k + c - 1) % c + 1)]
        have hmod : ((k + c - 1) % c + 1) % c = k % c := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : k + c - 1 + 1 = k + c := by omega
          rw [this, Nat.add_mod_right]
        rw [hmod, Nat.mod_eq_of_lt hk]
      have h2 := congrArg B h1
      rw [hB] at h2
      exact h2
    · obtain ⟨k, hk, rfl⟩ := (hO_mem _).mp hu
      refine Or.inl ((hO_mem _).mpr ⟨(k + 1) % c, Nat.mod_lt _ hcpos, ?_⟩)
      rw [bg_iter_mod s v0 c hsc, Function.iterate_succ_apply']
      rfl
  -- Case 1: H is a proper subset of Finset.univ
  by_cases hHfull : H = Finset.univ
  · -- Case 2: R ∪ B is a single Hamiltonian N-cycle
    have hdisj_OR : Disjoint O (O.image R) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨i, _, rfl⟩ := (hO_mem _).mp hv1
      obtain ⟨u, hu, hRu⟩ := Finset.mem_image.mp hv2
      obtain ⟨j, _, rfl⟩ := (hO_mem _).mp hu
      exact bg_orbit_disj R B hR hB hRne hBne v0 i j hRu.symm
    have hOcard : O.card = c := by
      rw [hOdef, Finset.card_image_of_injOn]
      · simp
      · intro i hi j hj heq
        exact hsinj_lt i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) heq
    have hORcard : (O.image R).card = c := by
      rw [Finset.card_image_of_injective _ (fun a b h => by have := congrArg R h; rwa [hR, hR] at this)]
      exact hOcard
    have h2c : 2 * c = N := by
      have hHc := Finset.card_union_of_disjoint hdisj_OR
      rw [← hHdef, hHfull, Finset.card_univ, Fintype.card_fin, hOcard, hORcard] at hHc
      omega
    -- Position bijection `pos : Fin N → Fin N`
    set pos : Fin N → Fin N :=
      fun p => if p.val % 2 = 0 then s^[p.val / 2] v0 else R (s^[p.val / 2] v0) with hposdef
    have hpos_inj : Function.Injective pos := by
      intro p q hpq
      ext
      simp only [hposdef] at hpq
      by_cases hp : p.val % 2 = 0 <;> by_cases hq : q.val % 2 = 0
      · simp only [hp, hq, ↓reduceIte] at hpq
        have hdiv := hsinj_lt (p.val / 2) (by omega) (q.val / 2) (by omega) hpq
        omega
      · simp only [hp, hq, ↓reduceIte] at hpq
        exact absurd hpq (bg_orbit_disj R B hR hB hRne hBne v0 _ _)
      · simp only [hp, hq, ↓reduceIte] at hpq
        exact absurd hpq.symm (bg_orbit_disj R B hR hB hRne hBne v0 _ _)
      · simp only [hp, hq, ↓reduceIte] at hpq
        have h1 : R (R (s^[p.val / 2] v0)) = R (R (s^[q.val / 2] v0)) := congrArg R hpq
        rw [hR, hR] at h1
        have hdiv := hsinj_lt (p.val / 2) (by omega) (q.val / 2) (by omega) h1
        omega
    let ePos : Fin N ≃ Fin N := Equiv.ofBijective pos (Finite.injective_iff_bijective.mp hpos_inj)
    have hePos : ∀ p, ePos p = pos p := fun _ => rfl
    set r0 := bg_r0 N hNeven with hr0def
    set b0 := bg_b0 N (by omega) with hb0def
    set g : Fin N → Fin N := fun p => ePos.symm (G (pos p)) with hgdef
    have hpos_r0 : ∀ p, pos (r0 p) = R (pos p) := by
      intro p
      simp only [hposdef, hr0def, bg_r0]
      by_cases hp : p.val % 2 = 0
      · simp only [hp, ↓reduceIte]
        have h1 : (p.val + 1) % 2 ≠ 0 := by omega
        have h2 : (p.val + 1) / 2 = p.val / 2 := by omega
        simp only [h1, ↓reduceIte, h2]
      · simp only [hp, ↓reduceIte]
        have h1 : (p.val - 1) % 2 = 0 := by omega
        have h2 : (p.val - 1) / 2 = p.val / 2 := by omega
        simp only [h1, ↓reduceIte, h2, hR]
    have hpos_b0_odd : ∀ p : Fin N, p.val % 2 = 1 → pos (b0 p) = B (pos p) := by
      intro p hp
      have hpe0 : p.val % 2 ≠ 0 := by omega
      have hmod_even : ((p.val + 1) % N) % 2 = 0 := by
        rcases hNeven with ⟨m, hm⟩
        have := p.isLt
        by_cases hlast : p.val + 1 = N
        · rw [hlast, Nat.mod_self]
        · have hlt : (p.val + 1) % N = p.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hlt]; omega
      have hdiv : ((p.val + 1) % N) / 2 = (p.val / 2 + 1) % c := by
        have := p.isLt
        by_cases hlast : p.val + 1 = N
        · rw [hlast, Nat.mod_self]
          have : p.val / 2 + 1 = c := by omega
          rw [this, Nat.mod_self]
        · have hltN : (p.val + 1) % N = p.val + 1 := Nat.mod_eq_of_lt (by omega)
          have hltc : (p.val / 2 + 1) % c = p.val / 2 + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hltN, hltc]; omega
      have hb0val : (b0 p).val = (p.val + 1) % N := by
        simp only [hb0def, bg_b0, hp, ↓reduceIte]
      simp only [hposdef, hb0val, hmod_even, hpe0, ↓reduceIte, hdiv]
      rw [bg_iter_mod s v0 c hsc, Function.iterate_succ_apply']
      rfl
    have hpos_b0 : ∀ p, pos (b0 p) = B (pos p) := by
      intro p
      by_cases hp : p.val % 2 = 1
      · exact hpos_b0_odd p hp
      · have hb0_odd : (b0 p).val % 2 = 1 := by
          simp only [hb0def, bg_b0, hp, ↓reduceIte]
          rcases hNeven with ⟨m, hm⟩
          have := p.isLt
          by_cases h0 : p.val = 0
          · have h1 : (p.val + N - 1) % N = N - 1 := by
              rw [h0, zero_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [h1]; omega
          · have h1 : (p.val + N - 1) % N = p.val - 1 := by
              have e1 : p.val + N - 1 = (p.val - 1) + N := by omega
              rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1]; omega
        have hodd_case := hpos_b0_odd (b0 p) hb0_odd
        have hinv_p : b0 (b0 p) = p := bg_b0_inv N (by omega) hNeven p
        rw [hinv_p] at hodd_case
        have := congrArg B hodd_case
        rw [hB] at this
        exact this.symm
    have hpos_g : ∀ p, pos (g p) = G (pos p) := fun p => ePos.apply_symm_apply (G (pos p))
    have hg_inv : ∀ p, g (g p) = p := by
      intro p; apply hpos_inj; rw [hpos_g, hpos_g, hG]
    have hg_ne : ∀ p, g p ≠ p := by
      intro p h; exact hGne (pos p) (by rw [← hpos_g, h])
    have hg_ne_r0 : ∀ p, g p ≠ r0 p := by
      intro p h; exact hRG (pos p) (by rw [← hpos_r0, ← hpos_g, h])
    have hg_ne_b0 : ∀ p, g p ≠ b0 p := by
      intro p h; exact hBG (pos p) (by rw [← hpos_b0, ← hpos_g, h])
    set m0 : Fin 3 → Fin N → Fin N := ![r0, b0, g] with hm0def
    have hpos_m0 : ∀ k p, pos (m0 k p) = m k (pos p) := by
      intro k p
      fin_cases k
      · exact hpos_r0 p
      · exact hpos_b0 p
      · exact hpos_g p
    -- Suffices to construct `lab : Fin N → Fin 3` on cycle positions
    suffices hlab : ∃ lab : Fin N → Fin 3,
        (∀ p, lab (m0 (lab p) p) = lab p) ∧ ∃ p₁ p₂, lab p₁ ≠ lab p₂ by
      obtain ⟨lab, hlab_inv, p₁, p₂, hp12⟩ := hlab
      refine ⟨fun v => lab (ePos.symm v), ?_, pos p₁, pos p₂, ?_⟩
      · intro v
        dsimp only
        have h1 : m (lab (ePos.symm v)) v = pos (m0 (lab (ePos.symm v)) (ePos.symm v)) := by
          rw [hpos_m0, ← hePos, ePos.apply_symm_apply]
        rw [h1, ← hePos, ePos.symm_apply_apply]
        exact hlab_inv (ePos.symm v)
      · simpa only [← hePos, ePos.symm_apply_apply] using hp12
    -- Split into Subcase 2a (opposite-parity chord) and Subcase 2b (all chords preserve parity)
    by_cases hopp : ∃ p : Fin N, p.val % 2 ≠ (g p).val % 2
    · -- Subcase 2a: opposite-parity chord exists
      obtain ⟨p0, hp0⟩ := hopp
      have hex_eo : ∃ p : Fin N, p.val % 2 = 0 ∧ (g p).val % 2 = 1 := by
        by_cases h0 : p0.val % 2 = 0
        · exact ⟨p0, h0, by omega⟩
        · exact ⟨g p0, by omega, by rw [hg_inv]; omega⟩
      obtain ⟨p, hpe, hgo⟩ := hex_eo
      set a := p.val with ha_def
      set b := (g p).val with hb_def
      have ha_lt : a < N := p.isLt
      have hb_lt : b < N := (g p).isLt
      have hab_ne : a ≠ b := Fin.val_ne_of_ne (hg_ne p).symm
      rcases lt_or_gt_of_ne hab_ne with hlt | hgt
      · -- a < b, a even, b odd
        have hab1 : a + 1 < b := by
          have hne : b ≠ a + 1 := by
            intro h
            apply hg_ne_r0 p
            ext
            have hr0val : (r0 p).val = a + 1 := by
              simp only [hr0def, bg_r0, ha_def]
              exact if_pos hpe
            rw [hr0val]; exact h
          omega
        set lab : Fin N → Fin 3 :=
          fun q => if q.val = a ∨ q.val = b then 2 else if a < q.val ∧ q.val < b then 1 else 0
        refine ⟨lab, ?_, p, ⟨a + 1, by omega⟩, ?_⟩
        · intro q
          by_cases h2 : q.val = a ∨ q.val = b
          · have hq2 : lab q = 2 := by simp [lab, h2]
            rw [hq2]
            have hgq : (g q).val = a ∨ (g q).val = b := by
              rcases h2 with hqa | hqb
              · have : q = p := Fin.ext hqa
                rw [this]; exact Or.inr rfl
              · have : q = g p := Fin.ext hqb
                rw [this, hg_inv]; exact Or.inl rfl
            simp [lab, m0, hgq]
          · by_cases h1 : a < q.val ∧ q.val < b
            · have hq1 : lab q = 1 := by simp [lab, h2, h1]
              rw [hq1]
              have hb0_in : a < (b0 q).val ∧ (b0 q).val < b := by
                simp only [hb0def, bg_b0]
                have hqlt := q.isLt
                by_cases hqo : q.val % 2 = 1
                · simp only [hqo, ↓reduceIte]
                  rw [Nat.mod_eq_of_lt (by omega)]; omega
                · simp only [hqo, ↓reduceIte]
                  have e1 : q.val + N - 1 = (q.val - 1) + N := by omega
                  rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
              have hb0_n2 : ¬ ((b0 q).val = a ∨ (b0 q).val = b) := by omega
              simp [lab, m0, hb0_n2, hb0_in]
            · have hq0 : lab q = 0 := by simp [lab, h2, h1]
              rw [hq0]
              have hr0_out : (r0 q).val < a ∨ b < (r0 q).val := by
                simp only [hr0def, bg_r0]
                have hqlt := q.isLt
                split_ifs <;> omega
              have hr0_n2 : ¬ ((r0 q).val = a ∨ (r0 q).val = b) := by omega
              have hr0_n1 : ¬ (a < (r0 q).val ∧ (r0 q).val < b) := by omega
              simp [lab, m0, hr0_n2, hr0_n1]
        · have hlp : lab p = 2 := by
            dsimp only [lab]
            rw [if_pos (Or.inl ha_def.symm)]
          have hl1 : lab ⟨a + 1, by omega⟩ = 1 := by
            have hn : ¬ (a + 1 = a ∨ a + 1 = b) := by omega
            have hi : a < a + 1 ∧ a + 1 < b := by omega
            dsimp only [lab]
            rw [if_neg hn, if_pos hi]
          rw [hlp, hl1]; decide
      · -- b < a, b odd, a even
        have hba1 : b + 1 < a := by
          have hne : b ≠ a - 1 := by
            intro h
            apply hg_ne_b0 p
            ext
            have hb0val : (b0 p).val = a - 1 := by
              simp only [hb0def, bg_b0]
              have hpo : p.val % 2 ≠ 1 := by omega
              simp only [hpo, ↓reduceIte]
              have e1 : p.val + N - 1 = (p.val - 1) + N := by omega
              rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hb0val]; exact h
          omega
        set lab : Fin N → Fin 3 :=
          fun q => if q.val = a ∨ q.val = b then 2 else if b < q.val ∧ q.val < a then 0 else 1
        refine ⟨lab, ?_, p, ⟨b + 1, by omega⟩, ?_⟩
        · intro q
          by_cases h2 : q.val = a ∨ q.val = b
          · have hq2 : lab q = 2 := by simp [lab, h2]
            rw [hq2]
            have hgq : (g q).val = a ∨ (g q).val = b := by
              rcases h2 with hqa | hqb
              · have : q = p := Fin.ext hqa
                rw [this]; exact Or.inr rfl
              · have : q = g p := Fin.ext hqb
                rw [this, hg_inv]; exact Or.inl rfl
            simp [lab, m0, hgq]
          · by_cases h0 : b < q.val ∧ q.val < a
            · have hq0 : lab q = 0 := by simp [lab, h2, h0]
              rw [hq0]
              have hr0_in : b < (r0 q).val ∧ (r0 q).val < a := by
                simp only [hr0def, bg_r0]
                have hqlt := q.isLt
                split_ifs <;> omega
              have hr0_n2 : ¬ ((r0 q).val = a ∨ (r0 q).val = b) := by omega
              simp [lab, m0, hr0_n2, hr0_in]
            · have hq1 : lab q = 1 := by simp [lab, h2, h0]
              rw [hq1]
              have hb0_out : (b0 q).val < b ∨ a < (b0 q).val := by
                simp only [hb0def, bg_b0]
                have hqlt := q.isLt
                rcases hNeven with ⟨m, hm⟩
                by_cases hqo : q.val % 2 = 1
                · simp only [hqo, ↓reduceIte]
                  by_cases hlast : q.val + 1 = N
                  · rw [hlast, Nat.mod_self]; omega
                  · rw [Nat.mod_eq_of_lt (by omega)]; omega
                · simp only [hqo, ↓reduceIte]
                  by_cases hq0z : q.val = 0
                  · rw [hq0z, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
                  · have e1 : q.val + N - 1 = (q.val - 1) + N := by omega
                    rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
              have hb0_n2 : ¬ ((b0 q).val = a ∨ (b0 q).val = b) := by omega
              have hb0_n0 : ¬ (b < (b0 q).val ∧ (b0 q).val < a) := by omega
              simp [lab, m0, hb0_n2, hb0_n0]
        · have hlp : lab p = 2 := by
            dsimp only [lab]
            rw [if_pos (Or.inl ha_def.symm)]
          have hl0 : lab ⟨b + 1, by omega⟩ = 0 := by
            have hn : ¬ (b + 1 = a ∨ b + 1 = b) := by omega
            have hi : b < b + 1 ∧ b + 1 < a := by omega
            dsimp only [lab]
            rw [if_neg hn, if_pos hi]
          rw [hlp, hl0]; decide
    · -- Subcase 2b: Every chord of `g` preserves parity! (Minimal-chord interleaving)
      push Not at hopp
      set cdist : Fin N → Nat := fun u => min (bg_fwd u (g u)) (bg_fwd (g u) u) with hcddef
      obtain ⟨u0, -, hu0_min⟩ :=
        Finset.exists_min_image (Finset.univ : Finset (Fin N)) cdist
          (Finset.univ_nonempty_iff.mpr ⟨v0⟩)
      set p : Fin N := if bg_fwd u0 (g u0) ≤ bg_fwd (g u0) u0 then u0 else g u0 with hp_def
      set d : Nat := bg_fwd p (g p) with hd_def
      have hd_eq : d = cdist u0 := by
        simp only [hd_def, hp_def, hcddef]
        split_ifs with hle
        · exact (min_eq_left hle).symm
        · rw [hg_inv]; exact (min_eq_right (le_of_not_ge hle)).symm
      have hd_min : ∀ u : Fin N, d ≤ cdist u := by
        intro u; rw [hd_eq]; exact hu0_min u (Finset.mem_univ u)
      have hd_symm : bg_fwd p (g p) + bg_fwd (g p) p = N := bg_fwd_add_symm p (g p) (hg_ne p).symm
      have hd_le_half : 2 * d ≤ N := by
        have h1 : d ≤ bg_fwd (g p) p := by
          simp only [hd_def, hp_def]
          split_ifs with hle
          · exact hle
          · rw [hg_inv]; omega
        omega
      have hd_even : d % 2 = 0 := by
        have hgp := hopp p
        rw [hd_def, bg_fwd_mod_two hNeven]; omega
      have hd_pos : 2 ≤ d := by
        have hnz : d ≠ 0 := by
          intro h; exact hg_ne p ((bg_fwd_eq_zero_iff p (g p)).mp h).symm
        omega
      set z : Fin N := ⟨(p.val + 1) % N, Nat.mod_lt _ (by omega)⟩ with hz_def
      set w : Fin N := g z with hw_def
      set k : Nat := bg_fwd p w with hk_def
      have hz_fwd : bg_fwd p z = 1 := by
        have h1 := bg_fwd_succ_mod (by omega : 2 ≤ N) p p
        have h0 : bg_fwd p p = 0 := (bg_fwd_eq_zero_iff p p).mpr rfl
        rw [h0, zero_add, Nat.mod_eq_of_lt (by omega : 1 < N)] at h1
        exact h1
      have hk_lt : k < N := bg_fwd_lt (by omega) p w
      have hk_odd : k % 2 = 1 := by
        have hgz := hopp z
        have hzval : z.val = (p.val + 1) % N := rfl
        rw [hk_def, bg_fwd_mod_two hNeven, hw_def]
        rcases hNeven with ⟨m, hm⟩
        have := p.isLt
        by_cases hlast : p.val + 1 = N
        · have hz0 : z.val = 0 := by rw [hzval, hlast, Nat.mod_self]
          omega
        · have hzp1 : z.val = p.val + 1 := by rw [hzval, Nat.mod_eq_of_lt (by omega)]
          omega
      have hk_ne_one : k ≠ 1 := by
        intro h
        have : w = z := bg_fwd_inj p w z (h.trans hz_fwd.symm)
        exact hg_ne z this
      have hk_gt_d : d < k := by
        by_contra hle
        have hklt : k < d := by omega
        have hkge1 : 1 ≤ k := by omega
        have hzw : bg_fwd z w = k - 1 := bg_fwd_from_succ (by omega : 2 ≤ N) p w hkge1
        have hmin := hd_min z
        have hcdz : cdist z ≤ bg_fwd z w := min_le_left _ _
        omega
      -- Key shifted-coordinate identities for `c_next` and `c_alt`
      set c_next : Fin 3 := if p.val % 2 = 0 then 0 else 1 with hcn_def
      set c_alt : Fin 3 := if p.val % 2 = 0 then 1 else 0 with hca_def
      have hfwd_next : ∀ q : Fin N,
          bg_fwd p (m0 c_next q) =
            if (bg_fwd p q) % 2 = 0 then bg_fwd p q + 1 else bg_fwd p q - 1 := by
        intro q
        have hf_lt := bg_fwd_lt (by omega : 0 < N) p q
        have hpar := bg_fwd_mod_two hNeven p q
        rcases hNeven with ⟨m, hm⟩
        by_cases hpe : p.val % 2 = 0
        · simp only [hcn_def, hpe, ↓reduceIte, m0, Matrix.cons_val_zero, hr0def, bg_r0]
          by_cases hqe : q.val % 2 = 0
          · have hfe : (bg_fwd p q) % 2 = 0 := by omega
            simp only [hqe, hfe, ↓reduceIte]
            have hqlt := q.isLt
            have h1 := bg_fwd_succ_mod (by omega : 2 ≤ N) p q
            have hq1 : (q.val + 1) % N = q.val + 1 := Nat.mod_eq_of_lt (by omega)
            have heq : (⟨q.val + 1, by omega⟩ : Fin N) = ⟨(q.val + 1) % N, Nat.mod_lt _ (by omega)⟩ :=
              Fin.ext hq1.symm
            rw [heq, h1, Nat.mod_eq_of_lt (by omega)]
          · have hfe : ¬ (bg_fwd p q) % 2 = 0 := by omega
            simp only [hqe, hfe, ↓reduceIte]
            have hqlt := q.isLt
            have h1 := bg_fwd_pred_mod (by omega : 2 ≤ N) p q
            have hq1 : (q.val + N - 1) % N = q.val - 1 := by
              have : q.val + N - 1 = (q.val - 1) + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have heq : (⟨q.val - 1, by omega⟩ : Fin N) = ⟨(q.val + N - 1) % N, Nat.mod_lt _ (by omega)⟩ :=
              Fin.ext hq1.symm
            rw [heq, h1]
            have : bg_fwd p q + N - 1 = (bg_fwd p q - 1) + N := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · simp only [hcn_def, hpe, ↓reduceIte, m0, Matrix.cons_val_one, Matrix.cons_val_zero, hb0def, bg_b0]
          by_cases hqo : q.val % 2 = 1
          · have hfe : (bg_fwd p q) % 2 = 0 := by omega
            simp only [hqo, hfe, ↓reduceIte]
            rw [bg_fwd_succ_mod (by omega : 2 ≤ N) p q, Nat.mod_eq_of_lt (by omega)]
          · have hfe : ¬ (bg_fwd p q) % 2 = 0 := by omega
            simp only [hqo, hfe, ↓reduceIte]
            rw [bg_fwd_pred_mod (by omega : 2 ≤ N) p q]
            have : bg_fwd p q + N - 1 = (bg_fwd p q - 1) + N := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hfwd_alt : ∀ q : Fin N,
          bg_fwd p (m0 c_alt q) =
            if (bg_fwd p q) % 2 = 1 then (bg_fwd p q + 1) % N else (bg_fwd p q + N - 1) % N := by
        intro q
        have hf_lt := bg_fwd_lt (by omega : 0 < N) p q
        have hpar := bg_fwd_mod_two hNeven p q
        rcases hNeven with ⟨m, hm⟩
        by_cases hpe : p.val % 2 = 0
        · simp only [hca_def, hpe, ↓reduceIte, m0, Matrix.cons_val_one, Matrix.cons_val_zero, hb0def, bg_b0]
          by_cases hqo : q.val % 2 = 1
          · have hfo : (bg_fwd p q) % 2 = 1 := by omega
            simp only [hqo, hfo, ↓reduceIte]
            exact bg_fwd_succ_mod (by omega : 2 ≤ N) p q
          · have hfo : ¬ (bg_fwd p q) % 2 = 1 := by omega
            simp only [hqo, hfo, ↓reduceIte]
            exact bg_fwd_pred_mod (by omega : 2 ≤ N) p q
        · simp only [hca_def, hpe, ↓reduceIte, m0, Matrix.cons_val_zero, hr0def, bg_r0]
          by_cases hqe : q.val % 2 = 0
          · have hfo : (bg_fwd p q) % 2 = 1 := by omega
            simp only [hqe, hfo, ↓reduceIte]
            have hqlt := q.isLt
            have h1 := bg_fwd_succ_mod (by omega : 2 ≤ N) p q
            have hq1 : (q.val + 1) % N = q.val + 1 := Nat.mod_eq_of_lt (by omega)
            have heq : (⟨q.val + 1, by omega⟩ : Fin N) = ⟨(q.val + 1) % N, Nat.mod_lt _ (by omega)⟩ :=
              Fin.ext hq1.symm
            rw [heq, h1]
          · have hfo : ¬ (bg_fwd p q) % 2 = 1 := by omega
            simp only [hqe, hfo, ↓reduceIte]
            have hqlt := q.isLt
            have h1 := bg_fwd_pred_mod (by omega : 2 ≤ N) p q
            have hq1 : (q.val + N - 1) % N = q.val - 1 := by
              have : q.val + N - 1 = (q.val - 1) + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have heq : (⟨q.val - 1, by omega⟩ : Fin N) = ⟨(q.val + N - 1) % N, Nat.mod_lt _ (by omega)⟩ :=
              Fin.ext hq1.symm
            rw [heq, h1]
      set lab : Fin N → Fin 3 := fun q =>
        if bg_fwd p q = 0 ∨ bg_fwd p q = 1 ∨ bg_fwd p q = d ∨ bg_fwd p q = k then 2
        else if d < bg_fwd p q ∧ bg_fwd p q < k then c_alt
        else c_next
      -- Find a vertex outside `{p, z, g p, w}` so `lab` is non-constant
      have hex_out : ∃ q : Fin N, q ∉ ({p, z, g p, w} : Finset (Fin N)) := by
        have hlt : ({p, z, g p, w} : Finset (Fin N)).card < (Finset.univ : Finset (Fin N)).card := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact lt_of_le_of_lt Finset.card_le_four (by omega)
        obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        exact ⟨q, hq⟩
      obtain ⟨q_out, hq_out⟩ := hex_out
      refine ⟨lab, ?_, p, q_out, ?_⟩
      · intro q
        have hfq_lt := bg_fwd_lt (by omega : 0 < N) p q
        by_cases h2 : bg_fwd p q = 0 ∨ bg_fwd p q = 1 ∨ bg_fwd p q = d ∨ bg_fwd p q = k
        · have hq2 : lab q = 2 := by simp [lab, h2]
          rw [hq2]
          have hgq : bg_fwd p (g q) = 0 ∨ bg_fwd p (g q) = 1 ∨ bg_fwd p (g q) = d ∨ bg_fwd p (g q) = k := by
            rcases h2 with h0 | h1 | hd | hk
            · have : q = p := (bg_fwd_eq_zero_iff p q).mp h0 |>.symm
              rw [this]; exact Or.inr (Or.inr (Or.inl rfl))
            · have : q = z := bg_fwd_inj p q z (h1.trans hz_fwd.symm)
              rw [this]; exact Or.inr (Or.inr (Or.inr rfl))
            · have : q = g p := bg_fwd_inj p q (g p) hd
              rw [this, hg_inv]; exact Or.inl ((bg_fwd_eq_zero_iff p p).mpr rfl)
            · have : q = w := bg_fwd_inj p q w hk
              rw [this, hw_def, hg_inv]; exact Or.inr (Or.inl hz_fwd)
          simp [lab, m0, hgq]
        · by_cases ha : d < bg_fwd p q ∧ bg_fwd p q < k
          · have hqa : lab q = c_alt := by simp [lab, h2, ha]
            rw [hqa]
            have hfa := hfwd_alt q
            have hin : d < bg_fwd p (m0 c_alt q) ∧ bg_fwd p (m0 c_alt q) < k := by
              rw [hfa]
              by_cases ho : bg_fwd p q % 2 = 1
              · simp only [ho, ↓reduceIte, Nat.mod_eq_of_lt (by omega : bg_fwd p q + 1 < N)]
                omega
              · simp only [ho, ↓reduceIte]
                have e1 : bg_fwd p q + N - 1 = (bg_fwd p q - 1) + N := by omega
                rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                omega
            have hn2 : ¬ (bg_fwd p (m0 c_alt q) = 0 ∨ bg_fwd p (m0 c_alt q) = 1 ∨
                bg_fwd p (m0 c_alt q) = d ∨ bg_fwd p (m0 c_alt q) = k) := by omega
            simp [lab, hn2, hin]
          · have hqn : lab q = c_next := by simp [lab, h2, ha]
            rw [hqn]
            have hfn := hfwd_next q
            set x := bg_fwd p q with hx_def
            have hstay : ¬ (bg_fwd p (m0 c_next q) = 0 ∨ bg_fwd p (m0 c_next q) = 1 ∨
                bg_fwd p (m0 c_next q) = d ∨ bg_fwd p (m0 c_next q) = k) ∧
                ¬ (d < bg_fwd p (m0 c_next q) ∧ bg_fwd p (m0 c_next q) < k) := by
              rw [hfn]
              rcases hNeven with ⟨m, hm⟩
              by_cases hxe : x % 2 = 0
              · simp only [hxe, ↓reduceIte]; omega
              · simp only [hxe, ↓reduceIte]; omega
            simp [lab, hstay.1, hstay.2]
      · have hlp : lab p = 2 := by
          simp [lab, (bg_fwd_eq_zero_iff p p).mpr rfl]
        have hq_not2 : ¬ (bg_fwd p q_out = 0 ∨ bg_fwd p q_out = 1 ∨
            bg_fwd p q_out = d ∨ bg_fwd p q_out = k) := by
          intro h
          apply hq_out
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases h with h0 | h1 | hd | hk
          · exact Or.inl ((bg_fwd_eq_zero_iff p q_out).mp h0).symm
          · exact Or.inr (Or.inl (bg_fwd_inj p q_out z (h1.trans hz_fwd.symm)))
          · exact Or.inr (Or.inr (Or.inl (bg_fwd_inj p q_out (g p) hd)))
          · exact Or.inr (Or.inr (Or.inr (bg_fwd_inj p q_out w hk)))
        rw [hlp]
        simp only [lab, hq_not2, ↓reduceIte]
        split_ifs <;> simp [hca_def, hcn_def] <;> split_ifs <;> decide
  · -- Case 1: H ≠ Finset.univ
    have hex_out : ∃ w : Fin N, w ∉ H := by
      by_contra h
      push Not at h
      exact hHfull (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨w, hw⟩ := hex_out
    have hv0_H : v0 ∈ H := by
      simp only [hHdef, Finset.mem_union]
      exact Or.inl ((hO_mem v0).mpr ⟨0, hcpos, rfl⟩)
    refine ⟨fun v => if v ∈ H then 0 else 1, ?_, v0, w, ?_⟩
    · intro v
      dsimp only
      by_cases hv : v ∈ H
      · rw [if_pos hv, if_pos (hH_R v hv)]
      · have hBv : B v ∉ H := fun h => hv (by rw [← hB v]; exact hH_B (B v) h)
        rw [if_neg hv, if_neg hBv]
    · simp [hv0_H, hw]

end GeneralBogdanov

/-! ## Section: Final World-Record Assembly (`∀ even N ≥ 10, D ≥ N - 2`) -/

section FinalAssembly

/-- Color restriction: any solution of `EqSystemN N D W` restricts along `Fin.castLE` to
any smaller color count `D' ≤ D`. -/
theorem eqSystemN_restrict {α : Type} [Semiring α] {N D D' : Nat} (hD : D' ≤ D)
    {W : WeightsN N D α} (hW : EqSystemN N D W) :
    EqSystemN N D' (fun e => W ⟨e.u, e.v, Fin.castLE hD e.i, Fin.castLE hD e.j⟩) := by
  let W' : WeightsN N D' α := fun e => W ⟨e.u, e.v, Fin.castLE hD e.i, Fin.castLE hD e.j⟩
  have haux : ∀ (fuel : Nat) (ι : V N → Fin D') (L : List (V N)),
      pmSumListAux W' ι fuel L = pmSumListAux W (fun v => Fin.castLE hD (ι v)) fuel L := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro ι L
      match fuel, L with
      | 0, _ => rfl
      | 1, _ => rfl
      | _ + 2, [] => rfl
      | _ + 2, [_] => rfl
      | m + 2, v :: u :: us =>
        simp only [pmSumListAux]
        congr 1
        apply List.map_congr_left
        intro x _
        rw [ih m (by omega) ι ((u :: us).erase x)]
        rfl
  intro ι
  have hpm : pmSumN N D' W' ι = pmSumN N D W (fun v => Fin.castLE hD (ι v)) := by
    unfold pmSumN pmSumList
    exact haux (vertices N).length ι (vertices N)
  rw [hpm, hW (fun v => Fin.castLE hD (ι v))]
  have hiff : allEqual (fun v => Fin.castLE hD (ι v)) ↔ allEqual ι := by
    rw [allEqual_iff_forall_eq, allEqual_iff_forall_eq]
    constructor
    · intro h u v
      exact Fin.ext (by simpa using congrArg Fin.val (h u v))
    · intro h u v
      exact congrArg (Fin.castLE hD) (h u v)
  by_cases h : allEqual ι
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]

/-- Over any field, `EqSystemN (n + 2) n W` has no solution for any even `n ≥ 8`. -/
private theorem no_eqSystem_add_two_field {K : Type} [Field K] {n : Nat} [ValidDim n]
    (W : WeightsN (n + 2) n K) (hW : EqSystemN (n + 2) n W) : False := by
  classical
  have hB := two_mul_Bset_card_le W hW
  have hge := ValidDim.ge_eight (n := n)
  have hS : 2 < (Finset.univ \ Bset W hW).card := by
    rw [Finset.card_univ_sdiff]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, h01, h02, h12⟩ := Finset.two_lt_card.mp hS
  set col : Fin 3 → Fin n := ![c₀, c₁, c₂] with hcol
  have hcl : ∀ k : Fin 3, col k ∉ Bset W hW := by
    intro k
    fin_cases k
    · exact (Finset.mem_sdiff.mp hc₀).2
    · exact (Finset.mem_sdiff.mp hc₁).2
    · exact (Finset.mem_sdiff.mp hc₂).2
  have hcolinj : Function.Injective col := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [col]
  set m : Fin 3 → Fin (n + 2) → Fin (n + 2) := fun k w => anchor W hW w (col k) with hm
  have hinv : ∀ k v, m k (m k v) = v := fun k v => clean_involutive W hW v (col k) (hcl k)
  have hfix : ∀ k v, m k v ≠ v := fun k v => anchor_ne W hW v (col k)
  have hdisj : ∀ k l v, k ≠ l → m k v ≠ m l v :=
    fun k l v hkl h => hkl (hcolinj (anchor_injective W hW v h))
  obtain ⟨τ, hτ, v₁, v₂, hv⟩ :=
    exists_mixed_matching_general (by omega) (by rcases ValidDim.even (n := n) with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩) m hinv hfix hdisj
  set η : Fin (n + 2) → Fin n := fun w => col (τ w) with hη
  set μ : Fin (n + 2) → Fin (n + 2) := fun w => m (τ w) w with hμ
  have hητ : ∀ w, η (μ w) = η w := by
    intro w
    simp only [η, μ]
    rw [hτ w]
  have hμμ : ∀ w, μ (μ w) = w := by
    intro w
    show m (τ (μ w)) (μ w) = w
    have : τ (μ w) = τ w := hτ w
    rw [this]
    exact hinv (τ w) w
  have hne : msum W η Finset.univ ≠ 0 := by
    apply msum_ne_zero_of_involution W η μ hμμ (fun w => hfix (τ w) w)
    · intro w
      rw [hητ w]
      exact clean_edge_ne_zero W hW w (col (τ w)) (hcl (τ w))
    · intro w y hyw hyμ
      by_contra hnz
      have hij := clean_diag W hW w y (η w) (η y) (hcl (τ w)) (hcl (τ y)) hnz
      rw [← hij] at hnz
      exact hyμ (clean_unique W hW w y (η w) (hcl (τ w)) hnz)
    · intro w _
      exact Finset.mem_univ _
  have hconst := msum_univ_ne_zero_const W hW η hne v₁ v₂
  exact hv (hcolinj hconst)

end FinalAssembly

end PPL007General

/-!
## Public World-Record Theorems (Zero Custom Types / Classes in Signatures)
-/

open MonochromaticQuantumGraph

/-- **PPL 007 New World-Record General Bound (`D ≤ N - 3` for all even `N ≥ 10`, integral domains):**
Over any commutative integral domain `K`, no monochromatic quantum graph equation system
`EqSystemN N D W` has a solution when `N ≥ 10` is even and `D ≥ N - 2`.

This strictly improves the 2026 global sharp bound `D ≤ N - 2` (`KitaKen1`, PR #4661) and closes
infinitely many open cases `(12, 10), (14, 12), (16, 14), …` without any SAT solver.
(Note: this is a general bound milestone, NOT a proof of the full €3,000 `D = 3` conjecture.) -/
theorem ppl007_world_record_domain {K : Type} [CommRing K] [IsDomain K]
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D K, EqSystemN N D W := by
  rintro ⟨W, hW⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hm8 : 8 ≤ m := by omega
  have hmeven : Even m := by
    rcases hNeven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have hDm : m ≤ D := by omega
  have hW_res := PPL007General.eqSystemN_restrict hDm hW
  have hW_frac := QuantumCR.EqSystemN.mapWeights hW_res (algebraMap K (FractionRing K))
  have : PPL007General.ValidDim m := ⟨hm8, hmeven⟩
  exact PPL007General.no_eqSystem_add_two_field (K := FractionRing K) _ hW_frac

/-- **PPL 007 New World-Record General Bound over `ℂ` (`D ≤ N - 3` for all even `N ≥ 10`):**
Over `ℂ`, no monochromatic quantum graph equation system has a solution when `N ≥ 10` is even
and `D ≥ N - 2`. -/
theorem ppl007_world_record_complex
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D ℂ, EqSystemN N D W :=
  ppl007_world_record_domain N D hN hNeven hD

/-- **PPL 007 New World-Record General Bound over `ℝ` (`D ≤ N - 3` for all even `N ≥ 10`):**
Over `ℝ`, no monochromatic quantum graph equation system has a solution when `N ≥ 10` is even
and `D ≥ N - 2`. -/
theorem ppl007_world_record_real
    (N D : Nat) (hN : 10 ≤ N) (hNeven : Even N) (hD : N - 2 ≤ D) :
    ¬ ∃ W : WeightsN N D ℝ, EqSystemN N D W :=
  ppl007_world_record_domain N D hN hNeven hD

/-- Previously open concrete case `(N = 12, D = 10)` over `ℂ` (`4 ∣ N`). -/
theorem ppl007_no_solution_n12_d10_complex :
    ¬ ∃ W : WeightsN 12 10 ℂ, EqSystemN 12 10 W :=
  ppl007_world_record_complex 12 10 (by omega) ⟨6, rfl⟩ (by omega)

/-- Previously open concrete case `(N = 14, D = 12)` over `ℂ`. -/
theorem ppl007_no_solution_n14_d12_complex :
    ¬ ∃ W : WeightsN 14 12 ℂ, EqSystemN 14 12 W :=
  ppl007_world_record_complex 14 12 (by omega) ⟨7, rfl⟩ (by omega)
