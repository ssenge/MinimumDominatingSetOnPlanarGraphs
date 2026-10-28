import Mathlib

/-!
# Packing, repair and averaging over windows

The graph-independent steps of Theorems `thm:forests` and `thm:outerplanar`, for a finite simple
graph `G` (Mathlib's `SimpleGraph`):
* `packing`: if the closed neighbourhoods of the vertices of `A` are pairwise disjoint, every
  fractional dominating set has weight at least `|A|`.
* `repair` (paper, (eq:repair)): a vector that dominates a window `U`, restricted to `U`, plus
  weight `1` on a boundary set `B`, dominates every vertex of `U`. `B` need not lie in `U`, and `y`
  only has to dominate `U`, so this is also the feasibility claim in the repair step of Theorem
  `thm:outerplanar`, on the finite graph induced by `N[W]`.
* `window_average`: windows with weights cover every vertex with total weight exactly `1`. Each window
  has a local solution that dominates `U` and is optimal among the vectors supported on a set `S ⊇ U`
  (`S = U` for `opt(W)` in Theorem `thm:forests`, `S = N[U]` for `opt⁺(W)` in Theorem
  `thm:outerplanar`), and `B ⊆ S`. Then the weighted average of the local solutions is a fractional
  dominating set of weight at most `y(V) + Σ_W wt(W)·|B_W|` for every fractional dominating set `y`.

## Elsewhere and not formalized
The windows of Theorem `thm:forests` and the bounds on their boundaries are in `ForestCore.lean`
to `ForestLocal.lean`, and its randomized part is in `ForestRand.lean`. For Theorem
`thm:outerplanar`, the runs, the anchors and the counting are in `Outer.lean`. Not formalized:
the covering graph of Theorem `thm:outerplanar` with its group action and continuous window
weights, its windows and their boundaries, and the LOCAL implementation of that theorem.
-/

open Finset

namespace Op4

section Windows

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighbourhood `N[v]`. -/
def cnbhd (v : V) : Finset V := insert v (G.neighborFinset v)

/-- `x` dominates `u`: `x(N[u]) ≥ 1`. -/
def Dom (x : V → ℝ) (u : V) : Prop := 1 ≤ ∑ v ∈ cnbhd G u, x v

/-- **Packing bound.** -/
theorem packing (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (hd : ∀ u, Dom G x u) (A : Finset V)
    (hA : (A : Set V).PairwiseDisjoint (cnbhd G)) : (A.card : ℝ) ≤ ∑ v, x v := by
  calc (A.card : ℝ) = ∑ _a ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ a ∈ A, ∑ v ∈ cnbhd G a, x v := sum_le_sum fun a _ => hd a
    _ = ∑ v ∈ A.biUnion (cnbhd G), x v := (sum_biUnion hA).symm
    _ ≤ ∑ v, x v := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => hx v

/-- The repaired vector: `y` on `U`, plus `1` on `B`. -/
def repaired (y : V → ℝ) (U B : Finset V) (v : V) : ℝ :=
  (if v ∈ U then y v else 0) + (if v ∈ B then 1 else 0)

/-- **Repair.** Let every `u ∈ U` with a neighbour outside `U` have a vertex of `B` in `N[u]`.
For `y ≥ 0` that dominates every vertex of `U`, the repaired vector is nonnegative, vanishes
outside `U ∪ B`, dominates every vertex of `U`, and has weight `y(U) + |B|`. -/
theorem repair (y : V → ℝ) (hy : ∀ v, 0 ≤ y v) (U B : Finset V) (hd : ∀ u ∈ U, Dom G y u)
    (hB : ∀ u ∈ U, (∃ v, G.Adj u v ∧ v ∉ U) → ∃ b ∈ B, b ∈ cnbhd G u) :
    (∀ v, 0 ≤ repaired y U B v) ∧ (∀ v, v ∉ U → v ∉ B → repaired y U B v = 0) ∧
      (∀ u ∈ U, Dom G (repaired y U B) u) ∧
      ∑ v, repaired y U B v = ∑ v ∈ U, y v + B.card := by
  have hz0 : ∀ v, 0 ≤ repaired y U B v := fun v => by
    unfold repaired; have := hy v; split_ifs <;> linarith
  refine ⟨hz0, fun v hv hvB => ?_, fun u hu => ?_, ?_⟩
  · unfold repaired
    rw [ite_eq_right hv, ite_eq_right hvB]; norm_num
  · unfold Dom
    by_cases hout : ∃ v, G.Adj u v ∧ v ∉ U
    · obtain ⟨b, hb, hbN⟩ := hB u hu hout
      have hzb : 1 ≤ repaired y U B b := by
        unfold repaired; rw [ite_eq_left hb]; split_ifs <;> linarith [hy b]
      exact le_trans hzb (single_le_sum (fun v _ => hz0 v) hbN)
    · push Not at hout
      have hsub : ∀ v ∈ cnbhd G u, v ∈ U := fun v hv => by
        unfold cnbhd at hv
        rcases mem_insert.1 hv with h | h
        · exact h ▸ hu
        · exact hout v ((G.mem_neighborFinset u v).1 h)
      refine le_trans (hd u hu) (sum_le_sum fun v hv => ?_)
      unfold repaired; rw [ite_eq_left (hsub v hv)]; split_ifs <;> linarith
  · unfold repaired
    rw [sum_add_distrib, ← sum_filter, ← sum_filter, filter_mem_eq_inter, filter_mem_eq_inter,
      univ_inter, univ_inter]
    simp

/-- **Averaging over windows.** -/
theorem window_average {ι : Type*} (s : Finset ι) (U S B : ι → Finset V) (wt : ι → ℝ)
    (x : ι → V → ℝ) (hwt : ∀ i ∈ s, 0 ≤ wt i)
    (hcover : ∀ v, ∑ i ∈ s.filter (fun i => v ∈ U i), wt i = 1)
    (hUS : ∀ i ∈ s, U i ⊆ S i) (hBS : ∀ i ∈ s, B i ⊆ S i)
    (hB : ∀ i ∈ s, ∀ u ∈ U i, (∃ v, G.Adj u v ∧ v ∉ U i) → ∃ b ∈ B i, b ∈ cnbhd G u)
    (hx0 : ∀ i ∈ s, ∀ v, 0 ≤ x i v) (hxdom : ∀ i ∈ s, ∀ u ∈ U i, Dom G (x i) u)
    (hxopt : ∀ i ∈ s, ∀ z : V → ℝ, (∀ v, 0 ≤ z v) → (∀ v, v ∉ S i → z v = 0) →
      (∀ u ∈ U i, Dom G z u) → ∑ v, x i v ≤ ∑ v, z v)
    (y : V → ℝ) (hy : ∀ v, 0 ≤ y v) (hyd : ∀ u, Dom G y u) :
    (∀ u, Dom G (fun v => ∑ i ∈ s, wt i * x i v) u) ∧
      ∑ v, ∑ i ∈ s, wt i * x i v ≤ ∑ v, y v + ∑ i ∈ s, wt i * (B i).card := by
  constructor
  · intro u
    unfold Dom
    rw [sum_comm]
    calc (1 : ℝ) = ∑ i ∈ s.filter (fun i => u ∈ U i), wt i := (hcover u).symm
      _ ≤ ∑ i ∈ s.filter (fun i => u ∈ U i), ∑ v ∈ cnbhd G u, wt i * x i v := by
          refine sum_le_sum fun i hi => ?_
          obtain ⟨his, hui⟩ := mem_filter.1 hi
          rw [← mul_sum]
          have := hxdom i his u hui
          unfold Dom at this
          nlinarith [hwt i his]
      _ ≤ ∑ i ∈ s, ∑ v ∈ cnbhd G u, wt i * x i v :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i his _ =>
            sum_nonneg fun v _ => mul_nonneg (hwt i his) (hx0 i his v)
  · have hloc : ∀ i ∈ s, ∑ v, x i v ≤ ∑ v ∈ U i, y v + (B i).card := fun i his => by
      obtain ⟨h0, h1, h2, h3⟩ := repair G y hy (U i) (B i) (fun u _ => hyd u) (hB i his)
      rw [← h3]
      exact hxopt i his _ h0 (fun v hv => h1 v (fun h => hv (hUS i his h))
        (fun h => hv (hBS i his h))) h2
    have hy' : ∑ i ∈ s, wt i * ∑ v ∈ U i, y v = ∑ v, y v := by
      simp_rw [mul_sum]
      rw [sum_comm' (t' := univ) (s' := fun v => s.filter fun i => v ∈ U i)
        (h := fun i v => by simp [and_comm])]
      refine sum_congr rfl fun v _ => ?_
      rw [← sum_mul, hcover v, one_mul]
    calc ∑ v, ∑ i ∈ s, wt i * x i v = ∑ i ∈ s, wt i * ∑ v, x i v := by
          rw [sum_comm]; exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
      _ ≤ ∑ i ∈ s, wt i * (∑ v ∈ U i, y v + (B i).card) :=
          sum_le_sum fun i his => mul_le_mul_of_nonneg_left (hloc i his) (hwt i his)
      _ = ∑ v, y v + ∑ i ∈ s, wt i * (B i).card := by
          simp_rw [mul_add]; rw [sum_add_distrib, hy']

end Windows

end Op4

