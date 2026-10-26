import Mathlib

/-!
# Symmetric fractional dominating sets of paths lose an additive 2/3

Vertices of `P_L` are `0, …, L-1` with `L = 2R + M`. Under uniformly random identifiers, the expected
output of an `r`-round algorithm (`R = r + 1`) is a fractional dominating set that takes one value `μ`
on the `M` middle vertices, which have isomorphic views, and is invariant under the reflection
`v ↦ L-1-v`. `path_excess`: such a fractional dominating set has weight at least `L/3 + 2/3` once
`M ≥ 4`. No nonnegativity is needed.

Only the domination constraints used by the proof enter: the left end `x 0 + x 1 ≥ 1` and the
interior vertices `u + 1` with closed neighbourhood `{u, u+1, u+2}`.

## Not formalised
The symmetrisation over identifiers (paper, Theorem `thm:lower`) and `γ(P_L) = L/3` for `3 ∣ L`.
-/

open Finset

namespace Op4

/-- The disjoint closed neighbourhoods `N[0], N[3], …, N[3t]` cover `{0, …, 3t+1}`. -/
lemma left_sum (x : ℕ → ℝ) (L : ℕ) (h0 : 1 ≤ x 0 + x 1)
    (hd : ∀ u, u + 2 < L → 1 ≤ x u + x (u + 1) + x (u + 2)) :
    ∀ t, 3 * t + 1 < L → (t + 1 : ℝ) ≤ ∑ i ∈ range (3 * t + 2), x i := by
  intro t
  induction t with
  | zero => intro _; simpa [sum_range_succ] using h0
  | succ t ih =>
    intro ht
    have h := hd (3 * t + 2) (by omega)
    have e : 3 * (t + 1) + 2 = 3 * t + 2 + 1 + 1 + 1 := by ring
    rw [e, sum_range_succ, sum_range_succ, sum_range_succ]
    push_cast
    linarith [ih (by omega)]

/-- **Additive loss 2/3 on paths.** -/
theorem path_excess (x : ℕ → ℝ) (R M : ℕ) (μ : ℝ) (hM : 4 ≤ M)
    (h0 : 1 ≤ x 0 + x 1)
    (hd : ∀ u, u + 2 < 2 * R + M → 1 ≤ x u + x (u + 1) + x (u + 2))
    (hmid : ∀ i, R ≤ i → i < R + M → x i = μ)
    (hsym : ∀ i, i < R → x (2 * R + M - 1 - i) = x i) :
    ((2 * R + M : ℕ) : ℝ) / 3 + 2 / 3 ≤ ∑ i ∈ range (2 * R + M), x i := by
  -- `R + k = 3t + 2` with `k ≤ 2`: the cover of the left part reaches `k` middle vertices
  obtain ⟨t, k, hk, hRk⟩ : ∃ t k, k ≤ 2 ∧ R + k = 3 * t + 2 :=
    ⟨(R + (2 * R + 2) % 3 - 2) / 3, (2 * R + 2) % 3, by omega, by omega⟩
  have hleft := left_sum x (2 * R + M) h0 hd t (by omega)
  have hμ : 1 / 3 ≤ μ := by
    have h := hd R (by omega)
    rw [hmid R le_rfl (by omega), hmid (R + 1) (by omega) (by omega),
      hmid (R + 2) (by omega) (by omega)] at h
    linarith
  have hconst : ∀ m, m ≤ M → ∑ i ∈ range m, x (R + i) = m * μ := fun m hm => by
    rw [sum_congr rfl fun i hi => hmid (R + i) (by omega) (by simp at hi; omega)]
    simp
  have hA : ∑ i ∈ range (3 * t + 2), x i = ∑ i ∈ range R, x i + k * μ := by
    rw [← hRk, sum_range_add, hconst k (by omega)]
  have hright : ∑ i ∈ range R, x (R + M + i) = ∑ i ∈ range R, x i := by
    rw [← sum_range_reflect]
    exact sum_congr rfl fun i hi => by
      simp at hi
      rw [← hsym i hi]
      congr 1; omega
  have htot : ∑ i ∈ range (2 * R + M), x i = 2 * ∑ i ∈ range R, x i + M * μ := by
    rw [show 2 * R + M = R + M + R by ring, sum_range_add, sum_range_add, hconst M le_rfl, hright]
    ring
  have hRk' : (R : ℝ) + k = 3 * t + 2 := by exact_mod_cast hRk
  have hMk : (2 * k : ℝ) ≤ M := by exact_mod_cast (by omega : 2 * k ≤ M)
  rw [htot]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.2 hMk) (sub_nonneg.2 hμ)]

end Op4
