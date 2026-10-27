import Mathlib

/-!
# Symmetric fractional dominating sets of paths lose an additive 2/3

Vertices of `P_L` are `0, …, L-1` with `L = 2R + M`. Under uniformly random identifiers, the expected
output of an `r`-round algorithm (`R = r + 1`) is a fractional dominating set that takes one value `μ`
on the `M` middle vertices, which have isomorphic views, and is invariant under the reflection
`v ↦ L-1-v`. `path_excess`: such a fractional dominating set has weight at least `L/3 + 2/3` once
`M ≥ 4`. No nonnegativity is needed.

`path_gamma`: `γ(P_{3m}) = γ_f(P_{3m}) = m`. `path_lower`: for `L = 2r + 6 + (r mod 3)` we have
`3 ∣ L`, the weight is at least `(1 + 2/L)·γ_f(P_L)`, and `1 + 2/L ≥ 1 + 1/(r+4)`. `rounds_lower`: a
ratio of at most `1 + ε` then forces `r ≥ 1/ε - 4`.

Only the domination constraints used by the proof enter: the left end `x 0 + x 1 ≥ 1` and the
interior vertices `u + 1` with closed neighbourhood `{u, u+1, u+2}`.

## Not formalised
The symmetrisation over identifiers (paper, Theorem `thm:lower`): the passage from an algorithm to
a fractional dominating set that is constant on the middle and invariant under reflection.
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

/-- The triples `{3j, 3j+1, 3j+2}` are the closed neighbourhoods `N[3j+1]`, so every fractional
dominating set of `P_L` has weight at least `m` on its first `3m ≤ L` vertices. -/
lemma path_triples (x : ℕ → ℝ) (L : ℕ)
    (hd : ∀ u, u + 2 < L → 1 ≤ x u + x (u + 1) + x (u + 2)) :
    ∀ m, 3 * m ≤ L → (m : ℝ) ≤ ∑ i ∈ range (3 * m), x i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have := hd (3 * m) (by omega)
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ]
    push_cast
    linarith [ih (by omega)]

/-- The vertices `1, 4, 7, …` of the path. -/
noncomputable def pathDom (i : ℕ) : ℝ := if i % 3 = 1 then 1 else 0

lemma pathDom_nonneg (i : ℕ) : 0 ≤ pathDom i := by unfold pathDom; split_ifs <;> norm_num

lemma pathDom_sum (m : ℕ) : ∑ i ∈ range (3 * m), pathDom i = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
      ih]
    unfold pathDom
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    push_cast; ring

/-- **`γ(P_{3m}) = γ_f(P_{3m}) = m`.** The vertices `1, 4, …, 3m-2` form a dominating set of `P_{3m}`
(all closed neighbourhoods `{0,1}`, `{u,u+1,u+2}` and `{3m-2,3m-1}` are hit), and every fractional
dominating set has weight at least `m`. -/
theorem path_gamma (m : ℕ) (hm : 1 ≤ m) :
    (1 ≤ pathDom 0 + pathDom 1 ∧ 1 ≤ pathDom (3 * m - 2) + pathDom (3 * m - 1) ∧
      (∀ u, u + 2 < 3 * m → 1 ≤ pathDom u + pathDom (u + 1) + pathDom (u + 2)) ∧
      ∑ i ∈ range (3 * m), pathDom i = m) ∧
    ∀ x : ℕ → ℝ, (∀ u, u + 2 < 3 * m → 1 ≤ x u + x (u + 1) + x (u + 2)) →
      (m : ℝ) ≤ ∑ i ∈ range (3 * m), x i := by
  refine ⟨⟨?_, ?_, ?_, pathDom_sum m⟩, fun x hd => path_triples x (3 * m) hd m le_rfl⟩
  · unfold pathDom; norm_num
  · have := pathDom_nonneg (3 * m - 1)
    have h : pathDom (3 * m - 2) = 1 := by unfold pathDom; rw [ite_eq_left (by omega)]
    linarith
  · intro u _
    have h0 := pathDom_nonneg u
    have h1 := pathDom_nonneg (u + 1)
    have h2 := pathDom_nonneg (u + 2)
    rcases (by omega : u % 3 = 1 ∨ (u + 1) % 3 = 1 ∨ (u + 2) % 3 = 1) with h | h | h
    · have : pathDom u = 1 := by unfold pathDom; rw [ite_eq_left h]
      linarith
    · have : pathDom (u + 1) = 1 := by unfold pathDom; rw [ite_eq_left h]
      linarith
    · have : pathDom (u + 2) = 1 := by unfold pathDom; rw [ite_eq_left h]
      linarith

/-- **Theorem `thm:lower`, counting part.** Let `R = r + 1`, `M = 4 + (r mod 3)` and
`L = 2R + M = 2r + 6 + (r mod 3)`. Then `3 ∣ L`, so `γ(P_L) = γ_f(P_L) = L/3` by `path_gamma`. Every
fractional dominating set of `P_L` that takes one value on the `M` middle vertices and is invariant
under reflection has weight at least `(1 + 2/L)·L/3`, and `1 + 2/L ≥ 1 + 1/(r+4)`. -/
theorem path_lower (r : ℕ) (x : ℕ → ℝ) (μ : ℝ)
    (h0 : 1 ≤ x 0 + x 1)
    (hd : ∀ u, u + 2 < 2 * (r + 1) + (4 + r % 3) → 1 ≤ x u + x (u + 1) + x (u + 2))
    (hmid : ∀ i, r + 1 ≤ i → i < r + 1 + (4 + r % 3) → x i = μ)
    (hsym : ∀ i, i < r + 1 → x (2 * (r + 1) + (4 + r % 3) - 1 - i) = x i) :
    3 ∣ 2 * (r + 1) + (4 + r % 3) ∧
    (1 + 2 / ((2 * (r + 1) + (4 + r % 3) : ℕ) : ℝ)) * (((2 * (r + 1) + (4 + r % 3) : ℕ) : ℝ) / 3)
      ≤ ∑ i ∈ range (2 * (r + 1) + (4 + r % 3)), x i ∧
    1 + 1 / ((r : ℝ) + 4) ≤ 1 + 2 / ((2 * (r + 1) + (4 + r % 3) : ℕ) : ℝ) := by
  have hex := path_excess x (r + 1) (4 + r % 3) μ (by omega) h0 hd hmid hsym
  set L := 2 * (r + 1) + (4 + r % 3) with hLdef
  have hL : (0 : ℝ) < L := by positivity
  have hL8 : (L : ℝ) ≤ 2 * r + 8 := by
    have : L ≤ 2 * r + 8 := by omega
    exact_mod_cast this
  refine ⟨by omega, ?_, ?_⟩
  · have e : (1 + 2 / (L : ℝ)) * ((L : ℝ) / 3) = (L : ℝ) / 3 + 2 / 3 := by field_simp
    rw [e]; exact hex
  · have hr : (0 : ℝ) < r + 4 := by positivity
    have : 1 / ((r : ℝ) + 4) ≤ 2 / L := by
      rw [div_le_div_iff₀ hr hL]; linarith
    linarith

/-- **Rounds.** If ratio `1 + 1/(r+4)` is at most `1 + ε`, then `r ≥ 1/ε - 4`. -/
theorem rounds_lower {r : ℕ} {ε : ℝ} (hε : 0 < ε) (h : 1 + 1 / ((r : ℝ) + 4) ≤ 1 + ε) :
    1 / ε - 4 ≤ r := by
  have hr : (0 : ℝ) < r + 4 := by positivity
  have h1 : 1 ≤ ε * ((r : ℝ) + 4) := (div_le_iff₀ hr).1 (by linarith)
  have h2 : 1 / ε ≤ (r : ℝ) + 4 := (div_le_iff₀ hε).2 (by linarith)
  linarith

end Op4
