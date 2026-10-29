import Op4.PathLower

/-!
# Theorem `thm:lower` in the LOCAL model on paths

This file removes the last hypothesis of `path_lower`: the symmetrization over identifiers.

## The model
* The path `P_L` has positions `0, …, L-1`; position `u` has degree `pdeg L u ∈ {1, 2}`.
* An identifier assignment is an injective map `σ : Fin L ↪ Fin N` into a finite identifier space
  of size `N ≥ L`.
* The view of `v` after `r` rounds (`view r σ v`) is its radius-`r` ball with the identifiers and the
  degrees in `P_L` of its vertices: entry `i : Fin (2r+1)` describes position `v + i - r`, and is
  `none` if that position does not exist. The ball of a path has no left and right, so an algorithm
  must not depend on the direction in which the ball is listed: `A (w ∘ Fin.rev) = A w`.
* A deterministic `r`-round algorithm is a map `A` from views to reals, its output. It may depend
  on `L`, `N` and `r`, that is, it knows the graph. The hypothesis is that `v ↦ A (view r σ v)` is a
  fractional dominating set of `P_L` for every `σ` (`FracDomPath`). Randomized algorithms, with
  explicit coins, are in `Op4.LocalRandom`.

## Results
* `local_path_lower`: for `L = 2r + 6 + (r mod 3)` some identifier assignment forces total weight at
  least `(1 + 2/L)·L/3`, where `L/3 = γ(P_L) = γ_f(P_L)` by `path_gamma` (and `3 ∣ L`).
* `local_ratio`: the ratio is at least `1 + 1/(r+4)`.
* `local_rounds_lower`: if the ratio is at most `1 + ε` for every identifier assignment, then
  `r ≥ 1/ε - 4`.

The proof averages over all identifier assignments. Precomposing `σ` with a permutation of the
positions is a bijection of the assignments, so the average is invariant under the reflection
`v ↦ L-1-v` and takes one value on the middle vertices, whose balls are full paths of degree-2
vertices. Then `path_lower` applies, and some assignment is at least as bad as the average.
-/

open Finset

namespace Op4

section LocalPath

/-- Degree of position `u` in the path `P_L`. -/
def pdeg (L u : ℕ) : ℕ := (if 0 < u then 1 else 0) + (if u + 1 < L then 1 else 0)

/-- A view after `r` rounds: entry `i` describes the position at offset `i - r`. -/
abbrev View (r N : ℕ) := Fin (2 * r + 1) → Option (Fin N × ℕ)

/-- The view of position `v`: identifier and degree of every position `v + i - r` of the ball. -/
def view {L N : ℕ} (r : ℕ) (σ : Fin L ↪ Fin N) (v : ℕ) : View r N := fun i =>
  if h : r ≤ v + i ∧ v + i - r < L then some (σ ⟨v + i - r, h.2⟩, pdeg L (v + i - r)) else none

/-- The output of the algorithm `A` at position `v` (zero outside the path). -/
noncomputable def out {L N r : ℕ} (A : View r N → ℝ) (σ : Fin L ↪ Fin N) (v : ℕ) : ℝ :=
  if v < L then A (view r σ v) else 0

/-- `x` is a fractional dominating set of `P_L`: the closed neighbourhoods are `{0, 1}`,
`{L-2, L-1}` and `{u, u+1, u+2}`. -/
def FracDomPath (L : ℕ) (x : ℕ → ℝ) : Prop :=
  1 ≤ x 0 + x 1 ∧ 1 ≤ x (L - 2) + x (L - 1) ∧ ∀ u, u + 2 < L → 1 ≤ x u + x (u + 1) + x (u + 2)

/-- Precomposing with a permutation of the positions permutes the identifier assignments. -/
lemma sum_comp_perm {L N : ℕ} (π : Equiv.Perm (Fin L)) (F : (Fin L ↪ Fin N) → ℝ) :
    ∑ σ, F (π.toEmbedding.trans σ) = ∑ σ, F σ := by
  let e : (Fin L ↪ Fin N) ≃ (Fin L ↪ Fin N) :=
    { toFun := fun σ => π.toEmbedding.trans σ
      invFun := fun σ => π.symm.toEmbedding.trans σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Reflection: the view of `L-1-v` under `σ ∘ rev` is the view of `v` under `σ`, read backwards. -/
lemma view_rev {L N : ℕ} (r : ℕ) (σ : Fin L ↪ Fin N) (v : ℕ) (hv : v < L) :
    view r (Fin.revPerm.toEmbedding.trans σ) (L - 1 - v) = view r σ v ∘ Fin.rev := by
  funext i
  have hi := i.isLt
  simp only [view, Function.comp_apply, Fin.val_rev]
  split_ifs with h1 h2 h2
  · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.revPerm_apply,
      Option.some.injEq, Prod.mk.injEq]
    refine ⟨congrArg σ (Fin.ext ?_), ?_⟩
    · simp only [Fin.val_rev]; omega
    · unfold pdeg; split_ifs <;> omega
  · exact (h2 ⟨by omega, by omega⟩).elim
  · exact (h1 ⟨by omega, by omega⟩).elim
  · rfl

/-- Shift: the view of `v` under `σ ∘ (· + 1)` is the view of `v + 1` under `σ`, when both balls
are full and consist of vertices of degree 2. -/
lemma view_shift {L N : ℕ} [NeZero L] (r : ℕ) (hL : 1 < L) (σ : Fin L ↪ Fin N) (v : ℕ)
    (hv : r + 1 ≤ v) (hv' : v + r + 3 ≤ L) :
    view r ((Equiv.addRight (⟨1, hL⟩ : Fin L)).toEmbedding.trans σ) v = view r σ (v + 1) := by
  funext i
  have hi := i.isLt
  simp only [view]
  split_ifs with h1 h2 h2
  · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_addRight,
      Option.some.injEq, Prod.mk.injEq]
    refine ⟨congrArg σ (Fin.ext ?_), ?_⟩
    · rw [Fin.val_add]; simp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · unfold pdeg; split_ifs <;> omega
  · exact (h2 ⟨by omega, by omega⟩).elim
  · exact (h1 ⟨by omega, by omega⟩).elim
  · rfl

/-- The path length `L = 2(r+1) + 4 + (r mod 3)` of Theorem `thm:lower`. -/
abbrev pl (r : ℕ) : ℕ := 2 * (r + 1) + (4 + r % 3)

lemma three_dvd_pl (r : ℕ) : 3 ∣ pl r := by unfold pl; omega

/-- **Theorem `thm:lower` in the LOCAL model.** Let `L = 2r + 6 + (r mod 3)` and `N ≥ L`. For every
`r`-round algorithm `A` whose output is a fractional dominating set of `P_L` for every identifier
assignment, some identifier assignment gives total weight at least `(1 + 2/L)·L/3`. -/
theorem local_path_lower (r N : ℕ) (hN : pl r ≤ N) (A : View r N → ℝ)
    (hrev : ∀ w : View r N, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ σ : Fin (pl r) ↪ Fin N, FracDomPath (pl r) (out A σ)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), out A σ i := by
  have hLr : pl r = 2 * (r + 1) + (4 + r % 3) := rfl
  have : NeZero (pl r) := ⟨by omega⟩
  have : Nonempty (Fin (pl r) ↪ Fin N) := ⟨⟨Fin.castLE hN, Fin.castLE_injective hN⟩⟩
  set c : ℝ := (Fintype.card (Fin (pl r) ↪ Fin N) : ℝ) with hc_def
  have hc : 0 < c := by rw [hc_def]; exact_mod_cast Fintype.card_pos
  -- the average output over all identifier assignments
  set x : ℕ → ℝ := fun i => (∑ σ : Fin (pl r) ↪ Fin N, out A σ i) / c with hx
  have avg : ∀ F : (Fin (pl r) ↪ Fin N) → ℝ, (∀ σ, 1 ≤ F σ) → 1 ≤ (∑ σ, F σ) / c := by
    intro F hF
    rw [le_div_iff₀ hc]
    have := sum_le_sum fun σ (_ : σ ∈ (univ : Finset (Fin (pl r) ↪ Fin N))) => hF σ
    simpa [hc_def] using this
  have h0 : 1 ≤ x 0 + x 1 := by
    have := avg (fun σ => out A σ 0 + out A σ 1) fun σ => (hdom σ).1
    rw [sum_add_distrib, add_div] at this
    exact this
  have hd : ∀ u, u + 2 < pl r → 1 ≤ x u + x (u + 1) + x (u + 2) := by
    intro u hu
    have := avg (fun σ => out A σ u + out A σ (u + 1) + out A σ (u + 2)) fun σ => (hdom σ).2.2 u hu
    rw [sum_add_distrib, sum_add_distrib, add_div, add_div] at this
    exact this
  -- reflection invariance
  have hsymm : ∀ i, i < pl r → x (pl r - 1 - i) = x i := by
    intro i hi
    simp only [hx]
    congr 1
    calc ∑ σ : Fin (pl r) ↪ Fin N, out A σ (pl r - 1 - i)
        = ∑ σ : Fin (pl r) ↪ Fin N, out A (Fin.revPerm.toEmbedding.trans σ) (pl r - 1 - i) :=
          (sum_comp_perm Fin.revPerm (fun σ => out A σ (pl r - 1 - i))).symm
      _ = ∑ σ : Fin (pl r) ↪ Fin N, out A σ i := sum_congr rfl fun σ _ => by
          unfold out
          rw [ite_eq_left (by omega), ite_eq_left hi, view_rev r σ i hi, hrev]
  -- the middle vertices have the same value
  have hshift : ∀ v, r + 1 ≤ v → v + r + 3 ≤ pl r → x v = x (v + 1) := by
    intro v h1 h2
    have hk : 1 < pl r := by omega
    simp only [hx]
    congr 1
    calc ∑ σ : Fin (pl r) ↪ Fin N, out A σ v
        = ∑ σ : Fin (pl r) ↪ Fin N, out A ((Equiv.addRight (⟨1, hk⟩ : Fin (pl r))).toEmbedding.trans σ) v :=
          (sum_comp_perm (Equiv.addRight (⟨1, hk⟩ : Fin (pl r))) (fun σ => out A σ v)).symm
      _ = ∑ σ : Fin (pl r) ↪ Fin N, out A σ (v + 1) := sum_congr rfl fun σ _ => by
          unfold out
          rw [ite_eq_left (by omega), ite_eq_left (by omega), view_shift r hk σ v h1 h2]
  have hmid : ∀ i, r + 1 ≤ i → i < r + 1 + (4 + r % 3) → x i = x (r + 1) := by
    intro i h1 h2
    induction i, h1 using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [← hshift n hn (by omega), ih (by omega)]
  obtain ⟨-, hbound, -⟩ := path_lower r x (x (r + 1)) h0 hd hmid fun i hi => hsymm i (by omega)
  -- some assignment is at least as bad as the average
  have hsum : ∑ i ∈ range (pl r), x i = (∑ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), out A σ i) / c := by
    simp only [hx]
    rw [← sum_div, sum_comm]
  by_contra hcon
  have hcon' : ∀ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), out A σ i
      < (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) := fun σ => not_le.1 fun h => hcon ⟨σ, h⟩
  have hlt : ∑ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), out A σ i
      < ∑ _σ : Fin (pl r) ↪ Fin N, (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) :=
    sum_lt_sum_of_nonempty univ_nonempty fun σ _ => hcon' σ
  rw [sum_const, card_univ, nsmul_eq_mul] at hlt
  rw [hsum, le_div_iff₀ hc] at hbound
  rw [hc_def] at hbound
  linarith

/-- `1 + 1/(r+4) ≤ 1 + 2/L`, since `L ≤ 2r + 8`. -/
lemma ratio_le (r : ℕ) : 1 + 1 / ((r : ℝ) + 4) ≤ 1 + 2 / ((pl r : ℕ) : ℝ) := by
  have hL : (0 : ℝ) < (pl r : ℕ) := by positivity
  have hL8 : ((pl r : ℕ) : ℝ) ≤ 2 * r + 8 := by
    have : pl r ≤ 2 * r + 8 := by unfold pl; omega
    exact_mod_cast this
  have hr : (0 : ℝ) < r + 4 := by positivity
  have : 1 / ((r : ℝ) + 4) ≤ 2 / ((pl r : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hr hL]; linarith
  linarith

/-- **Ratio.** Some identifier assignment gives weight at least `(1 + 1/(r+4))·γ_f(P_L)`. -/
theorem local_ratio (r N : ℕ) (hN : pl r ≤ N) (A : View r N → ℝ)
    (hrev : ∀ w : View r N, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ σ : Fin (pl r) ↪ Fin N, FracDomPath (pl r) (out A σ)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 1 / ((r : ℝ) + 4)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), out A σ i := by
  obtain ⟨σ, hσ⟩ := local_path_lower r N hN A hrev hdom
  exact ⟨σ, le_trans (mul_le_mul_of_nonneg_right (ratio_le r) (by positivity)) hσ⟩

/-- **Rounds.** If an `r`-round algorithm has ratio at most `1 + ε` on `P_L` for every identifier
assignment, measured against `γ_f(P_L) = L/3` (`path_gamma`), then `r ≥ 1/ε - 4`. -/
theorem local_rounds_lower (r N : ℕ) (hN : pl r ≤ N) (A : View r N → ℝ)
    (hrev : ∀ w : View r N, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ σ : Fin (pl r) ↪ Fin N, FracDomPath (pl r) (out A σ))
    {ε : ℝ} (hε : 0 < ε)
    (hratio : ∀ σ : Fin (pl r) ↪ Fin N,
      ∑ i ∈ range (pl r), out A σ i ≤ (1 + ε) * (((pl r : ℕ) : ℝ) / 3)) :
    1 / ε - 4 ≤ r := by
  obtain ⟨σ, hσ⟩ := local_ratio r N hN A hrev hdom
  have hL : (0 : ℝ) < ((pl r : ℕ) : ℝ) / 3 := by positivity
  have h := le_trans hσ (hratio σ)
  exact rounds_lower hε (le_of_mul_le_mul_right h hL)

end LocalPath

end Op4
