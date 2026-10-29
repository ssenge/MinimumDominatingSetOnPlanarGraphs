import Op4.LocalPath

/-!
# Theorem `thm:lower` for randomized algorithms

The model of `Op4.LocalPath`, with coins. Every position `j` of `P_L` draws a coin `c j` from a
finite set `Ω`, independently with distribution `μ` and independently of the identifiers.
* The view of `v` after `r` rounds (`rview r σ c v`) is its radius-`r` ball with the identifiers,
  the degrees in `P_L` and the coins of its vertices. As before, the algorithm is a map `A` from
  views to reals that does not depend on the direction in which the ball is listed, and it may
  depend on `L`, `N`, `r`, `Ω` and `μ`.
* The expected output at `v` is `eout μ A σ v = Σ_c P(c)·A(rview r σ c v)`, with
  `P(c) = Π_j μ(c j)`.

## Results
* `random_path_lower`: if the output is a fractional dominating set of `P_L` for every identifier
  assignment and every outcome of the coins (in particular, if it always is a dominating set), then
  for `L = 2r + 6 + (r mod 3)` some identifier assignment has expected total weight at least
  `(1 + 2/L)·L/3`.
* `random_ratio`, `random_rounds_lower`: the expected ratio is at least `1 + 1/(r+4)`, and expected
  ratio at most `1 + ε` for every identifier assignment forces `r ≥ 1/ε - 4`.

The proof averages over the identifier assignments and the coins together. Precomposing both with
a permutation of the positions preserves the distribution of the coins, so the average is again
invariant under the reflection and constant on the middle vertices (`family_lower`).

Here the coins take finitely many values, so expectations are finite sums. `Op4.LocalMeasure`
allows coins in an arbitrary probability space.
-/

open Finset

namespace Op4

/-- **Averaging.** A family of fractional dominating sets of `P_L`, indexed by the identifier
assignments, that transforms under the reflection and under a shift `π` like the output of a local
algorithm, has a member of weight at least `(1 + 2/L)·L/3`. -/
lemma family_lower (r N : ℕ) (hN : pl r ≤ N) (y : (Fin (pl r) ↪ Fin N) → ℕ → ℝ)
    (hdom : ∀ σ, FracDomPath (pl r) (y σ))
    (hrev : ∀ σ i, i < pl r → y (Fin.revPerm.toEmbedding.trans σ) (pl r - 1 - i) = y σ i)
    (π : Equiv.Perm (Fin (pl r)))
    (hshift : ∀ σ v, r + 1 ≤ v → v + r + 3 ≤ pl r → y (π.toEmbedding.trans σ) v = y σ (v + 1)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), y σ i := by
  have hLr : pl r = 2 * (r + 1) + (4 + r % 3) := rfl
  have : Nonempty (Fin (pl r) ↪ Fin N) := ⟨⟨Fin.castLE hN, Fin.castLE_injective hN⟩⟩
  set c : ℝ := (Fintype.card (Fin (pl r) ↪ Fin N) : ℝ) with hc_def
  have hc : 0 < c := by rw [hc_def]; exact_mod_cast Fintype.card_pos
  set x : ℕ → ℝ := fun i => (∑ σ : Fin (pl r) ↪ Fin N, y σ i) / c with hx
  have avg : ∀ F : (Fin (pl r) ↪ Fin N) → ℝ, (∀ σ, 1 ≤ F σ) → 1 ≤ (∑ σ, F σ) / c := by
    intro F hF
    rw [le_div_iff₀ hc]
    have := sum_le_sum fun σ (_ : σ ∈ (univ : Finset (Fin (pl r) ↪ Fin N))) => hF σ
    simpa [hc_def] using this
  have h0 : 1 ≤ x 0 + x 1 := by
    have := avg (fun σ => y σ 0 + y σ 1) fun σ => (hdom σ).1
    rw [sum_add_distrib, add_div] at this
    exact this
  have hd : ∀ u, u + 2 < pl r → 1 ≤ x u + x (u + 1) + x (u + 2) := by
    intro u hu
    have := avg (fun σ => y σ u + y σ (u + 1) + y σ (u + 2)) fun σ => (hdom σ).2.2 u hu
    rw [sum_add_distrib, sum_add_distrib, add_div, add_div] at this
    exact this
  have hsymm : ∀ i, i < pl r → x (pl r - 1 - i) = x i := by
    intro i hi
    simp only [hx]
    congr 1
    calc ∑ σ : Fin (pl r) ↪ Fin N, y σ (pl r - 1 - i)
        = ∑ σ : Fin (pl r) ↪ Fin N, y (Fin.revPerm.toEmbedding.trans σ) (pl r - 1 - i) :=
          (sum_comp_perm Fin.revPerm (fun σ => y σ (pl r - 1 - i))).symm
      _ = ∑ σ : Fin (pl r) ↪ Fin N, y σ i := sum_congr rfl fun σ _ => hrev σ i hi
  have hsh : ∀ v, r + 1 ≤ v → v + r + 3 ≤ pl r → x v = x (v + 1) := by
    intro v h1 h2
    simp only [hx]
    congr 1
    calc ∑ σ : Fin (pl r) ↪ Fin N, y σ v
        = ∑ σ : Fin (pl r) ↪ Fin N, y (π.toEmbedding.trans σ) v :=
          (sum_comp_perm π (fun σ => y σ v)).symm
      _ = ∑ σ : Fin (pl r) ↪ Fin N, y σ (v + 1) := sum_congr rfl fun σ _ => hshift σ v h1 h2
  have hmid : ∀ i, r + 1 ≤ i → i < r + 1 + (4 + r % 3) → x i = x (r + 1) := by
    intro i h1 h2
    induction i, h1 using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [← hsh n hn (by omega), ih (by omega)]
  obtain ⟨-, hbound, -⟩ := path_lower r x (x (r + 1)) h0 hd hmid fun i hi => hsymm i (by omega)
  have hsum : ∑ i ∈ range (pl r), x i = (∑ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), y σ i) / c := by
    simp only [hx]
    rw [← sum_div, sum_comm]
  by_contra hcon
  have hcon' : ∀ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), y σ i
      < (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) := fun σ => not_le.1 fun h => hcon ⟨σ, h⟩
  have hlt : ∑ σ : Fin (pl r) ↪ Fin N, ∑ i ∈ range (pl r), y σ i
      < ∑ _σ : Fin (pl r) ↪ Fin N, (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) :=
    sum_lt_sum_of_nonempty univ_nonempty fun σ _ => hcon' σ
  rw [sum_const, card_univ, nsmul_eq_mul] at hlt
  rw [hsum, le_div_iff₀ hc] at hbound
  rw [hc_def] at hbound
  linarith

section LocalRandom

variable {Ω : Type*} [Fintype Ω]

/-- A view of a randomized algorithm: identifier, degree and coin of every position of the ball. -/
abbrev RView (r N : ℕ) (Ω : Type*) := Fin (2 * r + 1) → Option ((Fin N × ℕ) × Ω)

/-- The view of position `v` under the identifiers `σ` and the coins `c`. -/
def rview {L N : ℕ} (r : ℕ) (σ : Fin L ↪ Fin N) (c : Fin L → Ω) (v : ℕ) : RView r N Ω := fun i =>
  if h : r ≤ v + i ∧ v + i - r < L then
    some ((σ ⟨v + i - r, h.2⟩, pdeg L (v + i - r)), c ⟨v + i - r, h.2⟩)
  else none

/-- The output at position `v` (zero outside the path). -/
noncomputable def rout {L N r : ℕ} (A : RView r N Ω → ℝ) (σ : Fin L ↪ Fin N) (c : Fin L → Ω)
    (v : ℕ) : ℝ :=
  if v < L then A (rview r σ c v) else 0

/-- The probability of the coin vector `c`. -/
noncomputable def cprob {L : ℕ} (μ : Ω → ℝ) (c : Fin L → Ω) : ℝ := ∏ j, μ (c j)

/-- The expected output at position `v`. -/
noncomputable def eout {L N r : ℕ} (μ : Ω → ℝ) (A : RView r N Ω → ℝ) (σ : Fin L ↪ Fin N)
    (v : ℕ) : ℝ :=
  ∑ c : Fin L → Ω, cprob μ c * rout A σ c v

omit [Fintype Ω] in
lemma cprob_nonneg {L : ℕ} {μ : Ω → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (c : Fin L → Ω) : 0 ≤ cprob μ c :=
  prod_nonneg fun j _ => hμ0 (c j)

lemma cprob_sum {L : ℕ} (μ : Ω → ℝ) (hμ1 : ∑ ω, μ ω = 1) : ∑ c : Fin L → Ω, cprob μ c = 1 := by
  unfold cprob
  rw [← Fintype.sum_pow, hμ1, one_pow]

/-- Precomposing the coins with a permutation of the positions preserves their distribution. -/
lemma sum_coins_perm {L : ℕ} (μ : Ω → ℝ) (π : Equiv.Perm (Fin L)) (F : (Fin L → Ω) → ℝ) :
    ∑ c, cprob μ c * F (c ∘ π) = ∑ c, cprob μ c * F c := by
  let e : (Fin L → Ω) ≃ (Fin L → Ω) :=
    { toFun := fun c => c ∘ π
      invFun := fun c => c ∘ π.symm
      left_inv := fun c => by funext j; simp
      right_inv := fun c => by funext j; simp }
  refine Fintype.sum_equiv e _ _ fun c => ?_
  show cprob μ c * F (c ∘ π) = cprob μ (c ∘ π) * F (c ∘ π)
  congr 1
  unfold cprob
  exact (Equiv.prod_comp π (fun j => μ (c j))).symm

/-- The expected output of an algorithm that always outputs a fractional dominating set is one. -/
lemma eout_dom {L N r : ℕ} (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (A : RView r N Ω → ℝ) (σ : Fin L ↪ Fin N) (h : ∀ c, FracDomPath L (rout A σ c)) :
    FracDomPath L (eout μ A σ) := by
  have key : ∀ F : (Fin L → Ω) → ℝ, (∀ c, 1 ≤ F c) → 1 ≤ ∑ c, cprob μ c * F c := by
    intro F hF
    calc (1 : ℝ) = ∑ c : Fin L → Ω, cprob μ c := (cprob_sum μ hμ1).symm
      _ ≤ ∑ c, cprob μ c * F c := sum_le_sum fun c _ => by
          have := cprob_nonneg hμ0 c
          nlinarith [hF c]
  unfold FracDomPath eout
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · have := key (fun c => rout A σ c 0 + rout A σ c 1) fun c => (h c).1
    simp only [mul_add, sum_add_distrib] at this
    exact this
  · have := key (fun c => rout A σ c (L - 2) + rout A σ c (L - 1)) fun c => (h c).2.1
    simp only [mul_add, sum_add_distrib] at this
    exact this
  · have := key (fun c => rout A σ c u + rout A σ c (u + 1) + rout A σ c (u + 2))
      fun c => (h c).2.2 u hu
    simp only [mul_add, sum_add_distrib] at this
    exact this

omit [Fintype Ω] in
/-- Reflection, as in `view_rev`. -/
lemma rview_rev {L N : ℕ} (r : ℕ) (σ : Fin L ↪ Fin N) (c : Fin L → Ω) (v : ℕ) (hv : v < L) :
    rview r (Fin.revPerm.toEmbedding.trans σ) (c ∘ Fin.revPerm) (L - 1 - v)
      = rview r σ c v ∘ Fin.rev := by
  funext i
  have hi := i.isLt
  simp only [rview, Function.comp_apply, Fin.val_rev]
  split_ifs with h1 h2 h2
  · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.revPerm_apply,
      Option.some.injEq, Prod.mk.injEq]
    refine ⟨⟨congrArg σ (Fin.ext ?_), ?_⟩, congrArg c (Fin.ext ?_)⟩
    · simp only [Fin.val_rev]; omega
    · unfold pdeg; split_ifs <;> omega
    · simp only [Fin.val_rev]; omega
  · exact (h2 ⟨by omega, by omega⟩).elim
  · exact (h1 ⟨by omega, by omega⟩).elim
  · rfl

omit [Fintype Ω] in
/-- Shift, as in `view_shift`. -/
lemma rview_shift {L N : ℕ} [NeZero L] (r : ℕ) (hL : 1 < L) (σ : Fin L ↪ Fin N) (c : Fin L → Ω)
    (v : ℕ) (hv : r + 1 ≤ v) (hv' : v + r + 3 ≤ L) :
    rview r ((Equiv.addRight (⟨1, hL⟩ : Fin L)).toEmbedding.trans σ)
      (c ∘ Equiv.addRight (⟨1, hL⟩ : Fin L)) v = rview r σ c (v + 1) := by
  funext i
  have hi := i.isLt
  simp only [rview]
  split_ifs with h1 h2 h2
  · simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_addRight,
      Function.comp_apply, Option.some.injEq, Prod.mk.injEq]
    refine ⟨⟨congrArg σ (Fin.ext ?_), ?_⟩, congrArg c (Fin.ext ?_)⟩
    · rw [Fin.val_add]; simp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · unfold pdeg; split_ifs <;> omega
    · rw [Fin.val_add]; simp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  · exact (h2 ⟨by omega, by omega⟩).elim
  · exact (h1 ⟨by omega, by omega⟩).elim
  · rfl

/-- **Theorem `thm:lower` for randomized algorithms.** Let `L = 2r + 6 + (r mod 3)` and `N ≥ L`.
For every randomized `r`-round algorithm whose output is a fractional dominating set of `P_L` for
every identifier assignment and every outcome of the coins, some identifier assignment gives
expected total weight at least `(1 + 2/L)·L/3`. -/
theorem random_path_lower (r N : ℕ) (hN : pl r ≤ N) (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), eout μ A σ i := by
  have hLr : pl r = 2 * (r + 1) + (4 + r % 3) := rfl
  have : NeZero (pl r) := ⟨by omega⟩
  have hk : 1 < pl r := by omega
  refine family_lower r N hN (eout μ A) (fun σ => eout_dom μ hμ0 hμ1 A σ (hdom σ))
    (fun σ i hi => ?_) (Equiv.addRight (⟨1, hk⟩ : Fin (pl r))) (fun σ v h1 h2 => ?_)
  · refine (sum_coins_perm μ Fin.revPerm _).symm.trans (sum_congr rfl fun c _ => ?_)
    congr 1
    unfold rout
    rw [ite_eq_left (by omega), ite_eq_left hi, rview_rev r σ c i hi, hrev]
  · refine (sum_coins_perm μ (Equiv.addRight (⟨1, hk⟩ : Fin (pl r))) _).symm.trans
      (sum_congr rfl fun c _ => ?_)
    congr 1
    unfold rout
    rw [ite_eq_left (by omega), ite_eq_left (by omega), rview_shift r hk σ c v h1 h2]

/-- **Ratio.** Some identifier assignment gives expected weight at least `(1 + 1/(r+4))·γ_f(P_L)`. -/
theorem random_ratio (r N : ℕ) (hN : pl r ≤ N) (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 1 / ((r : ℝ) + 4)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), eout μ A σ i := by
  obtain ⟨σ, hσ⟩ := random_path_lower r N hN μ hμ0 hμ1 A hrev hdom
  exact ⟨σ, le_trans (mul_le_mul_of_nonneg_right (ratio_le r) (by positivity)) hσ⟩

/-- **Rounds.** If the expected ratio is at most `1 + ε` for every identifier assignment, then
`r ≥ 1/ε - 4`. -/
theorem random_rounds_lower (r N : ℕ) (hN : pl r ≤ N) (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c))
    {ε : ℝ} (hε : 0 < ε)
    (hratio : ∀ σ : Fin (pl r) ↪ Fin N,
      ∑ i ∈ range (pl r), eout μ A σ i ≤ (1 + ε) * (((pl r : ℕ) : ℝ) / 3)) :
    1 / ε - 4 ≤ r := by
  obtain ⟨σ, hσ⟩ := random_ratio r N hN μ hμ0 hμ1 A hrev hdom
  have hL : (0 : ℝ) < ((pl r : ℕ) : ℝ) / 3 := by positivity
  exact rounds_lower hε (le_of_mul_le_mul_right (le_trans hσ (hratio σ)) hL)

end LocalRandom

end Op4

