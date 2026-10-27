import Op4.LocalRandom

/-!
# Theorem `thm:lower` for randomized algorithms with arbitrary coins

The model of `Op4.LocalRandom`, with the coins in an arbitrary probability space `(Ω, μ)`: every
position draws its coin independently with law `μ`, so the coin vector has law `μ^L`
(`Measure.pi`). This covers algorithms with real-valued randomness (uniform values, exponential
clocks) and with an unbounded number of random bits. The expected output at `v` is
`∫ A(rview r σ c v) dμ^L(c)`, and the only requirement is that it exists: the output at `v` is
integrable in the coins (`hint`). This holds, for instance, if it is measurable and bounded, as for
an algorithm that outputs a dominating set.

## Results
* `measure_path_lower`: if the output is a fractional dominating set of `P_L` for every identifier
  assignment and every outcome of the coins, then for `L = 2r + 6 + (r mod 3)` some identifier
  assignment has expected total weight at least `(1 + 2/L)·L/3`.
* `measure_ratio`, `measure_rounds_lower`: the expected ratio is at least `1 + 1/(r+4)`, and
  expected ratio at most `1 + ε` for every identifier assignment forces `r ≥ 1/ε - 4`.

The proof is that of `Op4.LocalRandom`: permuting the coordinates of an i.i.d. vector preserves
its law (`measurePreserving_arrowCongr'`), so the averaged output is invariant under the
reflection and the shift, and `family_lower` applies.
-/

open Finset MeasureTheory

namespace Op4

section LocalMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected output at position `v` when the coins are i.i.d. with law `μ`. -/
noncomputable def mout {L N r : ℕ} (μ : Measure Ω) (A : RView r N Ω → ℝ) (σ : Fin L ↪ Fin N)
    (v : ℕ) : ℝ :=
  ∫ c, rout A σ c v ∂(Measure.pi fun _ : Fin L => μ)

/-- Precomposing an i.i.d. coin vector with a permutation of the positions preserves its law. -/
lemma integral_coins_perm {L : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : Equiv.Perm (Fin L)) (F : (Fin L → Ω) → ℝ) :
    ∫ c, F (c ∘ π) ∂(Measure.pi fun _ : Fin L => μ) = ∫ c, F c ∂(Measure.pi fun _ : Fin L => μ) := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin L => μ) (fun _ : Fin L => μ) π.symm
    (MeasurableEquiv.refl Ω) (fun _ => MeasurePreserving.id μ)
  rw [← h.integral_comp' F]
  rfl

/-- The expected output of an algorithm that always outputs a fractional dominating set is one. -/
lemma mout_dom {L N r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RView r N Ω → ℝ)
    (σ : Fin L ↪ Fin N)
    (hint : ∀ v, Integrable (fun c => rout A σ c v) (Measure.pi fun _ : Fin L => μ))
    (h : ∀ c, FracDomPath L (rout A σ c)) : FracDomPath L (mout μ A σ) := by
  have key : ∀ F : (Fin L → Ω) → ℝ, Integrable F (Measure.pi fun _ : Fin L => μ) →
      (∀ c, 1 ≤ F c) → 1 ≤ ∫ c, F c ∂(Measure.pi fun _ : Fin L => μ) := by
    intro F hF h1
    calc (1 : ℝ) = ∫ _c, (1 : ℝ) ∂(Measure.pi fun _ : Fin L => μ) := by simp
      _ ≤ ∫ c, F c ∂(Measure.pi fun _ : Fin L => μ) := integral_mono (integrable_const 1) hF h1
  unfold FracDomPath mout
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · rw [← integral_add (hint 0) (hint 1)]
    exact key _ ((hint 0).add (hint 1)) fun c => (h c).1
  · rw [← integral_add (hint (L - 2)) (hint (L - 1))]
    exact key _ ((hint (L - 2)).add (hint (L - 1))) fun c => (h c).2.1
  · have h2 : Integrable (fun c => rout A σ c u + rout A σ c (u + 1))
        (Measure.pi fun _ : Fin L => μ) := (hint u).add (hint (u + 1))
    rw [← integral_add (hint u) (hint (u + 1)), ← integral_add h2 (hint (u + 2))]
    exact key _ (h2.add (hint (u + 2))) fun c => (h c).2.2 u hu

/-- **Theorem `thm:lower` for randomized algorithms with arbitrary coins.** Let
`L = 2r + 6 + (r mod 3)` and `N ≥ L`, and let the coins be i.i.d. with law `μ`. For every
randomized `r`-round algorithm whose output is a fractional dominating set of `P_L` for every
identifier assignment and every outcome of the coins, and is integrable in the coins, some
identifier assignment gives expected total weight at least `(1 + 2/L)·L/3`. -/
theorem measure_path_lower (r N : ℕ) (hN : pl r ≤ N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hint : ∀ (σ : Fin (pl r) ↪ Fin N) v,
      Integrable (fun c => rout A σ c v) (Measure.pi fun _ : Fin (pl r) => μ))
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 2 / ((pl r : ℕ) : ℝ)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), mout μ A σ i := by
  have hLr : pl r = 2 * (r + 1) + (4 + r % 3) := rfl
  have : NeZero (pl r) := ⟨by omega⟩
  have hk : 1 < pl r := by omega
  refine family_lower r N hN (mout μ A) (fun σ => mout_dom μ A σ (hint σ) (hdom σ))
    (fun σ i hi => ?_) (Equiv.addRight (⟨1, hk⟩ : Fin (pl r))) (fun σ v h1 h2 => ?_)
  · unfold mout
    rw [← integral_coins_perm μ Fin.revPerm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [rout]
    rw [ite_eq_left (by omega), ite_eq_left hi, rview_rev r σ c i hi, hrev]
  · unfold mout
    rw [← integral_coins_perm μ (Equiv.addRight (⟨1, hk⟩ : Fin (pl r)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [rout]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), rview_shift r hk σ c v h1 h2]

/-- **Ratio.** Some identifier assignment gives expected weight at least `(1 + 1/(r+4))·γ_f(P_L)`. -/
theorem measure_ratio (r N : ℕ) (hN : pl r ≤ N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hint : ∀ (σ : Fin (pl r) ↪ Fin N) v,
      Integrable (fun c => rout A σ c v) (Measure.pi fun _ : Fin (pl r) => μ))
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c)) :
    ∃ σ : Fin (pl r) ↪ Fin N,
      (1 + 1 / ((r : ℝ) + 4)) * (((pl r : ℕ) : ℝ) / 3) ≤ ∑ i ∈ range (pl r), mout μ A σ i := by
  obtain ⟨σ, hσ⟩ := measure_path_lower r N hN μ A hrev hint hdom
  exact ⟨σ, le_trans (mul_le_mul_of_nonneg_right (ratio_le r) (by positivity)) hσ⟩

/-- **Rounds.** If the expected ratio is at most `1 + ε` for every identifier assignment, then
`r ≥ 1/ε - 4`. -/
theorem measure_rounds_lower (r N : ℕ) (hN : pl r ≤ N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : RView r N Ω → ℝ) (hrev : ∀ w : RView r N Ω, A (w ∘ Fin.rev) = A w)
    (hint : ∀ (σ : Fin (pl r) ↪ Fin N) v,
      Integrable (fun c => rout A σ c v) (Measure.pi fun _ : Fin (pl r) => μ))
    (hdom : ∀ (σ : Fin (pl r) ↪ Fin N) (c : Fin (pl r) → Ω), FracDomPath (pl r) (rout A σ c))
    {ε : ℝ} (hε : 0 < ε)
    (hratio : ∀ σ : Fin (pl r) ↪ Fin N,
      ∑ i ∈ range (pl r), mout μ A σ i ≤ (1 + ε) * (((pl r : ℕ) : ℝ) / 3)) :
    1 / ε - 4 ≤ r := by
  obtain ⟨σ, hσ⟩ := measure_ratio r N hN μ A hrev hint hdom
  have hL : (0 : ℝ) < ((pl r : ℕ) : ℝ) / 3 := by positivity
  exact rounds_lower hε (le_of_mul_le_mul_right (le_trans hσ (hratio σ)) hL)

end LocalMeasure

end Op4

