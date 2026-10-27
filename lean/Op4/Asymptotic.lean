import Op4.RandomCentres

/-!
# The exponent ratio tends to 8

For a class of density `a`, the exponent of [1] is `κ(1 - 1/(8a))` and the new one is
`κ(1 - f)` with `f = (1-p)(1 - (1-p)^k)/k` and `k = ⌈a⌉` (`random_centres`). Their ratio is
`log(1/(1-f)) / log(1/(1-1/(8a)))`, and `x ≤ log(1/(1-x)) ≤ x/(1-x)` squeezes it between
`8af·(1 - 1/(8a))` and `8af/(1-f)`.

* `expRatio_tendsto_eight`: if `p → 0` and `a·p → ∞`, the ratio tends to `8`.
* `expRatio_tendsto_const`: for a fixed `p ∈ (0, 1]` it tends to `8(1-p)`.
* `dyadic_p`: `p = 2^{-j}` with `j = ⌊log₂ ⌈a⌉⌋ / 2` fair coins satisfies the hypotheses of the first.
* `never_worse`: for `a ≥ 1/2`, already `p = 1/2` gives an exponent at most that of [1].
-/

open Filter Topology

namespace Op4

section Asymptotic

/-- The per-level fraction of `random_centres` with `k = ⌈a⌉`. -/
noncomputable def fa (a p : ℝ) : ℝ := (1 - p) * (1 - (1 - p) ^ ⌈a⌉₊) / ⌈a⌉₊

/-- The exponent of [1] divided by the new exponent. -/
noncomputable def expRatio (a p : ℝ) : ℝ := kappa (1 - 1 / (8 * a)) / kappa (1 - fa a p)

lemma log_inv_one_sub_bounds {x : ℝ} (_h0 : 0 ≤ x) (h1 : x < 1) :
    x ≤ Real.log (1 / (1 - x)) ∧ Real.log (1 / (1 - x)) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have := Real.log_le_sub_one_of_pos (one_div_pos.2 hpos)
    have e : 1 / (1 - x) - 1 = x / (1 - x) := by field_simp; ring
    linarith

lemma fa_nonneg {a p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ fa a p := by
  unfold fa
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : (1 - p) ^ ⌈a⌉₊ ≤ 1 := pow_le_one₀ h1 (by linarith)
  have h3 : 0 ≤ 1 - (1 - p) ^ ⌈a⌉₊ := by linarith
  positivity

/-- **Core.** If `8a·f → G`, the exponent ratio tends to `G`. -/
theorem expRatio_tendsto_of {p : ℝ → ℝ} {G : ℝ} (hp : ∀ᶠ a in atTop, 0 ≤ p a ∧ p a ≤ 1)
    (hg : Tendsto (fun a => 8 * a * fa a (p a)) atTop (𝓝 G)) :
    Tendsto (fun a => expRatio a (p a)) atTop (𝓝 G) := by
  -- `y = 1/(8a) → 0` and `f = (8af)·y → 0`
  have hy : Tendsto (fun a : ℝ => 1 / (8 * a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
  have hf : Tendsto (fun a => fa a (p a)) atTop (𝓝 0) := by
    have := hg.mul hy
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    field_simp
  have hf1 : ∀ᶠ a in atTop, fa a (p a) < 1 / 2 := hf.eventually (gt_mem_nhds (by norm_num))
  have hlow : Tendsto (fun a => 8 * a * fa a (p a) * (1 - 1 / (8 * a))) atTop (𝓝 G) := by
    have := hg.mul ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hy)
    simpa using this
  have hup : Tendsto (fun a => 8 * a * fa a (p a) / (1 - fa a (p a))) atTop (𝓝 G) := by
    have := hg.div ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hf) (by norm_num)
    rw [sub_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  all_goals
    filter_upwards [hp, hf1, eventually_ge_atTop (1 : ℝ)] with a hpa hfa ha
    have hf0 := fa_nonneg (a := a) hpa.1 hpa.2
    have hy0 : 0 < 1 / (8 * a) := by positivity
    have hy1 : 1 / (8 * a) < 1 := by rw [div_lt_one (by positivity)]; linarith
    obtain ⟨hyl, hyu⟩ := log_inv_one_sub_bounds hy0.le hy1
    obtain ⟨hfl, hfu⟩ := log_inv_one_sub_bounds hf0 (by linarith)
    have hLy : 0 < Real.log (1 / (1 - 1 / (8 * a))) := lt_of_lt_of_le hy0 hyl
    have hl3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hR : expRatio a (p a) = Real.log (1 / (1 - fa a (p a)))
        / Real.log (1 / (1 - 1 / (8 * a))) := by
      unfold expRatio kappa
      rcases eq_or_ne (Real.log (1 / (1 - fa a (p a)))) 0 with h0 | h0
      · rw [h0]; simp
      · field_simp
    rw [hR]
  · -- lower bound: `log(1/(1-f)) / log(1/(1-y)) ≥ f / (y/(1-y)) = 8af(1-y)`
    have e : 8 * a * fa a (p a) * (1 - 1 / (8 * a)) = fa a (p a) / ((1 / (8 * a)) / (1 - 1 / (8 * a))) := by
      have : (1 : ℝ) - 1 / (8 * a) ≠ 0 := by linarith
      field_simp
    rw [e]
    calc fa a (p a) / ((1 / (8 * a)) / (1 - 1 / (8 * a)))
        ≤ fa a (p a) / Real.log (1 / (1 - 1 / (8 * a))) :=
          div_le_div_of_nonneg_left hf0 hLy hyu
      _ ≤ Real.log (1 / (1 - fa a (p a))) / Real.log (1 / (1 - 1 / (8 * a))) :=
          div_le_div_of_nonneg_right hfl hLy.le
  · -- upper bound: `≤ (f/(1-f)) / y = 8af/(1-f)`
    have e : 8 * a * fa a (p a) / (1 - fa a (p a)) = (fa a (p a) / (1 - fa a (p a))) / (1 / (8 * a)) := by
      field_simp
    rw [e]
    calc Real.log (1 / (1 - fa a (p a))) / Real.log (1 / (1 - 1 / (8 * a)))
        ≤ (fa a (p a) / (1 - fa a (p a))) / Real.log (1 / (1 - 1 / (8 * a))) :=
          div_le_div_of_nonneg_right hfu hLy.le
      _ ≤ (fa a (p a) / (1 - fa a (p a))) / (1 / (8 * a)) :=
          div_le_div_of_nonneg_left (div_nonneg hf0 (by linarith)) hy0 hyl

/-- `a / ⌈a⌉ → 1`. -/
lemma div_ceil_tendsto : Tendsto (fun a : ℝ => a / ⌈a⌉₊) atTop (𝓝 1) := by
  have hl : Tendsto (fun a : ℝ => 1 - 1 / (a + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun a : ℝ => 1 / (a + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id)
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  all_goals filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  · have hk : (a : ℝ) ≤ ⌈a⌉₊ := Nat.le_ceil a
    have hk1 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    have e : 1 - 1 / (a + 1) = a / (a + 1) := by field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) hk1.le
  · have hk : (a : ℝ) ≤ ⌈a⌉₊ := Nat.le_ceil a
    rw [div_le_one (by linarith)]; exact hk

/-- `8a·f = 8·(a/k)·(1-p)·(1-(1-p)^k)`. -/
lemma g_eq (a p : ℝ) : 8 * a * fa a p = 8 * (a / ⌈a⌉₊) * (1 - p) * (1 - (1 - p) ^ ⌈a⌉₊) := by
  unfold fa; ring

/-- **The ratio tends to 8** when `p → 0` and `a·p → ∞`. -/
theorem expRatio_tendsto_eight {p : ℝ → ℝ} (hp : ∀ᶠ a in atTop, 0 ≤ p a ∧ p a ≤ 1)
    (hp0 : Tendsto p atTop (𝓝 0)) (hap : Tendsto (fun a => a * p a) atTop atTop) :
    Tendsto (fun a => expRatio a (p a)) atTop (𝓝 8) := by
  apply expRatio_tendsto_of hp
  -- `(1-p)^k ≤ exp(-p)^k = exp(-kp) ≤ exp(-ap) → 0`
  have hpow : Tendsto (fun a => (1 - p a) ^ ⌈a⌉₊) atTop (𝓝 0) := by
    have he : Tendsto (fun a => Real.exp (-(a * p a))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hap
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he ?_ ?_
    all_goals filter_upwards [hp, eventually_ge_atTop (0 : ℝ)] with a hpa ha
    · exact pow_nonneg (by linarith [hpa.2]) _
    · have h1 : 1 - p a ≤ Real.exp (-p a) := by linarith [Real.add_one_le_exp (-p a)]
      calc (1 - p a) ^ ⌈a⌉₊ ≤ Real.exp (-p a) ^ ⌈a⌉₊ :=
            pow_le_pow_left₀ (by linarith [hpa.2]) h1 _
        _ = Real.exp (⌈a⌉₊ * -p a) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (-(a * p a)) := by
            apply Real.exp_le_exp.2
            have := Nat.le_ceil a
            nlinarith [hpa.1]
  have := ((div_ceil_tendsto.const_mul 8).mul ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hp0)).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hpow)
  simp only [g_eq]
  simpa [mul_assoc] using this

/-- For a **fixed** `p ∈ (0, 1]` the ratio tends to `8(1-p)`. -/
theorem expRatio_tendsto_const {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun a => expRatio a p) atTop (𝓝 (8 * (1 - p))) := by
  apply expRatio_tendsto_of (p := fun _ => p) (Eventually.of_forall fun _ => ⟨hp0.le, hp1⟩)
  have hpow : Tendsto (fun a : ℝ => (1 - p) ^ ⌈a⌉₊) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp tendsto_nat_ceil_atTop
  have := ((div_ceil_tendsto.const_mul 8).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => 1 - p) atTop (𝓝 (1 - p)))).mul ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hpow)
  simp only [g_eq]
  simpa [mul_assoc] using this

/-- A dyadic schedule: `p = 2^{-j}` with `j = ⌊log₂ ⌈a⌉⌋ / 2` fair coins per part and level. Then
`p → 0` and `a·p → ∞`, so the ratio tends to `8`. -/
theorem dyadic_p :
    Tendsto (fun a : ℝ => expRatio a ((1 / 2) ^ (Nat.log 2 ⌈a⌉₊ / 2))) atTop (𝓝 8) := by
  set j : ℝ → ℕ := fun a => Nat.log 2 ⌈a⌉₊ / 2 with hj
  -- `4^j ≤ ⌈a⌉ < 4·4^j`
  have hsq : ∀ a : ℝ, 1 ≤ a → ((2 : ℝ) ^ j a) ^ 2 ≤ a + 1 ∧ a < 4 * ((2 : ℝ) ^ j a) ^ 2 := by
    intro a ha
    have hja : j a = Nat.log 2 ⌈a⌉₊ / 2 := rfl
    have hk0 : ⌈a⌉₊ ≠ 0 := (Nat.ceil_pos.2 (by linarith)).ne'
    have h1 : 2 ^ (2 * j a) ≤ ⌈a⌉₊ :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_log_le_self 2 hk0)
    have h2 : ⌈a⌉₊ < 2 ^ (2 * j a + 2) :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1' : ((2 : ℝ) ^ j a) ^ 2 ≤ ⌈a⌉₊ := by
      rw [← pow_mul, mul_comm]; exact_mod_cast h1
    have h2' : (⌈a⌉₊ : ℝ) < 4 * ((2 : ℝ) ^ j a) ^ 2 := by
      rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, mul_comm, add_comm]
      exact_mod_cast h2
    exact ⟨le_trans h1' (Nat.ceil_lt_add_one (by linarith)).le,
      lt_of_le_of_lt (Nat.le_ceil a) h2'⟩
  have hp : ∀ a : ℝ, (1 / 2 : ℝ) ^ (Nat.log 2 ⌈a⌉₊ / 2) = 1 / (2 : ℝ) ^ j a := fun a => by
    rw [one_div_pow]
  apply expRatio_tendsto_eight
  · exact Eventually.of_forall fun a => ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · -- `p² = 1/4^j < 4/a → 0`
    have hs : Tendsto (fun a : ℝ => Real.sqrt (4 / a)) atTop (𝓝 0) := by
      have h4 : Tendsto (fun a : ℝ => 4 / a) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have := (Real.continuous_sqrt.tendsto 0).comp h4
      rw [Real.sqrt_zero] at this
      exact this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
    all_goals filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    · positivity
    · rw [hp a, Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow,
        div_le_div_iff₀ (by positivity) (by linarith)]
      linarith [(hsq a ha).2]
  · -- `(a·p)² = a²/4^j ≥ a²/(a+1) ≥ a/2`, so `a·p ≥ √(a/2) → ∞`
    have hs : Tendsto (fun a : ℝ => Real.sqrt (a / 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    refine tendsto_atTop_mono' atTop ?_ hs
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have h4 := (hsq a ha).1
    have hpos : (0 : ℝ) < (2 : ℝ) ^ j a := by positivity
    rw [hp a, mul_one_div, Real.sqrt_le_left (by positivity), div_pow,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ a / 2)]

/-- **Never worse.** For `a ≥ 1/2`, one fair coin already gives an exponent at most that of [1]. -/
theorem never_worse {a : ℝ} (ha : 1 / 2 ≤ a) :
    kappa (1 - fa a (1 / 2)) ≤ kappa (1 - 1 / (8 * a)) := by
  have hd : 1 / (8 * a) ≤ fa a (1 / 2) := dominates_paper a ha
  have hk1 : (1 : ℝ) ≤ ⌈a⌉₊ := by exact_mod_cast Nat.ceil_pos.2 (by linarith)
  have hf1 : fa a (1 / 2) < 1 := by
    unfold fa
    rw [div_lt_one (by linarith)]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) ⌈a⌉₊]
  have hy0 : 0 < 1 / (8 * a) := by positivity
  have hy1 : 1 / (8 * a) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hLy : 0 < Real.log (1 / (1 - 1 / (8 * a))) :=
    Real.log_pos (one_lt_one_div (by linarith) (by linarith))
  unfold kappa
  apply div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hLy
  exact Real.log_le_log (by positivity)
    (one_div_le_one_div_of_le (by linarith) (by linarith))

end Asymptotic

end Op4
