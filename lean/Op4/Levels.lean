import Op4.RandomCentres

/-!
# From the per-level factor to the round exponent

In the clustering of [1], level `t` multiplies the part radii by `3` and the expected weight between
parts by at most `q` (paper, Section `sec:integration`). `levels`: if `c (t+1) ≤ q·c t`, then after
`L = ⌈log x / log(1/q)⌉` levels `c L ≤ c 0 / x`, and `3^L ≤ 3·x^κ` with `κ = ln 3 / ln(1/q)`. With
`x = c₀/ε` this is the round bound `T + 9·3^L = T + O((c₀/ε)^κ)` of [1, Thm. 5.4].

## Not formalized
The clustering algorithm of [1] itself and the remaining steps of [1, Thm. 5.4 and Cor. 8.1].
-/

namespace Op4

/-- A geometric decrease: `c t ≤ q^t·c 0`. -/
lemma geom_decay {q : ℝ} (hq0 : 0 ≤ q) (c : ℕ → ℝ) (hc : ∀ t, c (t + 1) ≤ q * c t) (t : ℕ) :
    c t ≤ q ^ t * c 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc c (t + 1) ≤ q * c t := hc t
      _ ≤ q * (q ^ t * c 0) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (t + 1) * c 0 := by ring

/-- **Levels.** -/
theorem levels {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : 1 ≤ x) (c : ℕ → ℝ) (hc0 : 0 ≤ c 0)
    (hc : ∀ t, c (t + 1) ≤ q * c t) :
    c ⌈Real.log x / Real.log (1 / q)⌉₊ ≤ c 0 / x ∧
      (3 : ℝ) ^ ⌈Real.log x / Real.log (1 / q)⌉₊ ≤ 3 * x ^ kappa q := by
  set L := ⌈Real.log x / Real.log (1 / q)⌉₊ with hL
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (one_lt_one_div hq0 hq1)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have hL1 : Real.log x / Real.log (1 / q) ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < Real.log x / Real.log (1 / q) + 1 := Nat.ceil_lt_add_one (by positivity)
  constructor
  · -- `q^L ≤ 1/x`, because `L·log(1/q) ≥ log x`
    have hqL : q ^ L ≤ 1 / x := by
      have h1 : Real.log x ≤ L * Real.log (1 / q) := by rwa [div_le_iff₀ hlq] at hL1
      have h2 : Real.log (q ^ L) ≤ Real.log (1 / x) := by
        rw [Real.log_pow, one_div, Real.log_inv]
        rw [one_div, Real.log_inv] at h1
        linarith
      exact (Real.log_le_log_iff (by positivity) (by positivity)).1 h2
    calc c L ≤ q ^ L * c 0 := geom_decay hq0.le c hc L
      _ ≤ 1 / x * c 0 := mul_le_mul_of_nonneg_right hqL hc0
      _ = c 0 / x := by ring
  · -- `3^L = exp(L·ln 3) ≤ exp((log x / log(1/q) + 1)·ln 3) = 3·x^κ`
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have e1 : (3 : ℝ) ^ L = Real.exp (L * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have e2 : 3 * x ^ kappa q = Real.exp ((Real.log x / Real.log (1 / q) + 1) * Real.log 3) := by
      rw [Real.rpow_def_of_pos hx0, add_mul, one_mul, Real.exp_add, Real.exp_log (by norm_num)]
      unfold kappa
      rw [mul_comm]; congr 1; ring_nf
    rw [e1, e2]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hL2.le hl3.le)

end Op4
