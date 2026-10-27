import Op4.LocalPath

/-!
# The upper bound on paths

In the model of `Op4.LocalPath`, an `r`-round algorithm that knows the length `L` of the path has
ratio at most `1 + 2/(2r+3)` (`local_path_upper`). So on paths the smallest number of rounds for
ratio `1 + ε` is at most `1/ε - 1/2` (`local_rounds_upper`); by `local_rounds_lower` it is at least
`1/ε - 4`.

## The algorithm
A view shows a vertex of degree at most `1`, an end of the path, at distance `k` from its centre
(`SeesEnd`). `edist w` is the smallest such `k`, capped at `r + 1`; it does not change when the view
is read backwards, and on the path it is the distance to the nearer end, capped (`edist_view`).
* If `L ≥ 2r + 3`, the ends output `2/3` and the other vertices `1/3`: a fractional dominating set
  of weight `(L+2)/3 ≤ (1 + 2/L)·L/3`.
* Otherwise every vertex sees the nearer end, so it knows its position up to reflection. It outputs
  the average of the dominating set `dD L` of size `⌈L/3⌉` and its mirror image.
Every fractional dominating set of `P_L` has weight at least `⌈L/3⌉` (`path_lower_ceil`).
-/

open Finset

namespace Op4

section PathUpper

/-- `w` shows a vertex of degree at most `1` at distance `k` from its centre. -/
def SeesEnd {r N : ℕ} (w : View r N) (k : ℕ) : Prop :=
  ∃ i : Fin (2 * r + 1), ((i : ℕ) + k = r ∨ (i : ℕ) = r + k) ∧
    ∃ a d, w i = some (a, d) ∧ d ≤ 1

open Classical in
/-- The distance to the nearer end that `w` shows, capped at `r + 1`. -/
noncomputable def edist {r N : ℕ} (w : View r N) : ℕ :=
  Nat.find (⟨r + 1, Or.inr rfl⟩ : ∃ k, SeesEnd w k ∨ k = r + 1)

lemma seesEnd_rev {r N : ℕ} (w : View r N) (k : ℕ) : SeesEnd (w ∘ Fin.rev) k ↔ SeesEnd w k := by
  constructor
  · rintro ⟨i, hi, a, d, hw, hd⟩
    refine ⟨Fin.rev i, ?_, a, d, hw, hd⟩
    have := i.isLt
    rw [Fin.val_rev]
    omega
  · rintro ⟨i, hi, a, d, hw, hd⟩
    refine ⟨Fin.rev i, ?_, a, d, by simp only [Function.comp_apply, Fin.rev_rev]; exact hw, hd⟩
    have := i.isLt
    rw [Fin.val_rev]
    omega

lemma edist_rev {r N : ℕ} (w : View r N) : edist (w ∘ Fin.rev) = edist w := by
  classical
  unfold edist
  exact Nat.find_congr' fun {k} => or_congr_left (seesEnd_rev w k)

/-- On the path, a view shows an end at distance `k ≤ r` exactly when `k` is the distance to one of
the two ends. -/
lemma seesEnd_view {L N r : ℕ} (σ : Fin L ↪ Fin N) {v : ℕ} (hv : v < L) (k : ℕ) :
    SeesEnd (view r σ v) k ↔ k ≤ r ∧ (k = v ∨ k + v + 1 = L) := by
  constructor
  · rintro ⟨i, hi, a, d, hw, hd⟩
    have := i.isLt
    unfold view at hw
    split_ifs at hw with h
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      unfold pdeg at hd
      split_ifs at hd <;> omega
  · rintro ⟨hk, h | h⟩
    · have hc : r ≤ v + (r - k) ∧ v + (r - k) - r < L := ⟨by omega, by omega⟩
      refine ⟨⟨r - k, by omega⟩, Or.inl (by simp only; omega), σ ⟨v + (r - k) - r, hc.2⟩,
        pdeg L (v + (r - k) - r), by simp [view, hc], ?_⟩
      unfold pdeg
      split_ifs <;> omega
    · have hc : r ≤ v + (r + k) ∧ v + (r + k) - r < L := ⟨by omega, by omega⟩
      refine ⟨⟨r + k, by omega⟩, Or.inr rfl, σ ⟨v + (r + k) - r, hc.2⟩,
        pdeg L (v + (r + k) - r), by simp [view, hc], ?_⟩
      unfold pdeg
      split_ifs <;> omega

/-- On the path, `edist` is the distance to the nearer end, capped at `r + 1`. -/
lemma edist_view {L N r : ℕ} (σ : Fin L ↪ Fin N) {v : ℕ} (hv : v < L) :
    edist (view r σ v) = min (min v (L - 1 - v)) (r + 1) := by
  classical
  unfold edist
  rw [Nat.find_eq_iff]
  refine ⟨?_, fun n hn hp => ?_⟩
  · by_cases h : min (min v (L - 1 - v)) (r + 1) = r + 1
    · exact Or.inr h
    · left
      rw [seesEnd_view σ hv]
      omega
  · rcases hp with hp | hp
    · rw [seesEnd_view σ hv] at hp
      omega
    · omega

/-- The output of an algorithm that depends on the view through `edist` only. -/
lemma out_edist {L N r : ℕ} (g : ℕ → ℝ) (σ : Fin L ↪ Fin N) (v : ℕ) :
    out (fun w : View r N => g (edist w)) σ v =
      if v < L then g (min (min v (L - 1 - v)) (r + 1)) else 0 := by
  unfold out
  split_ifs with hv
  · show g (edist (view r σ v)) = _
    rw [edist_view σ hv]
  · rfl

/-! ### Fractional dominating sets of paths -/

lemma fracDom_avg {L : ℕ} {x x' : ℕ → ℝ} (h : FracDomPath L x) (h' : FracDomPath L x') :
    FracDomPath L (fun v => (x v + x' v) / 2) := by
  obtain ⟨a0, a1, a2⟩ := h
  obtain ⟨b0, b1, b2⟩ := h'
  refine ⟨by dsimp only; linarith, by dsimp only; linarith, fun u hu => ?_⟩
  dsimp only
  linarith [a2 u hu, b2 u hu]

/-- The mirror image of a fractional dominating set of `P_L` is one. -/
lemma fracDom_rev {L : ℕ} (hL : 1 ≤ L) {x : ℕ → ℝ} (hx : ∀ v, L ≤ v → x v = 0)
    (h : FracDomPath L x) : FracDomPath L (fun v => if v < L then x (L - 1 - v) else 0) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · by_cases hL1 : L = 1
    · subst hL1
      simp only [zero_lt_one, ↓reduceIte, lt_self_iff_false, add_zero]
      linarith [hx 1 le_rfl]
    · simp only [show 0 < L by omega, show 1 < L by omega, ↓reduceIte]
      rw [show L - 1 - 0 = L - 1 by omega, show L - 1 - 1 = L - 2 by omega]
      linarith
  · by_cases hL1 : L = 1
    · subst hL1
      simp only [Nat.reduceSub, zero_lt_one, ↓reduceIte]
      linarith [hx 1 le_rfl]
    · simp only [show L - 2 < L by omega, show L - 1 < L by omega, ↓reduceIte]
      rw [show L - 1 - (L - 2) = 1 by omega, show L - 1 - (L - 1) = 0 by omega]
      linarith
  · simp only [show u < L by omega, show u + 1 < L by omega, show u + 2 < L by omega,
      ↓reduceIte]
    have := h2 (L - 3 - u) (by omega)
    rw [show L - 3 - u + 1 = L - 1 - (u + 1) by omega, show L - 3 - u + 2 = L - 1 - u by omega,
      show L - 3 - u = L - 1 - (u + 2) by omega] at this
    linarith

/-- **Every fractional dominating set of `P_L` has weight at least `⌈L/3⌉`.** -/
lemma path_lower_ceil {L : ℕ} (hL : 1 ≤ L) {y : ℕ → ℝ} (hyL : ∀ v, L ≤ v → y v = 0)
    (hd : FracDomPath L y) : (((L + 2) / 3 : ℕ) : ℝ) ≤ ∑ i ∈ range L, y i := by
  obtain ⟨h0, h1, h2⟩ := hd
  obtain ⟨m, hm | hm | hm | hm⟩ :
      ∃ m, L = 3 * m + 3 ∨ L = 1 ∨ L = 3 * m + 4 ∨ L = 3 * m + 2 :=
    ⟨if L % 3 = 0 then L / 3 - 1 else if L % 3 = 1 then L / 3 - 1 else L / 3, by
      split_ifs <;> omega⟩
  · rw [show (L + 2) / 3 = m + 1 by omega, hm]
    exact_mod_cast path_triples y (3 * m + 3) (hm ▸ h2) (m + 1) (by omega)
  · subst hm
    simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.cast_one, range_one, sum_singleton]
    linarith [hyL 1 le_rfl]
  · have hl := left_sum y L h0 h2 m (by omega)
    rw [show L - 2 = 3 * m + 2 by omega, show L - 1 = 3 * m + 3 by omega] at h1
    rw [show (L + 2) / 3 = m + 2 by omega, show L = 3 * m + 2 + 1 + 1 by omega, sum_range_succ,
      sum_range_succ]
    push_cast
    linarith
  · have hl := left_sum y L h0 h2 m (by omega)
    rw [show (L + 2) / 3 = m + 1 by omega, hm]
    push_cast
    linarith

/-! ### Long paths: the ends output `2/3`, the other vertices `1/3` -/

/-- The output on long paths. -/
noncomputable def xl (L v : ℕ) : ℝ :=
  if v < L then (if v = 0 ∨ v + 1 = L then 2 / 3 else 1 / 3) else 0

lemma xl_nonneg (L v : ℕ) : 0 ≤ xl L v := by
  unfold xl
  split_ifs <;> norm_num

lemma fracDom_xl {L : ℕ} (hL : 3 ≤ L) : FracDomPath L (xl L) := by
  unfold FracDomPath xl
  refine ⟨?_, ?_, fun u hu => ?_⟩ <;> split_ifs <;> first | (exfalso; omega) | norm_num

lemma sum_xl {L : ℕ} (hL : 2 ≤ L) : ∑ v ∈ range L, xl L v = ((L : ℝ) + 2) / 3 := by
  have e : ∀ v ∈ range L, xl L v =
      1 / 3 + ((if v = 0 then 1 / 3 else 0) + (if v = L - 1 then 1 / 3 else 0)) := by
    intro v hv
    rw [mem_range] at hv
    unfold xl
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib, sum_const, card_range, sum_ite_eq',
    sum_ite_eq']
  simp only [mem_range, show 0 < L by omega, show L - 1 < L by omega, ↓reduceIte, nsmul_eq_mul]
  ring

/-! ### Short paths: a dominating set of size `⌈L/3⌉` and its mirror image -/

/-- The dominating set `{v : v ≡ 0}` if `L ≡ 1 (mod 3)`, and `{v : v ≡ 1}` otherwise. -/
noncomputable def dD (L v : ℕ) : ℝ :=
  if v < L ∧ ((L % 3 = 1 ∧ v % 3 = 0) ∨ (L % 3 ≠ 1 ∧ v % 3 = 1)) then 1 else 0

lemma dD_nonneg (L v : ℕ) : 0 ≤ dD L v := by
  unfold dD
  split_ifs <;> norm_num

lemma fracDom_dD {L : ℕ} (hL : 1 ≤ L) : FracDomPath L (dD L) := by
  unfold FracDomPath dD
  refine ⟨?_, ?_, fun u hu => ?_⟩ <;> split_ifs <;> first | (exfalso; omega) | norm_num

lemma sum_mod3 {q : ℕ} (hq : q < 3) (m s : ℕ) :
    ∑ v ∈ range (3 * m + s), (if v % 3 = q then (1 : ℝ) else 0) =
      m + ∑ v ∈ range s, (if v % 3 = q then (1 : ℝ) else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 3 * (m + 1) + s = 3 * m + s + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih]
    push_cast
    split_ifs <;> first | (exfalso; omega) | ring

/-- `dD L` has `⌈L/3⌉` vertices. -/
lemma sum_dD (L : ℕ) : ∑ v ∈ range L, dD L v = (((L + 2) / 3 : ℕ) : ℝ) := by
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, L = 3 * m ∨ L = 3 * m + 1 ∨ L = 3 * m + 2 :=
    ⟨L / 3, by omega⟩
  · have e : ∀ v ∈ range (3 * m), dD (3 * m) v = if v % 3 = 1 then 1 else 0 := by
      intro v hv
      rw [mem_range] at hv
      unfold dD
      split_ifs <;> first | rfl | omega
    rw [sum_congr rfl e, show (3 * m + 2) / 3 = m by omega]
    simpa using sum_mod3 (q := 1) (by norm_num) m 0
  · have e : ∀ v ∈ range (3 * m + 1), dD (3 * m + 1) v = if v % 3 = 0 then 1 else 0 := by
      intro v hv
      rw [mem_range] at hv
      unfold dD
      split_ifs <;> first | rfl | omega
    rw [sum_congr rfl e, show (3 * m + 1 + 2) / 3 = m + 1 by omega, sum_mod3 (q := 0) (by norm_num) m 1,
      sum_range_succ, sum_range_zero]
    push_cast
    norm_num
  · have e : ∀ v ∈ range (3 * m + 2), dD (3 * m + 2) v = if v % 3 = 1 then 1 else 0 := by
      intro v hv
      rw [mem_range] at hv
      unfold dD
      split_ifs <;> first | rfl | omega
    rw [sum_congr rfl e, show (3 * m + 2 + 2) / 3 = m + 1 by omega, sum_mod3 (q := 1) (by norm_num) m 2,
      sum_range_succ, sum_range_succ, sum_range_zero]
    push_cast
    norm_num

/-- The output on short paths. -/
noncomputable def xs (L v : ℕ) : ℝ := if v < L then (dD L v + dD L (L - 1 - v)) / 2 else 0

lemma xs_nonneg (L v : ℕ) : 0 ≤ xs L v := by
  unfold xs
  split_ifs
  · have := dD_nonneg L v
    have := dD_nonneg L (L - 1 - v)
    linarith
  · exact le_rfl

lemma fracDom_xs {L : ℕ} (hL : 1 ≤ L) : FracDomPath L (xs L) := by
  have e : xs L = fun v => (dD L v + (if v < L then dD L (L - 1 - v) else 0)) / 2 := by
    funext v
    unfold xs
    split_ifs with hv
    · rfl
    · have : dD L v = 0 := by unfold dD; rw [ite_eq_right_iff]; omega
      rw [this]
      norm_num
  rw [e]
  refine fracDom_avg (fracDom_dD hL) (fracDom_rev hL (fun v hv => ?_) (fracDom_dD hL))
  unfold dD
  rw [ite_eq_right_iff]
  omega

lemma sum_xs (L : ℕ) : ∑ v ∈ range L, xs L v = (((L + 2) / 3 : ℕ) : ℝ) := by
  have e : ∀ v ∈ range L, xs L v = (dD L v + dD L (L - 1 - v)) / 2 := by
    intro v hv
    rw [mem_range] at hv
    unfold xs
    simp only [hv, ↓reduceIte]
  rw [sum_congr rfl e, ← sum_div, sum_add_distrib, sum_range_reflect (dD L) L, sum_dD]
  ring

/-! ### The algorithm -/

/-- **The algorithm.** It knows the length `L` of the path. -/
noncomputable def pathAlg (r N L : ℕ) (w : View r N) : ℝ :=
  if 2 * r + 3 ≤ L then (if edist w = 0 then 2 / 3 else 1 / 3)
  else (dD L (edist w) + dD L (L - 1 - edist w)) / 2

lemma pathAlg_rev (r N L : ℕ) (w : View r N) : pathAlg r N L (w ∘ Fin.rev) = pathAlg r N L w := by
  unfold pathAlg
  rw [edist_rev]

lemma out_pathAlg {r N L : ℕ} (σ : Fin L ↪ Fin N) :
    out (pathAlg r N L) σ = if 2 * r + 3 ≤ L then xl L else xs L := by
  funext v
  have h := out_edist (r := r) (fun k => if 2 * r + 3 ≤ L then (if k = 0 then (2 : ℝ) / 3 else 1 / 3)
    else (dD L k + dD L (L - 1 - k)) / 2) σ v
  have e : pathAlg r N L = fun w : View r N =>
      (fun k => if 2 * r + 3 ≤ L then (if k = 0 then (2 : ℝ) / 3 else 1 / 3)
        else (dD L k + dD L (L - 1 - k)) / 2) (edist w) := rfl
  rw [e, h]
  by_cases hlong : 2 * r + 3 ≤ L
  · simp only [hlong, ↓reduceIte]
    unfold xl
    split_ifs <;> first | rfl | omega
  · simp only [hlong, ↓reduceIte]
    unfold xs
    split_ifs with hv
    · rw [show min (min v (L - 1 - v)) (r + 1) = min v (L - 1 - v) by omega]
      rcases le_total v (L - 1 - v) with hle | hle
      · rw [min_eq_left hle]
      · rw [min_eq_right hle, show L - 1 - (L - 1 - v) = v by omega, add_comm]
    · rfl

/-- **The upper bound on paths.** For every `r` and every length `L ≥ 1`, an `r`-round algorithm
that knows `L` outputs, for every identifier assignment, a fractional dominating set of `P_L` of
weight at most `(1 + 2/(2r+3))·y(P_L)` for every fractional dominating set `y` of `P_L`. -/
theorem local_path_upper (r N L : ℕ) (hL : 1 ≤ L) :
    ∃ A : View r N → ℝ, (∀ w, A (w ∘ Fin.rev) = A w) ∧ ∀ σ : Fin L ↪ Fin N,
      (∀ v, 0 ≤ out A σ v) ∧ FracDomPath L (out A σ) ∧
      ∀ y : ℕ → ℝ, (∀ v, L ≤ v → y v = 0) → FracDomPath L y →
        ∑ i ∈ range L, out A σ i ≤ (1 + 2 / (2 * (r : ℝ) + 3)) * ∑ i ∈ range L, y i := by
  refine ⟨pathAlg r N L, pathAlg_rev r N L, fun σ => ?_⟩
  rw [out_pathAlg σ]
  have hc : (0 : ℝ) ≤ 2 / (2 * (r : ℝ) + 3) := by positivity
  split_ifs with hlong
  · refine ⟨xl_nonneg L, fracDom_xl (by omega), fun y hyL hy => ?_⟩
    have hy3 := path_lower_ceil hL hyL hy
    have hcl : (L : ℝ) ≤ 3 * (((L + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : L ≤ 3 * ((L + 2) / 3))
    have hLr : (2 * (r : ℝ) + 3) ≤ L := by exact_mod_cast hlong
    rw [sum_xl (by omega)]
    have key : ((L : ℝ) + 2) / 3 ≤ (1 + 2 / (2 * (r : ℝ) + 3)) * ((L : ℝ) / 3) := by
      rw [← sub_nonneg]
      have e : (1 + 2 / (2 * (r : ℝ) + 3)) * ((L : ℝ) / 3) - ((L : ℝ) + 2) / 3 =
          2 * ((L : ℝ) - (2 * r + 3)) / (3 * (2 * r + 3)) := by
        field_simp
        ring
      rw [e]
      apply div_nonneg <;> nlinarith
    calc ((L : ℝ) + 2) / 3 ≤ (1 + 2 / (2 * (r : ℝ) + 3)) * ((L : ℝ) / 3) := key
      _ ≤ (1 + 2 / (2 * (r : ℝ) + 3)) * ∑ i ∈ range L, y i :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · refine ⟨xs_nonneg L, fracDom_xs hL, fun y hyL hy => ?_⟩
    have hy3 := path_lower_ceil hL hyL hy
    have h0 : (0 : ℝ) ≤ ∑ i ∈ range L, y i := le_trans (Nat.cast_nonneg _) hy3
    rw [sum_xs]
    nlinarith

/-- **Rounds on paths.** For `ε ∈ (0, 1]`, ratio `1 + ε` is reached in at most `1/ε - 1/2`
rounds by an algorithm that knows the length. With `local_rounds_lower`, the smallest number of
rounds lies between `1/ε - 4` and `1/ε - 1/2`. -/
theorem local_rounds_upper {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r : ℕ, (r : ℝ) ≤ 1 / ε - 1 / 2 ∧ ∀ N L : ℕ, 1 ≤ L →
      ∃ A : View r N → ℝ, (∀ w, A (w ∘ Fin.rev) = A w) ∧ ∀ σ : Fin L ↪ Fin N,
        (∀ v, 0 ≤ out A σ v) ∧ FracDomPath L (out A σ) ∧
        ∀ y : ℕ → ℝ, (∀ v, L ≤ v → y v = 0) → FracDomPath L y →
          ∑ i ∈ range L, out A σ i ≤ (1 + ε) * ∑ i ∈ range L, y i := by
  set r := ⌈1 / ε - 3 / 2⌉₊ with hr
  have hinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  refine ⟨r, ?_, fun N L hL => ?_⟩
  · by_cases h : 0 ≤ 1 / ε - 3 / 2
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [hr, Nat.ceil_eq_zero.2 (by linarith)]
      push_cast
      linarith
  · obtain ⟨A, hA, hσ⟩ := local_path_upper r N L hL
    have hle : 2 / (2 * (r : ℝ) + 3) ≤ ε := by
      have h1 := Nat.le_ceil (1 / ε - 3 / 2)
      rw [← hr] at h1
      rw [div_le_iff₀ (by positivity)]
      have h2 : ε * (1 / ε) = 1 := by field_simp
      nlinarith
    refine ⟨A, hA, fun σ => ?_⟩
    obtain ⟨h0, hd, hw⟩ := hσ σ
    refine ⟨h0, hd, fun y hyL hy => ?_⟩
    have h1 := hw y hyL hy
    have hs : (0 : ℝ) ≤ ∑ i ∈ range L, y i :=
      le_trans (Nat.cast_nonneg _) (path_lower_ceil hL hyL hy)
    nlinarith

end PathUpper

end Op4
