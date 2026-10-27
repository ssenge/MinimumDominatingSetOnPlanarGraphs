import Mathlib

/-!
# Random-centre star contraction: one-level progress bound

Machine-checked core of Theorem 1 in the README, which improves the round exponent of the planar
(7+ε)-MDS algorithm of arXiv:2610.09618 from κ ≈ 25.8 to κ ≈ 6.41.

One level of the algorithm, on a weighted graph `w : V → V → ℝ≥0` (weight 0 = no edge):
* every vertex becomes a *centre* independently with probability `p`;
* every non-centre `P` joins its heaviest centre neighbour `c P`, and the edge `P – c P` is contracted.

## Results
* `gain_eq_join_edges`: the contracted weight `gain w C` is the weight of a set of pairwise distinct
  edges (one per joining vertex).
* `random_centres`: if the edges admit an orientation with out-degree ≤ k, then
  `E[gain] ≥ (1-p)(1-(1-p)^k)/k · w(G)`.
* `arcs_eq_half_total`: for a genuine orientation, the arc sum in `random_centres` equals `w(G)`.
* `f_three_eighths`, `f_le`: with `k = 3`, `p = 3/8` gives `1935/12288`, and no `p` exceeds `63/400`
  in this bound, so `3/8` is optimal up to `3·10⁻⁵`.
* `kappa_new`, `kappa_paper`: `6.4 < κ_new < 6.42` and `25 < κ_paper < 26`.

## Not formalized here (stated as hypotheses or left on paper)
* The orientation with out-degree at most `k` enters as the hypotheses on `O`. `Op4.Orientation`
  derives it from the density bound (the orientation theorem of [5] in the README), and
  `random_centres_densityA` in `Op4.Density` states Theorem 1 with the density bound alone. That
  planar graphs satisfy the bound with `k = 3` is Euler's formula, which we take as given.
* That the algorithm is local (the view radius), the derandomization step, and plugging the
  per-level factor `q = 1 - f` into the paper's Theorem 5.4. These are unchanged from the paper.
  `Op4.Levels` checks the step from the per-level factor to the round exponent.

The random centre set is modelled exactly: `E p A f` is the expectation of `f D` for a random
`D ⊆ A` that contains each element independently with probability `p`.
-/

open Finset

namespace Op4

section Expectation

variable {α : Type*} [DecidableEq α]

/-- Probability that the random subset of `A` equals `D` (for `D ⊆ A`). -/
noncomputable def pw (p : ℝ) (A D : Finset α) : ℝ := p ^ D.card * (1 - p) ^ (A.card - D.card)

/-- Expectation of `f` over a random subset of `A` (independent inclusion with probability `p`). -/
noncomputable def E (p : ℝ) (A : Finset α) (f : Finset α → ℝ) : ℝ :=
  ∑ D ∈ A.powerset, pw p A D * f D

omit [DecidableEq α] in
lemma pw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A D : Finset α) : 0 ≤ pw p A D :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma E_empty (p : ℝ) (f : Finset α → ℝ) : E p ∅ f = f ∅ := by
  simp [E, pw]

/-- Conditioning on one coin: the basic recursion for `E`. -/
lemma E_insert (p : ℝ) {a : α} {A : Finset α} (ha : a ∉ A) (f : Finset α → ℝ) :
    E p (insert a A) f = (1 - p) * E p A f + p * E p A (fun D => f (insert a D)) := by
  unfold E
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun D hD => ?_
    have h1 : D.card ≤ A.card := card_le_card (mem_powerset.mp hD)
    simp only [pw, card_insert_of_notMem ha]
    rw [Nat.sub_add_comm h1, pow_succ]
    ring
  · refine sum_congr rfl fun D hD => ?_
    have haD : a ∉ D := fun h => ha (mem_powerset.mp hD h)
    simp only [pw, card_insert_of_notMem ha, card_insert_of_notMem haD, Nat.add_sub_add_right,
      pow_succ]
    ring

omit [DecidableEq α] in
lemma E_congr (p : ℝ) (A : Finset α) {f g : Finset α → ℝ} (h : ∀ D ⊆ A, f D = g D) :
    E p A f = E p A g :=
  sum_congr rfl fun D hD => by rw [h D (mem_powerset.mp hD)]

omit [DecidableEq α] in
lemma E_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) {f g : Finset α → ℝ}
    (h : ∀ D ⊆ A, f D ≤ g D) : E p A f ≤ E p A g :=
  sum_le_sum fun D hD =>
    mul_le_mul_of_nonneg_left (h D (mem_powerset.mp hD)) (pw_nonneg hp0 hp1 A D)

/-- `pw p A` is a probability distribution. -/
lemma E_const (p : ℝ) (A : Finset α) (c : ℝ) : E p A (fun _ => c) = c := by
  induction A using Finset.induction_on with
  | empty => simp [E_empty]
  | insert a A ha ih => rw [E_insert p ha]; simp only [ih]; ring

lemma E_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) {f : Finset α → ℝ}
    (h : ∀ D ⊆ A, 0 ≤ f D) : 0 ≤ E p A f := by
  have := E_mono hp0 hp1 A (f := fun _ => 0) h
  rwa [E_const] at this

omit [DecidableEq α] in
lemma E_sum {ι : Type*} (p : ℝ) (A : Finset α) (s : Finset ι) (f : ι → Finset α → ℝ) :
    E p A (fun D => ∑ i ∈ s, f i D) = ∑ i ∈ s, E p A (f i) := by
  unfold E; simp_rw [mul_sum]; exact sum_comm

/-- Marginalization: coins outside `A` do not affect a function of `D ∩ A`. -/
lemma E_marg (p : ℝ) {A B : Finset α} (hAB : A ⊆ B) (f : Finset α → ℝ) :
    E p B (fun D => f (D ∩ A)) = E p A f := by
  have key : ∀ S : Finset α, Disjoint S A → E p (S ∪ A) (fun D => f (D ∩ A)) = E p A f := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [empty_union]
      exact E_congr p A fun D hD => by rw [inter_eq_left.mpr hD]
    | insert y S hy ih =>
      intro hdis
      have hyA : y ∉ A := disjoint_left.mp hdis (mem_insert_self y S)
      have hyS : y ∉ S ∪ A := by simp [hy, hyA]
      rw [insert_union, E_insert p hyS]
      simp only [insert_inter_of_notMem hyA]
      rw [ih (disjoint_of_subset_left (subset_insert y S) hdis)]
      ring
  have h := key (B \ A) sdiff_disjoint
  rwa [sdiff_union_of_subset hAB] at h

end Expectation

section Inequalities

/-- Bernoulli's inequality. -/
lemma bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) : 1 - n * p ≤ (1 - p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1),
      mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (mul_nonneg hp0 hp0)]

lemma ratio_step {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) :
    (n : ℝ) * (1 - s ^ (n + 1)) ≤ (n + 1) * (1 - s ^ n) := by
  have key : ∀ m : ℕ, s ^ m * (1 + m * (1 - s)) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : s ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℝ) * (1 - s))
          = s ^ m * (1 + m * (1 - s)) - s ^ m * ((m + 1) * (1 - s) ^ 2) := by push_cast; ring
      rw [this]
      have : 0 ≤ s ^ m * ((m + 1) * (1 - s) ^ 2) := by positivity
      linarith
  have : (n + 1) * (1 - s ^ n) - n * (1 - s ^ (n + 1)) = 1 - s ^ n * (1 + n * (1 - s)) := by ring
  linarith [key n]

/-- `g(m)/m` is non-increasing, where `g(m) = 1 - s^m`: `m·g(k) ≤ k·g(m)` for `m ≤ k`. -/
lemma ratio_mono {s : ℝ} (hs0 : 0 ≤ s) {m k : ℕ} (hmk : m ≤ k) :
    (m : ℝ) * (1 - s ^ k) ≤ k * (1 - s ^ m) := by
  induction k, hmk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hmk ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain rfl : m = 0 := by omega
      simp
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hstep := ratio_step hs0 k
      push_cast
      refine le_of_mul_le_mul_left ?_ hkR
      nlinarith [mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
        mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ k + 1)]

/-- The algebraic step of the vertex lemma, with `t = (1-p)^n`. -/
lemma step_ineq {p E' W' wy : ℝ} {n : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht1 : (1 - p) ^ n ≤ 1)
    (hB : 1 - n * p ≤ (1 - p) ^ n) (hE0 : 0 ≤ E') (hW0 : 0 ≤ W') (hW : W' ≤ n * wy)
    (hIH : (1 - (1 - p) ^ n) * W' ≤ n * E') :
    (1 - (1 - p) ^ (n + 1)) * (wy + W') ≤ (n + 1) * ((1 - p) * E' + p * wy) := by
  rw [pow_succ]
  generalize (1 - p) ^ n = t at *
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add] at *
    obtain rfl : t = 1 := le_antisymm ht1 hB
    obtain rfl : W' = 0 := le_antisymm hW hW0
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hE0]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hid : (n : ℝ) * ((n + 1) * ((1 - p) * E' + p * wy) - (1 - t * (1 - p)) * (wy + W'))
        = (n + 1) * (1 - p) * (n * E' - (1 - t) * W')
          + (n * wy - W') * (n * p - (1 - p) * (1 - t)) := by ring
    have h1 : 0 ≤ (n + 1) * (1 - p) * (n * E' - (1 - t) * W') :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    have h2 : 0 ≤ (n * wy - W') * (n * p - (1 - p) * (1 - t)) :=
      mul_nonneg (by linarith) (by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr ht1)])
    have h3 : 0 ≤ (n : ℝ) * ((n + 1) * ((1 - p) * E' + p * wy) - (1 - t * (1 - p)) * (wy + W')) := by
      rw [hid]; linarith
    nlinarith

end Inequalities

section VertexBound

variable {α : Type*} [DecidableEq α]

/-- Weight of the heaviest element of `D` (0 if `D = ∅`). -/
noncomputable def mx {α : Type*} (w : α → NNReal) (D : Finset α) : ℝ := ((D.sup w : NNReal) : ℝ)

omit [DecidableEq α] in
lemma mx_nonneg (w : α → NNReal) (D : Finset α) : 0 ≤ mx w D := NNReal.coe_nonneg _

omit [DecidableEq α] in
lemma mx_mono (w : α → NNReal) {D D' : Finset α} (h : D ⊆ D') : mx w D ≤ mx w D' :=
  NNReal.coe_le_coe.mpr (sup_mono h)

/-- **Vertex lemma.** If each element of `A` is a centre independently with probability `p`, the
expected heaviest centre weighs at least `(1 - (1-p)^|A|)/|A|` times the total weight of `A`.
Proof: condition on a heaviest element `y` and induct on `|A|`. -/
theorem vertex_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : α → NNReal) (A : Finset α) :
    (1 - (1 - p) ^ A.card) * ∑ x ∈ A, (w x : ℝ) ≤ A.card * E p A (mx w) := by
  suffices h : ∀ n (A : Finset α), A.card = n →
      (1 - (1 - p) ^ n) * ∑ x ∈ A, (w x : ℝ) ≤ n * E p A (mx w) from h _ A rfl
  intro n
  induction n with
  | zero => intro A _; simp
  | succ n ih =>
    intro A hn
    obtain ⟨y, hy, hmax⟩ := A.exists_max_image w (card_pos.mp (by omega))
    have hyA : y ∉ A.erase y := notMem_erase y A
    -- if `y` is a centre, it is the heaviest one
    have hX : E p (A.erase y) (fun D => mx w (insert y D)) = w y := by
      refine (E_congr p _ (g := fun _ => (w y : ℝ)) fun D hD => ?_).trans (E_const p _ _)
      have : D.sup w ≤ w y := Finset.sup_le fun x hx => hmax x (mem_of_mem_erase (hD hx))
      simp only [mx, sup_insert, sup_eq_left.mpr this]
    have hrec := E_insert p hyA (mx w)
    rw [insert_erase hy, hX] at hrec
    have hW : ∑ x ∈ A.erase y, (w x : ℝ) ≤ n * w y := by
      have := sum_le_card_nsmul (A.erase y) (fun x => (w x : ℝ)) (w y)
        fun x hx => by exact_mod_cast hmax x (mem_of_mem_erase hx)
      rwa [card_erase_of_mem hy, hn, Nat.add_sub_cancel, nsmul_eq_mul] at this
    have hIH := ih (A.erase y) (by rw [card_erase_of_mem hy]; omega)
    rw [hrec, ← add_sum_erase A _ hy]
    push_cast
    exact step_ineq hp0 hp1 (pow_le_one₀ (by linarith) (by linarith)) (bernoulli hp0 hp1 n)
      (E_nonneg hp0 hp1 _ fun D _ => mx_nonneg w D) (sum_nonneg fun x _ => NNReal.coe_nonneg _)
      hW hIH

end VertexBound

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- What `P` contributes for centre set `C`: nothing if `P` is a centre, otherwise the weight of its
heaviest edge into `C`, which is the edge it contracts. -/
noncomputable def leafGain (w : V → V → NNReal) (P : V) (C : Finset V) : ℝ :=
  if P ∈ C then 0 else mx (w P) C

/-- Total weight contracted in one level with centre set `C`. -/
noncomputable def gain (w : V → V → NNReal) (C : Finset V) : ℝ := ∑ P, leafGain w P C

/-- `gain` is the weight of the joining edges, and these edges are pairwise distinct: a joining edge
`s(P, c P)` has exactly one non-centre endpoint, namely `P`. -/
theorem gain_eq_join_edges (w : V → V → NNReal) (hw : ∀ a b, w a b = w b a) (C : Finset V)
    (c : V → V) (hc : ∀ P, P ∉ C → 0 < mx (w P) C → c P ∈ C ∧ w P (c P) = C.sup (w P)) :
    gain w C = ∑ e ∈ (univ.filter fun P => P ∉ C ∧ 0 < mx (w P) C).image (fun P => s(P, c P)),
      Sym2.lift ⟨fun a b => (w a b : ℝ), fun a b => by simp only [hw a b]⟩ e := by
  have hinj : Set.InjOn (fun P => s(P, c P))
      ↑(univ.filter fun P => P ∉ C ∧ 0 < mx (w P) C) := by
    intro P hP Q hQ h
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hP hQ
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd (show P ∈ C from h1 ▸ (hc Q hQ.1 hQ.2).1) hP.1
  rw [sum_image hinj, sum_filter]
  refine sum_congr rfl fun P _ => ?_
  unfold leafGain
  by_cases hPC : P ∈ C
  · rw [ite_eq_left hPC, ite_eq_right (fun h => h.1 hPC)]
  · by_cases hpos : 0 < mx (w P) C
    · rw [ite_eq_right hPC, ite_eq_left ⟨hPC, hpos⟩, Sym2.lift_mk]
      show mx (w P) C = (w P (c P) : ℝ)
      rw [(hc P hPC hpos).2]; rfl
    · rw [ite_eq_right hPC, ite_eq_right (fun h => hpos h.2)]
      exact le_antisymm (not_lt.mp hpos) (mx_nonneg _ _)

/-- Per-vertex bound: with out-neighbours `A` (`P ∉ A`, `|A| ≤ k`),
`E[leafGain P] ≥ (1-p)(1-(1-p)^k)/k · Σ_{X∈A} w(P,X)`. -/
theorem per_vertex {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : V → V → NNReal) (P : V)
    (A : Finset V) (hPA : P ∉ A) {k : ℕ} (hAk : A.card ≤ k) :
    (1 - p) * (1 - (1 - p) ^ k) * ∑ X ∈ A, (w P X : ℝ) ≤ k * E p univ (leafGain w P) := by
  have h1p : 0 ≤ 1 - p := by linarith
  -- 1. restricting the max to centres in `A` can only lower it
  have h1 : E p univ (fun D => leafGain w P (D ∩ insert P A)) ≤ E p univ (leafGain w P) := by
    refine E_mono hp0 hp1 _ fun D _ => ?_
    unfold leafGain
    by_cases hP : P ∈ D
    · rw [ite_eq_left hP, ite_eq_left (mem_inter.mpr ⟨hP, mem_insert_self P A⟩)]
    · rw [ite_eq_right hP, ite_eq_right (fun h => hP (mem_inter.mp h).1)]
      exact mx_mono _ inter_subset_left
  -- 2. only the coins of `P` and `A` matter; `P` is a non-centre with probability `1-p`
  have h2 : E p univ (fun D => leafGain w P (D ∩ insert P A)) = (1 - p) * E p A (mx (w P)) := by
    rw [E_marg p (subset_univ (insert P A)) (leafGain w P), E_insert p hPA]
    have ha : E p A (fun D => leafGain w P (insert P D)) = 0 :=
      (E_congr p A (g := fun _ => 0) fun D _ => by
        unfold leafGain; rw [ite_eq_left (mem_insert_self P D)]).trans (E_const p A 0)
    have hb : E p A (leafGain w P) = E p A (mx (w P)) :=
      E_congr p A fun D hD => by unfold leafGain; rw [ite_eq_right (fun h => hPA (hD h))]
    rw [ha, hb, mul_zero, add_zero]
  -- 3. vertex lemma plus monotonicity of g(m)/m
  have hE0 : 0 ≤ E p A (mx (w P)) := E_nonneg hp0 hp1 A fun D _ => mx_nonneg _ D
  have hS0 : 0 ≤ ∑ X ∈ A, (w P X : ℝ) := sum_nonneg fun X _ => NNReal.coe_nonneg _
  have key : (1 - (1 - p) ^ k) * ∑ X ∈ A, (w P X : ℝ) ≤ k * E p A (mx (w P)) := by
    rcases Nat.eq_zero_or_pos A.card with h0 | hA
    · rw [card_eq_zero.mp h0, sum_empty, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg k) (by rw [card_eq_zero.mp h0] at hE0; exact hE0)
    · have hAR : (0 : ℝ) < A.card := by exact_mod_cast hA
      have hv := vertex_bound hp0 hp1 (w P) A
      have hr := ratio_mono h1p hAk
      refine le_of_mul_le_mul_left ?_ hAR
      calc (A.card : ℝ) * ((1 - (1 - p) ^ k) * ∑ X ∈ A, (w P X : ℝ))
          = (A.card * (1 - (1 - p) ^ k)) * ∑ X ∈ A, (w P X : ℝ) := by ring
        _ ≤ (k * (1 - (1 - p) ^ A.card)) * ∑ X ∈ A, (w P X : ℝ) :=
          mul_le_mul_of_nonneg_right hr hS0
        _ = k * ((1 - (1 - p) ^ A.card) * ∑ X ∈ A, (w P X : ℝ)) := by ring
        _ ≤ k * (A.card * E p A (mx (w P))) := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg k)
        _ = A.card * (k * E p A (mx (w P))) := by ring
  calc (1 - p) * (1 - (1 - p) ^ k) * ∑ X ∈ A, (w P X : ℝ)
      = (1 - p) * ((1 - (1 - p) ^ k) * ∑ X ∈ A, (w P X : ℝ)) := by ring
    _ ≤ (1 - p) * (k * E p A (mx (w P))) := mul_le_mul_of_nonneg_left key h1p
    _ = k * E p univ (fun D => leafGain w P (D ∩ insert P A)) := by rw [h2]; ring
    _ ≤ k * E p univ (leafGain w P) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)

/-- **Main theorem (one level of random-centre contraction).** Let `O P` be the out-neighbours of
`P` in an orientation with out-degree ≤ k. Each vertex becomes a centre independently with
probability `p`, and every non-centre contracts its heaviest edge into the centre set. Then the
expected contracted weight is at least `(1-p)(1-(1-p)^k)/k` times the arc weight `Σ_P Σ_{X∈O P} w`,
which equals the total edge weight by `arcs_eq_half_total`. -/
theorem random_centres {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : V → V → NNReal)
    (O : V → Finset V) (hO : ∀ P, P ∉ O P) {k : ℕ} (hk : 0 < k) (hOk : ∀ P, (O P).card ≤ k) :
    (1 - p) * (1 - (1 - p) ^ k) / k * ∑ P, ∑ X ∈ O P, (w P X : ℝ) ≤ E p univ (gain w) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [show E p univ (gain w) = ∑ P, E p univ (leafGain w P) from E_sum p univ univ (leafGain w),
    div_mul_eq_mul_div, div_le_iff₀ hkR, mul_sum, sum_mul]
  exact sum_le_sum fun P _ => by linarith [per_vertex hp0 hp1 w P (O P) (hO P) (hOk P)]

omit [DecidableEq V] in
/-- If `O` orients every edge exactly once, the arc sum is the total edge weight (each edge is
counted twice in the ordered double sum on the right). -/
theorem arcs_eq_half_total (w : V → V → NNReal) (hw : ∀ a b, w a b = w b a) (O : V → Finset V)
    (hO : ∀ P X, w P X ≠ 0 → (X ∈ O P ↔ P ∉ O X)) :
    2 * ∑ P, ∑ X ∈ O P, (w P X : ℝ) = ∑ P, ∑ X, (w P X : ℝ) := by
  classical
  have hA : ∑ P, ∑ X ∈ O P, (w P X : ℝ) = ∑ P, ∑ X, if X ∈ O P then (w P X : ℝ) else 0 :=
    sum_congr rfl fun P _ => by rw [sum_ite_mem, univ_inter]
  have hA' : ∑ P, ∑ X ∈ O P, (w P X : ℝ) = ∑ P, ∑ X, if P ∈ O X then (w X P : ℝ) else 0 := by
    rw [hA, sum_comm]
  rw [two_mul]
  nth_rewrite 1 [hA]
  rw [hA', ← sum_add_distrib]
  refine sum_congr rfl fun P _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun X _ => ?_
  by_cases h0 : w P X = 0
  · simp [h0, ← hw P X]
  · have h := hO P X h0
    by_cases hX : X ∈ O P
    · simp [hX, h.mp hX]
    · simp [hX, show P ∈ O X by tauto, hw X P]

end Main

section Numbers

/-- Planar graphs: `k = 3`, and `p = 3/8` (three fair coins) gives the per-level fraction `f`. -/
theorem f_three_eighths : (1 - (3 / 8 : ℝ)) * (1 - (1 - 3 / 8) ^ 3) / 3 = 1935 / 12288 := by
  norm_num

/-- `3/8` is not a guess: no `p` (indeed no real `p`) beats it in this bound by more than
`63/400 - 1935/12288 < 3·10⁻⁵`. The best `p` is `1 - 4^(-1/3) ≈ 0.370`. -/
theorem f_le (p : ℝ) : (1 - p) * (1 - (1 - p) ^ 3) / 3 ≤ 63 / 400 := by
  nlinarith [sq_nonneg ((1 - p) ^ 2 - 397 / 1000), sq_nonneg ((1 - p) - 250 / 397)]

/-- Round exponent for per-level decay factor `q`: rounds grow like `(1/ε)^κ` with
`κ = ln 3 / ln(1/q)` (paper, Thm 5.4: radius ×3 per level, `log_{1/q}(1/ε)` levels). -/
noncomputable def kappa (q : ℝ) : ℝ := Real.log 3 / Real.log (1 / q)

lemma kappa_lt {q : ℝ} {a b : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hb : 0 < b)
    (h : (3 : ℝ) ^ b < (1 / q) ^ a) : kappa q < a / b := by
  have hL : 0 < Real.log (1 / q) := Real.log_pos (one_lt_one_div hq0 hq1)
  have := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  unfold kappa
  rw [div_lt_iff₀ hL, div_mul_eq_mul_div, lt_div_iff₀ (by exact_mod_cast hb)]
  linarith

lemma lt_kappa {q : ℝ} {a b : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hb : 0 < b)
    (h : (1 / q) ^ a < (3 : ℝ) ^ b) : (a : ℝ) / b < kappa q := by
  have hL : 0 < Real.log (1 / q) := Real.log_pos (one_lt_one_div hq0 hq1)
  have := Real.log_lt_log (pow_pos (by positivity) _) h
  rw [Real.log_pow, Real.log_pow] at this
  unfold kappa
  rw [lt_div_iff₀ hL, div_mul_eq_mul_div, div_lt_iff₀ (by exact_mod_cast hb)]
  linarith

set_option exponentiation.threshold 400 in
/-- New exponent: `q = 1 - 1935/12288`, so `6.4 < κ < 6.42`. -/
theorem kappa_new : 32 / 5 < kappa (1 - 1935 / 12288) ∧ kappa (1 - 1935 / 12288) < 321 / 50 := by
  constructor
  · have := lt_kappa (q := 1 - 1935 / 12288) (a := 32) (b := 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    norm_num at this ⊢; exact this
  · -- 1/q = 4096/3451; compare `3^50 · 3451^321 < 4096^321` exactly in ℕ
    have hN : (3 : ℕ) ^ 50 * 3451 ^ 321 < 4096 ^ 321 := by decide
    have h : (3 : ℝ) ^ 50 < (1 / (1 - 1935 / 12288)) ^ 321 := by
      rw [show (1 : ℝ) / (1 - 1935 / 12288) = 4096 / 3451 by norm_num, div_pow,
        lt_div_iff₀ (by positivity)]
      exact_mod_cast hN
    have := kappa_lt (a := 321) (b := 50) (by norm_num) (by norm_num) (by norm_num) h
    norm_num at this ⊢; exact this

/-- With the paper's exact coin budget (one fair coin per part and level, `p = 1/2`) the planar
fraction is `7/48`, and already `κ < 7`. -/
theorem kappa_one_coin : kappa (1 - (1 - 1 / 2) * (1 - (1 - 1 / 2) ^ 3) / 3) < 7 := by
  have h : (3 : ℝ) ^ 1 < (1 / (1 - (1 - 1 / 2) * (1 - (1 - 1 / 2) ^ 3) / 3)) ^ 7 := by norm_num
  have := kappa_lt (a := 7) (b := 1) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- For every density `a ≥ 1/2`, the new fraction with `k = ⌈a⌉` (even at `p = 1/2`) is at least
the paper's `1/(8a)`. So the new exponent is never worse, for any class. -/
theorem dominates_paper (a : ℝ) (ha : 1 / 2 ≤ a) :
    1 / (8 * a) ≤ (1 - 1 / 2) * (1 - (1 - 1 / 2) ^ ⌈a⌉₊) / ⌈a⌉₊ := by
  set k := ⌈a⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.ceil_pos.mpr (by linarith)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2a : (k : ℝ) ≤ 2 * a := by
    have hlt : (k : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      rw [this]; push_cast; linarith
    · have : (2 : ℝ) ≤ k := by exact_mod_cast h
      linarith
  have hpow : (1 - 1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    calc (1 - 1 / 2 : ℝ) ^ k ≤ (1 - 1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1
      _ = 1 / 2 := by norm_num
  calc 1 / (8 * a) ≤ 1 / (4 * k) := one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = (1 / 4) / k := by ring
    _ ≤ (1 - 1 / 2) * (1 - (1 - 1 / 2) ^ k) / k := by
      apply div_le_div_of_nonneg_right _ hkpos.le
      linarith

/-- Paper's exponent: `q = 1 - 1/(8·3) = 23/24`, so `25 < κ < 26`. -/
theorem kappa_paper : 25 < kappa (23 / 24) ∧ kappa (23 / 24) < 26 := by
  constructor
  · have := lt_kappa (q := 23 / 24) (a := 25) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    norm_num at this; exact this
  · have := kappa_lt (q := 23 / 24) (a := 26) (b := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    norm_num at this; exact this

end Numbers

end Op4
