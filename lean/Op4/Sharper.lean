import Op4.RandomCentres

/-!
# Sharper one-level bound for random centres on planar graphs

Same algorithm as `Op4.RandomCentres` (centre with probability `p`, every non-centre joins its
heaviest centre neighbour). The orientation step of `random_centres` is replaced by an exact layer-cake
count plus a degree inequality, giving for `p = 3/8` the per-level fraction
`357115/2097152 ≈ 0.1703` (was `1935/12288 ≈ 0.1575`), hence `5.88 < κ < 5.89` (was `6.42`).
With one fair coin (`p = 1/2`) it gives `175/1152` and `κ < 6.7` (was `7`).

## Proof outline
* `leafGain_split`: subtracting the smallest edge weight `t` from every edge splits the gain into
  `t · [P is a non-centre with a centre neighbour]` plus the gain for the reduced weights.
* `E_leaf_ind`: that event has probability `(1-p)(1-(1-p)^deg P)`.
* `degree_lemma`: for a graph satisfying `FactA` and `FactB`,
  `Σ_P (1 - s^deg P) ≥ (a + 2b)·|E|`, given a pointwise certificate for `a, b`.
* `sharper`: induction on the support, which shrinks with every subtraction.

## Not formalised
`FactA` and `FactB` hold for every planar graph. Both are consequences of Euler's formula, and
Mathlib has no planarity.
* `FactA`: `|E| ≤ Σ_v min(d_v, 3)`. Edges inside `{d ≥ 3}` number at most `3·|{d ≥ 3}|`, and every
  other edge has an endpoint of degree at most 2.
* `FactB`: `2|E| ≤ Σ_v min(d_v, 6) + 2·#{d_v ≥ 1}`. Here `Σ_{d_v ≥ 6} (d_v - 6) ≤ e(H, V∖H) ≤ 2n'`
  for `H = {d ≥ 6}`, using `e(H) ≤ 3|H|` and the bipartite bound.
Both facts are inherited by every subgraph, and they enter as the hypothesis `Hpl`.
-/

open Finset

namespace Op4

section Sharper

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma E_lin (p c : ℝ) (A : Finset α) (f g : Finset α → ℝ) :
    E p A (fun D => c * f D + g D) = c * E p A f + E p A g := by
  unfold E; rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun D _ => by ring

/-- Probability that the random subset of `A` is non-empty. -/
lemma E_nonempty (p : ℝ) (A : Finset α) :
    E p A (fun D => if D.Nonempty then 1 else 0) = 1 - (1 - p) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp [E_empty]
  | insert a A ha ih =>
    rw [E_insert p ha, ih, card_insert_of_notMem ha]
    have : E p A (fun D => if (insert a D).Nonempty then (1 : ℝ) else 0) = 1 :=
      (E_congr p A (g := fun _ => 1) fun D _ => by simp).trans (E_const p A 1)
    rw [this, pow_succ]; ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Neighbourhood of `P` in the support graph of `w`. -/
noncomputable def nbr (w : V → V → NNReal) (P : V) : Finset V := univ.filter fun X => w P X ≠ 0

/-- Degree of `P` in the support graph of `w`. -/
noncomputable def deg (w : V → V → NNReal) (P : V) : ℕ := (nbr w P).card

/-- Planar degree fact A: `2|E| ≤ 2 Σ_v min(d_v, 3)`. -/
def FactA (w : V → V → NNReal) : Prop := ∑ P, deg w P ≤ 2 * ∑ P, min (deg w P) 3

/-- Planar degree fact B: `2|E| ≤ Σ_v min(d_v, 6) + 2·#(non-isolated vertices)`. -/
def FactB (w : V → V → NNReal) : Prop :=
  ∑ P, deg w P ≤ ∑ P, min (deg w P) 6 + 2 * (univ.filter fun P => deg w P ≠ 0).card

omit [DecidableEq V] in
/-- **Degree lemma.** If `a, b ≥ 0` satisfy the pointwise certificate, every graph with facts A and B
has `Σ_P (1 - s^{d_P}) ≥ (a + 2b)·|E|`, where `|E| = Σ_P d_P / 2`. -/
theorem degree_lemma {s a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcert : ∀ d : ℕ, a * ((min d 3 : ℕ) : ℝ) + b * (((min d 6 : ℕ) : ℝ) + if d = 0 then 0 else 2)
      ≤ 1 - s ^ d)
    (w : V → V → NNReal) (hA : FactA w) (hB : FactB w) :
    (a + 2 * b) * (((∑ P, deg w P : ℕ) : ℝ) / 2) ≤ ∑ P, (1 - s ^ deg w P) := by
  have hA' : ((∑ P, deg w P : ℕ) : ℝ) ≤ 2 * ∑ P, ((min (deg w P) 3 : ℕ) : ℝ) := by
    exact_mod_cast hA
  have hcard : (((univ.filter fun P => deg w P ≠ 0).card : ℕ) : ℝ)
      = ∑ P, (if deg w P = 0 then (0 : ℝ) else 1) := by
    rw [card_filter]; push_cast; exact sum_congr rfl fun P _ => by split_ifs <;> simp_all
  have hB' : ((∑ P, deg w P : ℕ) : ℝ)
      ≤ ∑ P, ((min (deg w P) 6 : ℕ) : ℝ) + 2 * ∑ P, (if deg w P = 0 then (0 : ℝ) else 1) := by
    rw [← hcard]; exact_mod_cast hB
  have h1 := sum_le_sum fun P (_ : P ∈ univ) => hcert (deg w P)
  have h2 : ∑ P, (a * ((min (deg w P) 3 : ℕ) : ℝ)
        + b * (((min (deg w P) 6 : ℕ) : ℝ) + if deg w P = 0 then 0 else 2))
      = a * ∑ P, ((min (deg w P) 3 : ℕ) : ℝ) + b * ∑ P, ((min (deg w P) 6 : ℕ) : ℝ)
        + 2 * b * ∑ P, (if deg w P = 0 then (0 : ℝ) else 1) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun P _ => by split_ifs <;> ring
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left hA' ha, mul_le_mul_of_nonneg_left hB' hb]

/-- Indicator that `P` is a non-centre with a centre neighbour. -/
noncomputable def ind (w : V → V → NNReal) (P : V) (C : Finset V) : ℝ :=
  if P ∉ C ∧ (C ∩ nbr w P).Nonempty then 1 else 0

lemma E_leaf_ind (p : ℝ) (w : V → V → NNReal) (hloop : ∀ P, w P P = 0) (P : V) :
    E p univ (ind w P) = (1 - p) * (1 - (1 - p) ^ deg w P) := by
  have hPN : P ∉ nbr w P := by simp [nbr, hloop]
  have hf : ind w P = fun D => ind w P (D ∩ insert P (nbr w P)) := by
    funext D
    have h1 : P ∈ D ∩ insert P (nbr w P) ↔ P ∈ D := by simp
    have h2 : D ∩ insert P (nbr w P) ∩ nbr w P = D ∩ nbr w P := by
      rw [inter_assoc, insert_inter_of_notMem hPN, inter_self]
    simp only [ind, h1, h2]
  rw [hf, E_marg p (subset_univ _), E_insert p hPN]
  have h0 : E p (nbr w P) (fun D => ind w P (insert P D)) = 0 :=
    (E_congr p _ (g := fun _ => 0) fun D _ => by simp [ind]).trans (E_const p _ 0)
  have h1 : E p (nbr w P) (ind w P) = E p (nbr w P) (fun D => if D.Nonempty then 1 else 0) :=
    E_congr p _ fun D hD => by
      have hP : P ∉ D := fun h => hPN (hD h)
      simp [ind, hP, inter_eq_left.mpr hD]
  rw [h0, h1, E_nonempty]; unfold deg; ring

/-- Subtracting a lower bound `t` of all positive weights splits `leafGain` exactly. -/
lemma leafGain_split (w : V → V → NNReal) (t : NNReal) (ht : ∀ P X, w P X ≠ 0 → t ≤ w P X)
    (P : V) (C : Finset V) :
    leafGain w P C = t * ind w P C + leafGain (fun P X => w P X - t) P C := by
  unfold leafGain ind
  by_cases hPC : P ∈ C
  · simp [hPC]
  · simp only [hPC, not_false_eq_true, true_and, ite_false]
    have hsub : C.sup (fun X => w P X - t) = C.sup (w P) - t := by
      have hmono : Monotone fun x : NNReal => x - t := fun x y h => tsub_le_tsub_right h t
      exact (apply_sup_eq_sup_comp_of_linearOrder (fun x : NNReal => x - t) hmono (zero_tsub t)).symm
    unfold mx
    rw [hsub]
    by_cases hne : (C ∩ nbr w P).Nonempty
    · obtain ⟨X, hX⟩ := hne
      simp only [mem_inter, nbr, mem_filter, mem_univ, true_and] at hX
      have htM : t ≤ C.sup (w P) := (ht P X hX.2).trans (le_sup hX.1)
      rw [ite_eq_left ⟨X, by simp [nbr, hX.1, hX.2]⟩, NNReal.coe_sub htM]; ring
    · have hz : C.sup (w P) = 0 := by
        refine le_antisymm (Finset.sup_le fun X hX => ?_) bot_le
        by_contra h
        exact hne ⟨X, by simp [nbr, hX, (not_le.mp h).ne']⟩
      rw [ite_eq_right hne, hz, zero_tsub]; simp

/-- Support of `w` as a set of ordered pairs. -/
noncomputable def supp (w : V → V → NNReal) : Finset (V × V) := univ.filter fun x => w x.1 x.2 ≠ 0

/-- **Sharper one-level theorem.** Assume every symmetric subgraph of the support of `w` satisfies
facts A and B (true for planar graphs), and `a, b` satisfy the pointwise certificate for `s = 1-p`.
Then `E[gain] ≥ (1-p)(a+2b) · w(G)`, where `w(G) = Σ_P Σ_X w(P,X) / 2`. -/
theorem sharper {p a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcert : ∀ d : ℕ, a * ((min d 3 : ℕ) : ℝ) + b * (((min d 6 : ℕ) : ℝ) + if d = 0 then 0 else 2)
      ≤ 1 - (1 - p) ^ d)
    (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (Hpl : ∀ u : V → V → NNReal, (∀ P X, u P X = u X P) → (∀ P X, u P X ≠ 0 → w P X ≠ 0) →
      FactA u ∧ FactB u) :
    (1 - p) * (a + 2 * b) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) := by
  suffices h : ∀ n (w : V → V → NNReal), (supp w).card = n → (∀ P X, w P X = w X P) →
      (∀ P, w P P = 0) →
      (∀ u : V → V → NNReal, (∀ P X, u P X = u X P) → (∀ P X, u P X ≠ 0 → w P X ≠ 0) →
        FactA u ∧ FactB u) →
      (1 - p) * (a + 2 * b) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) from
    h _ w rfl hw hloop Hpl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn hw hloop Hpl
  have hgain0 : ∀ u : V → V → NNReal, 0 ≤ E p univ (gain u) := fun u =>
    E_nonneg hp0 hp1 _ fun D _ => sum_nonneg fun P _ => by
      unfold leafGain; split_ifs
      · exact le_rfl
      · exact mx_nonneg _ _
  rcases (supp w).eq_empty_or_nonempty with h0 | hne
  · have hw0 : ∀ P X, w P X = 0 := fun P X => by
      by_contra h
      have : (P, X) ∈ supp w := by simp [supp, h]
      rw [h0] at this; simp at this
    simp only [hw0, NNReal.coe_zero, sum_const_zero, zero_div, mul_zero]
    exact hgain0 w
  · obtain ⟨⟨P0, X0⟩, hx0, hmin⟩ := (supp w).exists_min_image (fun x => w x.1 x.2) hne
    set t := w P0 X0 with ht_def
    have hx0' : w P0 X0 ≠ 0 := by simpa [supp] using hx0
    have ht : ∀ P X, w P X ≠ 0 → t ≤ w P X := fun P X h => hmin (P, X) (by simp [supp, h])
    set w' : V → V → NNReal := fun P X => w P X - t with hw'_def
    have hsub : ∀ P X, w' P X ≠ 0 → w P X ≠ 0 := fun P X h h0 => h (by simp [hw'_def, h0])
    have hlt : (supp w').card < n := by
      rw [← hn]
      refine card_lt_card ⟨fun x hx => ?_, fun hcon => ?_⟩
      · simp only [supp, mem_filter, mem_univ, true_and] at hx ⊢; exact hsub _ _ hx
      · have : (P0, X0) ∈ supp w' := hcon hx0
        simp [supp, hw'_def, ht_def] at this
    have hIH := ih _ hlt w' rfl (fun P X => by simp [hw'_def, hw P X])
      (fun P => by simp [hw'_def, hloop P])
      (fun u hu hu' => Hpl u hu fun P X h => hsub P X (hu' P X h))
    -- the gain splits
    have hsplit : E p univ (gain w)
        = (t : ℝ) * ∑ P, (1 - p) * (1 - (1 - p) ^ deg w P) + E p univ (gain w') := by
      have : gain w = fun C => (t : ℝ) * ∑ P, ind w P C + gain w' C := by
        funext C; unfold gain
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun P _ => leafGain_split w t ht P C
      rw [this, E_lin, E_sum]
      simp only [E_leaf_ind p w hloop]
    -- the weight splits
    have hW : ∑ P, ∑ X, (w P X : ℝ) = (t : ℝ) * ((∑ P, deg w P : ℕ) : ℝ) + ∑ P, ∑ X, (w' P X : ℝ) := by
      push_cast
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun P _ => ?_
      have hd : ((deg w P : ℕ) : ℝ) = ∑ X, (if w P X ≠ 0 then (1 : ℝ) else 0) := by
        unfold deg nbr; rw [card_filter]; push_cast; rfl
      rw [hd, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun X _ => ?_
      by_cases h0 : w P X = 0
      · simp [hw'_def, h0]
      · rw [ite_eq_left h0, hw'_def]; simp only
        rw [NNReal.coe_sub (ht P X h0)]; ring
    obtain ⟨hA, hB⟩ := Hpl w hw fun P X h => h
    have hdeg := degree_lemma ha hb hcert w hA hB
    have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    have h1p : 0 ≤ 1 - p := by linarith
    rw [hsplit, hW]
    have key : (1 - p) * ((a + 2 * b) * (((∑ P, deg w P : ℕ) : ℝ) / 2))
        ≤ ∑ P, (1 - p) * (1 - (1 - p) ^ deg w P) := by
      rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg h1p
    nlinarith [mul_le_mul_of_nonneg_left key ht0]

end Sharper

section SharperNumbers

/-- Certificate for `p = 3/8`: `a = 39173/2^18`, `b = 16125/2^18`. -/
theorem cert_three_eighths (d : ℕ) :
    (39173 / 262144 : ℝ) * ((min d 3 : ℕ) : ℝ)
      + 16125 / 262144 * (((min d 6 : ℕ) : ℝ) + if d = 0 then 0 else 2) ≤ 1 - (1 - 3 / 8) ^ d := by
  rcases Nat.lt_or_ge d 6 with h | h
  · interval_cases d <;> norm_num
  · have h3 : min d 3 = 3 := by omega
    have h6 : min d 6 = 6 := by omega
    have hd0 : d ≠ 0 := by omega
    rw [h3, h6, ite_eq_right hd0]
    have : (1 - 3 / 8 : ℝ) ^ d ≤ (1 - 3 / 8) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢; linarith

/-- The new planar per-level fraction for `p = 3/8`. -/
theorem f_sharper : (1 - (3 / 8 : ℝ)) * (39173 / 262144 + 2 * (16125 / 262144)) = 357115 / 2097152 := by
  norm_num

set_option exponentiation.threshold 600 in
/-- New exponent: `q = 1 - 357115/2097152 = 1740037/2097152`, so `5.88 < κ < 5.89`. -/
theorem kappa_sharper : 147 / 25 < kappa (1 - 357115 / 2097152) ∧
    kappa (1 - 357115 / 2097152) < 589 / 100 := by
  have hq : (1 : ℝ) / (1 - 357115 / 2097152) = 2097152 / 1740037 := by norm_num
  constructor
  · have hN : (2097152 : ℕ) ^ 147 < 3 ^ 25 * 1740037 ^ 147 := by decide
    have h : (1 / (1 - 357115 / 2097152 : ℝ)) ^ 147 < (3 : ℝ) ^ 25 := by
      rw [hq, div_pow, div_lt_iff₀ (by positivity)]; exact_mod_cast hN
    have := lt_kappa (a := 147) (b := 25) (by norm_num) (by norm_num) (by norm_num) h
    norm_num at this ⊢; exact this
  · have hN : (3 : ℕ) ^ 100 * 1740037 ^ 589 < 2097152 ^ 589 := by decide
    have h : (3 : ℝ) ^ 100 < (1 / (1 - 357115 / 2097152)) ^ 589 := by
      rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
    have := kappa_lt (a := 589) (b := 100) (by norm_num) (by norm_num) (by norm_num) h
    norm_num at this ⊢; exact this

/-- Certificate for one fair coin (`p = 1/2`): `a = 133/576`, `b = 21/576`. -/
theorem cert_half (d : ℕ) :
    (133 / 576 : ℝ) * ((min d 3 : ℕ) : ℝ)
      + 21 / 576 * (((min d 6 : ℕ) : ℝ) + if d = 0 then 0 else 2) ≤ 1 - (1 - 1 / 2) ^ d := by
  rcases Nat.lt_or_ge d 6 with h | h
  · interval_cases d <;> norm_num
  · have h3 : min d 3 = 3 := by omega
    have h6 : min d 6 = 6 := by omega
    have hd0 : d ≠ 0 := by omega
    rw [h3, h6, ite_eq_right hd0]
    have : (1 - 1 / 2 : ℝ) ^ d ≤ (1 - 1 / 2) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢; linarith

theorem f_sharper_half : (1 - (1 / 2 : ℝ)) * (133 / 576 + 2 * (21 / 576)) = 175 / 1152 := by
  norm_num

/-- With the paper's coin budget (`p = 1/2`): `q = 977/1152` and `κ < 6.7` (was `< 7`). -/
theorem kappa_sharper_half : kappa (1 - 175 / 1152) < 67 / 10 := by
  have hN : (3 : ℕ) ^ 10 * 977 ^ 67 < 1152 ^ 67 := by decide
  have h : (3 : ℝ) ^ 10 < (1 / (1 - 175 / 1152)) ^ 67 := by
    rw [show (1 : ℝ) / (1 - 175 / 1152) = 1152 / 977 by norm_num, div_pow,
      lt_div_iff₀ (by positivity)]
    exact_mod_cast hN
  have := kappa_lt (a := 67) (b := 10) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

end SharperNumbers

end Op4
