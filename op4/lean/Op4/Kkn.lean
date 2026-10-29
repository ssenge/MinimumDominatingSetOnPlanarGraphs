import Op4.RandomCentres

/-!
# The random-centre rule on `K_{k,n}`

Proposition `prop:kkn`: on `K_{k,n}` with unit weights, one level of the random-centre rule makes in
expectation at most a fraction `f_k(p) + 1/n` of the edges internal, where
`f_k(p) = (1-p)(1-(1-p)^k)/k` (`kkn_internal`). So no analysis of the rule gives a per-level
fraction above `f_k(p)` on a class that contains all `K_{k,n}` (`kkn_optimal`). For planar graphs,
which contain all `K_{2,n}`, this is `max_p f_2(p) = 1/(3√3)`, an exponent above `5.13`
(`kkn_planar`). That `K_{2,n}` is planar is not stated, since Mathlib has no planarity.

With unit weights every centre neighbour of a non-centre is a heaviest one, so we allow every
choice of centre neighbour (`IsChoice`). An edge is internal if its ends lie in the same star. On a
graph without triangles every internal edge is a join edge (`internal_subset`), since two leaves of
a star have a common neighbour, its centre.
-/

open Finset

namespace Op4

section Stars

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For the centre set `C`, the vertex `P` joins a star: it is not a centre and has a centre
neighbour. -/
def Joins (C : Finset V) (P : V) : Prop := P ∉ C ∧ ∃ X ∈ C, G.Adj P X

instance (C : Finset V) (P : V) : Decidable (Joins G C P) := by unfold Joins; infer_instance

/-- `c` picks for every joining vertex a centre neighbour, the centre of its star. With unit
weights every centre neighbour is a heaviest one. -/
def IsChoice (C : Finset V) (c : V → V) : Prop := ∀ P, Joins G C P → c P ∈ C ∧ G.Adj P (c P)

/-- The centre of the star of `X`. A centre is its own centre, and a vertex that neither is a
centre nor joins forms a part of its own. -/
def starOf (C : Finset V) (c : V → V) (X : V) : V := if Joins G C X then c X else X

open Classical in
/-- The edges whose ends lie in the same star. -/
noncomputable def internal (C : Finset V) (c : V → V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ a b, e = s(a, b) ∧ starOf G C c a = starOf G C c b

/-- The vertices that join a star. -/
def joined (C : Finset V) : Finset V := univ.filter (Joins G C)

/-- **Without triangles, every internal edge is a join edge** `s(P, c P)`. -/
lemma internal_subset (hT : ∀ a b r, G.Adj a b → G.Adj a r → ¬ G.Adj b r) {C : Finset V}
    {c : V → V} (hc : IsChoice G C c) :
    internal G C c ⊆ (joined G C).image fun P => s(P, c P) := by
  intro e he
  simp only [internal, mem_filter] at he
  obtain ⟨he, a, b, rfl, hab⟩ := he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  simp only [mem_image, joined, mem_filter, mem_univ, true_and]
  unfold starOf at hab
  by_cases ha : Joins G C a <;> by_cases hb : Joins G C b <;>
    simp only [ha, hb, ↓reduceIte] at hab
  · exact absurd (by rw [hab]; exact (hc b hb).2) (hT a b (c a) he (hc a ha).2)
  · exact ⟨a, ha, by rw [hab]⟩
  · exact ⟨b, hb, by rw [← hab, Sym2.eq_swap]⟩
  · exact absurd hab (G.ne_of_adj he)

lemma card_internal_le (hT : ∀ a b r, G.Adj a b → G.Adj a r → ¬ G.Adj b r) {C : Finset V}
    {c : V → V} (hc : IsChoice G C c) : #(internal G C c) ≤ #(joined G C) :=
  (card_le_card (internal_subset G hT hc)).trans card_image_le

end Stars

section Expectation

variable {α : Type*} [DecidableEq α]

/-- The random subset is empty with probability `(1-p)^|A|`. -/
lemma E_empty_ind (p : ℝ) (A : Finset α) :
    E p A (fun D => if D = ∅ then (1 : ℝ) else 0) = (1 - p) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp [E_empty]
  | insert a A ha ih =>
    have h0 : E p A (fun D => if insert a D = ∅ then (1 : ℝ) else 0) = 0 :=
      (E_congr p A (g := fun _ => 0) fun D _ => by simp).trans (E_const p A 0)
    rw [E_insert p ha, ih, h0, card_insert_of_notMem ha, pow_succ]
    ring

lemma E_one_sub (p : ℝ) (A : Finset α) (g : Finset α → ℝ) :
    E p A (fun D => 1 - g D) = 1 - E p A g := by
  have h := E_const p A 1
  unfold E at h ⊢
  simp only [mul_sub, mul_one, sum_sub_distrib] at h ⊢
  rw [h]

end Expectation

section Joining

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex of degree `d` joins a star with probability `(1-p)(1-(1-p)^d)`. -/
lemma E_joins (p : ℝ) (P : V) :
    E p univ (fun C => if Joins G C P then (1 : ℝ) else 0) =
      (1 - p) * (1 - (1 - p) ^ (G.neighborFinset P).card) := by
  set A := G.neighborFinset P with hA
  have hPA : P ∉ A := by simp [hA]
  set f : Finset V → ℝ := fun D => if P ∉ D ∧ (D ∩ A).Nonempty then 1 else 0 with hf
  have e1 : (fun C => if Joins G C P then (1 : ℝ) else 0) = fun C => f (C ∩ insert P A) := by
    funext C
    have h : Joins G C P ↔ (P ∉ C ∩ insert P A ∧ (C ∩ insert P A ∩ A).Nonempty) := by
      constructor
      · rintro ⟨h1, X, hX, hPX⟩
        have hXA : X ∈ A := by simpa [hA] using hPX
        exact ⟨fun h => h1 (mem_inter.1 h).1, X,
          mem_inter.2 ⟨mem_inter.2 ⟨hX, mem_insert_of_mem hXA⟩, hXA⟩⟩
      · rintro ⟨h1, X, hX⟩
        simp only [mem_inter] at hX
        exact ⟨fun h => h1 (mem_inter.2 ⟨h, mem_insert_self P A⟩), X, hX.1.1,
          by simpa [hA] using hX.2⟩
    exact if_congr h rfl rfl
  rw [e1, E_marg p (subset_univ _) f, E_insert p hPA]
  have h2 : E p A (fun D => f (insert P D)) = 0 :=
    (E_congr p A (g := fun _ => 0) fun D _ => by simp [hf]).trans (E_const p A 0)
  have h3 : E p A f = E p A (fun D => 1 - if D = ∅ then (1 : ℝ) else 0) :=
    E_congr p A fun D hD => by
      have hPD : P ∉ D := fun h => hPA (hD h)
      simp only [hf, inter_eq_left.2 hD]
      by_cases h0 : D = ∅
      · simp [h0]
      · simp [hPD, h0, nonempty_iff_ne_empty]
  rw [h2, h3, E_one_sub, E_empty_ind]
  ring

/-- **Expected number of internal edges** on a graph without triangles, for every choice of
centre neighbours: at most `∑_P (1-p)(1-(1-p)^{deg P})`. -/
theorem E_internal_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : ∀ a b r, G.Adj a b → G.Adj a r → ¬ G.Adj b r) (c : Finset V → V → V)
    (hc : ∀ C, IsChoice G C (c C)) :
    E p univ (fun C => (#(internal G C (c C)) : ℝ)) ≤
      ∑ P, (1 - p) * (1 - (1 - p) ^ (G.neighborFinset P).card) := by
  have h1 : E p univ (fun C => (#(internal G C (c C)) : ℝ)) ≤
      E p univ (fun C => ∑ P, if Joins G C P then (1 : ℝ) else 0) := by
    refine E_mono hp0 hp1 _ fun C _ => ?_
    have h := card_internal_le G hT (hc C)
    have e : (#(joined G C) : ℝ) = ∑ P, if Joins G C P then (1 : ℝ) else 0 := by
      rw [joined, card_filter]
      push_cast
      rfl
    rw [← e]
    exact_mod_cast h
  rw [E_sum] at h1
  simpa only [E_joins] using h1

end Joining

section Complete

/-- `K_{k,n}`, with the `k` hubs on the left. -/
abbrev Kkn (k n : ℕ) : SimpleGraph (Fin k ⊕ Fin n) := completeBipartiteGraph (Fin k) (Fin n)

lemma kkn_triangle (k n : ℕ) (a b r : Fin k ⊕ Fin n) :
    (Kkn k n).Adj a b → (Kkn k n).Adj a r → ¬ (Kkn k n).Adj b r := by
  rcases a with a | a <;> rcases b with b | b <;> rcases r with r | r <;> simp

open Classical in
lemma kkn_deg_inl (k n : ℕ) (i : Fin k) : ((Kkn k n).neighborFinset (Sum.inl i)).card = n := by
  have : (Kkn k n).neighborFinset (Sum.inl i) = univ.map Function.Embedding.inr := by
    ext v
    rcases v with v | v <;> simp
  rw [this, card_map, card_univ, Fintype.card_fin]

open Classical in
lemma kkn_deg_inr (k n : ℕ) (j : Fin n) : ((Kkn k n).neighborFinset (Sum.inr j)).card = k := by
  have : (Kkn k n).neighborFinset (Sum.inr j) = univ.map Function.Embedding.inl := by
    ext v
    rcases v with v | v <;> simp
  rw [this, card_map, card_univ, Fintype.card_fin]

open Classical in
lemma kkn_edges (k n : ℕ) : #(Kkn k n).edgeFinset = k * n := by
  have h := (Kkn k n).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp only [← SimpleGraph.card_neighborFinset_eq_degree, kkn_deg_inl, kkn_deg_inr, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul] at h
  linarith

open Classical in
/-- **Proposition `prop:kkn`.** On `K_{k,n}` with unit weights, for every `p ∈ [0,1]` and every
choice of centre neighbours, the expected number of internal edges is at most
`(f_k(p) + 1/n)·|E|`. -/
theorem kkn_internal {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Finset (Fin k ⊕ Fin n) → Fin k ⊕ Fin n → Fin k ⊕ Fin n)
    (hc : ∀ C, IsChoice (Kkn k n) C (c C)) :
    E p univ (fun C => (#(internal (Kkn k n) C (c C)) : ℝ)) ≤
      ((1 - p) * (1 - (1 - p) ^ k) / k + 1 / n) * #(Kkn k n).edgeFinset := by
  have h := E_internal_le (Kkn k n) hp0 hp1 (kkn_triangle k n) c hc
  rw [Fintype.sum_sum_type] at h
  simp only [kkn_deg_inl, kkn_deg_inr, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [kkn_edges]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ 1 - p := by linarith
  have hsn : (1 - p) ^ n ≤ 1 := pow_le_one₀ hs0 (by linarith)
  have hsn0 : 0 ≤ (1 - p) ^ n := pow_nonneg hs0 n
  have hl : (1 - p) * (1 - (1 - p) ^ n) ≤ 1 := by nlinarith
  have e : ((1 - p) * (1 - (1 - p) ^ k) / k + 1 / n) * ((k * n : ℕ) : ℝ) =
      n * ((1 - p) * (1 - (1 - p) ^ k)) + k := by
    push_cast
    field_simp
  rw [e]
  nlinarith

open Classical in
/-- **No analysis of the rule beats `f_k(p)` on a class that contains all `K_{k,n}`.** If for
every `n ≥ 1` some choice of centre neighbours makes the expected number of internal edges at
least `φ·|E|` on `K_{k,n}`, then `φ ≤ f_k(p)`. -/
theorem kkn_optimal {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {φ : ℝ}
    (h : ∀ n, 1 ≤ n → ∃ c : Finset (Fin k ⊕ Fin n) → Fin k ⊕ Fin n → Fin k ⊕ Fin n,
      (∀ C, IsChoice (Kkn k n) C (c C)) ∧
        φ * #(Kkn k n).edgeFinset ≤ E p univ (fun C => (#(internal (Kkn k n) C (c C)) : ℝ))) :
    φ ≤ (1 - p) * (1 - (1 - p) ^ k) / k := by
  by_contra hφ
  push Not at hφ
  set f := (1 - p) * (1 - (1 - p) ^ k) / k
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (φ - f))
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < 1 / (φ - f) := by apply div_pos one_pos; linarith
    exact_mod_cast (show (0 : ℝ) < n by linarith)
  obtain ⟨c, hc, hφn⟩ := h n hn1
  have hup := kkn_internal hk hn1 hp0 hp1 c hc
  have hE : (0 : ℝ) < #(Kkn k n).edgeFinset := by
    rw [kkn_edges]
    exact_mod_cast Nat.mul_pos hk hn1
  have hle : φ ≤ f + 1 / n := le_of_mul_le_mul_right (hφn.trans hup) hE
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have : 1 / (n : ℝ) < φ - f := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith
  linarith

end Complete

section Planar

/-- **`max_p f_2(p) = 1/(3√3) = √3/9`** for `p ≤ 1`. -/
theorem f_two_le {p : ℝ} (hp1 : p ≤ 1) : (1 - p) * (1 - (1 - p) ^ 2) / 2 ≤ Real.sqrt 3 / 9 := by
  set t := Real.sqrt 3 with htd
  have ht : t ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg 3
  set s := 1 - p with hsd
  have hs : 0 ≤ s := by linarith
  have h1 : t ^ 2 * s = 3 * s := by rw [ht]
  have h2 : t ^ 3 = 3 * t := by rw [pow_succ, ht]
  have hP := mul_nonneg (sq_nonneg (s - t / 3)) (show 0 ≤ s + 2 * t / 3 by linarith)
  nlinarith

/-- The maximum is attained at `p = 1 - 1/√3`. -/
theorem f_two_max : (1 - (1 - Real.sqrt 3 / 3)) * (1 - (1 - (1 - Real.sqrt 3 / 3)) ^ 2) / 2 =
    Real.sqrt 3 / 9 := by
  have ht : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [show 1 - (1 - Real.sqrt 3 / 3) = Real.sqrt 3 / 3 by ring, div_pow, ht]
  ring

set_option exponentiation.threshold 600 in
/-- A per-level fraction `φ ≤ √3/9` gives an exponent above `5.13`. -/
theorem kappa_of_le_f_two {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ Real.sqrt 3 / 9) :
    513 / 100 < kappa (1 - φ) := by
  have hs : Real.sqrt 3 < 17321 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hq : (72679 : ℝ) / 90000 ≤ 1 - φ := by linarith
  have hq0 : 0 < 1 - φ := by linarith
  have hq1 : 1 - φ < 1 := by linarith
  have hN : (90000 : ℕ) ^ 513 < 3 ^ 100 * 72679 ^ 513 := by decide
  have h : (1 / (1 - φ)) ^ 513 < (3 : ℝ) ^ 100 := by
    calc (1 / (1 - φ)) ^ 513 ≤ ((90000 : ℝ) / 72679) ^ 513 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [div_le_div_iff₀ hq0 (by norm_num)]
          linarith
      _ < 3 ^ 100 := by
          rw [div_pow, div_lt_iff₀ (by positivity)]
          exact_mod_cast hN
  have := lt_kappa (a := 513) (b := 100) hq0 hq1 (by norm_num) h
  norm_num at this ⊢
  exact this

open Classical in
/-- **Planar graphs.** They contain all `K_{2,n}`. If an analysis of the random-centre rule gives
the per-level fraction `φ > 0` on every `K_{2,n}`, then `φ ≤ 1/(3√3) ≈ 0.1925`, and its exponent
is above `5.13`. -/
theorem kkn_planar {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {φ : ℝ} (hφ : 0 < φ)
    (h : ∀ n, 1 ≤ n → ∃ c : Finset (Fin 2 ⊕ Fin n) → Fin 2 ⊕ Fin n → Fin 2 ⊕ Fin n,
      (∀ C, IsChoice (Kkn 2 n) C (c C)) ∧
        φ * #(Kkn 2 n).edgeFinset ≤ E p univ (fun C => (#(internal (Kkn 2 n) C (c C)) : ℝ))) :
    φ ≤ Real.sqrt 3 / 9 ∧ 513 / 100 < kappa (1 - φ) := by
  have h1 : φ ≤ Real.sqrt 3 / 9 := by
    have := kkn_optimal (k := 2) (by norm_num) hp0 hp1 h
    push_cast at this
    exact this.trans (f_two_le hp1)
  exact ⟨h1, kappa_of_le_f_two hφ h1⟩

end Planar

end Op4
