import Op4.Kkn
import Op4.Table

/-!
# Identifier-free rules on the triangular grid

The last proposition of Section `sec:limits`: let every part become a centre independently, with a
probability that depends only on its radius-`r` neighbourhood and not on identifiers, and let every
non-centre join some centre neighbour. On the `m × m` triangular grid `tri m` with unit weights,
the expected number of join edges is at most `m²·max_s s(1-s⁶) + 4(r+1)m` (`idfree_joins`), and
the grid has at least `3m² - 12(r+1)m` edges (`tri_edges`). So an analysis of such a rule that
counts only join edges has a per-level fraction of at most `max_s s(1-s⁶)/3 = 2·7^{-7/6} ≈ 0.2066`
(`idfree_optimal`, with the rational bound `30987/150000`) and an exponent above `4.74`
(`idfree_kappa`).

The rule sees the presence of the vertices at the offsets `[-r, r]²` (`view`), which contains the
radius-`r` ball; seeing more only strengthens the rule. The coins are independent with
probability `q P` for the part `P` (`EQ`).
-/

open Finset SimpleGraph

namespace Op4

namespace TriGrid

/-! ### Independent coins with different probabilities -/

section EQ

variable {α : Type*} [DecidableEq α]

/-- Probability that the random subset of `A` is `D`, when `a` is included with probability
`q a`. -/
noncomputable def pwq (q : α → ℝ) (A D : Finset α) : ℝ := (∏ a ∈ D, q a) * ∏ a ∈ A \ D, (1 - q a)

/-- Expectation of `f` over the random subset of `A`. -/
noncomputable def EQ (q : α → ℝ) (A : Finset α) (f : Finset α → ℝ) : ℝ :=
  ∑ D ∈ A.powerset, pwq q A D * f D

lemma EQ_empty (q : α → ℝ) (f : Finset α → ℝ) : EQ q ∅ f = f ∅ := by
  simp [EQ, pwq]

lemma EQ_insert (q : α → ℝ) {a : α} {A : Finset α} (ha : a ∉ A) (f : Finset α → ℝ) :
    EQ q (insert a A) f = (1 - q a) * EQ q A f + q a * EQ q A (fun D => f (insert a D)) := by
  unfold EQ
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun D hD => ?_
    have haD : a ∉ D := fun h => ha (mem_powerset.1 hD h)
    unfold pwq
    rw [insert_sdiff_of_notMem _ haD, prod_insert (fun h => ha (mem_sdiff.1 h).1)]
    ring
  · refine sum_congr rfl fun D hD => ?_
    have haD : a ∉ D := fun h => ha (mem_powerset.1 hD h)
    unfold pwq
    rw [prod_insert haD, insert_sdiff_insert, sdiff_insert_of_notMem ha]
    ring

lemma EQ_congr (q : α → ℝ) (A : Finset α) {f g : Finset α → ℝ} (h : ∀ D ⊆ A, f D = g D) :
    EQ q A f = EQ q A g :=
  sum_congr rfl fun D hD => by rw [h D (mem_powerset.1 hD)]

lemma EQ_const (q : α → ℝ) (A : Finset α) (c : ℝ) : EQ q A (fun _ => c) = c := by
  induction A using Finset.induction_on with
  | empty => simp [EQ_empty]
  | insert a A ha ih => rw [EQ_insert q ha]; simp only [ih]; ring

lemma pwq_nonneg {q : α → ℝ} (hq : ∀ a, 0 ≤ q a ∧ q a ≤ 1) (A D : Finset α) : 0 ≤ pwq q A D :=
  mul_nonneg (prod_nonneg fun a _ => (hq a).1) (prod_nonneg fun a _ => by linarith [(hq a).2])

lemma EQ_mono {q : α → ℝ} (hq : ∀ a, 0 ≤ q a ∧ q a ≤ 1) (A : Finset α) {f g : Finset α → ℝ}
    (h : ∀ D ⊆ A, f D ≤ g D) : EQ q A f ≤ EQ q A g :=
  sum_le_sum fun D hD => mul_le_mul_of_nonneg_left (h D (mem_powerset.1 hD)) (pwq_nonneg hq A D)

lemma EQ_sum {ι : Type*} (q : α → ℝ) (A : Finset α) (s : Finset ι) (f : ι → Finset α → ℝ) :
    EQ q A (fun D => ∑ i ∈ s, f i D) = ∑ i ∈ s, EQ q A (f i) := by
  unfold EQ; simp_rw [mul_sum]; exact sum_comm

/-- Coins outside `A` do not affect a function of `D ∩ A`. -/
lemma EQ_marg (q : α → ℝ) {A B : Finset α} (hAB : A ⊆ B) (f : Finset α → ℝ) :
    EQ q B (fun D => f (D ∩ A)) = EQ q A f := by
  have key : ∀ S : Finset α, Disjoint S A → EQ q (S ∪ A) (fun D => f (D ∩ A)) = EQ q A f := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [empty_union]
      exact EQ_congr q A fun D hD => by rw [inter_eq_left.mpr hD]
    | insert y S hy ih =>
      intro hdis
      have hyA : y ∉ A := disjoint_left.mp hdis (mem_insert_self y S)
      have hyS : y ∉ S ∪ A := by simp [hy, hyA]
      rw [insert_union, EQ_insert q hyS]
      simp only [insert_inter_of_notMem hyA]
      rw [ih (disjoint_of_subset_left (subset_insert y S) hdis)]
      ring
  have h := key (B \ A) sdiff_disjoint
  rwa [sdiff_union_of_subset hAB] at h

lemma EQ_empty_ind (q : α → ℝ) (A : Finset α) :
    EQ q A (fun D => if D = ∅ then (1 : ℝ) else 0) = ∏ a ∈ A, (1 - q a) := by
  induction A using Finset.induction_on with
  | empty => simp [EQ_empty]
  | insert a A ha ih =>
    have h0 : EQ q A (fun D => if insert a D = ∅ then (1 : ℝ) else 0) = 0 :=
      (EQ_congr q A (g := fun _ => 0) fun D _ => by simp).trans (EQ_const q A 0)
    rw [EQ_insert q ha, ih, h0, prod_insert ha]
    ring

lemma EQ_one_sub (q : α → ℝ) (A : Finset α) (g : Finset α → ℝ) :
    EQ q A (fun D => 1 - g D) = 1 - EQ q A g := by
  have h := EQ_const q A 1
  unfold EQ at h ⊢
  simp only [mul_sub, mul_one, sum_sub_distrib] at h ⊢
  rw [h]

end EQ

section Joining

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `P` joins a star with probability `(1 - q P)(1 - ∏_{X ∈ N(P)} (1 - q X))`. -/
lemma EQ_joins (q : V → ℝ) (P : V) :
    EQ q univ (fun C => if Joins G C P then (1 : ℝ) else 0) =
      (1 - q P) * (1 - ∏ X ∈ G.neighborFinset P, (1 - q X)) := by
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
  rw [e1, EQ_marg q (subset_univ _) f, EQ_insert q hPA]
  have h2 : EQ q A (fun D => f (insert P D)) = 0 :=
    (EQ_congr q A (g := fun _ => 0) fun D _ => by simp [hf]).trans (EQ_const q A 0)
  have h3 : EQ q A f = EQ q A (fun D => 1 - if D = ∅ then (1 : ℝ) else 0) :=
    EQ_congr q A fun D hD => by
      have hPD : P ∉ D := fun h => hPA (hD h)
      simp only [hf, inter_eq_left.2 hD]
      by_cases h0 : D = ∅
      · simp [h0]
      · simp [hPD, h0, nonempty_iff_ne_empty]
  rw [h2, h3, EQ_one_sub, EQ_empty_ind]
  ring

end Joining

/-! ### The triangular grid -/

/-- The three edge directions. -/
def triRel (m : ℕ) (x y : Fin m × Fin m) : Prop :=
  (x.1.val + 1 = y.1.val ∧ x.2 = y.2) ∨ (x.1 = y.1 ∧ x.2.val + 1 = y.2.val) ∨
    (x.1.val + 1 = y.1.val ∧ y.2.val + 1 = x.2.val)

/-- The `m × m` triangular grid. -/
def tri (m : ℕ) : SimpleGraph (Fin m × Fin m) := SimpleGraph.fromRel (triRel m)

instance (m : ℕ) : DecidableRel (triRel m) := fun x y => by unfold triRel; infer_instance

instance (m : ℕ) : DecidableRel (tri m).Adj := fun x y =>
  decidable_of_iff (x ≠ y ∧ (triRel m x y ∨ triRel m y x)) (by rw [tri, fromRel_adj])

lemma tri_adj_val {m : ℕ} {x y : Fin m × Fin m} (h : (tri m).Adj x y) :
    (x.1.val + 1 = y.1.val ∧ x.2.val = y.2.val) ∨ (y.1.val + 1 = x.1.val ∧ x.2.val = y.2.val) ∨
    (x.1.val = y.1.val ∧ x.2.val + 1 = y.2.val) ∨ (x.1.val = y.1.val ∧ y.2.val + 1 = x.2.val) ∨
    (x.1.val + 1 = y.1.val ∧ y.2.val + 1 = x.2.val) ∨
    (y.1.val + 1 = x.1.val ∧ x.2.val + 1 = y.2.val) := by
  rw [tri, fromRel_adj] at h
  obtain ⟨-, h⟩ := h
  unfold triRel at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
    (try have h1' := congrArg Fin.val h1) <;> (try have h2' := congrArg Fin.val h2) <;> omega

lemma tri_adj_of_val {m : ℕ} {x y : Fin m × Fin m}
    (h : (x.1.val + 1 = y.1.val ∧ x.2.val = y.2.val) ∨ (x.1.val = y.1.val ∧ x.2.val + 1 = y.2.val) ∨
      (x.1.val + 1 = y.1.val ∧ y.2.val + 1 = x.2.val)) : (tri m).Adj x y := by
  rw [tri, fromRel_adj]
  refine ⟨fun hxy => ?_, Or.inl ?_⟩
  · subst hxy
    omega
  · unfold triRel
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, Fin.ext h2⟩
    · exact Or.inr (Or.inl ⟨Fin.ext h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The six offsets. -/
def S6 : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

lemma card_S6 : #S6 = 6 := by decide

/-- The offset of `X` from `P`. -/
def off {m : ℕ} (P X : Fin m × Fin m) : ℤ × ℤ :=
  ((X.1.val : ℤ) - P.1.val, (X.2.val : ℤ) - P.2.val)

lemma tri_degree_le (m : ℕ) (P : Fin m × Fin m) : (tri m).degree P ≤ 6 := by
  rw [← card_neighborFinset_eq_degree, ← card_S6]
  refine card_le_card_of_injOn (off P) (fun X hX => ?_) (fun X _ Y _ hXY => ?_)
  · rw [mem_coe, mem_neighborFinset] at hX
    have := tri_adj_val hX
    simp only [mem_coe, S6, off, mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  · simp only [off, Prod.mk.injEq] at hXY
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- `P` is at distance more than `r + 1` from the boundary. -/
def deep (r m : ℕ) (P : Fin m × Fin m) : Prop :=
  r + 1 ≤ P.1.val ∧ P.1.val + r + 2 ≤ m ∧ r + 1 ≤ P.2.val ∧ P.2.val + r + 2 ≤ m

instance (r m : ℕ) (P : Fin m × Fin m) : Decidable (deep r m P) := by unfold deep; infer_instance

lemma tri_degree_deep {r m : ℕ} {P : Fin m × Fin m} (hP : deep r m P) : 6 ≤ (tri m).degree P := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  rw [← card_neighborFinset_eq_degree, ← card_S6]
  refine (card_le_card fun d hd => ?_).trans (card_image_le (s := (tri m).neighborFinset P)
    (f := off P))
  simp only [S6, mem_insert, mem_singleton] at hd
  rw [mem_image]
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(⟨P.1.val + 1, by omega⟩, P.2), ?_, ?_⟩
    · rw [mem_neighborFinset]; exact tri_adj_of_val (Or.inl ⟨rfl, rfl⟩)
    · simp [off]
  · refine ⟨(⟨P.1.val - 1, by omega⟩, P.2), ?_, ?_⟩
    · rw [mem_neighborFinset]
      exact (tri_adj_of_val (x := (⟨P.1.val - 1, by omega⟩, P.2)) (y := P)
        (Or.inl ⟨by dsimp only; omega, rfl⟩)).symm
    · simp only [off, Prod.mk.injEq]; push_cast [show 1 ≤ P.1.val by omega]; constructor <;> ring
  · refine ⟨(P.1, ⟨P.2.val + 1, by omega⟩), ?_, ?_⟩
    · rw [mem_neighborFinset]; exact tri_adj_of_val (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [off]
  · refine ⟨(P.1, ⟨P.2.val - 1, by omega⟩), ?_, ?_⟩
    · rw [mem_neighborFinset]
      exact (tri_adj_of_val (x := (P.1, ⟨P.2.val - 1, by omega⟩)) (y := P)
        (Or.inr (Or.inl ⟨rfl, by dsimp only; omega⟩))).symm
    · simp only [off, Prod.mk.injEq]; push_cast [show 1 ≤ P.2.val by omega]; constructor <;> ring
  · refine ⟨(⟨P.1.val + 1, by omega⟩, ⟨P.2.val - 1, by omega⟩), ?_, ?_⟩
    · rw [mem_neighborFinset]; exact tri_adj_of_val (Or.inr (Or.inr ⟨rfl, by simp; omega⟩))
    · simp only [off, Prod.mk.injEq]; push_cast [show 1 ≤ P.2.val by omega]; constructor <;> ring
  · refine ⟨(⟨P.1.val - 1, by omega⟩, ⟨P.2.val + 1, by omega⟩), ?_, ?_⟩
    · rw [mem_neighborFinset]
      exact (tri_adj_of_val (Or.inr (Or.inr ⟨by simp; omega, by simp⟩))).symm
    · simp only [off, Prod.mk.injEq]; push_cast [show 1 ≤ P.1.val by omega]; constructor <;> ring

/-! ### Counting the vertices near the boundary -/

lemma card_fin_filter_le (m r : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ)
    (hf : ∀ i < m, p i → f i < r + 1) (hinj : ∀ i < m, ∀ j < m, p i → p j → f i = f j → i = j) :
    #(univ.filter fun i : Fin m => p i.val) ≤ r + 1 := by
  rw [← card_range (r + 1)]
  refine card_le_card_of_injOn (fun i => f i.val) (fun i hi => ?_) (fun i hi j hj h => ?_)
  · rw [mem_coe, mem_filter] at hi
    exact mem_coe.2 (mem_range.2 (hf i.val i.isLt hi.2))
  · rw [mem_coe, mem_filter] at hi hj
    exact Fin.ext (hinj i.val i.isLt j.val j.isLt hi.2 hj.2 h)

lemma card_not_deep (r m : ℕ) : #(univ.filter fun P : Fin m × Fin m => ¬ deep r m P) ≤
    4 * (r + 1) * m := by
  set A : Finset (Fin m) := univ.filter fun i => i.val < r + 1
  set B : Finset (Fin m) := univ.filter fun i => m < i.val + r + 2
  have hA : #A ≤ r + 1 := card_fin_filter_le m r (fun i => i < r + 1) id (fun i _ h => h)
    (fun i _ j _ _ _ h => h)
  have hB : #B ≤ r + 1 := card_fin_filter_le m r (fun i => m < i + r + 2) (fun i => m - 1 - i)
    (fun i hi h => by omega) (fun i hi j hj _ _ h => by omega)
  have hsub : (univ.filter fun P : Fin m × Fin m => ¬ deep r m P) ⊆
      ((A ×ˢ univ) ∪ (B ×ˢ univ)) ∪ ((univ ×ˢ A) ∪ (univ ×ˢ B)) := by
    intro P hP
    have hP2 := (mem_filter.1 hP).2
    unfold deep at hP2
    simp only [A, B, mem_union, mem_product, mem_filter, mem_univ, true_and, and_true]
    omega
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have h1 := card_union_le (A ×ˢ (univ : Finset (Fin m))) (B ×ˢ univ)
  have h2 := card_union_le ((univ : Finset (Fin m)) ×ˢ A) (univ ×ˢ B)
  simp only [card_product, card_univ, Fintype.card_fin] at h1 h2
  have : #A * m + #B * m + (m * #A + m * #B) ≤ 4 * (r + 1) * m := by
    have := Nat.mul_le_mul_right m hA
    have := Nat.mul_le_mul_right m hB
    nlinarith
  omega

open Classical in
/-- **The triangular grid has at least `3m² - 12(r+1)m` edges.** -/
theorem tri_edges (r m : ℕ) : 3 * (m * m) ≤ #(tri m).edgeFinset + 12 * (r + 1) * m := by
  have h := (tri m).sum_degrees_eq_twice_card_edges
  have h1 : ∑ P : Fin m × Fin m, (if deep r m P then 6 else 0) ≤ ∑ P, (tri m).degree P :=
    sum_le_sum fun P _ => by
      split_ifs with hP
      · exact tri_degree_deep hP
      · exact Nat.zero_le _
  have h2 : ∑ P : Fin m × Fin m, (if deep r m P then 6 else 0) =
      6 * #(univ.filter fun P : Fin m × Fin m => deep r m P) := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  have h3 := card_not_deep r m
  have h4 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m × Fin m)))
    (fun P => deep r m P)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h4
  have h5 : 12 * (r + 1) * m = 3 * (4 * (r + 1) * m) := by ring
  omega

/-! ### The rule -/

/-- What a part sees: the presence of the vertices at the offsets `[-r, r]²`. -/
def view (r m : ℕ) (P : Fin m × Fin m) : Fin (2 * r + 1) × Fin (2 * r + 1) → Bool := fun ab =>
  decide (r ≤ P.1.val + ab.1.val ∧ P.1.val + ab.1.val < m + r ∧
    r ≤ P.2.val + ab.2.val ∧ P.2.val + ab.2.val < m + r)

lemma view_interior {r m : ℕ} {P : Fin m × Fin m} (h1 : r ≤ P.1.val) (h2 : P.1.val + r < m)
    (h3 : r ≤ P.2.val) (h4 : P.2.val + r < m) : view r m P = fun _ => true := by
  funext ab
  have := ab.1.isLt
  have := ab.2.isLt
  simp only [view, decide_eq_true_eq]
  omega

/-- **`max_s s(1-s⁶) ≤ 30987/50000`** on `[0,1]`; the maximum is `6·7^{-7/6} ≈ 0.61973`. -/
lemma s_one_sub_le {s : ℝ} (hs0 : 0 ≤ s) : s * (1 - s ^ 6) ≤ 30987 / 50000 := by
  have hh : 0 ≤ (1707974020880829601 / 1250000000000000000 : ℝ) * s ^ 1 +
      (47245553950951 / 31250000000000 : ℝ) * s ^ 2 + (3920684403 / 2500000000 : ℝ) * s ^ 3 +
      (36151 / 25000 : ℝ) * s ^ 4 + (1 / 1 : ℝ) * s ^ 5 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (s - 36151 / 50000)) hh,
    sq_nonneg (s - 36151 / 50000 + (-1141024816159067789731 / 12348993765772574181150200000 : ℝ))]

open Classical in
/-- **Expected join edges.** For every identifier-free rule `ρ` with probabilities in `[0,1]`
and every choice of centre neighbours, the expected number of join edges on `tri m` is at most
`m²·30987/50000 + 4(r+1)m`. -/
theorem idfree_joins (r m : ℕ) (ρ : (Fin (2 * r + 1) × Fin (2 * r + 1) → Bool) → ℝ)
    (hρ : ∀ w, 0 ≤ ρ w ∧ ρ w ≤ 1) (c : Finset (Fin m × Fin m) → Fin m × Fin m → Fin m × Fin m) :
    EQ (fun P => ρ (view r m P)) univ
        (fun C => (#((joined (tri m) C).image fun P => s(P, c C P)) : ℝ)) ≤
      m * m * (30987 / 50000) + 4 * (r + 1) * m := by
  set q : Fin m × Fin m → ℝ := fun P => ρ (view r m P) with hq
  have hq01 : ∀ P, 0 ≤ q P ∧ q P ≤ 1 := fun P => hρ _
  set p₀ := ρ (fun _ => true)
  have h1 : EQ q univ (fun C => (#((joined (tri m) C).image fun P => s(P, c C P)) : ℝ)) ≤
      EQ q univ (fun C => ∑ P, if Joins (tri m) C P then (1 : ℝ) else 0) := by
    refine EQ_mono hq01 _ fun C _ => ?_
    have e : (#(joined (tri m) C) : ℝ) = ∑ P, if Joins (tri m) C P then (1 : ℝ) else 0 := by
      rw [joined, card_filter]
      push_cast
      rfl
    rw [← e]
    exact_mod_cast card_image_le
  rw [EQ_sum] at h1
  have h2 : ∀ P, EQ q univ (fun C => if Joins (tri m) C P then (1 : ℝ) else 0) ≤
      30987 / 50000 + (if deep r m P then 0 else 1) := by
    intro P
    rw [EQ_joins]
    have hP0 := hq01 P
    by_cases hP : deep r m P
    · obtain ⟨d1, d2, d3, d4⟩ := hP
      have hqP : q P = p₀ := by
        simp only [hq, p₀]
        rw [view_interior (by omega) (by omega) (by omega) (by omega)]
      have hprod : ∏ X ∈ (tri m).neighborFinset P, (1 - q X) =
          (1 - p₀) ^ #((tri m).neighborFinset P) := by
        rw [← prod_const]
        refine prod_congr rfl fun X hX => ?_
        rw [mem_neighborFinset] at hX
        have := tri_adj_val hX
        simp only [hq, p₀]
        rw [view_interior (by omega) (by omega) (by omega) (by omega)]
      rw [hqP, hprod, card_neighborFinset_eq_degree]
      have hs0 : 0 ≤ 1 - p₀ := by linarith [(hρ (fun _ => true)).2]
      have hs1 : 1 - p₀ ≤ 1 := by linarith [(hρ (fun _ => true)).1]
      have hd := tri_degree_le m P
      have hpow : (1 - p₀) ^ 6 ≤ (1 - p₀) ^ (tri m).degree P :=
        pow_le_pow_of_le_one hs0 hs1 hd
      have := s_one_sub_le hs0
      simp only [show deep r m P from ⟨d1, d2, d3, d4⟩, ↓reduceIte, add_zero]
      nlinarith
    · simp only [hP, ↓reduceIte]
      have hprod : 0 ≤ ∏ X ∈ (tri m).neighborFinset P, (1 - q X) :=
        prod_nonneg fun X _ => by linarith [(hq01 X).2]
      have hprod1 : ∏ X ∈ (tri m).neighborFinset P, (1 - q X) ≤ 1 :=
        prod_le_one₀ (fun X _ => by linarith [(hq01 X).2]) (fun X _ => by linarith [(hq01 X).1])
      nlinarith
  calc _ ≤ ∑ P, EQ q univ (fun C => if Joins (tri m) C P then (1 : ℝ) else 0) := h1
    _ ≤ ∑ P : Fin m × Fin m, (30987 / 50000 + (if deep r m P then (0 : ℝ) else 1)) :=
        sum_le_sum fun P _ => h2 P
    _ = m * m * (30987 / 50000) + #(univ.filter fun P : Fin m × Fin m => ¬ deep r m P) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
        push_cast
        ring
    _ ≤ m * m * (30987 / 50000) + 4 * (r + 1) * m := by
        have := card_not_deep r m
        have : ((#(univ.filter fun P : Fin m × Fin m => ¬ deep r m P) : ℕ) : ℝ) ≤
            ((4 * (r + 1) * m : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith

open Classical in
/-- **No analysis of join edges beats `2·7^{-7/6}`.** Let the rule `ρ m` on `tri m` depend on `m`
(so the parts may know `n`). If for every `m` some choice of centre neighbours gives at least
`φ·|E|` expected join edges on `tri m`, then `φ ≤ 30987/150000`. -/
theorem idfree_optimal (r : ℕ) (ρ : ℕ → (Fin (2 * r + 1) × Fin (2 * r + 1) → Bool) → ℝ)
    (hρ : ∀ m w, 0 ≤ ρ m w ∧ ρ m w ≤ 1) {φ : ℝ}
    (h : ∀ m : ℕ, ∃ c : Finset (Fin m × Fin m) → Fin m × Fin m → Fin m × Fin m,
      φ * #(tri m).edgeFinset ≤ EQ (fun P => ρ m (view r m P)) univ
        (fun C => (#((joined (tri m) C).image fun P => s(P, c C P)) : ℝ))) :
    φ ≤ 30987 / 150000 := by
  by_contra hφ
  push Not at hφ
  have hpos : (0 : ℝ) < 3 * φ - 30987 / 50000 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((12 * φ + 4) * (r + 1) / (3 * φ - 30987 / 50000))
  set m := n + 1 with hm
  obtain ⟨c, hc⟩ := h m
  have hup := idfree_joins r m (ρ m) (hρ m) c
  have hE := tri_edges r m
  have hER : (3 : ℝ) * (m * m) ≤ #(tri m).edgeFinset + 12 * (r + 1) * m := by exact_mod_cast hE
  have hφ0 : (0 : ℝ) ≤ φ := by linarith
  have hmR : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- `φ(3m² - 12(r+1)m) ≤ m²M + 4(r+1)m`
  have h1 : φ * (3 * (m * m) - 12 * (r + 1) * m) ≤ m * m * (30987 / 50000) + 4 * (r + 1) * m := by
    have : φ * (3 * (m * m) - 12 * (r + 1) * m) ≤ φ * #(tri m).edgeFinset :=
      mul_le_mul_of_nonneg_left (by linarith) hφ0
    linarith
  have h2 : (m : ℝ) * (3 * φ - 30987 / 50000) ≤ (12 * φ + 4) * (r + 1) := by
    have hm0 : (0 : ℝ) < m := by linarith
    nlinarith
  have hnm : (n : ℝ) < m := by rw [hm]; push_cast; linarith
  have h3 := hn.trans hnm
  rw [div_lt_iff₀ hpos] at h3
  linarith

set_option exponentiation.threshold 2000 in
/-- The exponent for a per-level fraction `φ ∈ (0, 30987/150000]` is above `4.74`. -/
theorem idfree_kappa {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 30987 / 150000) :
    474 / 100 < kappa (1 - φ) := by
  have h := lt_kappa_nat (q := 1 - 30987 / 150000) 150000 119013 474 100 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hm := kappa_mono (q := 1 - 30987 / 150000) (q' := 1 - φ) (by norm_num) (by linarith)
    (by linarith)
  have : ((474 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 474 / 100 := by norm_num
  linarith

end TriGrid

end Op4
