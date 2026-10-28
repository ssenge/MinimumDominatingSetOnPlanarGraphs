import Op4.Stars

/-!
# Proposition `prop:jointop`: nested triangles

For even `k ≥ 2`, `H` consists of `k` nested triangles `(i,0),(i,1),(i,2)` (that is, `a_i,b_i,c_i`),
and two vertices of consecutive triangles are adjacent if they have different letters. For even
`i`, the faces `a_i b_i c_{i+1}` and `a_{i+1} b_{i+1} c_i` lie in the band between the triangles
`i` and `i+1`; so face `j` is `{(j,0), (j,1), (j xor 1, 2)}`. The graph `nest k` inserts a vertex
`inr j` into every face `j`. It has `n = 4k` vertices and `12k - 6 = 3n - 6` edges (`nest_edges`).
* The closed neighbourhoods of the inserted vertices are disjoint, so every dominating set has
  at least `k = n/4` vertices (`nest_gamma`), and the inserted vertices dominate.
* Hence every star partition has at most `3n/4` join edges (`nest_join`), and an analysis that
  counts only join edges and bounds every level by a uniform fraction `φ` has `φ ≤ 1/4`
  (`nest_optimal`) and an exponent above `3.818` (`nest_kappa`).
That `nest k` is a planar triangulation is not stated, since Mathlib has no planarity.
-/

open Finset SimpleGraph

namespace Op4

namespace Nest

open Stars

variable {k : ℕ}

/-- The vertex `x` of `H` lies on face `j`. -/
def inFace (j : Fin k) (x : Fin k × Fin 3) : Prop :=
  (x.1.val = j.val ∧ x.2.val ≠ 2) ∨
    (x.2.val = 2 ∧ ((x.1.val % 2 = 0 ∧ j.val = x.1.val + 1) ∨ (x.1.val % 2 = 1 ∧ j.val + 1 = x.1.val)))

/-- The adjacency of `nest k`. -/
def nestAdj (k : ℕ) : (Fin k × Fin 3 ⊕ Fin k) → (Fin k × Fin 3 ⊕ Fin k) → Prop
  | .inl x, .inl y => x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ (pathGraph k).Adj x.1 y.1)
  | .inl x, .inr j => inFace j x
  | .inr j, .inl x => inFace j x
  | .inr _, .inr _ => False

/-- `k` nested triangles with a vertex inserted into every face of the chosen family. -/
def nest (k : ℕ) : SimpleGraph (Fin k × Fin 3 ⊕ Fin k) where
  Adj := nestAdj k
  symm := ⟨fun x y h => by
    rcases x with x | j <;> rcases y with y | j' <;> simp only [nestAdj] at h ⊢
    · exact ⟨fun e => h.1 e.symm, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩
    · exact h
    · exact h⟩
  loopless := ⟨fun x h => by
    rcases x with x | j <;> simp only [nestAdj] at h
    exact h.1 rfl⟩

lemma adj_inl_inl {x y : Fin k × Fin 3} :
    (nest k).Adj (.inl x) (.inl y) ↔ x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ (pathGraph k).Adj x.1 y.1) := Iff.rfl

lemma adj_inl_inr {x : Fin k × Fin 3} {j : Fin k} : (nest k).Adj (.inl x) (.inr j) ↔ inFace j x :=
  Iff.rfl

lemma adj_inr_inl {x : Fin k × Fin 3} {j : Fin k} : (nest k).Adj (.inr j) (.inl x) ↔ inFace j x :=
  Iff.rfl

lemma adj_inr_inr {j j' : Fin k} : ¬ (nest k).Adj (.inr j) (.inr j') := id

/-- The face of `x`. -/
def faceOf (hk : k % 2 = 0) (x : Fin k × Fin 3) : Fin k :=
  ⟨if x.2.val = 2 then (if x.1.val % 2 = 0 then x.1.val + 1 else x.1.val - 1) else x.1.val, by
    have := x.1.isLt
    split_ifs <;> omega⟩

/-- Every vertex of `H` lies on exactly one face. -/
lemma inFace_iff (hk : k % 2 = 0) (j : Fin k) (x : Fin k × Fin 3) : inFace j x ↔ j = faceOf hk x := by
  have := x.2.isLt
  rw [Fin.ext_iff]
  unfold inFace faceOf
  dsimp only
  split_ifs <;> omega

open Classical

/-! ### Counting the edges -/

open Classical in
lemma two_mul_edges (k : ℕ) :
    2 * #(nest k).edgeFinset = ∑ v, ∑ w, if (nest k).Adj v w then 1 else 0 := by
  rw [← sum_degrees_eq_twice_card_edges]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

lemma sum_ne_fin3 : ∀ t : Fin 3, ∑ t' : Fin 3, (if t ≠ t' then 1 else 0) = 2 := by decide

open Classical in
lemma sum_near (i : Fin k) :
    ∑ i' : Fin k, (if i = i' ∨ (pathGraph k).Adj i i' then 1 else 0) = 1 + (pathGraph k).degree i := by
  rw [← card_filter, ← card_neighborFinset_eq_degree]
  have e : (univ.filter fun i' => i = i' ∨ (pathGraph k).Adj i i') = insert i ((pathGraph k).neighborFinset i) := by
    ext i'
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_neighborFinset, eq_comm]
  rw [e, card_insert_of_notMem (by simp), add_comm]

open Classical in
/-- `nest k` has `12k - 6` edges. -/
theorem nest_edges (hk : k % 2 = 0) (hk1 : 1 ≤ k) : #(nest k).edgeFinset = 12 * k - 6 := by
  have h := two_mul_edges k
  simp only [Fintype.sum_sum_type] at h
  -- the four blocks
  have hA : ∀ x : Fin k × Fin 3, ∑ y : Fin k × Fin 3, (if (nest k).Adj (.inl x) (.inl y) then 1 else 0)
      = 2 * (1 + (pathGraph k).degree x.1) := by
    intro x
    simp only [adj_inl_inl]
    rw [Fintype.sum_prod_type]
    have e : ∀ i' : Fin k, ∑ t' : Fin 3,
        (if x.2 ≠ (i', t').2 ∧ (x.1 = (i', t').1 ∨ (pathGraph k).Adj x.1 (i', t').1) then 1 else 0)
        = 2 * (if x.1 = i' ∨ (pathGraph k).Adj x.1 i' then 1 else 0) := by
      intro i'
      by_cases hn : x.1 = i' ∨ (pathGraph k).Adj x.1 i'
      · simp only [hn, and_true, ↓reduceIte, mul_one]
        exact sum_ne_fin3 x.2
      · simp [hn]
    rw [sum_congr rfl fun i' _ => e i', ← mul_sum, sum_near]
  have hB : ∀ x : Fin k × Fin 3, ∑ j : Fin k, (if (nest k).Adj (.inl x) (.inr j) then 1 else 0) = 1 := by
    intro x
    simp only [adj_inl_inr, inFace_iff hk]
    rw [sum_ite_eq']
    simp
  have hC : ∑ j : Fin k, ∑ y : Fin k × Fin 3, (if (nest k).Adj (.inr j) (.inl y) then 1 else 0) =
      3 * k := by
    simp only [adj_inr_inl]
    rw [sum_comm]
    simp only [← adj_inl_inr, hB, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      smul_eq_mul, mul_one]
    ring
  have hD : ∀ j : Fin k, ∑ j' : Fin k, (if (nest k).Adj (.inr j) (.inr j') then 1 else 0) = 0 :=
    fun j => sum_eq_zero fun j' _ => by simp [adj_inr_inr]
  simp only [sum_add_distrib, hA, hB, hD, add_zero] at h
  rw [hC] at h
  have hdeg : ∑ x : Fin k × Fin 3, 2 * (1 + (pathGraph k).degree x.1) = 6 * (k + 2 * (k - 1)) := by
    rw [Fintype.sum_prod_type]
    have e : ∀ i : Fin k, ∑ _t : Fin 3, 2 * (1 + (pathGraph k).degree i) =
        6 + 6 * (pathGraph k).degree i := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Grid.sum_path_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [hdeg] at h
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

/-! ### Domination -/

lemma mem_cnbhd_inr {j : Fin k} {w : Fin k × Fin 3 ⊕ Fin k} :
    w ∈ cnbhd (nest k) (.inr j) ↔ w = .inr j ∨ ∃ x, w = .inl x ∧ inFace j x := by
  simp only [cnbhd, mem_insert, mem_neighborFinset]
  rcases w with x | j'
  · constructor
    · rintro (h | h)
      · exact absurd h (by simp)
      · exact Or.inr ⟨x, rfl, h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact absurd h (by simp)
      · rw [Sum.inl.inj hy]
        exact Or.inr h
  · constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact absurd h adj_inr_inr
    · rintro (h | ⟨y, hy, -⟩)
      · exact Or.inl h
      · exact absurd hy (by simp)

/-- **Every dominating set has at least `k = n/4` vertices.** -/
theorem nest_gamma (hk : k % 2 = 0) (D : Finset (Fin k × Fin 3 ⊕ Fin k))
    (hD : ∀ u, ∃ w ∈ D, w ∈ cnbhd (nest k) u) : k ≤ #D := by
  classical
  choose f hfD hfu using fun j : Fin k => hD (.inr j)
  have hinj : Set.InjOn f (univ : Finset (Fin k)) := by
    intro j _ j' _ h
    have h1 := mem_cnbhd_inr.1 (hfu j)
    have h2 := mem_cnbhd_inr.1 (hfu j')
    rw [h] at h1
    rcases h1 with h1 | ⟨x, hx, hjx⟩ <;> rcases h2 with h2 | ⟨y, hy, hjy⟩
    · exact Sum.inr.inj (h1.symm.trans h2)
    · rw [h1] at hy; exact absurd hy (by simp)
    · rw [hx] at h2; exact absurd h2 (by simp)
    · rw [hx] at hy
      rw [Sum.inl.inj hy] at hjx
      exact ((inFace_iff hk j _).1 hjx).trans ((inFace_iff hk j' _).1 hjy).symm
  have := card_le_card_of_injOn f (fun j _ => hfD j) hinj
  simpa using this

/-- The inserted vertices dominate, so `γ(nest k) = k`. -/
theorem nest_dominate (hk : k % 2 = 0) (u : Fin k × Fin 3 ⊕ Fin k) :
    ∃ w ∈ univ.image (Sum.inr : Fin k → Fin k × Fin 3 ⊕ Fin k), w ∈ cnbhd (nest k) u := by
  rcases u with x | j
  · refine ⟨.inr (faceOf hk x), mem_image_of_mem _ (mem_univ _), ?_⟩
    simp only [cnbhd, mem_insert, mem_neighborFinset, reduceCtorEq, false_or]
    exact (inFace_iff hk _ x).2 rfl
  · exact ⟨.inr j, mem_image_of_mem _ (mem_univ _), mem_insert_self _ _⟩

open Classical in
/-- **Proposition `prop:jointop`.** Every star partition of `nest k` has at most `3k = 3n/4` join
edges. -/
theorem nest_join (hk : k % 2 = 0) {σ : Fin k × Fin 3 ⊕ Fin k → Fin k × Fin 3 ⊕ Fin k}
    (hσ : IsStarMap (nest k) σ) : #(joinE σ) ≤ 3 * k := by
  have := card_joinE_add_le hσ (nest_gamma hk)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
  omega

open Classical in
/-- **No uniform analysis of join edges beats `1/4`.** If for every even `k ≥ 2` some star
partition of `nest k` has at least `φ·|E|` join edges, then `φ ≤ 1/4`. -/
theorem nest_optimal {φ : ℝ}
    (h : ∀ k, 2 ≤ k → k % 2 = 0 → ∃ σ : Fin k × Fin 3 ⊕ Fin k → Fin k × Fin 3 ⊕ Fin k,
      IsStarMap (nest k) σ ∧ φ * #(nest k).edgeFinset ≤ #(joinE σ)) : φ ≤ 1 / 4 := by
  by_contra hφ
  push Not at hφ
  obtain ⟨n, hn⟩ := exists_nat_gt (6 * φ / (12 * φ - 3))
  set m := 2 * n + 2 with hm
  obtain ⟨σ, hσ, hle⟩ := h m (by omega) (by omega)
  have h1 := nest_join (by omega) hσ
  rw [nest_edges (by omega) (by omega)] at hle
  have e : ((12 * m - 6 : ℕ) : ℝ) = 12 * m - 6 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e] at hle
  have h1R : ((#(joinE σ) : ℕ) : ℝ) ≤ 3 * m := by exact_mod_cast h1
  have hpos : (0 : ℝ) < 12 * φ - 3 := by linarith
  have h4 : (m : ℝ) * (12 * φ - 3) ≤ 6 * φ := by nlinarith
  have hnm : (n : ℝ) < m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h5 : 6 * φ / (12 * φ - 3) < m := hn.trans hnm
  rw [div_lt_iff₀ hpos] at h5
  linarith

set_option exponentiation.threshold 3000 in
/-- The exponent for a per-level fraction `φ ∈ (0, 1/4]` is above `3.818`. -/
theorem nest_kappa {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 1 / 4) : 1909 / 500 < kappa (1 - φ) := by
  have h := lt_kappa_nat (q := 3 / 4) 4 3 1909 500 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hm := kappa_mono (q := 3 / 4) (q' := 1 - φ) (by norm_num) (by linarith) (by linarith)
  have : ((1909 : ℕ) : ℝ) / ((500 : ℕ) : ℝ) = 1909 / 500 := by norm_num
  linarith

end Nest

end Op4
