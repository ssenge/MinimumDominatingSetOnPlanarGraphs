import Op4.Table
import Op4.Windows

/-!
# Star partitions: limits on the square grid

A one-level star contraction partitions the vertices into stars (`IsStarMap`): every vertex is a
centre, or a leaf adjacent to its centre. The join edges are the edges `s(x, σ x)` of the leaves;
the internal edges have both ends in the same star.
* `card_joinE_add_le`: the centres dominate, so if every dominating set has at least `γ`
  vertices, there are at most `n - γ` join edges.
* `card_internalE_le`: in a graph without triangles every internal edge is a join edge, and a
  centre has at most `Δ` leaves, so at most `Δ n/(Δ+1)` edges are internal.
* The square grid `P_m □ P_m` has no triangles, maximum degree `4` and `2m(m-1)` edges
  (`grid_edges`). So no star contraction makes more than a fraction `(2/5)·m/(m-1)` of its edges
  internal (`grid_internal`), and an analysis that bounds every level by a uniform fraction `φ`
  has `φ ≤ 2/5` (`grid_optimal`) and an exponent above `2.15` (`grid_kappa`).
-/

open Finset SimpleGraph

namespace Op4

namespace Stars

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A partition into stars, given by the centre `σ x` of the star of every vertex: `x` is a centre,
or a leaf adjacent to its centre, which is a centre. A centre without leaves is a singleton. -/
def IsStarMap (σ : V → V) : Prop := ∀ x, σ x = x ∨ (G.Adj x (σ x) ∧ σ (σ x) = σ x)

/-- The leaves. -/
def leaves (σ : V → V) : Finset V := univ.filter fun x => ¬ σ x = x

/-- The centres. -/
def centres (σ : V → V) : Finset V := univ.filter fun x => σ x = x

/-- The join edges `s(x, σ x)` of the leaves. -/
def joinE (σ : V → V) : Finset (Sym2 V) := (leaves σ).image fun x => s(x, σ x)

open Classical in
/-- The internal edges: both ends lie in the same star. -/
noncomputable def internalE (σ : V → V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ a b, e = s(a, b) ∧ σ a = σ b

variable {G}

lemma card_leaves_add (σ : V → V) : #(leaves σ) + #(centres σ) = Fintype.card V := by
  rw [add_comm, leaves, centres, card_filter_add_card_filter_not, card_univ]

/-- The centres dominate. -/
lemma centres_dominate {σ : V → V} (hσ : IsStarMap G σ) (u : V) :
    ∃ w ∈ centres σ, w ∈ cnbhd G u := by
  rcases hσ u with h | ⟨h1, h2⟩
  · exact ⟨u, mem_filter.2 ⟨mem_univ _, h⟩, mem_insert_self _ _⟩
  · exact ⟨σ u, mem_filter.2 ⟨mem_univ _, h2⟩, mem_insert_of_mem ((G.mem_neighborFinset u (σ u)).2 h1)⟩

/-- **Join edges and domination.** If every dominating set has at least `γ` vertices, a star
partition has at most `n - γ` join edges. -/
theorem card_joinE_add_le {σ : V → V} (hσ : IsStarMap G σ) {γ : ℕ}
    (hγ : ∀ D : Finset V, (∀ u, ∃ w ∈ D, w ∈ cnbhd G u) → γ ≤ #D) :
    #(joinE σ) + γ ≤ Fintype.card V := by
  have h1 := hγ _ (centres_dominate hσ)
  have h2 := card_leaves_add σ
  have h3 : #(joinE σ) ≤ #(leaves σ) := card_image_le
  omega

/-- **Without triangles, every internal edge is a join edge.** -/
lemma internalE_subset (hT : ∀ a b r, G.Adj a b → G.Adj a r → ¬ G.Adj b r) {σ : V → V}
    (hσ : IsStarMap G σ) : internalE G σ ⊆ joinE σ := by
  intro e he
  simp only [internalE, mem_filter] at he
  obtain ⟨he, a, b, rfl, hab⟩ := he
  rw [mem_edgeFinset, mem_edgeSet] at he
  simp only [joinE, leaves, mem_image, mem_filter, mem_univ, true_and]
  rcases hσ a with ha | ⟨ha1, -⟩ <;> rcases hσ b with hb | ⟨hb1, -⟩
  · exact absurd (ha.symm.trans (hab.trans hb)) (G.ne_of_adj he)
  · refine ⟨b, fun h => G.ne_of_adj he (ha.symm.trans (hab.trans h)), ?_⟩
    rw [← hab, ha, Sym2.eq_swap]
  · exact ⟨a, fun h => G.ne_of_adj he (h.symm.trans (hab.trans hb)), by rw [hab, hb]⟩
  · exact absurd (by rw [hab]; exact hb1) (hT a b (σ a) he ha1)

/-- **Internal edges in a graph without triangles.** If every degree is at most `Δ`, at most a
fraction `Δ/(Δ+1)` of the vertices are leaves, and so at most `Δn/(Δ+1)` edges are internal. -/
theorem card_internalE_le (hT : ∀ a b r, G.Adj a b → G.Adj a r → ¬ G.Adj b r) {σ : V → V}
    (hσ : IsStarMap G σ) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    (Δ + 1) * #(internalE G σ) ≤ Δ * Fintype.card V := by
  have h1 : #(internalE G σ) ≤ #(leaves σ) :=
    (card_le_card (internalE_subset hT hσ)).trans card_image_le
  have h2 : #(leaves σ) ≤ Δ * #(centres σ) := by
    refine card_le_mul_card_image_of_maps_to (f := σ) (fun x hx => ?_) Δ fun c _ => ?_
    · rw [leaves, mem_filter] at hx
      rcases hσ x with h | ⟨-, h⟩
      · exact absurd h hx.2
      · exact mem_filter.2 ⟨mem_univ _, h⟩
    · calc #{a ∈ leaves σ | σ a = c} ≤ #(G.neighborFinset c) := by
            refine card_le_card fun x hx => ?_
            rw [mem_filter, leaves, mem_filter] at hx
            rw [mem_neighborFinset]
            rcases hσ x with h | ⟨h, -⟩
            · exact absurd h hx.1.2
            · rw [← hx.2]
              exact h.symm
        _ = G.degree c := card_neighborFinset_eq_degree G c
        _ ≤ Δ := hΔ c
  have h3 := card_leaves_add σ
  calc (Δ + 1) * #(internalE G σ) ≤ (Δ + 1) * #(leaves σ) := Nat.mul_le_mul_left _ h1
    _ = Δ * #(leaves σ) + #(leaves σ) := by ring
    _ ≤ Δ * #(leaves σ) + Δ * #(centres σ) := Nat.add_le_add_left h2 _
    _ = Δ * Fintype.card V := by rw [← h3]; ring

end Stars

namespace Grid

open Stars

/-- The `m × m` square grid `P_m □ P_m`. -/
abbrev grid (m : ℕ) : SimpleGraph (Fin m × Fin m) := pathGraph m □ pathGraph m

lemma grid_adj_sum {m : ℕ} {x y : Fin m × Fin m} (h : (grid m).Adj x y) :
    x.1.val + x.2.val + 1 = y.1.val + y.2.val ∨ y.1.val + y.2.val + 1 = x.1.val + x.2.val := by
  rw [boxProd_adj, pathGraph_adj, pathGraph_adj] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> have := congrArg Fin.val h2 <;> omega

lemma grid_triangle (m : ℕ) (a b r : Fin m × Fin m) :
    (grid m).Adj a b → (grid m).Adj a r → ¬ (grid m).Adj b r := fun h1 h2 h3 => by
  have := grid_adj_sum h1
  have := grid_adj_sum h2
  have := grid_adj_sum h3
  omega

lemma path_degree (m : ℕ) (a : Fin m) :
    (pathGraph m).degree a = (if 0 < a.val then 1 else 0) + (if a.val + 1 < m then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree]
  have e : (pathGraph m).neighborFinset a =
      (univ.filter fun w : Fin m => w.val + 1 = a.val) ∪ (univ.filter fun w : Fin m => a.val + 1 = w.val) := by
    ext w
    simp only [mem_neighborFinset, pathGraph_adj, mem_union, mem_filter, mem_univ, true_and]
    tauto
  rw [e, card_union_of_disjoint (disjoint_filter.2 fun w _ h1 h2 => by omega)]
  congr 1
  · split_ifs with h
    · rw [card_eq_one]
      refine ⟨⟨a.val - 1, by omega⟩, ?_⟩
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
      omega
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro w _
      omega
  · split_ifs with h
    · rw [card_eq_one]
      refine ⟨⟨a.val + 1, h⟩, ?_⟩
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
      omega
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro w _
      have := w.isLt
      omega

lemma path_degree_le (m : ℕ) (a : Fin m) : (pathGraph m).degree a ≤ 2 := by
  rw [path_degree]
  split_ifs <;> omega

lemma sum_path_degree (m : ℕ) : ∑ a : Fin m, (pathGraph m).degree a = 2 * (m - 1) := by
  simp only [path_degree]
  rw [Fin.sum_univ_eq_sum_range (fun i => (if 0 < i then 1 else 0) + (if i + 1 < m then 1 else 0)) m,
    sum_add_distrib, ← card_filter, ← card_filter]
  have e1 : (range m).filter (fun i => 0 < i) = Ico 1 m := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  have e2 : (range m).filter (fun i => i + 1 < m) = range (m - 1) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [e1, e2, Nat.card_Ico, card_range]
  omega

open Classical in
lemma grid_degree_le (m : ℕ) (x : Fin m × Fin m) : (grid m).degree x ≤ 4 := by
  rw [degree_boxProd]
  have := path_degree_le m x.1
  have := path_degree_le m x.2
  omega

open Classical in
/-- The grid has `2m(m-1)` edges. -/
lemma grid_edges (m : ℕ) : #(grid m).edgeFinset = 2 * m * (m - 1) := by
  have h := (grid m).sum_degrees_eq_twice_card_edges
  simp only [degree_boxProd] at h
  rw [Fintype.sum_prod_type] at h
  have e : ∀ x : Fin m, ∑ y : Fin m, ((pathGraph m).degree x + (pathGraph m).degree y) =
      m * (pathGraph m).degree x + 2 * (m - 1) := by
    intro x
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_path_degree]
  simp only [e, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, sum_path_degree] at h
  have : 2 * #(grid m).edgeFinset = 2 * (2 * m * (m - 1)) := by rw [← h]; ring
  omega

open Classical in
/-- **The square grid.** In every star contraction of the `m × m` grid, at most `4m²/5` edges
become internal. -/
theorem grid_internal (m : ℕ) {σ : Fin m × Fin m → Fin m × Fin m} (hσ : IsStarMap (grid m) σ) :
    5 * #(internalE (grid m) σ) ≤ 4 * (m * m) := by
  have := card_internalE_le (grid_triangle m) hσ (fun x => by convert grid_degree_le m x)
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  exact this

open Classical in
/-- **No uniform analysis beats `2/5` on grids.** If for every `m ≥ 2` some star contraction of
the `m × m` grid makes at least a fraction `φ` of its edges internal, then `φ ≤ 2/5`. -/
theorem grid_optimal {φ : ℝ}
    (h : ∀ m, 2 ≤ m → ∃ σ : Fin m × Fin m → Fin m × Fin m, IsStarMap (grid m) σ ∧
      φ * #(grid m).edgeFinset ≤ #(internalE (grid m) σ)) : φ ≤ 2 / 5 := by
  by_contra hφ
  push Not at hφ
  obtain ⟨n, hn⟩ := exists_nat_gt (φ / (φ - 2 / 5))
  set m := n + 2 with hm
  obtain ⟨σ, hσ, hle⟩ := h m (by omega)
  have h1 := grid_internal m hσ
  rw [grid_edges] at hle
  have hmR : (2 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h1R : (5 : ℝ) * #(internalE (grid m) σ) ≤ 4 * (m * m) := by exact_mod_cast h1
  have e : ((2 * m * (m - 1) : ℕ) : ℝ) = 2 * m * (m - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e] at hle
  -- `φ·2m(m-1) ≤ 4m²/5`, so `φ(m-1) ≤ 2m/5`, so `m(φ - 2/5) ≤ φ`
  have hpos : (0 : ℝ) < φ - 2 / 5 := by linarith
  have h2 : φ * (2 * m * (m - 1)) ≤ 4 * (m * m) / 5 := by linarith
  have h3 : φ * (m - 1) ≤ 2 * m / 5 := by
    have hm0 : (0 : ℝ) < 2 * m := by linarith
    nlinarith
  have h4 : (m : ℝ) * (φ - 2 / 5) ≤ φ := by linarith
  have hnm : (n : ℝ) < m := by rw [hm]; push_cast; linarith
  have h5 : φ / (φ - 2 / 5) < m := hn.trans hnm
  rw [div_lt_iff₀ hpos] at h5
  linarith

set_option exponentiation.threshold 400 in
/-- The exponent for a per-level fraction `φ ∈ (0, 2/5]` is above `2.15`. -/
theorem grid_kappa {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 2 / 5) : 215 / 100 < kappa (1 - φ) := by
  have h := lt_kappa_nat (q := 3 / 5) 5 3 215 100 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have hm := kappa_mono (q := 3 / 5) (q' := 1 - φ) (by norm_num) (by linarith) (by linarith)
  have : ((215 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 215 / 100 := by norm_num
  linarith

end Grid

end Op4
