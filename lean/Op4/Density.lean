import Op4.General
import Op4.Orientation

/-!
# Facts A and B from the two density bounds

The degree facts of `Op4.Sharper` and `Op4.General` follow from two density bounds on the support
graph of `w` (paper, Lemmas `lem:facts` and `lem:factsgen`):
* `DensityA a w`: every vertex set `S` spans at most `a·|S|` edges;
* `DensityB b w`: for disjoint `S` and `T`, at most `b·(|S| + |T|)` edges join `S` to `T`.

Both bounds pass to every weighting whose support lies in that of `w` (`densityA_mono`,
`densityB_mono`). `facts_of_density` derives `A_t` for `t ≥ a` and `B_u` for `u ≥ 2a`, so the
hypothesis `Hcl` of `general` becomes the density bounds of `w` alone (`general_density`). For
planar graphs (`a = 3`, `b = 2`, from Euler's formula) this gives `sharper_range_density`.
With `orientation_of_density`, `random_centres_densityA` gives Theorem `thm:level` from the bound
`DensityA k w` alone.

## Not formalized
Euler's formula: a simple planar graph with `n ≥ 3` vertices has at most `3n - 6` edges, and at most
`2n - 4` if it is bipartite. Mathlib has no planarity.
-/

open Finset

namespace Op4

section Density

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator of a support edge. -/
noncomputable def e1 (w : V → V → NNReal) (P X : V) : ℝ := if w P X = 0 then 0 else 1

omit [Fintype V] [DecidableEq V] in
lemma e1_nonneg (w : V → V → NNReal) (P X : V) : 0 ≤ e1 w P X := by
  unfold e1; split_ifs <;> norm_num

/-- `2·e(S)`: the ordered pairs of adjacent vertices of `S`. -/
noncomputable def eIn (w : V → V → NNReal) (S : Finset V) : ℝ := ∑ P ∈ S, ∑ X ∈ S, e1 w P X

/-- The number of edges from `S` to `T`, for disjoint `S` and `T`. -/
noncomputable def eCr (w : V → V → NNReal) (S T : Finset V) : ℝ := ∑ P ∈ S, ∑ X ∈ T, e1 w P X

/-- Every vertex set `S` spans at most `a·|S|` edges. -/
def DensityA (a : ℝ) (w : V → V → NNReal) : Prop := ∀ S : Finset V, eIn w S ≤ 2 * a * S.card

/-- Every bipartite subgraph, between disjoint `S` and `T`, has at most `b·(|S| + |T|)` edges. -/
def DensityB (b : ℝ) (w : V → V → NNReal) : Prop :=
  ∀ S T : Finset V, Disjoint S T → eCr w S T ≤ b * (S.card + T.card)

omit [Fintype V] [DecidableEq V] in
lemma e1_mono {v w : V → V → NNReal} (hsub : ∀ P X, v P X ≠ 0 → w P X ≠ 0) (P X : V) :
    e1 v P X ≤ e1 w P X := by
  unfold e1
  by_cases h : v P X = 0
  · rw [ite_eq_left h]; split_ifs <;> norm_num
  · rw [ite_eq_right h, ite_eq_right (hsub P X h)]

omit [Fintype V] [DecidableEq V] in
lemma densityA_mono {a : ℝ} {v w : V → V → NNReal} (hsub : ∀ P X, v P X ≠ 0 → w P X ≠ 0)
    (hA : DensityA a w) : DensityA a v := fun S =>
  le_trans (sum_le_sum fun P _ => sum_le_sum fun X _ => e1_mono hsub P X) (hA S)

omit [Fintype V] [DecidableEq V] in
lemma densityB_mono {b : ℝ} {v w : V → V → NNReal} (hsub : ∀ P X, v P X ≠ 0 → w P X ≠ 0)
    (hB : DensityB b w) : DensityB b v := fun S T hST =>
  le_trans (sum_le_sum fun P _ => sum_le_sum fun X _ => e1_mono hsub P X) (hB S T hST)

omit [DecidableEq V] in
lemma deg_eq (w : V → V → NNReal) (P : V) : ((deg w P : ℕ) : ℝ) = ∑ X, e1 w P X := by
  unfold deg nbr e1
  rw [card_filter]; push_cast
  exact sum_congr rfl fun X _ => by split_ifs <;> simp_all

omit [DecidableEq V] in
lemma e1_eq_zero_of_deg {w : V → V → NNReal} {P : V} (h : deg w P = 0) (X : V) : e1 w P X = 0 := by
  have := deg_eq w P
  rw [h, Nat.cast_zero] at this
  have hle : e1 w P X ≤ ∑ Y, e1 w P Y :=
    single_le_sum (fun Y _ => e1_nonneg w P Y) (mem_univ X)
  linarith [e1_nonneg w P X]

/-- `Σ_{P ∈ S} d_P = 2e(S) + e(S, S^c)`. -/
lemma sum_deg_split (w : V → V → NNReal) (S : Finset V) :
    ∑ P ∈ S, ((deg w P : ℕ) : ℝ) = eIn w S + eCr w S Sᶜ := by
  unfold eIn eCr
  rw [← sum_add_distrib]
  exact sum_congr rfl fun P _ => by rw [deg_eq, sum_add_sum_compl]

omit [Fintype V] [DecidableEq V] in
lemma eCr_comm {w : V → V → NNReal} (hw : ∀ P X, w P X = w X P) (S T : Finset V) :
    eCr w S T = eCr w T S := by
  unfold eCr; rw [sum_comm]
  exact sum_congr rfl fun X _ => sum_congr rfl fun P _ => by unfold e1; rw [hw]

omit [DecidableEq V] in
lemma eCr_le_deg (w : V → V → NNReal) (S T : Finset V) :
    eCr w S T ≤ ∑ P ∈ S, ((deg w P : ℕ) : ℝ) := by
  unfold eCr
  refine sum_le_sum fun P _ => ?_
  rw [deg_eq]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun X _ _ => e1_nonneg w P X

/-- `Σ_P min(d_P, t) = t·|H| + Σ_{P ∉ H} d_P` for `H = {d ≥ t}`. -/
lemma sum_min_split (w : V → V → NNReal) (t : ℝ) :
    ∑ P, min ((deg w P : ℕ) : ℝ) t
      = t * (univ.filter fun P => t ≤ ((deg w P : ℕ) : ℝ)).card
        + ∑ P ∈ (univ.filter fun P => t ≤ ((deg w P : ℕ) : ℝ))ᶜ, ((deg w P : ℕ) : ℝ) := by
  rw [← sum_add_sum_compl (univ.filter fun P => t ≤ ((deg w P : ℕ) : ℝ))]
  congr 1
  · rw [sum_congr rfl fun P hP => min_eq_right (mem_filter.1 hP).2, sum_const, nsmul_eq_mul,
      mul_comm]
  · refine sum_congr rfl fun P hP => min_eq_left ?_
    have := mem_compl.1 hP
    simp only [mem_filter, mem_univ, true_and, not_le] at this
    exact this.le

/-- **Fact `A_t` for `t ≥ a`.** -/
theorem factAt_of_density {a t : ℝ} (ht : a ≤ t) {w : V → V → NNReal} (hw : ∀ P X, w P X = w X P)
    (hA : DensityA a w) : FactAt t w := by
  unfold FactAt
  set H := univ.filter fun P => t ≤ ((deg w P : ℕ) : ℝ) with hH
  have htot : ((∑ P, deg w P : ℕ) : ℝ)
      = ∑ P ∈ H, ((deg w P : ℕ) : ℝ) + ∑ P ∈ Hᶜ, ((deg w P : ℕ) : ℝ) := by
    push_cast; rw [sum_add_sum_compl]
  have h1 := sum_deg_split w H
  have h2 : eCr w H Hᶜ ≤ ∑ P ∈ Hᶜ, ((deg w P : ℕ) : ℝ) := by
    rw [eCr_comm hw]; exact eCr_le_deg w Hᶜ H
  have h3 := hA H
  have h4 := sum_min_split w t
  have hc : (0 : ℝ) ≤ H.card := by positivity
  have h5 : 2 * a * H.card ≤ 2 * t * H.card := by nlinarith
  rw [← hH] at h4
  linarith

/-- **Fact `B_u` for `u ≥ 2a`.** -/
theorem factBu_of_density {a b u : ℝ} (hu : 2 * a ≤ u) {w : V → V → NNReal}
    (hw : ∀ P X, w P X = w X P) (hA : DensityA a w) (hB : DensityB b w) : FactBu u b w := by
  unfold FactBu
  set H := univ.filter fun P => u ≤ ((deg w P : ℕ) : ℝ) with hH
  have htot : ((∑ P, deg w P : ℕ) : ℝ)
      = ∑ P ∈ H, ((deg w P : ℕ) : ℝ) + ∑ P ∈ Hᶜ, ((deg w P : ℕ) : ℝ) := by
    push_cast; rw [sum_add_sum_compl]
  have h1 := sum_deg_split w H
  have h3 := hA H
  have h4 := sum_min_split w u
  rw [← hH] at h4
  have hc : (0 : ℝ) ≤ H.card := by positivity
  have h5 : 2 * a * H.card ≤ u * H.card := by nlinarith
  -- the edges between `H` and `H^c` join non-isolated vertices
  have hST : eCr w H Hᶜ
      = eCr w (H.filter fun P => deg w P ≠ 0) (Hᶜ.filter fun P => deg w P ≠ 0) := by
    unfold eCr
    rw [sum_filter (s := H)]
    refine sum_congr rfl fun P _ => ?_
    by_cases hP : deg w P = 0
    · rw [ite_eq_right (not_not.2 hP)]
      exact sum_eq_zero fun X _ => e1_eq_zero_of_deg hP X
    · rw [ite_eq_left hP, sum_filter (s := Hᶜ)]
      refine sum_congr rfl fun X _ => ?_
      by_cases hX : deg w X = 0
      · rw [ite_eq_right (not_not.2 hX)]
        have := e1_eq_zero_of_deg hX P
        unfold e1 at this ⊢; rw [hw]; exact this
      · rw [ite_eq_left hX]
  have hdisj : Disjoint (H.filter fun P => deg w P ≠ 0) (Hᶜ.filter fun P => deg w P ≠ 0) :=
    disjoint_filter_filter disjoint_compl_right
  have hcard : (H.filter fun P => deg w P ≠ 0).card + (Hᶜ.filter fun P => deg w P ≠ 0).card
      = (univ.filter fun P => deg w P ≠ 0).card := by
    rw [← card_union_of_disjoint hdisj, ← filter_union, union_compl]
  have h6 := hB _ _ hdisj
  have hcard' : ((H.filter fun P => deg w P ≠ 0).card : ℝ) + (Hᶜ.filter fun P => deg w P ≠ 0).card
      = ((univ.filter fun P => deg w P ≠ 0).card : ℕ) := by
    exact_mod_cast hcard
  rw [hST] at h1
  rw [hcard'] at h6
  linarith

theorem facts_of_density {a b t u : ℝ} (ht : a ≤ t) (hu : 2 * a ≤ u) {w : V → V → NNReal}
    (hw : ∀ P X, w P X = w X P) (hA : DensityA a w) (hB : DensityB b w) :
    FactAt t w ∧ FactBu u b w :=
  ⟨factAt_of_density ht hw hA, factBu_of_density hu hw hA hB⟩

/-- The hypothesis `Hcl` of `general`, from the density bounds of `w` alone. -/
theorem hcl_of_density {a b : ℝ} {m l : ℕ} (t : Fin m → ℝ) (u : Fin l → ℝ) (ht : ∀ i, a ≤ t i)
    (hu : ∀ j, 2 * a ≤ u j) {w : V → V → NNReal} (hA : DensityA a w) (hB : DensityB b w) :
    ∀ v : V → V → NNReal, (∀ P X, v P X = v X P) → (∀ P X, v P X ≠ 0 → w P X ≠ 0) →
      (∀ i, FactAt (t i) v) ∧ (∀ j, FactBu (u j) b v) := fun _ hv hsub =>
  ⟨fun i => factAt_of_density (ht i) hv (densityA_mono hsub hA),
    fun j => factBu_of_density (hu j) hv (densityA_mono hsub hA) (densityB_mono hsub hB)⟩

/-- **Theorem `thm:general` from the density bounds.** -/
theorem general_density {p a b : ℝ} {m l : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (al t : Fin m → ℝ) (be u : Fin l → ℝ) (hal : ∀ i, 0 ≤ al i) (hbe : ∀ j, 0 ≤ be j)
    (ht : ∀ i, a ≤ t i) (hu : ∀ j, 2 * a ≤ u j)
    (hcert : ∀ d : ℕ, ∑ i, al i * min (d : ℝ) (t i)
      + ∑ j, be j * (min (d : ℝ) (u j) + if d = 0 then 0 else b) ≤ 1 - (1 - p) ^ d)
    (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA a w) (hB : DensityB b w) :
    (1 - p) * (∑ i, al i + 2 * ∑ j, be j) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) :=
  general hp0 hp1 al t be u hal hbe hcert w hw hloop (hcl_of_density t u ht hu hA hB)

omit [Fintype V] [DecidableEq V] in
lemma eIn_eq_card (w : V → V → NNReal) (S : Finset V) : eIn w S = ((pairsIn w S).card : ℝ) := by
  unfold eIn pairsIn e1
  rw [card_filter, sum_product]; push_cast
  exact sum_congr rfl fun P _ => sum_congr rfl fun X _ => by split_ifs <;> simp_all

/-- **Theorem `thm:level` from the density bound alone**: no orientation is needed. -/
theorem random_centres_densityA {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : V → V → NNReal)
    (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0) {k : ℕ} (hk : 0 < k)
    (hA : DensityA k w) :
    (1 - p) * (1 - (1 - p) ^ k) / k * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) :=
  random_centres_density hp0 hp1 w hw hloop hk fun S => by
    have := hA S
    rw [eIn_eq_card] at this
    exact_mod_cast this

/-- The planar facts A and B from `|E(S)| ≤ 3|S|` and the bipartite bound `2(|S| + |T|)`. -/
theorem planar_facts {w : V → V → NNReal} (hw : ∀ P X, w P X = w X P) (hA : DensityA 3 w)
    (hB : DensityB 2 w) : FactA w ∧ FactB w := by
  obtain ⟨hA', hB'⟩ := facts_of_density (t := 3) (u := 6) le_rfl (by norm_num) hw hA hB
  unfold FactAt at hA'
  unfold FactBu at hB'
  constructor
  · unfold FactA
    have : ((∑ P, deg w P : ℕ) : ℝ) ≤ ((2 * ∑ P, min (deg w P) 3 : ℕ) : ℝ) := by
      push_cast [Nat.cast_min] at hA' ⊢; exact hA'
    exact_mod_cast this
  · unfold FactB
    have : ((∑ P, deg w P : ℕ) : ℝ)
        ≤ ((∑ P, min (deg w P) 6 + 2 * (univ.filter fun P => deg w P ≠ 0).card : ℕ) : ℝ) := by
      push_cast [Nat.cast_min] at hB' ⊢; exact hB'
    exact_mod_cast this

/-- **Theorem `thm:planar` for every `p ∈ [21/64, 1]`, from the planar density bounds.** -/
theorem sharper_range_density {p : ℝ} (hp0 : 21 / 64 ≤ p) (hp1 : p ≤ 1)
    (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA 3 w) (hB : DensityB 2 w) :
    (1 - p) * (3 - 2 * (1 - p) ^ 3 - (1 - p) ^ 6) / 9 * ((∑ P, ∑ X, (w P X : ℝ)) / 2)
      ≤ E p univ (gain w) :=
  sharper_range hp0 hp1 w hw hloop fun _ hv hsub =>
    planar_facts hv (densityA_mono hsub hA) (densityB_mono hsub hB)

end Density

end Op4
