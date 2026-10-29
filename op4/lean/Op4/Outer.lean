import Mathlib

/-!
# Outerplanar graphs, Theorem `thm:outerplanar`: the combinatorial steps

The proof of Theorem `thm:outerplanar` unfolds the graph into a covering graph whose decomposition
is a tree, and runs the construction of Theorem `thm:forests` on it. This file checks the steps
that can be stated on their own, with the structure of the unfolded graph as hypotheses.

* **Runs** (`CorePath`). A core path has adhesions `X i` (`i ∈ ℤ`), each one vertex or one edge
  (`card_X`, `near`), and every vertex lies in the adhesions of an interval of indices, its run
  (`mem_run`, `interval`). The distance `d` is any function with the triangle inequality and
  `d x y = 0 → x = y`, for example `G.dist` in a connected graph (`ofGraph`).
  - `R1`: the adhesions at maximal runs `I_c` and `I_{c'}` with `c' ≥ c + 3` are disjoint.
  - `R2_upper`, `R2_lower`: if `k` maximal runs meet `[a, b]`, then
    `(k - 4)/2 ≤ Σ_{i ∈ [a,b]} 1/ρ_i ≤ k`.
  - `R3`: `d(X_a, X_b) ≤ 2 Σ_{i ∈ [a,b]} μ(e_i) + 3`; hence a path window of length at most `R`
    has its adhesions within distance `2R + 3` of the first one (`window_radius`).
* **Windows** (`window_weight`): with weight `dτ/R`, every node has total weight `1`.
* **Counting** (`core_paths_le`, `sum_mu_le`, `cut_weight_le`, `det_cut_le`, `det_excess`,
  `rand_cut_le`, `rand_size`): the constants of the proof, from the per-step bounds as
  hypotheses.
* **Branch nodes** (`branch_count`, `branch_neighbours`): in a finite graph,
  `Σ_{deg ≥ 3} (deg - 2) ≤ 2·rk + #{deg = 1}`, so the nodes of degree other than `2` have at most
  `6·rk + 4·#{deg = 1}` neighbours in total.
* **Anchors** (`big_of_not_subset_left`, `big_of_not_subset_right`, `card_symmDiff_le`,
  `sum_symmDiff_le`, `anchor_cuts`): the interval facts behind the cut probability of the
  randomized version.
* **Holes** (`few_holes`, `exists_sparse`, `cycle_packing`): the count `h ≤ 3γ_f/(ℓ - 13)` from
  the packing sets, and the packing on an isometric cycle.

## Not formalized
The faces of an outerplanar graph, the decomposition graph and its cycle rank, the universal cover
and its group action, the core and the hairs on it, the continuous windows and the averaging over
orbits, the separation arguments behind the packing bounds, the exponential clocks, and the LOCAL
implementation. These enter only through the hypotheses of the counting theorems.
-/

open Finset

namespace Op4

namespace Outer

/-! ### Runs on a core path -/

/-- An abstract core path. The edge `e_i = p_i p_{i+1}` has the adhesion `X i`, one vertex or one
edge. The run of `v` is the finite set `run v` of indices `i` with `v ∈ X i`; it is an interval.
`d` is a distance. Outside a finite core path, `X i = ∅`. -/
structure CorePath (V : Type*) where
  /-- The adhesions. -/
  X : ℤ → Finset V
  /-- The runs. -/
  run : V → Finset ℤ
  /-- The distance. -/
  d : V → V → ℕ
  mem_run : ∀ v i, i ∈ run v ↔ v ∈ X i
  interval : ∀ v i j k, i ≤ j → j ≤ k → i ∈ run v → k ∈ run v → j ∈ run v
  card_X : ∀ i, #(X i) ≤ 2
  near : ∀ i, ∀ x ∈ X i, ∀ y ∈ X i, d x y ≤ 1
  d_self : ∀ x, d x x = 0
  d_tri : ∀ x y z, d x z ≤ d x y + d y z
  eq_of_d : ∀ x y, d x y = 0 → x = y

namespace CorePath

variable {V : Type*} (P : CorePath V)

/-- The run of `v` is maximal: no run strictly contains it. -/
def IsMax (v : V) : Prop := ∀ w, P.run v ⊆ P.run w → P.run w ⊆ P.run v

/-- `I` is a maximal run. Runs are counted as sets of indices. -/
def IsMaxRun (I : Finset ℤ) : Prop := ∃ v, P.IsMax v ∧ P.run v = I

open Classical in
/-- The maximal runs that contain `i`. -/
noncomputable def maxAt (i : ℤ) : Finset (Finset ℤ) := ((P.X i).filter P.IsMax).image P.run

open Classical in
/-- The maximal runs that meet `[a, b]`. -/
noncomputable def maxIn (a b : ℤ) : Finset (Finset ℤ) :=
  (((Icc a b).biUnion P.X).filter P.IsMax).image P.run

open Classical in
/-- The maximal runs inside `[a, b]`. -/
noncomputable def inner (a b : ℤ) : Finset (Finset ℤ) := (P.maxIn a b).filter (· ⊆ Icc a b)

open Classical in
/-- `ρ i`: the length of the shortest maximal run that contains `i`. -/
noncomputable def rho (i : ℤ) : ℕ :=
  if h : (P.maxAt i).Nonempty then (P.maxAt i).inf' h card else 0

lemma mem_maxAt {i : ℤ} {I : Finset ℤ} : I ∈ P.maxAt i ↔ P.IsMaxRun I ∧ i ∈ I := by
  classical
  unfold maxAt IsMaxRun
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := mem_image.1 h
    rw [mem_filter] at hv
    exact ⟨⟨v, hv.2, rfl⟩, (P.mem_run v i).2 hv.1⟩
  · rintro ⟨⟨v, hv, rfl⟩, hi⟩
    exact mem_image.2 ⟨v, mem_filter.2 ⟨(P.mem_run v i).1 hi, hv⟩, rfl⟩

lemma card_maxAt (i : ℤ) : #(P.maxAt i) ≤ 2 := by
  classical
  exact card_image_le.trans ((card_filter_le _ _).trans (P.card_X i))

lemma mem_maxIn {a b : ℤ} {I : Finset ℤ} :
    I ∈ P.maxIn a b ↔ P.IsMaxRun I ∧ ∃ i ∈ I, a ≤ i ∧ i ≤ b := by
  classical
  unfold maxIn IsMaxRun
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := mem_image.1 h
    rw [mem_filter, mem_biUnion] at hv
    obtain ⟨⟨i, hi, hvi⟩, hv⟩ := hv
    exact ⟨⟨v, hv, rfl⟩, i, (P.mem_run v i).2 hvi, mem_Icc.1 hi⟩
  · rintro ⟨⟨v, hv, rfl⟩, i, hi, hai, hib⟩
    exact mem_image.2 ⟨v, mem_filter.2 ⟨mem_biUnion.2 ⟨i, mem_Icc.2 ⟨hai, hib⟩,
      (P.mem_run v i).1 hi⟩, hv⟩, rfl⟩

lemma maxRun_interval {I : Finset ℤ} (hI : P.IsMaxRun I) {x y z : ℤ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hx : x ∈ I) (hz : z ∈ I) : y ∈ I := by
  obtain ⟨v, -, rfl⟩ := hI
  exact P.interval v x y z hxy hyz hx hz

lemma maxRun_eq {I J : Finset ℤ} (hI : P.IsMaxRun I) (hJ : P.IsMaxRun J) (h : I ⊆ J) : I = J := by
  obtain ⟨v, hv, rfl⟩ := hI
  obtain ⟨w, -, rfl⟩ := hJ
  exact Subset.antisymm h (hv w h)

/-- Every run lies in a maximal run. -/
lemma exists_max {v : V} {i : ℤ} (hi : i ∈ P.run v) : ∃ w, P.IsMax w ∧ P.run v ⊆ P.run w := by
  classical
  have hv : v ∈ (P.X i).filter (fun w => P.run v ⊆ P.run w) :=
    mem_filter.2 ⟨(P.mem_run v i).1 hi, Subset.refl _⟩
  obtain ⟨w, hw, hmax⟩ := exists_max_image _ (fun w => #(P.run w)) ⟨v, hv⟩
  rw [mem_filter] at hw
  refine ⟨w, fun w' hww' => ?_, hw.2⟩
  have hiw : i ∈ P.run w := (P.mem_run w i).2 hw.1
  have hw' : w' ∈ (P.X i).filter (fun w => P.run v ⊆ P.run w) :=
    mem_filter.2 ⟨(P.mem_run w' i).1 (hww' hiw), hw.2.trans hww'⟩
  have e := eq_of_subset_of_card_le hww' (hmax w' hw')
  intro x hx
  rw [e]
  exact hx

lemma maxAt_nonempty {i : ℤ} (h : (P.X i).Nonempty) : (P.maxAt i).Nonempty := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨w, hw, hvw⟩ := P.exists_max ((P.mem_run v i).2 hv)
  exact ⟨P.run w, P.mem_maxAt.2 ⟨⟨w, hw, rfl⟩, hvw ((P.mem_run v i).2 hv)⟩⟩

lemma rho_le {i : ℤ} {I : Finset ℤ} (hI : I ∈ P.maxAt i) : P.rho i ≤ #I := by
  unfold rho
  rw [dite_eq_left_of_eq_true (eq_true ⟨I, hI⟩)]
  exact inf'_le _ hI

lemma one_le_rho {i : ℤ} (h : (P.maxAt i).Nonempty) : 1 ≤ P.rho i := by
  unfold rho
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact le_inf' h _ fun I hI => card_pos.2 ⟨i, (P.mem_maxAt.1 hI).2⟩

lemma exists_rho {i : ℤ} (h : (P.maxAt i).Nonempty) : ∃ I ∈ P.maxAt i, #I = P.rho i := by
  unfold rho
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨I, hI, he⟩ := exists_mem_eq_inf' h card
  exact ⟨I, hI, he.symm⟩

/-- No index lies in three maximal runs, since an adhesion has at most two vertices. -/
lemma not_three {I J K : Finset ℤ} {x : ℤ} (hI : P.IsMaxRun I) (hJ : P.IsMaxRun J)
    (hK : P.IsMaxRun K) (hIJ : I ≠ J) (hIK : I ≠ K) (hJK : J ≠ K) (hxI : x ∈ I) (hxJ : x ∈ J)
    (hxK : x ∈ K) : False := by
  classical
  have hsub : ({I, J, K} : Finset (Finset ℤ)) ⊆ P.maxAt x := by
    intro L hL
    simp only [mem_insert, mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact P.mem_maxAt.2 ⟨hI, hxI⟩
    · exact P.mem_maxAt.2 ⟨hJ, hxJ⟩
    · exact P.mem_maxAt.2 ⟨hK, hxK⟩
  have h3 : #({I, J, K} : Finset (Finset ℤ)) = 3 := by
    rw [card_insert_of_notMem (by simp [hIJ, hIK]), card_pair hJK]
  have := (card_le_card hsub).trans (P.card_maxAt x)
  omega

omit P in
lemma ne_of_least {I J : Finset ℤ} {a b : ℤ} (ha : ∀ x ∈ I, a ≤ x) (hb : b ∈ J) (h : b < a) :
    I ≠ J := by
  rintro rfl
  exact absurd (ha b hb) (by omega)

/-- **(R1).** Let `A`, `B`, `C`, `D` be maximal runs with least elements `a₁ < b₁ < c₁ < d₁`, that
is, `A = I_c`, `D = I_{c'}` with `c' ≥ c + 3` in the order of the left ends. Then the adhesions at
an index of `A` and at an index of `D` are disjoint. (For `A` it suffices that `a₁ ∈ A`.) -/
theorem R1 {A B C D : Finset ℤ} (hA : P.IsMaxRun A) (hB : P.IsMaxRun B) (hC : P.IsMaxRun C)
    (hD : P.IsMaxRun D) {a₁ b₁ c₁ d₁ : ℤ} (ha : a₁ ∈ A) (hb : b₁ ∈ B)
    (hb' : ∀ x ∈ B, b₁ ≤ x) (hc : c₁ ∈ C) (hc' : ∀ x ∈ C, c₁ ≤ x) (hd' : ∀ x ∈ D, d₁ ≤ x)
    (hab : a₁ < b₁) (hbc : b₁ < c₁) (hcd : c₁ < d₁) {i j : ℤ} (hi : i ∈ A) (hj : j ∈ D) :
    Disjoint (P.X i) (P.X j) := by
  have hAB : A ≠ B := (ne_of_least hb' ha hab).symm
  have hAC : A ≠ C := (ne_of_least hc' ha (by omega)).symm
  have hBC : B ≠ C := (ne_of_least hc' hb hbc).symm
  have hCD : C ≠ D := (ne_of_least hd' hc hcd).symm
  -- `A` and `C` are disjoint, so `c₁ ∉ A`
  have hcA : c₁ ∉ A := by
    intro hcA
    have hBA : ¬ B ⊆ A := fun h => hAB (P.maxRun_eq hB hA h).symm
    obtain ⟨y, hyB, hyA⟩ := not_subset.1 hBA
    have hy1 := hb' y hyB
    have hy2 : c₁ < y := by
      by_contra hle
      push Not at hle
      exact hyA (P.maxRun_interval hA (by omega : a₁ ≤ y) hle ha hcA)
    have hcB : c₁ ∈ B := P.maxRun_interval hB (by omega : b₁ ≤ c₁) hy2.le hb hyB
    exact P.not_three hA hB hC hAB hAC hBC hcA hcB hc
  have hic : i < c₁ := by
    by_contra hle
    push Not at hle
    exact hcA (P.maxRun_interval hA (by omega) hle ha hi)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hri := (P.mem_run v i).2 hvi
  have hrj := (P.mem_run v j).2 hvj
  obtain ⟨w, hw, hvw⟩ := P.exists_max hri
  have hM : P.IsMaxRun (P.run w) := ⟨w, hw, rfl⟩
  have hiM := hvw hri
  have hjM := hvw hrj
  have hjd := hd' j hj
  have hMC : P.run w ≠ C := fun e => by
    rw [e] at hiM
    exact absurd (hc' i hiM) (by omega)
  have hMD : P.run w ≠ D := fun e => by
    rw [e] at hiM
    exact absurd (hd' i hiM) (by omega)
  obtain ⟨y, hyC, hyM⟩ := not_subset.1 fun h => hMC (P.maxRun_eq hC hM h).symm
  have hy1 := hc' y hyC
  have hy2 : j < y := by
    by_contra hle
    push Not at hle
    exact hyM (P.maxRun_interval hM (by omega : i ≤ y) hle hiM hjM)
  have hjC : j ∈ C := P.maxRun_interval hC (by omega : c₁ ≤ j) hy2.le hc hyC
  exact P.not_three hC hD hM hCD hMC.symm hMD.symm hjC hj hjM

/-- **(R2), upper bound.** If `k` maximal runs meet `[a, b]`, then `Σ_{i ∈ [a,b]} 1/ρ_i ≤ k`. -/
theorem R2_upper (a b : ℤ) (hne : ∀ i ∈ Icc a b, (P.X i).Nonempty) :
    ∑ i ∈ Icc a b, (1 : ℝ) / P.rho i ≤ #(P.maxIn a b) := by
  classical
  have h1 : ∀ i ∈ Icc a b, (1 : ℝ) / P.rho i ≤
      ∑ I ∈ P.maxIn a b, if i ∈ I then (1 : ℝ) / #I else 0 := by
    intro i hi
    obtain ⟨I, hI, he⟩ := P.exists_rho (P.maxAt_nonempty (hne i hi))
    have hImem : I ∈ P.maxIn a b :=
      P.mem_maxIn.2 ⟨(P.mem_maxAt.1 hI).1, i, (P.mem_maxAt.1 hI).2, mem_Icc.1 hi⟩
    have e : (1 : ℝ) / P.rho i = if i ∈ I then (1 : ℝ) / #I else 0 := by
      rw [ite_eq_left_of_eq_true _ _ (eq_true (P.mem_maxAt.1 hI).2), he]
    rw [e]
    exact single_le_sum (f := fun I => if i ∈ I then (1 : ℝ) / #I else 0)
      (fun J _ => by split_ifs <;> positivity) hImem
  calc ∑ i ∈ Icc a b, (1 : ℝ) / P.rho i
      ≤ ∑ i ∈ Icc a b, ∑ I ∈ P.maxIn a b, if i ∈ I then (1 : ℝ) / #I else 0 := sum_le_sum h1
    _ = ∑ I ∈ P.maxIn a b, ∑ i ∈ Icc a b, if i ∈ I then (1 : ℝ) / #I else 0 := sum_comm
    _ ≤ ∑ I ∈ P.maxIn a b, (1 : ℝ) := sum_le_sum fun I _ => by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have hsub : (Icc a b).filter (· ∈ I) ⊆ I := fun x hx => (mem_filter.1 hx).2
        have hc : (#((Icc a b).filter (· ∈ I)) : ℝ) ≤ #I := by exact_mod_cast card_le_card hsub
        rcases Nat.eq_zero_or_pos #I with h0 | hpos
        · rw [h0]
          simp
        · rw [mul_one_div, div_le_one (by exact_mod_cast hpos)]
          exact hc
    _ = #(P.maxIn a b) := by simp

/-- **(R2), lower bound.** If `k` maximal runs meet `[a, b]`, then
`(k - 4)/2 ≤ Σ_{i ∈ [a,b]} 1/ρ_i`. -/
theorem R2_lower (a b : ℤ) : ((#(P.maxIn a b) : ℝ) - 4) / 2 ≤ ∑ i ∈ Icc a b, (1 : ℝ) / P.rho i := by
  classical
  -- a run that sticks out contains `a` or `b`
  have h1 : (P.maxIn a b).filter (fun I => ¬ I ⊆ Icc a b) ⊆ P.maxAt a ∪ P.maxAt b := by
    intro I hI
    rw [mem_filter] at hI
    obtain ⟨hIm, i, hiI, hai, hib⟩ := P.mem_maxIn.1 hI.1
    obtain ⟨x, hxI, hx⟩ := not_subset.1 hI.2
    rw [mem_Icc] at hx
    rw [mem_union]
    by_cases hxa : x < a
    · exact Or.inl (P.mem_maxAt.2 ⟨hIm, P.maxRun_interval hIm hxa.le hai hxI hiI⟩)
    · exact Or.inr (P.mem_maxAt.2 ⟨hIm, P.maxRun_interval hIm hib (by omega) hiI hxI⟩)
  have h2 : #(P.maxIn a b) ≤ #(P.inner a b) + 4 := by
    have e := card_filter_add_card_filter_not (s := P.maxIn a b) (fun I => I ⊆ Icc a b)
    have := (card_le_card h1).trans (card_union_le _ _)
    have := P.card_maxAt a
    have := P.card_maxAt b
    unfold inner
    omega
  -- every inner run carries weight at least `1`
  have h3 : ∀ I ∈ P.inner a b, (1 : ℝ) ≤ ∑ i ∈ I, (1 : ℝ) / P.rho i := by
    intro I hI
    unfold inner at hI
    rw [mem_filter] at hI
    have hIm := (P.mem_maxIn.1 hI.1).1
    obtain ⟨i, hiI, -⟩ := (P.mem_maxIn.1 hI.1).2
    have hpos : (0 : ℝ) < #I := by exact_mod_cast card_pos.2 ⟨i, hiI⟩
    calc (1 : ℝ) = ∑ x ∈ I, (1 : ℝ) / #I := by
          rw [sum_const, nsmul_eq_mul, mul_one_div, div_self hpos.ne']
      _ ≤ ∑ x ∈ I, (1 : ℝ) / P.rho x := sum_le_sum fun x hx => by
          have hxI : I ∈ P.maxAt x := P.mem_maxAt.2 ⟨hIm, hx⟩
          have r1 : (1 : ℝ) ≤ P.rho x := by exact_mod_cast P.one_le_rho ⟨I, hxI⟩
          have r2 : (P.rho x : ℝ) ≤ #I := by exact_mod_cast P.rho_le hxI
          exact one_div_le_one_div_of_le (by linarith) r2
  -- every index lies in at most two inner runs
  have h4 : ∑ I ∈ P.inner a b, ∑ i ∈ I, (1 : ℝ) / P.rho i ≤
      2 * ∑ i ∈ Icc a b, (1 : ℝ) / P.rho i := by
    calc ∑ I ∈ P.inner a b, ∑ i ∈ I, (1 : ℝ) / P.rho i
        = ∑ I ∈ P.inner a b, ∑ i ∈ Icc a b, if i ∈ I then (1 : ℝ) / P.rho i else 0 := by
          refine sum_congr rfl fun I hI => ?_
          unfold inner at hI
          rw [sum_ite_mem, inter_eq_right.2 (mem_filter.1 hI).2]
      _ = ∑ i ∈ Icc a b, ∑ I ∈ P.inner a b, if i ∈ I then (1 : ℝ) / P.rho i else 0 := sum_comm
      _ ≤ ∑ i ∈ Icc a b, 2 * ((1 : ℝ) / P.rho i) := sum_le_sum fun i _ => by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          have hsub : (P.inner a b).filter (fun I => i ∈ I) ⊆ P.maxAt i := fun I hI => by
            rw [mem_filter] at hI
            unfold inner at hI
            exact P.mem_maxAt.2 ⟨(P.mem_maxIn.1 (mem_filter.1 hI.1).1).1, hI.2⟩
          have hc : (#((P.inner a b).filter (fun I => i ∈ I)) : ℝ) ≤ 2 := by
            exact_mod_cast (card_le_card hsub).trans (P.card_maxAt i)
          have h0 : (0 : ℝ) ≤ 1 / P.rho i := by positivity
          nlinarith
      _ = 2 * ∑ i ∈ Icc a b, (1 : ℝ) / P.rho i := by rw [mul_sum]
  have h5 : (#(P.inner a b) : ℝ) ≤ ∑ I ∈ P.inner a b, ∑ i ∈ I, (1 : ℝ) / P.rho i := by
    have := sum_le_sum h3
    rwa [sum_const, nsmul_eq_mul, mul_one] at this
  have h2' : (#(P.maxIn a b) : ℝ) ≤ #(P.inner a b) + 4 := by exact_mod_cast h2
  linarith

/-- The distance between two sets of vertices (`0` if one of them is empty). -/
noncomputable def sd (A B : Finset V) : ℕ :=
  if h : (A ×ˢ B).Nonempty then (A ×ˢ B).inf' h (fun p => P.d p.1 p.2) else 0

lemma exists_sd {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x ∈ A, ∃ y ∈ B, P.d x y = P.sd A B := by
  have h : (A ×ˢ B).Nonempty := hA.product hB
  unfold sd
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨p, hp, he⟩ := exists_mem_eq_inf' h (fun p => P.d p.1 p.2)
  rw [mem_product] at hp
  exact ⟨p.1, hp.1, p.2, hp.2, he.symm⟩

open Classical in
/-- `λ` at the node `p_i` between the edges `e_{i-1}` and `e_i`: the distance between their
adhesions if these are disjoint, and `0` otherwise. -/
noncomputable def lam (i : ℤ) : ℝ :=
  if Disjoint (P.X (i - 1)) (P.X i) then (P.sd (P.X (i - 1)) (P.X i) : ℝ) else 0

lemma lam_nonneg (i : ℤ) : 0 ≤ P.lam i := by
  unfold lam
  split_ifs <;> positivity

/-- The length `μ(e_i) = 1/ρ_i + (L(p_i) + L(p_{i+1}))/2`. In the paper `L = λ`; at the two ends of a
finite core path, `λ` is measured towards the branch nodes, so any `L ≥ λ` is allowed. -/
noncomputable def mu (L : ℤ → ℝ) (i : ℤ) : ℝ := 1 / P.rho i + (L i + L (i + 1)) / 2

/-- The chain of maximal runs from `a` to `j`: a vertex with a maximal run through `j` is within
distance `k_j - 1 + 2 Σ_{a < g ≤ j} λ_g` of `X a`, where `k_j` counts the maximal runs that meet
`[a, j]`. -/
lemma chain (a b : ℤ) (hne : ∀ i ∈ Icc a b, (P.X i).Nonempty) (n : ℕ) :
    a + n ≤ b → ∀ v, P.IsMax v → a + n ∈ P.run v →
      ∃ u ∈ P.X a, (P.d u v : ℝ) ≤
        (#(P.maxIn a (a + n)) : ℝ) - 1 + 2 * ∑ g ∈ Ioc a (a + n), P.lam g := by
  induction n with
  | zero =>
    intro _ v hv ha
    simp only [Nat.cast_zero, add_zero] at ha ⊢
    refine ⟨v, (P.mem_run v a).1 ha, ?_⟩
    have h1 : P.run v ∈ P.maxIn a a := P.mem_maxIn.2 ⟨⟨v, hv, rfl⟩, a, ha, le_rfl, le_rfl⟩
    have h2 : (1 : ℝ) ≤ #(P.maxIn a a) := by exact_mod_cast card_pos.2 ⟨_, h1⟩
    rw [P.d_self, Ioc_self, sum_empty]
    push_cast
    linarith
  | succ n ih =>
    intro hjb v hv hj1
    set j := a + (n : ℤ) with hj
    have hj1' : a + ((n + 1 : ℕ) : ℤ) = j + 1 := by push_cast; ring
    rw [hj1'] at hjb hj1 ⊢
    have hjb' : j ≤ b := by omega
    have haj : a ≤ j := by omega
    have hsub : P.maxIn a j ⊆ P.maxIn a (j + 1) := fun I hI => by
      obtain ⟨hI, i, hiI, h1, h2⟩ := P.mem_maxIn.1 hI
      exact P.mem_maxIn.2 ⟨hI, i, hiI, h1, by omega⟩
    have hIoc : Ioc a (j + 1) = insert (j + 1) (Ioc a j) := by
      ext x
      simp only [mem_Ioc, mem_insert]
      omega
    have hsum : ∑ g ∈ Ioc a (j + 1), P.lam g = ∑ g ∈ Ioc a j, P.lam g + P.lam (j + 1) := by
      rw [hIoc, sum_insert (by simp only [mem_Ioc]; omega), add_comm]
    have hlam := P.lam_nonneg (j + 1)
    have hcard : (#(P.maxIn a j) : ℝ) ≤ #(P.maxIn a (j + 1)) := by
      exact_mod_cast card_le_card hsub
    have hS0 : 0 ≤ ∑ g ∈ Ioc a j, P.lam g := sum_nonneg fun g _ => P.lam_nonneg g
    by_cases hjv : j ∈ P.run v
    · obtain ⟨u, hu, hd⟩ := ih hjb' v hv hjv
      exact ⟨u, hu, by rw [hsum]; linarith⟩
    -- the run of `v` starts at `j + 1`, so it is a new maximal run
    have hnew : P.run v ∉ P.maxIn a j := fun h => by
      obtain ⟨-, i, hi, h1, h2⟩ := P.mem_maxIn.1 h
      exact hjv (P.interval v i j (j + 1) h2 (by omega) hi hj1)
    have hcard' : (#(P.maxIn a j) : ℝ) + 1 ≤ #(P.maxIn a (j + 1)) := by
      have hins : insert (P.run v) (P.maxIn a j) ⊆ P.maxIn a (j + 1) :=
        insert_subset (P.mem_maxIn.2 ⟨⟨v, hv, rfl⟩, j + 1, hj1, by omega, le_rfl⟩) hsub
      have := card_le_card hins
      rw [card_insert_of_notMem hnew] at this
      exact_mod_cast this
    have hv1 : v ∈ P.X (j + 1) := (P.mem_run v _).1 hj1
    by_cases hdis : Disjoint (P.X j) (P.X (j + 1))
    · -- a gap: go through the closest pair, at distance `λ_{j+1} ≥ 1`
      obtain ⟨z, hz⟩ := hne j (mem_Icc.2 ⟨haj, hjb'⟩)
      obtain ⟨w, hw, hzw⟩ := P.exists_max ((P.mem_run z j).2 hz)
      have hjw := hzw ((P.mem_run z j).2 hz)
      obtain ⟨u, hu, hd⟩ := ih hjb' w hw hjw
      have hwX : w ∈ P.X j := (P.mem_run w j).1 hjw
      obtain ⟨x, hx, y, hy, hxy⟩ := P.exists_sd ⟨w, hwX⟩ ⟨v, hv1⟩
      have hlj : P.lam (j + 1) = P.sd (P.X j) (P.X (j + 1)) := by
        unfold lam
        rw [add_sub_cancel_right, ite_eq_left_of_eq_true _ _ (eq_true hdis)]
      have hne' : x ≠ y := fun e => (disjoint_left.1 hdis hx) (e ▸ hy)
      have hpos : 1 ≤ P.d x y := Nat.one_le_iff_ne_zero.2 fun h0 => hne' (P.eq_of_d x y h0)
      have h1 := P.near j w hwX x hx
      have h2 := P.near (j + 1) y hy v hv1
      have t1 := P.d_tri u w v
      have t2 := P.d_tri w x v
      have t3 := P.d_tri x y v
      have hnat : P.d u v ≤ P.d u w + 2 * P.d x y + 1 := by omega
      have hreal : (P.d u v : ℝ) ≤ P.d u w + 2 * (P.d x y : ℝ) + 1 := by exact_mod_cast hnat
      rw [hxy, ← hlj] at hreal
      exact ⟨u, hu, by rw [hsum]; linarith⟩
    · -- a common vertex of `X j` and `X (j+1)`
      rw [not_disjoint_iff] at hdis
      obtain ⟨x, hxj, hxj1⟩ := hdis
      obtain ⟨w, hw, hxw⟩ := P.exists_max ((P.mem_run x j).2 hxj)
      have hjw := hxw ((P.mem_run x j).2 hxj)
      have hj1w := hxw ((P.mem_run x (j + 1)).2 hxj1)
      obtain ⟨u, hu, hd⟩ := ih hjb' w hw hjw
      have h1 := P.near (j + 1) w ((P.mem_run w _).1 hj1w) v hv1
      have t := P.d_tri u w v
      have hnat : P.d u v ≤ P.d u w + 1 := by omega
      have hreal : (P.d u v : ℝ) ≤ P.d u w + 1 := by exact_mod_cast hnat
      exact ⟨u, hu, by rw [hsum]; linarith⟩

omit P in
lemma tele (L : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ g ∈ Ioc a (a + n), L g + L a / 2 + L (a + n + 1) / 2 =
      ∑ i ∈ Icc a (a + n), (L i + L (i + 1)) / 2 := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, Ioc_self, Icc_self, sum_empty, sum_singleton]; ring
  | succ n ih =>
    have e0 : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
    have e1 : Ioc a (a + n + 1) = insert (a + n + 1) (Ioc a (a + n)) := by
      ext x
      simp only [mem_Ioc, mem_insert]
      omega
    have e2 : Icc a (a + n + 1) = insert (a + n + 1) (Icc a (a + n)) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [e0, e1, e2, sum_insert (by simp only [mem_Ioc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ← ih]
    ring

/-- **(R3).** For `a ≤ b`, `d(X_a, X_b) ≤ 2 Σ_{i ∈ [a,b]} μ(e_i) + 3`. -/
theorem R3 {a b : ℤ} (hab : a ≤ b) (hne : ∀ i ∈ Icc a b, (P.X i).Nonempty) {L : ℤ → ℝ}
    (hL : ∀ i, P.lam i ≤ L i) :
    ∃ x ∈ P.X a, ∃ y ∈ P.X b, (P.d x y : ℝ) ≤ 2 * ∑ i ∈ Icc a b, P.mu L i + 3 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst hn
  obtain ⟨z, hz⟩ := hne (a + n) (mem_Icc.2 ⟨hab, le_rfl⟩)
  obtain ⟨w, hw, hzw⟩ := P.exists_max ((P.mem_run z _).2 hz)
  have hbw := hzw ((P.mem_run z _).2 hz)
  obtain ⟨u, hu, hd⟩ := P.chain a (a + n) hne n le_rfl w hw hbw
  refine ⟨u, hu, w, (P.mem_run w _).1 hbw, ?_⟩
  have h2 := P.R2_lower a (a + n)
  have h3 := tele L a n
  have hLa : 0 ≤ L a := (P.lam_nonneg a).trans (hL a)
  have hLb : 0 ≤ L (a + n + 1) := (P.lam_nonneg _).trans (hL _)
  have h4 : ∑ g ∈ Ioc a (a + n), P.lam g ≤ ∑ g ∈ Ioc a (a + n), L g := sum_le_sum fun g _ => hL g
  have e : ∑ i ∈ Icc a (a + n), P.mu L i = ∑ i ∈ Icc a (a + n), (1 : ℝ) / P.rho i +
      ∑ i ∈ Icc a (a + n), (L i + L (i + 1)) / 2 := by
    unfold mu
    rw [sum_add_distrib]
  rw [e]
  linarith

lemma mu_nonneg {L : ℤ → ℝ} (hL : ∀ i, P.lam i ≤ L i) (i : ℤ) : 0 ≤ P.mu L i := by
  unfold mu
  have := (P.lam_nonneg i).trans (hL i)
  have := (P.lam_nonneg (i + 1)).trans (hL (i + 1))
  have : 0 ≤ (1 : ℝ) / P.rho i := by positivity
  linarith

/-- **Radius of a path window.** If the edges `e_a, …, e_b` of a window have total length at most
`R`, every adhesion `X_i` with `a ≤ i ≤ b` lies within distance `2R + 3` of `X_a`. -/
theorem window_radius {a b : ℤ} (hne : ∀ i ∈ Icc a b, (P.X i).Nonempty) {L : ℤ → ℝ}
    (hL : ∀ i, P.lam i ≤ L i) {R : ℝ} (hR : ∑ i ∈ Icc a b, P.mu L i ≤ R) {i : ℤ}
    (hi : i ∈ Icc a b) : ∃ x ∈ P.X a, ∃ y ∈ P.X i, (P.d x y : ℝ) ≤ 2 * R + 3 := by
  rw [mem_Icc] at hi
  obtain ⟨x, hx, y, hy, h⟩ :=
    P.R3 hi.1 (fun j hj => hne j (by rw [mem_Icc] at hj ⊢; omega)) hL
  have hsub : Icc a i ⊆ Icc a b := Icc_subset_Icc le_rfl hi.2
  have := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => P.mu_nonneg hL j
  exact ⟨x, hx, y, hy, by linarith⟩

end CorePath

open MeasureTheory in
/-- **Window weights.** The node at position `x` lies in the path windows `[τ, τ + R]` for a set
of shifts `τ` of measure `R`, so with weight `dτ/R` its total weight is `1`. -/
theorem window_weight {R : ℝ} (hR : 0 < R) (x : ℝ) :
    (volume {τ : ℝ | τ ≤ x ∧ x ≤ τ + R}).toReal / R = 1 := by
  have e : {τ : ℝ | τ ≤ x ∧ x ≤ τ + R} = Set.Icc (x - R) x := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [e, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), sub_sub_cancel, div_self hR.ne']

/-- A core path in a connected graph, with the graph distance. -/
noncomputable def ofGraph {V : Type*} (G : SimpleGraph V) (hG : G.Connected) (X : ℤ → Finset V)
    (run : V → Finset ℤ) (mem_run : ∀ v i, i ∈ run v ↔ v ∈ X i)
    (interval : ∀ v i j k, i ≤ j → j ≤ k → i ∈ run v → k ∈ run v → j ∈ run v)
    (card_X : ∀ i, #(X i) ≤ 2) (adj : ∀ i, ∀ x ∈ X i, ∀ y ∈ X i, x = y ∨ G.Adj x y) :
    CorePath V where
  X := X
  run := run
  d := G.dist
  mem_run := mem_run
  interval := interval
  card_X := card_X
  near i x hx y hy := by
    rcases adj i x hx y hy with rfl | h
    · simp
    · exact (SimpleGraph.dist_eq_one_iff_adj.2 h).le
  d_self _ := SimpleGraph.dist_self
  d_tri _ _ _ := hG.dist_triangle
  eq_of_d x y h := ((hG.preconnected x y).dist_eq_zero_iff).1 h

/-! ### The counting of the proof

The hypotheses are the per-step bounds of the proof, summed over the core paths up to the group
`Π`; the theorems check the arithmetic that leads to the constants. -/

/-- **Number of core paths.** A finite core path ends at two core edges at branch nodes, and an
infinite one projects onto a cycle component of `K_D`. With `B ≤ 6h + 4N₁` core edges at branch
nodes and at most `h` cycle components, there are at most `4h + 2N₁` core paths up to `Π`. -/
theorem core_paths_le {h N₁ B nCyc nP : ℝ} (hP : 2 * nP ≤ B + 2 * nCyc)
    (hB : B ≤ 6 * h + 4 * N₁) (hcyc : nCyc ≤ h) : nP ≤ 4 * h + 2 * N₁ := by
  linarith

/-- **Total length of the core paths.** With `nP ≤ 4h + 2N₁` core paths, `K = Σ_P k_P` maximal runs
with `(K - 28·nP)/12 ≤ γ_f` (packing), `Sρ = Σ 1/ρ ≤ K`, `Λ = Σ_p λ(p) ≤ 3γ_f + 5Z` over the
`Z ≤ K + 2nP` nodes with `λ(p) > 0`, and `Sμ ≤ Sρ + Λ`: `Sμ ≤ 75γ_f + 178(4h + 2N₁)`. -/
theorem sum_mu_le {γf h N₁ nP K Srho Λ Z Smu : ℝ} (hP : nP ≤ 4 * h + 2 * N₁)
    (hK : (K - 28 * nP) / 12 ≤ γf) (hrho : Srho ≤ K) (hΛ : Λ ≤ 3 * γf + 5 * Z)
    (hZ : Z ≤ K + 2 * nP) (hmu : Smu ≤ Srho + Λ) :
    Smu ≤ 75 * γf + 178 * (4 * h + 2 * N₁) := by
  linarith

/-- **Total weight of the windows at cut edges.** A core-path edge costs at most `2μ(e)/R`, and
each of the `B ≤ 6h + 4N₁` core edges at branch nodes at most `2`. -/
theorem cut_weight_le {γf h N₁ Smu B Sc R : ℝ} (hR : 0 < R)
    (hmu : Smu ≤ 75 * γf + 178 * (4 * h + 2 * N₁)) (hB : B ≤ 6 * h + 4 * N₁)
    (hc : Sc ≤ 2 * Smu / R + 2 * B) :
    Sc ≤ 150 * γf / R + (1424 / R + 12) * h + (712 / R + 8) * N₁ := by
  have h1 : 2 * Smu / R ≤ 2 * (75 * γf + 178 * (4 * h + 2 * N₁)) / R :=
    div_le_div_of_nonneg_right (by linarith) hR.le
  have hRne := hR.ne'
  have e : 150 * γf / R + (1424 / R + 12) * h + (712 / R + 8) * N₁ =
      2 * (75 * γf + 178 * (4 * h + 2 * N₁)) / R + 2 * (6 * h + 4 * N₁) := by
    field_simp
    ring
  rw [e]
  linarith

/-- **Deterministic version.** With `ℓ = R + 13`, `h ≤ 3γ_f/(ℓ - 13)`, `N₁ ≤ 3γ_f/(R - 2)` and
`R ≥ 1500`, the cut weight is at most `215γ_f/R`. -/
theorem det_cut_le {γf h N₁ Sc R ℓ : ℝ} (hR : 1500 ≤ R) (hℓ : ℓ = R + 13) (hγ : 0 ≤ γf)
    (hh : h ≤ 3 * γf / (ℓ - 13)) (hN : N₁ ≤ 3 * γf / (R - 2))
    (hc : Sc ≤ 150 * γf / R + (1424 / R + 12) * h + (712 / R + 8) * N₁) :
    Sc ≤ 215 * γf / R := by
  subst hℓ
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < R - 2 := by linarith
  have hRne := hR0.ne'
  have hR2ne := hR2.ne'
  rw [show R + 13 - 13 = R by ring] at hh
  have e1 : (1424 / R + 12) * h ≤ (1424 / R + 12) * (3 * γf / R) :=
    mul_le_mul_of_nonneg_left hh (add_pos (div_pos (by norm_num) hR0) (by norm_num)).le
  have e2 : (712 / R + 8) * N₁ ≤ (712 / R + 8) * (3 * γf / (R - 2)) :=
    mul_le_mul_of_nonneg_left hN (add_pos (div_pos (by norm_num) hR0) (by norm_num)).le
  have e3 : 215 * γf / R - (150 * γf / R + (1424 / R + 12) * (3 * γf / R) +
      (712 / R + 8) * (3 * γf / (R - 2))) =
      γf * (5 * R ^ 2 - 6466 * R + 8544) / (R ^ 2 * (R - 2)) := by
    field_simp
    ring
  have e4 : 0 ≤ γf * (5 * R ^ 2 - 6466 * R + 8544) / (R ^ 2 * (R - 2)) :=
    div_nonneg (mul_nonneg hγ (by nlinarith)) (mul_nonneg (sq_nonneg R) hR2.le)
  linarith

/-- **Deterministic excess.** If `Σ_v x_v ≤ γ_f + 2·Sc` and `Sc ≤ 215γ_f/R`, then
`Σ_v x_v ≤ γ_f + 430γ_f/R`, and `R ≥ 1500/ε` gives ratio `1 + ε`. -/
theorem det_excess {γf Sx Sc R ε : ℝ} (hε : 0 < ε) (hR : 1500 / ε ≤ R) (hγ : 0 ≤ γf)
    (hx : Sx ≤ γf + 2 * Sc) (hc : Sc ≤ 215 * γf / R) :
    Sx ≤ γf + 430 * γf / R ∧ Sx ≤ (1 + ε) * γf := by
  have hR0 : 0 < R := lt_of_lt_of_le (div_pos (by norm_num) hε) hR
  have h1 : 2 * (215 * γf / R) = 430 * γf / R := by ring
  have hRε : 1500 ≤ R * ε := (div_le_iff₀ hε).1 hR
  have h2 : 430 * γf / R ≤ ε * γf := by
    rw [div_le_iff₀ hR0]
    nlinarith
  constructor <;> nlinarith

/-- **Randomized version.** With `ℓ = 6R + 5`, the expected number of cut edges of `D` is at most
`2Sμ/R` (anchor cuts) plus `Sμ/R` (long edges) plus `B` (edges at branch nodes). For `R ≥ 2200`
this is at most `242γ_f/R`. -/
theorem rand_cut_le {γf h N₁ Smu B Ecut R ℓ : ℝ} (hR : 2200 ≤ R) (hℓ : ℓ = 6 * R + 5)
    (hγ : 0 ≤ γf) (hh : h ≤ 3 * γf / (ℓ - 13)) (hN : N₁ ≤ 3 * γf / (R - 2))
    (hmu : Smu ≤ 75 * γf + 178 * (4 * h + 2 * N₁)) (hB : B ≤ 6 * h + 4 * N₁)
    (hcut : Ecut ≤ 2 * Smu / R + Smu / R + B) :
    Ecut ≤ 242 * γf / R := by
  subst hℓ
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < R - 2 := by linarith
  have hR6 : 0 < 6 * R - 8 := by linarith
  have hRne := hR0.ne'
  have hR2ne := hR2.ne'
  have hR6ne := hR6.ne'
  rw [show 6 * R + 5 - 13 = 6 * R - 8 by ring] at hh
  have h1 : 2 * Smu / R + Smu / R ≤ 3 * (75 * γf + 178 * (4 * h + 2 * N₁)) / R := by
    rw [← add_div, show 2 * Smu + Smu = 3 * Smu by ring]
    exact div_le_div_of_nonneg_right (by linarith) hR0.le
  have e0 : 3 * (75 * γf + 178 * (4 * h + 2 * N₁)) / R + (6 * h + 4 * N₁) =
      225 * γf / R + (2136 / R + 6) * h + (1068 / R + 4) * N₁ := by
    field_simp
    ring
  have e1 : (2136 / R + 6) * h ≤ (2136 / R + 6) * (3 * γf / (6 * R - 8)) :=
    mul_le_mul_of_nonneg_left hh (add_pos (div_pos (by norm_num) hR0) (by norm_num)).le
  have e2 : (1068 / R + 4) * N₁ ≤ (1068 / R + 4) * (3 * γf / (R - 2)) :=
    mul_le_mul_of_nonneg_left hN (add_pos (div_pos (by norm_num) hR0) (by norm_num)).le
  have e3 : 242 * γf / R - (225 * γf / R + (2136 / R + 6) * (3 * γf / (6 * R - 8)) +
      (1068 / R + 4) * (3 * γf / (R - 2))) =
      γf * (12 * R ^ 2 - 25840 * R + 38720) / (R * (6 * R - 8) * (R - 2)) := by
    generalize hq : 6 * R - 8 = q at hR6ne ⊢
    field_simp
    rw [← hq]
    ring
  have e4 : 0 ≤ γf * (12 * R ^ 2 - 25840 * R + 38720) / (R * (6 * R - 8) * (R - 2)) :=
    div_nonneg (mul_nonneg hγ (by nlinarith)) (by positivity)
  linarith

/-- **Randomized size.** Each cut edge of `D` costs at most `4` (two clusters, an adhesion of at
most two vertices), so the expected size is at most `γ + 968γ/R`, and `R ≥ 2200/ε` gives
`(1 + ε)γ`. -/
theorem rand_size {γf γ Ecut Esize R ε : ℝ} (hε : 0 < ε) (hR : 2200 / ε ≤ R) (hγf : 0 ≤ γf)
    (hγ : γf ≤ γ) (hsize : Esize ≤ γ + 4 * Ecut) (hcut : Ecut ≤ 242 * γf / R) :
    Esize ≤ γ + 968 * γ / R ∧ Esize ≤ (1 + ε) * γ := by
  have hR0 : 0 < R := lt_of_lt_of_le (div_pos (by norm_num) hε) hR
  have h1 : 4 * (242 * γf / R) ≤ 968 * γ / R := by
    rw [show 4 * (242 * γf / R) = 968 * γf / R by ring]
    exact div_le_div_of_nonneg_right (by linarith) hR0.le
  have hRε : 2200 ≤ R * ε := (div_le_iff₀ hε).1 hR
  have h2 : 968 * γ / R ≤ ε * γ := by
    rw [div_le_iff₀ hR0]
    nlinarith
  constructor <;> nlinarith

/-! ### Branch nodes -/

section Branch

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Isolated vertices lie in distinct components. -/
lemma card_isolated_le :
    #(univ.filter fun v => G.degree v = 0) ≤ Fintype.card G.ConnectedComponent := by
  rw [← card_univ (α := G.ConnectedComponent)]
  refine card_le_card_of_injOn G.connectedComponentMk (fun v _ => mem_coe.2 (mem_univ _)) ?_
  intro u hu v _ huv
  rw [mem_coe, mem_filter] at hu
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact huv
  cases p with
  | nil => rfl
  | cons h _ =>
    have hn : G.neighborFinset u = ∅ :=
      card_eq_zero.1 (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hu.2)
    have := (G.mem_neighborFinset u _).2 h
    rw [hn] at this
    simp at this

/-- **The branch count.** `Σ_{deg v ≥ 3} (deg v - 2) ≤ 2·rk + #{deg v = 1}`, where
`rk = |E| - |V| + c` is the cycle rank. -/
theorem branch_count :
    ∑ v ∈ univ.filter (fun v => 3 ≤ G.degree v), ((G.degree v : ℤ) - 2) ≤
      2 * ((#G.edgeFinset : ℤ) - Fintype.card V + Fintype.card G.ConnectedComponent) +
        #(univ.filter fun v => G.degree v = 1) := by
  have hdeg : ∑ v, (G.degree v : ℤ) = 2 * #G.edgeFinset := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hiso := card_isolated_le G
  have hpt : ∀ v, (if 3 ≤ G.degree v then (G.degree v : ℤ) - 2 else 0) ≤
      ((G.degree v : ℤ) - 2) + 2 * (if G.degree v = 0 then 1 else 0) +
        (if G.degree v = 1 then 1 else 0) := by
    intro v
    split_ifs <;> omega
  calc ∑ v ∈ univ.filter (fun v => 3 ≤ G.degree v), ((G.degree v : ℤ) - 2)
      = ∑ v, (if 3 ≤ G.degree v then (G.degree v : ℤ) - 2 else 0) := sum_filter _ _
    _ ≤ ∑ v, (((G.degree v : ℤ) - 2) + 2 * (if G.degree v = 0 then 1 else 0) +
          (if G.degree v = 1 then 1 else 0)) := sum_le_sum fun v _ => hpt v
    _ = 2 * #G.edgeFinset - 2 * Fintype.card V + 2 * #(univ.filter fun v => G.degree v = 0) +
          #(univ.filter fun v => G.degree v = 1) := by
        rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib, hdeg, ← mul_sum, sum_boole,
          sum_boole, sum_const, card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := by omega

/-- **Neighbours of the branch nodes.** The nodes of degree other than `2` have at most
`6·rk + 4·#{deg v = 1}` neighbours in total. -/
theorem branch_neighbours :
    ∑ v ∈ univ.filter (fun v => G.degree v ≠ 2), (G.degree v : ℤ) ≤
      6 * ((#G.edgeFinset : ℤ) - Fintype.card V + Fintype.card G.ConnectedComponent) +
        4 * #(univ.filter fun v => G.degree v = 1) := by
  have h := branch_count G
  have hpt : ∀ v, (if G.degree v ≠ 2 then (G.degree v : ℤ) else 0) ≤
      3 * (if 3 ≤ G.degree v then (G.degree v : ℤ) - 2 else 0) +
        (if G.degree v = 1 then 1 else 0) := by
    intro v
    split_ifs <;> omega
  calc ∑ v ∈ univ.filter (fun v => G.degree v ≠ 2), (G.degree v : ℤ)
      = ∑ v, (if G.degree v ≠ 2 then (G.degree v : ℤ) else 0) := sum_filter _ _
    _ ≤ ∑ v, (3 * (if 3 ≤ G.degree v then (G.degree v : ℤ) - 2 else 0) +
          (if G.degree v = 1 then 1 else 0)) := sum_le_sum fun v _ => hpt v
    _ = 3 * ∑ v ∈ univ.filter (fun v => 3 ≤ G.degree v), ((G.degree v : ℤ) - 2) +
          #(univ.filter fun v => G.degree v = 1) := by
        rw [sum_add_distrib, ← mul_sum, sum_filter, sum_boole]
    _ ≤ _ := by linarith

end Branch

/-! ### Anchors on a segment

A segment of a core path has nodes `0, …, M` at positions `ψ 0 < ψ 1 < … < ψ M`, and the edge
`j < M` joins the nodes `j` and `j + 1`, with length `ψ (j+1) - ψ j ≤ R`. -/

section Segment

variable (ψ : ℕ → ℝ) (R : ℝ) (M : ℕ)

/-- `B(t)`: the edges of the segment whose two ends lie within `ψ`-distance `R` of the node `t`
(`mem_ball_iff`). -/
noncomputable def ball (t : ℕ) : Finset ℕ :=
  (range M).filter fun j => ψ (j + 1) - R ≤ ψ t ∧ ψ t ≤ ψ j + R

/-- The total length of a set of edges. -/
noncomputable def len (S : Finset ℕ) : ℝ := ∑ j ∈ S, (ψ (j + 1) - ψ j)

variable {ψ R M}

lemma mem_ball_iff (hψ : Monotone ψ) {t j : ℕ} :
    j ∈ ball ψ R M t ↔ j < M ∧ |ψ j - ψ t| ≤ R ∧ |ψ (j + 1) - ψ t| ≤ R := by
  have := hψ (Nat.le_succ j)
  simp only [ball, mem_filter, mem_range, abs_le]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩⟩
    exact ⟨h1, by linarith, by linarith⟩

omit M in
lemma len_Ico (j n : ℕ) : len ψ (Ico j (j + n)) = ψ (j + n) - ψ j := by
  induction n with
  | zero => simp [len]
  | succ n ih =>
    unfold len at ih ⊢
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    ring

omit M in
lemma len_nonneg (hψ : StrictMono ψ) (S : Finset ℕ) : 0 ≤ len ψ S :=
  sum_nonneg fun k _ => by have := hψ (Nat.lt_succ_self k); linarith

omit M in
lemma len_mono (hψ : StrictMono ψ) {S T : Finset ℕ} (h : S ⊆ T) : len ψ S ≤ len ψ T :=
  sum_le_sum_of_subset_of_nonneg h fun k _ _ => by have := hψ (Nat.lt_succ_self k); linarith

/-- If `B(t) ⊄ B(t+1)`, then `μ(B(t)) > R`. -/
theorem big_left (hψ : StrictMono ψ) (hlen : ∀ j < M, ψ (j + 1) - ψ j ≤ R) {t : ℕ} (ht : t < M)
    (h : ¬ ball ψ R M t ⊆ ball ψ R M (t + 1)) : R < len ψ (ball ψ R M t) := by
  obtain ⟨j, hj, hj'⟩ := not_subset.1 h
  simp only [ball, mem_filter, mem_range] at hj hj'
  obtain ⟨hjM, hj1, hj2⟩ := hj
  have hlt : ψ t < ψ (t + 1) := hψ (Nat.lt_succ_self t)
  have hRt := hlen t ht
  have hgap : ψ j + R < ψ (t + 1) := by
    by_contra hc
    push Not at hc
    exact hj' ⟨hjM, by linarith, hc⟩
  have hjt : j ≤ t := by
    by_contra hc
    push Not at hc
    have : ψ (t + 1) ≤ ψ j := hψ.monotone (by omega)
    linarith
  have hsub : Ico j (t + 1) ⊆ ball ψ R M t := by
    intro k hk
    rw [mem_Ico] at hk
    simp only [ball, mem_filter, mem_range]
    have h1 : ψ (k + 1) ≤ ψ (t + 1) := hψ.monotone (by omega)
    have h2 : ψ j ≤ ψ k := hψ.monotone (by omega)
    exact ⟨by omega, by linarith, by linarith⟩
  have e := len_Ico (ψ := ψ) j (t + 1 - j)
  rw [show j + (t + 1 - j) = t + 1 by omega] at e
  have := len_mono hψ hsub
  linarith

/-- If `B(t+1) ⊄ B(t)`, then `μ(B(t+1)) > R`. -/
theorem big_right (hψ : StrictMono ψ) (hlen : ∀ j < M, ψ (j + 1) - ψ j ≤ R) {t : ℕ} (ht : t < M)
    (h : ¬ ball ψ R M (t + 1) ⊆ ball ψ R M t) : R < len ψ (ball ψ R M (t + 1)) := by
  obtain ⟨j, hj, hj'⟩ := not_subset.1 h
  simp only [ball, mem_filter, mem_range] at hj hj'
  obtain ⟨hjM, hj1, hj2⟩ := hj
  have hlt : ψ t < ψ (t + 1) := hψ (Nat.lt_succ_self t)
  have hRt := hlen t ht
  have hgap : ψ t < ψ (j + 1) - R := by
    by_contra hc
    push Not at hc
    exact hj' ⟨hjM, hc, by linarith⟩
  have htj : t ≤ j := by
    by_contra hc
    push Not at hc
    have : ψ (j + 1) ≤ ψ t := hψ.monotone (by omega)
    linarith
  have hsub : Ico t (j + 1) ⊆ ball ψ R M (t + 1) := by
    intro k hk
    rw [mem_Ico] at hk
    simp only [ball, mem_filter, mem_range]
    have h1 : ψ (k + 1) ≤ ψ (j + 1) := hψ.monotone (by omega)
    have h2 : ψ t ≤ ψ k := hψ.monotone (by omega)
    exact ⟨by omega, by linarith, by linarith⟩
  have e := len_Ico (ψ := ψ) t (j + 1 - t)
  rw [show t + (j + 1 - t) = j + 1 by omega] at e
  have := len_mono hψ hsub
  linarith

/-- Every edge `j` lies in `B(t) △ B(t+1)` for at most two edges `t` of the segment. -/
theorem card_symmDiff_le (hψ : StrictMono ψ) (j : ℕ) :
    #((range M).filter fun t => j ∈ symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) ≤ 2 := by
  have one1 : ∀ c : ℝ, #((range M).filter fun t => ψ t ≤ c ∧ c < ψ (t + 1)) ≤ 1 := by
    intro c
    refine card_le_one.2 fun t ht t' ht' => ?_
    simp only [mem_filter] at ht ht'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hψ.monotone (show t + 1 ≤ t' by omega)
      linarith [ht.2.2, ht'.2.1]
    · have := hψ.monotone (show t' + 1 ≤ t by omega)
      linarith [ht'.2.2, ht.2.1]
  have one2 : ∀ c : ℝ, #((range M).filter fun t => ψ t < c ∧ c ≤ ψ (t + 1)) ≤ 1 := by
    intro c
    refine card_le_one.2 fun t ht t' ht' => ?_
    simp only [mem_filter] at ht ht'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hψ.monotone (show t + 1 ≤ t' by omega)
      linarith [ht.2.2, ht'.2.1]
    · have := hψ.monotone (show t' + 1 ≤ t by omega)
      linarith [ht'.2.2, ht.2.1]
  have hsub : ((range M).filter fun t => j ∈ symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) ⊆
      ((range M).filter fun t => ψ t ≤ ψ j + R ∧ ψ j + R < ψ (t + 1)) ∪
        ((range M).filter fun t => ψ t < ψ (j + 1) - R ∧ ψ (j + 1) - R ≤ ψ (t + 1)) := by
    intro t ht
    rw [mem_filter, mem_symmDiff] at ht
    obtain ⟨htM, ht⟩ := ht
    have hlt : ψ t < ψ (t + 1) := hψ (Nat.lt_succ_self t)
    rw [mem_union, mem_filter, mem_filter]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [ball, mem_filter, mem_range] at h1 h2
      refine Or.inl ⟨htM, h1.2.2, ?_⟩
      by_contra hc
      push Not at hc
      exact h2 ⟨h1.1, by linarith [h1.2.1], hc⟩
    · simp only [ball, mem_filter, mem_range] at h1 h2
      refine Or.inr ⟨htM, ?_, h1.2.1⟩
      by_contra hc
      push Not at hc
      exact h2 ⟨h1.1, hc, by linarith [h1.2.2]⟩
  have := (card_le_card hsub).trans (card_union_le _ _)
  have := one1 (ψ j + R)
  have := one2 (ψ (j + 1) - R)
  omega

/-- `Σ_t μ(B(t) △ B(t+1)) ≤ 2 Σ_f μ(f)`. -/
theorem sum_symmDiff_le (hψ : StrictMono ψ) :
    ∑ t ∈ range M, len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) ≤
      2 * len ψ (range M) := by
  have hsub : ∀ t, symmDiff (ball ψ R M t) (ball ψ R M (t + 1)) ⊆ range M := fun t j hj => by
    rcases mem_symmDiff.1 hj with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (mem_filter.1 h).1
  calc ∑ t ∈ range M, len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1)))
      = ∑ t ∈ range M, ∑ j ∈ range M,
          if j ∈ symmDiff (ball ψ R M t) (ball ψ R M (t + 1)) then ψ (j + 1) - ψ j else 0 := by
        refine sum_congr rfl fun t _ => ?_
        unfold len
        rw [sum_ite_mem, inter_eq_right.2 (hsub t)]
    _ = ∑ j ∈ range M, ∑ t ∈ range M,
          if j ∈ symmDiff (ball ψ R M t) (ball ψ R M (t + 1)) then ψ (j + 1) - ψ j else 0 :=
        sum_comm
    _ ≤ ∑ j ∈ range M, 2 * (ψ (j + 1) - ψ j) := sum_le_sum fun j _ => by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have hc := (Nat.cast_le (α := ℝ)).2 (card_symmDiff_le (R := R) (M := M) hψ j)
        push_cast at hc
        have h0 : 0 ≤ ψ (j + 1) - ψ j := by have := hψ (Nat.lt_succ_self j); linarith
        nlinarith
    _ = 2 * len ψ (range M) := by unfold len; rw [mul_sum]

/-- The anchors of the ends of the edge `t` differ with probability
`μ(B(t) △ B(t+1)) / μ(B(t) ∪ B(t+1))` (the exponential race, not formalized), which is at most
`μ(B(t) △ B(t+1)) / R`. -/
theorem cut_ratio_le (hψ : StrictMono ψ) (hR : 0 < R) (hlen : ∀ j < M, ψ (j + 1) - ψ j ≤ R)
    {t : ℕ} (ht : t < M) :
    len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) /
        len ψ (ball ψ R M t ∪ ball ψ R M (t + 1)) ≤
      len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) / R := by
  have hnn := len_nonneg hψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1)))
  by_cases h1 : ball ψ R M t ⊆ ball ψ R M (t + 1)
  · by_cases h2 : ball ψ R M (t + 1) ⊆ ball ψ R M t
    · rw [Subset.antisymm h1 h2, symmDiff_self]
      simp [len]
    · have hb := big_right hψ hlen ht h2
      have hu := len_mono hψ (subset_union_right : ball ψ R M (t + 1) ⊆ ball ψ R M t ∪ ball ψ R M (t + 1))
      exact div_le_div_of_nonneg_left hnn hR (by linarith)
  · have hb := big_left hψ hlen ht h1
    have hu := len_mono hψ (subset_union_left : ball ψ R M t ⊆ ball ψ R M t ∪ ball ψ R M (t + 1))
    exact div_le_div_of_nonneg_left hnn hR (by linarith)

/-- **Anchor cuts.** The expected number of anchor cuts on a segment is at most `2 Σ_f μ(f)/R`. -/
theorem anchor_cuts (hψ : StrictMono ψ) (hR : 0 < R) (hlen : ∀ j < M, ψ (j + 1) - ψ j ≤ R) :
    ∑ t ∈ range M, len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) /
        len ψ (ball ψ R M t ∪ ball ψ R M (t + 1)) ≤ 2 * len ψ (range M) / R := by
  calc _ ≤ ∑ t ∈ range M, len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1))) / R :=
        sum_le_sum fun t ht => cut_ratio_le hψ hR hlen (mem_range.1 ht)
    _ = (∑ t ∈ range M, len ψ (symmDiff (ball ψ R M t) (ball ψ R M (t + 1)))) / R := by
        rw [sum_div]
    _ ≤ 2 * len ψ (range M) / R := div_le_div_of_nonneg_right (sum_symmDiff_le hψ) hR.le

end Segment

/-! ### Holes -/

/-- **Few holes.** If every hole `F` has more than `ℓ` vertices, the holes have at most `3h`
separators in total, and the packing sets of the holes give
`Σ_F (|F| - 4|S(F)| - 2)/3 ≤ γ_f`, then `h(ℓ - 13)/3 ≤ γ_f`. -/
theorem few_holes {ι : Type*} (H : Finset ι) (len sep : ι → ℕ) (ℓ : ℕ) (γf : ℝ)
    (hlen : ∀ F ∈ H, ℓ + 1 ≤ len F) (hsep : ∑ F ∈ H, sep F ≤ 3 * #H)
    (hpack : ∑ F ∈ H, ((len F : ℝ) - 4 * sep F - 2) / 3 ≤ γf) :
    (#H : ℝ) * ((ℓ : ℝ) - 13) / 3 ≤ γf := by
  have h1 : ∑ F ∈ H, ((ℓ : ℝ) + 1) ≤ ∑ F ∈ H, (len F : ℝ) :=
    sum_le_sum fun F hF => by exact_mod_cast hlen F hF
  have h2 : (∑ F ∈ H, (sep F : ℝ)) ≤ 3 * #H := by exact_mod_cast hsep
  have e : ∑ F ∈ H, ((len F : ℝ) - 4 * sep F - 2) / 3 =
      (∑ F ∈ H, (len F : ℝ) - 4 * ∑ F ∈ H, (sep F : ℝ) - 2 * #H) / 3 := by
    rw [← sum_div, sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  rw [sum_const, nsmul_eq_mul] at h1
  rw [e] at hpack
  linarith

/-- Every finite set of naturals contains a subset of at least a third of its size whose elements
are pairwise at least `3` apart. -/
theorem exists_sparse (S : Finset ℕ) :
    ∃ A ⊆ S, #S ≤ 3 * #A ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨∅, empty_subset _, by simp, by simp⟩
    · have hmS := S.min'_mem hS
      set m := S.min' hS with hm
      have hS' : S.filter (fun x => m + 3 ≤ x) ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨filter_subset _ _, fun h => ?_⟩
        have hm' : m ∈ S.filter (fun x => m + 3 ≤ x) := by rw [h]; exact hmS
        rw [mem_filter] at hm'
        omega
      obtain ⟨A', hA'S, hcard, hsep⟩ := ih _ hS'
      have hmA : m ∉ A' := fun h => by
        have := (mem_filter.1 (hA'S h)).2
        omega
      refine ⟨insert m A', insert_subset hmS (hA'S.trans (filter_subset _ _)), ?_, ?_⟩
      · have h1 : S.filter (fun x => ¬ m + 3 ≤ x) ⊆ Icc m (m + 2) := by
          intro x hx
          rw [mem_filter] at hx
          rw [mem_Icc]
          exact ⟨S.min'_le x hx.1, by omega⟩
        have h2 := card_filter_add_card_filter_not (s := S) (fun x => m + 3 ≤ x)
        have h3 := card_le_card h1
        rw [Nat.card_Icc] at h3
        rw [card_insert_of_notMem hmA]
        omega
      · intro x hx y hy hxy
        rw [mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · omega
        · exact (mem_filter.1 (hA'S hy)).2
        · have := (mem_filter.1 (hA'S hx)).2
          omega
        · exact hsep x hx y hy hxy

/-- **Packing on an isometric cycle.** Let the positions `0, …, n-1` of a cycle have distance at
least the cyclic distance. Every set `W` of positions contains a set `A` with `#W ≤ 3#A + 2` whose
vertices have pairwise distance at least `3`. -/
theorem cycle_packing {V : Type*} (d : V → V → ℕ) (n : ℕ) (c : ℕ → V)
    (hc : ∀ x y, x < y → y < n → min (y - x) (n - (y - x)) ≤ d (c x) (c y))
    (W : Finset ℕ) (hW : W ⊆ range n) :
    ∃ A ⊆ W, #W ≤ 3 * #A + 2 ∧ ∀ x ∈ A, ∀ y ∈ A, x < y → 3 ≤ d (c x) (c y) := by
  obtain ⟨A, hAS, hcard, hsep⟩ := exists_sparse (W.filter fun x => x + 3 ≤ n)
  refine ⟨A, hAS.trans (filter_subset _ _), ?_, ?_⟩
  · have h1 : W.filter (fun x => ¬ x + 3 ≤ n) ⊆ Ico (n - 2) n := by
      intro x hx
      rw [mem_filter] at hx
      have := mem_range.1 (hW hx.1)
      rw [mem_Ico]
      omega
    have h2 := card_filter_add_card_filter_not (s := W) (fun x => x + 3 ≤ n)
    have h3 := card_le_card h1
    rw [Nat.card_Ico] at h3
    omega
  · intro x hx y hy hxy
    have hx' := (mem_filter.1 (hAS hx)).2
    have hy' := (mem_filter.1 (hAS hy)).2
    have h := hc x y hxy (by omega)
    have := hsep x hx y hy hxy
    have : 3 ≤ min (y - x) (n - (y - x)) := le_min (by omega) (by omega)
    omega

end Outer

end Op4
