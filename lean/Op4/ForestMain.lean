import Op4.ForestCount
import Op4.ForestLP

/-!
# Theorem `thm:forests`, deterministic fractional part: the guarantee

`forestSol G R` averages, over the windows of `Op4.ForestWindows` with their weights, a fixed
optimal solution `locOpt` of the fractional problem of each window. On every finite forest and for
every `R ≥ 1`, it is a fractional dominating set of weight at most `(1 + 72/R)·y(V)` for every
fractional dominating set `y` (`forest_frac`). In the LOCAL model, `V` is the identifier space and
the identifiers that are not nodes are isolated vertices; then the bound holds on the nodes
(`forest_frac_on`). That `forestSol G R v` depends only on the part of `G` near `v` is
`Op4.ForestLocal`.
-/

namespace Op4

namespace Forest

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : ℕ}

open Classical in
/-- The closed neighbourhoods that the problem of a window uses: those of its vertices. -/
noncomputable def wnb (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (i : WIdx V R) :
    V → Finset V :=
  fun u => if u ∈ wU G R i then cnbhd G u else ∅

/-- **The output**: the weighted average of the window optima. -/
noncomputable def forestSol (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : ℝ :=
  ∑ i : WIdx V R, wt G R i * locOpt (wU G R i) (wnb G R i) v

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma wt_nonneg (i : WIdx V R) : 0 ≤ wt G R i := by
  rcases i with u | q | b | u <;> simp only [wt] <;> positivity

lemma wnb_self (i : WIdx V R) : ∀ u ∈ wU G R i, u ∈ wnb G R i u := fun u hu => by
  simp only [wnb, hu, ↓reduceIte]
  exact mem_insert_self _ _

lemma locOpt_isOpt (i : WIdx V R) : IsOpt (wU G R i) (wnb G R i) (locOpt (wU G R i) (wnb G R i)) :=
  locOpt_spec (wnb_self i)

/-- **The averaging step.** `forestSol G R` is a fractional dominating set of weight at most
`y(V) + ∑ wt·|wB|` for every fractional dominating set `y`. -/
lemma forest_avg (hG : G.IsAcyclic) (hR : 1 ≤ R) :
    (∀ u, Dom G (forestSol G R) u) ∧ ∀ y : V → ℝ, (∀ v, 0 ≤ y v) → (∀ u, Dom G y u) →
      ∑ v, forestSol G R v ≤ ∑ v, y v + ∑ i, wt G R i * #(wB G R i) := by
  have hxdom : ∀ i ∈ (univ : Finset (WIdx V R)), ∀ u ∈ wU G R i,
      Dom G (locOpt (wU G R i) (wnb G R i)) u := by
    intro i _ u hu
    have := (locOpt_isOpt (G := G) i).1.2.2 u hu
    simp only [wnb, hu, ↓reduceIte] at this
    exact this
  have hxopt : ∀ i ∈ (univ : Finset (WIdx V R)), ∀ z : V → ℝ, (∀ v, 0 ≤ z v) →
      (∀ v, v ∉ wU G R i → z v = 0) → (∀ u ∈ wU G R i, Dom G z u) →
        ∑ v, locOpt (wU G R i) (wnb G R i) v ≤ ∑ v, z v := by
    intro i _ z hz0 hzS hzd
    refine (locOpt_isOpt (G := G) i).2 z ⟨hz0, hzS, fun u hu => ?_⟩
    simp only [wnb, hu, ↓reduceIte]
    exact hzd u hu
  have hx0 : ∀ i ∈ (univ : Finset (WIdx V R)), ∀ v, 0 ≤ locOpt (wU G R i) (wnb G R i) v :=
    fun i _ => (locOpt_isOpt (G := G) i).1.1
  have hB : ∀ i ∈ (univ : Finset (WIdx V R)), ∀ u ∈ wU G R i,
      (∃ v, G.Adj u v ∧ v ∉ wU G R i) → ∃ b ∈ wB G R i, b ∈ cnbhd G u := by
    intro i _ u hu h
    exact ⟨u, mem_filter.2 ⟨hu, h⟩, mem_insert_self _ _⟩
  have havg := fun y hy hyd => window_average G univ (wU G R) (wU G R) (wB G R) (wt G R)
    (fun i => locOpt (wU G R i) (wnb G R i)) (fun i _ => wt_nonneg i) (cover hG hR)
    (fun i _ => subset_refl _) (fun i _ => filter_subset _ _) hB hx0 hxdom hxopt y hy hyd
  have hone : ∀ u, Dom G (fun _ => (1 : ℝ)) u := fun u =>
    (single_le_sum (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (mem_insert_self u _)).trans
      le_rfl
  exact ⟨(havg _ (fun _ => zero_le_one) hone).1, fun y hy hyd => (havg y hy hyd).2⟩

lemma forestSol_nonneg (v : V) : 0 ≤ forestSol G R v :=
  sum_nonneg fun i _ => mul_nonneg (wt_nonneg i) ((locOpt_isOpt i).1.1 v)

/-- **Theorem `thm:forests`, deterministic fractional part.** On a finite forest, for every
`R ≥ 1`, `forestSol G R` is a fractional dominating set of weight at most `(1 + 72/R)·y(V)` for
every fractional dominating set `y`. -/
theorem forest_frac (hG : G.IsAcyclic) (hR : 1 ≤ R) :
    (∀ v, 0 ≤ forestSol G R v) ∧ (∀ u, Dom G (forestSol G R) u) ∧
      ∀ y : V → ℝ, (∀ v, 0 ≤ y v) → (∀ u, Dom G y u) →
        ∑ v, forestSol G R v ≤ (1 + 72 / R) * ∑ v, y v := by
  obtain ⟨hdom, havg⟩ := forest_avg hG hR
  refine ⟨forestSol_nonneg, hdom, fun y hy hyd => ?_⟩
  have h1 := havg y hy hyd
  have h2 := sum_wt_wB_le hG hR y hy fun u _ => hyd u
  linarith

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex with no neighbour reaches no core vertex. -/
lemma free_of_isolated (hR : 1 ≤ R) {u : V} (hu : ∀ w, ¬ G.Adj u w) : Free G R u := by
  rintro c ⟨p⟩ hc
  cases p with
  | nil =>
    obtain ⟨u₁, u₂, -, ⟨x, q, -, hq, -⟩, -⟩ := hc
    cases q with
    | nil => rw [Walk.length_nil] at hq; omega
    | cons h _ => exact hu _ h
  | cons h _ => exact hu _ h

/-- **Theorem `thm:forests`, deterministic fractional part, on a network.** Let `V` be the
identifier space and let the forest `G` have all its edges inside the node set `S`; the
identifiers outside `S` are isolated vertices. On `S`, `forestSol G R` is a fractional dominating
set of weight at most `(1 + 72/R)·y(S)` for every `y ≥ 0` that dominates the nodes. -/
theorem forest_frac_on (hG : G.IsAcyclic) (hR : 1 ≤ R) (S : Finset V)
    (hS : ∀ u w, G.Adj u w → u ∈ S) :
    (∀ v, 0 ≤ forestSol G R v) ∧ (∀ u ∈ S, Dom G (forestSol G R) u) ∧
      ∀ y : V → ℝ, (∀ v, 0 ≤ y v) → (∀ u ∈ S, Dom G y u) →
        ∑ v ∈ S, forestSol G R v ≤ (1 + 72 / R) * ∑ v ∈ S, y v := by
  obtain ⟨hdom, havg⟩ := forest_avg hG hR
  refine ⟨forestSol_nonneg, fun u _ => hdom u, fun y hy hyd => ?_⟩
  have hiso : ∀ u, u ∉ S → ∀ w, ¬ G.Adj u w := fun u hu w h => hu (hS u w h)
  have hcn : ∀ u, u ∉ S → cnbhd G u = {u} := fun u hu => by
    ext w
    simp only [cnbhd, mem_insert, mem_neighborFinset, mem_singleton]
    exact ⟨fun h => h.resolve_right (hiso u hu w), Or.inl⟩
  have hsub : ∀ u ∈ S, ∀ w ∈ cnbhd G u, w ∈ S := fun u hu w hw => by
    simp only [cnbhd, mem_insert, mem_neighborFinset] at hw
    rcases hw with rfl | h
    · exact hu
    · exact hS w u h.symm
  -- `y` restricted to the nodes, and extended by `1` on the other identifiers
  set y₀ : V → ℝ := fun v => if v ∈ S then y v else 0 with hy₀
  set y₁ : V → ℝ := fun v => if v ∈ S then y v else 1 with hy₁
  have hdom₀ : ∀ u ∈ S, Dom G y₀ u := fun u hu => by
    have a : ∑ w ∈ cnbhd G u, y₀ w = ∑ w ∈ cnbhd G u, y w :=
      sum_congr rfl fun w hw => by simp [hy₀, hsub u hu w hw]
    unfold Dom
    rw [a]
    exact hyd u hu
  have hdom₁ : ∀ u, Dom G y₁ u := fun u => by
    unfold Dom
    by_cases hu : u ∈ S
    · have a : ∑ w ∈ cnbhd G u, y₁ w = ∑ w ∈ cnbhd G u, y w :=
        sum_congr rfl fun w hw => by simp [hy₁, hsub u hu w hw]
      rw [a]
      exact hyd u hu
    · rw [hcn u hu, sum_singleton]
      simp [hy₁, hu]
  have h1 := havg y₁ (fun v => by simp only [hy₁]; split_ifs <;> linarith [hy v]) hdom₁
  have h2 := sum_wt_wB_le hG hR y₀ (fun v => by simp only [hy₀]; split_ifs <;> linarith [hy v])
    fun u hu => hdom₀ u (by by_contra h; exact hu (free_of_isolated hR (hiso u h)))
  have e₀ : ∑ v, y₀ v = ∑ v ∈ S, y v := by
    have a : ∑ v ∈ S, y₀ v = ∑ v ∈ S, y v := sum_congr rfl fun v hv => by simp [hy₀, hv]
    have b : ∑ v ∈ Sᶜ, y₀ v = 0 := sum_eq_zero fun v hv => by simp [hy₀, mem_compl.1 hv]
    rw [← sum_add_sum_compl S y₀, a, b, add_zero]
  have e₁ : ∑ v, y₁ v = ∑ v ∈ S, y v + ∑ v ∈ Sᶜ, (1 : ℝ) := by
    have a : ∑ v ∈ S, y₁ v = ∑ v ∈ S, y v := sum_congr rfl fun v hv => by simp [hy₁, hv]
    have b : ∑ v ∈ Sᶜ, y₁ v = ∑ v ∈ Sᶜ, (1 : ℝ) :=
      sum_congr rfl fun v hv => by simp [hy₁, mem_compl.1 hv]
    rw [← sum_add_sum_compl S y₁, a, b]
  have e₂ : ∑ v ∈ Sᶜ, (1 : ℝ) ≤ ∑ v ∈ Sᶜ, forestSol G R v := sum_le_sum fun u hu => by
    have := hdom u
    unfold Dom at this
    rwa [hcn u (mem_compl.1 hu), sum_singleton] at this
  have e₃ := sum_add_sum_compl S (forestSol G R)
  rw [e₀] at h2
  rw [e₁] at h1
  linarith

end Forest

end Op4
