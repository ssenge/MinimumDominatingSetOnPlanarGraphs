import Op4.ForestRays

/-!
# The windows of Theorem `thm:forests`

The windows are unions of hairs, plus the components that contain no core vertex:
* for every P-vertex `u`, the hairs of `pball u R`, with weight `1/(2R+1)`;
* for every P-vertex `e`, every missing direction `s < slots e` and every `1 ≤ t ≤ R`, the hairs
  of `pball e (R - t)`, with weight `1/(2R+1)` (index `t - 1 : Fin R`);
* for every branch vertex `b`, the hair of `b`, with weight `1`;
* for every vertex `u` that reaches no core vertex, its component, with weight `1/#(comp u)`.
On a core path, the first two kinds are the sliding intervals of length `2R+1`: the centred
intervals, and the intervals that stick out over an end.
* `cover`: every vertex lies in windows of total weight exactly `1`. On the core paths this is
  `cover_count`; a vertex outside the core is in the same windows as its projection.
* `bdry_hairs`, `bdry_pball`: a vertex of a window with a neighbour outside it is a core vertex of
  the window next to a branch vertex, or at distance exactly `k` from the centre of a P-ball of
  radius `k`. The other windows have boundary at most `{b}` (`wB_branch`) or none (`wB_free`).
-/

namespace Op4

namespace Forest

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {R : ℕ}

open Classical in
/-- The union of the hairs of the vertices of `X`. -/
noncomputable def hairs (G : SimpleGraph V) (R : ℕ) (X : Finset V) : Finset V :=
  univ.filter fun v => ∃ c ∈ X, Proj G R v c

/-- `v` reaches no core vertex. -/
def Free (G : SimpleGraph V) (R : ℕ) (v : V) : Prop :=
  ∀ c, G.Reachable v c → ¬ Core G R c

open Classical in
/-- The component of `v`. -/
noncomputable def comp (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter (G.Reachable v)

/-- The window indices: centres, end prefixes, branch vertices, core-free components. -/
abbrev WIdx (V : Type*) (R : ℕ) := V ⊕ (V × Fin 2 × Fin R) ⊕ V ⊕ V

open Classical in
/-- The core part of a window. -/
noncomputable def wX (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) : WIdx V R → Finset V
  | .inl u => if IsP G R u then pball G R u R else ∅
  | .inr (.inl (e, s, t)) =>
      if IsP G R e ∧ (s : ℕ) < slots G R e then pball G R e (R - 1 - t) else ∅
  | .inr (.inr (.inl b)) => if IsBr G R b then {b} else ∅
  | .inr (.inr (.inr _)) => ∅

open Classical in
/-- The vertex set of a window. -/
noncomputable def wU (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) : WIdx V R → Finset V
  | .inl u => hairs G R (wX G R (.inl u))
  | .inr (.inl q) => hairs G R (wX G R (.inr (.inl q)))
  | .inr (.inr (.inl b)) => hairs G R (wX G R (.inr (.inr (.inl b))))
  | .inr (.inr (.inr u)) => if Free G R u then comp G u else ∅

/-- The weight of a window. -/
noncomputable def wt (G : SimpleGraph V) (R : ℕ) : WIdx V R → ℝ
  | .inl _ => 1 / (2 * R + 1)
  | .inr (.inl _) => 1 / (2 * R + 1)
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr u)) => 1 / #(comp G u)

open Classical in
/-- The boundary of a window: its vertices with a neighbour outside it. -/
noncomputable def wB [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ)
    (i : WIdx V R) : Finset V :=
  (wU G R i).filter fun z => ∃ w, G.Adj z w ∧ w ∉ wU G R i

omit [DecidableRel G.Adj] in
lemma mem_hairs {X : Finset V} {v : V} : v ∈ hairs G R X ↔ ∃ c ∈ X, Proj G R v c := by
  simp [hairs]

omit [DecidableRel G.Adj] in
lemma mem_comp {u v : V} : v ∈ comp G u ↔ G.Reachable u v := by
  simp [comp]

omit [Fintype V] [DecidableRel G.Adj] in
lemma proj_self {c : V} (hc : Core G R c) : Proj G R c c :=
  ⟨hc, Walk.nil, Walk.IsPath.nil, fun x hx _ => by rwa [Walk.support_nil, List.mem_singleton] at hx⟩

omit [Fintype V] [DecidableRel G.Adj] in
lemma Proj.reachable {v c : V} (h : Proj G R v c) : G.Reachable v c :=
  let ⟨_, p, _⟩ := h
  ⟨p⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A non-core neighbour of a core vertex lies in its hair. -/
lemma proj_of_nbr {c w : V} (hc : Core G R c) (hadj : G.Adj c w) (hw : ¬ Core G R w) :
    Proj G R w c := by
  refine ⟨hc, hadj.symm.toWalk, hadj.symm.isPath_toWalk, fun x hx hxc => ?_⟩
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact absurd hxc hw
  · rfl

omit [DecidableRel G.Adj] in
/-- A vertex with a projection lies in the windows that contain its projection. -/
lemma mem_hairs_iff (hG : G.IsAcyclic) (hR : 1 ≤ R) {X : Finset V} {v c : V} (h : Proj G R v c) :
    v ∈ hairs G R X ↔ c ∈ X := by
  rw [mem_hairs]
  exact ⟨fun ⟨c', hc', h'⟩ => proj_unique hG hR h h' ▸ hc', fun hc => ⟨c, hc, h⟩⟩

omit [DecidableRel G.Adj] in
lemma mem_hairs_core (hG : G.IsAcyclic) (hR : 1 ≤ R) {X : Finset V} {c : V} (hc : Core G R c) :
    c ∈ hairs G R X ↔ c ∈ X :=
  mem_hairs_iff hG hR (proj_self hc)

lemma mem_wU_iff (hG : G.IsAcyclic) (hR : 1 ≤ R) {v c : V} (h : Proj G R v c) (i : WIdx V R) :
    v ∈ wU G R i ↔ c ∈ wU G R i := by
  rcases i with u | q | b | u
  · exact (mem_hairs_iff hG hR h).trans (mem_hairs_core hG hR h.1).symm
  · exact (mem_hairs_iff hG hR h).trans (mem_hairs_core hG hR h.1).symm
  · exact (mem_hairs_iff hG hR h).trans (mem_hairs_core hG hR h.1).symm
  · simp only [wU]
    split_ifs with hu
    · rw [mem_comp, mem_comp]
      exact ⟨fun h' => absurd h.1 (hu c (h'.trans h.reachable)), fun h' => absurd h.1 (hu c h')⟩
    · simp

/-- A core vertex is in no component window. -/
lemma not_mem_wU_free {c : V} (hc : Core G R c) (u : V) : c ∉ wU G R (.inr (.inr (.inr u))) := by
  simp only [wU]
  split_ifs with hu
  · rw [mem_comp]
    exact fun h => hu c h hc
  · exact notMem_empty c

lemma mem_wU_centre (hG : G.IsAcyclic) (hR : 1 ≤ R) {c u : V} (hc : IsP G R c) :
    c ∈ wU G R (.inl u) ↔ u ∈ pball G R c R := by
  simp only [wU]
  rw [mem_hairs_core hG hR hc.1]
  simp only [wX]
  split_ifs with hu
  · rw [mem_pball, mem_pball]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [notMem_empty, false_iff]
    exact fun h => hu (mem_pball.1 h).isP_end

lemma mem_wU_prefix (hG : G.IsAcyclic) (hR : 1 ≤ R) {c e : V} {s : Fin 2} {t : Fin R}
    (hc : IsP G R c) : c ∈ wU G R (.inr (.inl (e, s, t))) ↔
      e ∈ pball G R c R ∧ (s : ℕ) < slots G R e ∧ (t : ℕ) < R - G.dist c e := by
  have ht := t.isLt
  simp only [wU]
  rw [mem_hairs_core hG hR hc.1]
  simp only [wX]
  split_ifs with he
  · rw [mem_pball, mem_pball]
    constructor
    · intro h
      have h' := (inPBall_iff_dist hG (show R - 1 - t ≤ R by omega)).1 h.symm
      exact ⟨h'.1, he.2, by omega⟩
    · rintro ⟨h1, -, h3⟩
      exact ((inPBall_iff_dist hG (show R - 1 - (t : ℕ) ≤ R by omega)).2 ⟨h1, by omega⟩).symm
  · simp only [notMem_empty, false_iff]
    rintro ⟨h1, h2, -⟩
    exact he ⟨(mem_pball.1 h1).isP_end, h2⟩

lemma count_st (a b n : ℕ) :
    (∑ s : Fin 2, ∑ t : Fin n, if (s : ℕ) < a ∧ (t : ℕ) < b then 1 else 0) =
      min 2 a * min n b := by
  rw [← Fin.card_filter_val_lt, ← Fin.card_filter_val_lt, card_filter, card_filter, sum_mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  by_cases h1 : (s : ℕ) < a <;> by_cases h2 : (t : ℕ) < b <;> simp [h1, h2]

/-- The number of end-prefix windows that contain a P-vertex. -/
lemma card_prefix [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) {c : V} (hc : IsP G R c) :
    #(univ.filter fun q : V × Fin 2 × Fin R => c ∈ wU G R (.inr (.inl q))) =
      ∑ e ∈ pball G R c R, slots G R e * (R - G.dist c e) := by
  rw [card_filter, Fintype.sum_prod_type,
    ← Fintype.sum_ite_mem (pball G R c R) (fun e => slots G R e * (R - G.dist c e))]
  refine sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type]
  simp_rw [mem_wU_prefix hG hR hc]
  split_ifs with he
  · simp only [he, true_and]
    rw [count_st, min_eq_right (by unfold slots; omega), min_eq_right (Nat.sub_le _ _)]
  · simp [he]

lemma sum_ite_const {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (a : ℝ) :
    ∑ i, (if p i then a else 0) = (#(univ.filter p) : ℝ) * a := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- **Cover, on the core paths.** -/
lemma cover_P [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) {c : V} (hc : IsP G R c) :
    ∑ i ∈ univ.filter (fun i => c ∈ wU G R i), wt G R i = 1 := by
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt]
  have h1 : (∑ u : V, if c ∈ wU G R (.inl u) then (1 / (2 * R + 1) : ℝ) else 0) =
      #(pball G R c R) * (1 / (2 * R + 1)) := by
    simp_rw [mem_wU_centre hG hR hc]
    rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul]
  have h2 : (∑ q : V × Fin 2 × Fin R,
      if c ∈ wU G R (.inr (.inl q)) then (1 / (2 * R + 1) : ℝ) else 0) =
      ((∑ e ∈ pball G R c R, slots G R e * (R - G.dist c e) : ℕ) : ℝ) * (1 / (2 * R + 1)) := by
    rw [sum_ite_const, card_prefix hG hR hc]
  have h3 : (∑ b : V, if c ∈ wU G R (.inr (.inr (.inl b))) then (1 : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff]
    intro h
    simp only [wU] at h
    rw [mem_hairs_core hG hR hc.1] at h
    simp only [wX] at h
    split_ifs at h with hb
    · rw [mem_singleton] at h
      exact absurd (h ▸ hc) hb.2
    · exact absurd h (notMem_empty c)
  have h4 : (∑ u : V, if c ∈ wU G R (.inr (.inr (.inr u))) then (1 / #(comp G u) : ℝ) else 0)
      = 0 :=
    sum_eq_zero fun u _ => by rw [ite_eq_right_iff]; exact fun h => absurd h (not_mem_wU_free hc.1 u)
  rw [h1, h2, h3, h4]
  have hcc : ((#(pball G R c R) : ℕ) : ℝ) +
      ((∑ e ∈ pball G R c R, slots G R e * (R - G.dist c e) : ℕ) : ℝ) = 2 * R + 1 := by
    exact_mod_cast cover_count hG hc hR
  rw [show ((#(pball G R c R) : ℕ) : ℝ) * (1 / (2 * R + 1)) +
      (((∑ e ∈ pball G R c R, slots G R e * (R - G.dist c e) : ℕ) : ℝ) * (1 / (2 * R + 1)) +
        (0 + 0)) = (((#(pball G R c R) : ℕ) : ℝ) +
      ((∑ e ∈ pball G R c R, slots G R e * (R - G.dist c e) : ℕ) : ℝ)) * (1 / (2 * R + 1)) by
    ring, hcc]
  field_simp

/-- **Cover, at the branch vertices.** -/
lemma cover_Br [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) {c : V} (hc : IsBr G R c) :
    ∑ i ∈ univ.filter (fun i => c ∈ wU G R i), wt G R i = 1 := by
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt]
  have h1 : (∑ u : V, if c ∈ wU G R (.inl u) then (1 / (2 * R + 1) : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun u _ => ?_
    rw [ite_eq_right_iff]
    intro h
    simp only [wU] at h
    rw [mem_hairs_core hG hR hc.1] at h
    simp only [wX] at h
    split_ifs at h
    · exact absurd (mem_pball.1 h).isP_end hc.2
    · exact absurd h (notMem_empty c)
  have h2 : (∑ q : V × Fin 2 × Fin R,
      if c ∈ wU G R (.inr (.inl q)) then (1 / (2 * R + 1) : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun q _ => ?_
    rw [ite_eq_right_iff]
    intro h
    obtain ⟨e, s, t⟩ := q
    simp only [wU] at h
    rw [mem_hairs_core hG hR hc.1] at h
    simp only [wX] at h
    split_ifs at h
    · exact absurd (mem_pball.1 h).isP_end hc.2
    · exact absurd h (notMem_empty c)
  have h3 : (∑ b : V, if c ∈ wU G R (.inr (.inr (.inl b))) then (1 : ℝ) else 0) = 1 := by
    have hiff : ∀ b, c ∈ wU G R (.inr (.inr (.inl b))) ↔ c = b := by
      intro b
      simp only [wU]
      rw [mem_hairs_core hG hR hc.1]
      simp only [wX]
      split_ifs with hb
      · exact mem_singleton
      · simp only [notMem_empty, false_iff]
        rintro rfl
        exact hb hc
    simp_rw [hiff]
    simp
  have h4 : (∑ u : V, if c ∈ wU G R (.inr (.inr (.inr u))) then (1 / #(comp G u) : ℝ) else 0)
      = 0 :=
    sum_eq_zero fun u _ => by rw [ite_eq_right_iff]; exact fun h => absurd h (not_mem_wU_free hc.1 u)
  rw [h1, h2, h3, h4]
  norm_num

omit [DecidableRel G.Adj] in
lemma comp_eq {u v : V} (h : u ∈ comp G v) : comp G u = comp G v := by
  ext w
  rw [mem_comp, mem_comp]
  rw [mem_comp] at h
  exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- **Cover, on the core-free components.** -/
lemma cover_free [DecidableEq V] {v : V} (hv : Free G R v) :
    ∑ i ∈ univ.filter (fun i => v ∈ wU G R i), wt G R i = 1 := by
  have hnot : ∀ X, v ∉ hairs G R X := fun X h => by
    obtain ⟨c, -, hc⟩ := mem_hairs.1 h
    exact hv c hc.reachable hc.1
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt]
  have h1 : (∑ u : V, if v ∈ wU G R (.inl u) then (1 / (2 * R + 1) : ℝ) else 0) = 0 :=
    sum_eq_zero fun u _ => by rw [ite_eq_right_iff]; exact fun h => absurd h (hnot _)
  have h2 : (∑ q : V × Fin 2 × Fin R,
      if v ∈ wU G R (.inr (.inl q)) then (1 / (2 * R + 1) : ℝ) else 0) = 0 :=
    sum_eq_zero fun q _ => by rw [ite_eq_right_iff]; exact fun h => absurd h (hnot _)
  have h3 : (∑ b : V, if v ∈ wU G R (.inr (.inr (.inl b))) then (1 : ℝ) else 0) = 0 :=
    sum_eq_zero fun b _ => by rw [ite_eq_right_iff]; exact fun h => absurd h (hnot _)
  have hmem : ∀ u, v ∈ wU G R (.inr (.inr (.inr u))) ↔ u ∈ comp G v := by
    intro u
    simp only [wU]
    split_ifs with hu
    · rw [mem_comp, mem_comp]
      exact reachable_comm
    · simp only [notMem_empty, false_iff]
      intro huv
      rw [mem_comp] at huv
      exact hu fun c hc => hv c (huv.trans hc)
  have h4 : (∑ u : V, if v ∈ wU G R (.inr (.inr (.inr u))) then (1 / #(comp G u) : ℝ) else 0)
      = 1 := by
    simp_rw [hmem]
    rw [Fintype.sum_ite_mem, sum_congr rfl fun u hu => by rw [comp_eq hu], sum_const,
      nsmul_eq_mul]
    have : (0 : ℝ) < #(comp G v) := by
      exact_mod_cast card_pos.2 ⟨v, mem_comp.2 (Reachable.refl v)⟩
    field_simp
  rw [h1, h2, h3, h4]
  norm_num

/-- **Cover.** Every vertex lies in windows of total weight exactly `1`. -/
theorem cover [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) (v : V) :
    ∑ i ∈ univ.filter (fun i => v ∈ wU G R i), wt G R i = 1 := by
  by_cases hv : Free G R v
  · exact cover_free hv
  · simp only [Free, not_forall, not_not] at hv
    obtain ⟨c₀, hr, hc₀⟩ := hv
    obtain ⟨c, hc⟩ := exists_proj hc₀ hr
    rw [show univ.filter (fun i => v ∈ wU G R i) = univ.filter (fun i => c ∈ wU G R i) by
      ext i; simp only [mem_filter, mem_univ, true_and]; exact mem_wU_iff hG hR hc i]
    by_cases hP : IsP G R c
    · exact cover_P hG hR hP
    · exact cover_Br hG hR ⟨hc.1, hP⟩

omit [DecidableRel G.Adj] in
/-- A vertex of a union of hairs with a neighbour outside it is a core vertex of `X`, and the
neighbour is a core vertex outside `X`. -/
lemma bdry_hairs (hG : G.IsAcyclic) (hR : 1 ≤ R) {X : Finset V} {z w : V}
    (hz : z ∈ hairs G R X) (hadj : G.Adj z w) (hw : w ∉ hairs G R X) :
    z ∈ X ∧ Core G R w ∧ w ∉ X := by
  obtain ⟨c, hcX, hzc⟩ := mem_hairs.1 hz
  by_cases hzc' : z = c
  · subst hzc'
    by_cases hwc : Core G R w
    · exact ⟨hcX, hwc, fun hwX => hw (mem_hairs.2 ⟨w, hwX, proj_self hwc⟩)⟩
    · exact absurd (mem_hairs.2 ⟨z, hcX, proj_of_nbr hzc.1 hadj hwc⟩) hw
  · exact absurd (mem_hairs.2 ⟨c, hcX, proj_of_adj hG hR hzc hzc' hadj⟩) hw

/-- A P-ball that does not reach its radius in some direction contains the next P-vertex. -/
lemma inPBall_of_adj (hG : G.IsAcyclic) {z0 z w : V} {k : ℕ} (h : InPBall G R z0 k z)
    (hd : G.dist z0 z < k) (hw : w ∈ pnbr G R z) : InPBall G R z0 k w := by
  classical
  obtain ⟨p, hp, hpP, -⟩ := h
  rw [dist_eq_length hG hp] at hd
  obtain ⟨hadj, hwP⟩ := mem_pnbr.1 hw
  by_cases hws : w ∈ p.support
  · exact ⟨p.takeUntil w hws, hp.takeUntil hws,
      fun y hy => hpP y (p.support_takeUntil_subset_support hws hy),
      by have := p.length_takeUntil_le_length hws; omega⟩
  · refine ⟨p.concat hadj, hp.concat hws hadj, fun y hy => ?_, by rw [Walk.length_concat]; omega⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hpP y hy
    · exact hwP

/-- **Boundary of a P-ball window.** -/
lemma bdry_pball (hG : G.IsAcyclic) (hR : 1 ≤ R) {z0 z w : V} {k : ℕ}
    (hz : z ∈ hairs G R (pball G R z0 k)) (hadj : G.Adj z w)
    (hw : w ∉ hairs G R (pball G R z0 k)) :
    z ∈ pball G R z0 k ∧ ((∃ b, G.Adj z b ∧ IsBr G R b) ∨ G.dist z0 z = k) := by
  obtain ⟨hzX, hwc, hwX⟩ := bdry_hairs hG hR hz hadj hw
  refine ⟨hzX, ?_⟩
  by_cases hwP : IsP G R w
  · right
    obtain ⟨p, hp, hpP, hpl⟩ := mem_pball.1 hzX
    have hd : G.dist z0 z ≤ k := by rw [dist_eq_length hG hp]; exact hpl
    by_contra hne
    exact hwX (mem_pball.2 (inPBall_of_adj hG ⟨p, hp, hpP, hpl⟩ (by omega)
      (mem_pnbr.2 ⟨hadj, hwP⟩)))
  · exact Or.inl ⟨w, hadj, hwc, hwP⟩

/-- At most two vertices of a P-ball are at the largest distance, also for radius `0`. -/
lemma card_psphere_le' (hG : G.IsAcyclic) {z0 : V} (hz0 : IsP G R z0) (k : ℕ) :
    #((pball G R z0 k).filter fun x => G.dist z0 x = k) ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ((card_le_card fun x hx => ?_).trans (card_singleton z0).le).trans (by norm_num)
    rw [mem_filter, mem_pball] at hx
    obtain ⟨⟨p, -, -, hpl⟩, -⟩ := hx
    rw [mem_singleton]
    exact (Walk.eq_of_length_eq_zero (p := p) (by omega)).symm
  · exact card_psphere_le hG hz0 hk

open Classical in
/-- The boundary of a window around a P-ball: its vertices next to a branch vertex, and at most
two more. -/
lemma card_wB_pball [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) {z0 : V} (hz0 : IsP G R z0) (k : ℕ)
    {i : WIdx V R} (hi : wU G R i = hairs G R (pball G R z0 k)) :
    #(wB G R i) ≤ #((pball G R z0 k).filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b) + 2 := by
  classical
  have hsub : wB G R i ⊆ (pball G R z0 k).filter (fun z => ∃ b, G.Adj z b ∧ IsBr G R b) ∪
      (pball G R z0 k).filter (fun x => G.dist z0 x = k) := by
    intro z hz
    rw [wB, mem_filter, hi] at hz
    obtain ⟨hzU, w, hadj, hw⟩ := hz
    obtain ⟨hzX, h | h⟩ := bdry_pball hG hR hzU hadj hw
    · exact mem_union_left _ (mem_filter.2 ⟨hzX, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hzX, h⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_psphere_le' hG hz0 k) _))

/-- The boundary of a branch window is at most its branch vertex. -/
lemma wB_branch [DecidableEq V] (hG : G.IsAcyclic) (hR : 1 ≤ R) (b : V) :
    wB G R (.inr (.inr (.inl b))) ⊆ {b} := by
  classical
  intro z hz
  rw [wB, mem_filter] at hz
  obtain ⟨hzU, w, hadj, hw⟩ := hz
  simp only [wU] at hzU hw
  have h := (bdry_hairs hG hR hzU hadj hw).1
  simp only [wX] at h
  split_ifs at h
  · exact h
  · exact absurd h (notMem_empty z)

/-- A component window has no boundary. -/
lemma wB_free [DecidableEq V] (u : V) : wB G R (.inr (.inr (.inr u))) = ∅ := by
  classical
  ext z
  simp only [wB, mem_filter, notMem_empty, iff_false, not_and, not_exists]
  intro hz w hadj hw
  simp only [wU] at hz hw
  split_ifs at hz hw with hu
  · rw [mem_comp] at hz hw
    exact hw (hz.trans hadj.reachable)
  · exact notMem_empty z hz

end Forest

end Op4
