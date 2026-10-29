import Op4.ForestWindows
import Op4.Windows

/-!
# The boundary count of Theorem `thm:forests`

For every fractional dominating set `y` of a finite forest, the windows of `Op4.ForestWindows`
have total weighted boundary `∑ wt(W)·|B_W| ≤ (72/R)·y(V)` (`sum_wt_wB_le`). Here `L` is the
number of core vertices with at most one core neighbour.
* `card_L_le` (paper, (d)): `R·L ≤ 3·y(V)`. Each such vertex has a path `x₁ … x_R` in its hair,
  the `N[x_j]` cover every vertex at most three times, and the hairs are disjoint.
* `forest_deg`: the core is a forest, so its degrees sum to at most `2|K|`. Hence there are at
  most `3L` branch vertices, and they have at most `6L` core neighbours in total.
* `card_P_le`: the P-vertices with two P-neighbours and no branch neighbour have closed
  neighbourhoods that cover every vertex at most three times, so `|P| ≤ 3y(V) + 7L`.
* The P-ball windows that contain a given P-vertex number exactly `2R+1` (`cover_count`). So the
  boundary vertices next to branch vertices cost `#(P next to Br)`, and the at most two others per
  window cost `2(|P| + R·∑ slots)/(2R+1)`.
-/

namespace Op4

namespace Forest

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : ℕ}

open scoped Classical

/-- Closed neighbourhoods that cover every vertex at most `m` times. -/
lemma sum_cnbhd_le {ι : Type*} (I : Finset ι) (f : ι → V) (y : V → ℝ)
    (hy : ∀ v, 0 ≤ y v) (m : ℕ) (hm : ∀ w, #(I.filter fun i => w ∈ cnbhd G (f i)) ≤ m) :
    ∑ i ∈ I, ∑ w ∈ cnbhd G (f i), y w ≤ m * ∑ w, y w := by
  calc ∑ i ∈ I, ∑ w ∈ cnbhd G (f i), y w
        = ∑ w, ∑ i ∈ I.filter (fun i => w ∈ cnbhd G (f i)), y w := by
          rw [sum_comm' (t' := univ) (s' := fun w => I.filter fun i => w ∈ cnbhd G (f i))
            (h := fun i w => by simp [and_comm])]
    _ = ∑ w, (#(I.filter fun i => w ∈ cnbhd G (f i)) : ℝ) * y w := by
          simp [sum_const, nsmul_eq_mul]
    _ ≤ ∑ w, (m : ℝ) * y w :=
          sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hm w) (hy w)
    _ = m * ∑ w, y w := (mul_sum _ _ _).symm

/-- A dominated family with multiplicity `m` has at most `m·y(V)` members. -/
lemma card_le_of_mult {ι : Type*} (I : Finset ι) (f : ι → V) (y : V → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hyd : ∀ i ∈ I, Dom G y (f i)) (m : ℕ)
    (hm : ∀ w, #(I.filter fun i => w ∈ cnbhd G (f i)) ≤ m) :
    (#I : ℝ) ≤ m * ∑ w, y w := by
  calc (#I : ℝ) = ∑ _i ∈ I, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ I, ∑ w ∈ cnbhd G (f i), y w := sum_le_sum hyd
    _ ≤ m * ∑ w, y w := sum_cnbhd_le I f y hy m hm

lemma mem_cnbhd {u w : V} : w ∈ cnbhd G u ↔ w = u ∨ G.Adj u w := by
  simp [cnbhd, mem_neighborFinset]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A finite set of pairs with one first coordinate and second coordinates within `2` of each
other has at most three elements. -/
lemma card_le_three {α : Type*} [DecidableEq α] (S : Finset (α × ℕ))
    (h : ∀ i ∈ S, ∀ i' ∈ S, i.1 = i'.1 ∧ i.2 ≤ i'.2 + 2) : #S ≤ 3 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hmem := min'_mem (S.image Prod.snd) (hne.image _)
  obtain ⟨i₀, hi₀, him⟩ := mem_image.1 hmem
  calc #S ≤ #(Icc ((S.image Prod.snd).min' (hne.image _))
        ((S.image Prod.snd).min' (hne.image _) + 2)) :=
        card_le_card_of_injOn Prod.snd
          (fun i hi => mem_Icc.2 ⟨min'_le _ _ (mem_image_of_mem _ hi), by
            have := (h i hi i₀ hi₀).2; omega⟩)
          (fun i hi i' hi' he => Prod.ext (h i hi i' hi').1 he)
    _ = 3 := by rw [Nat.card_Icc]; omega

/-- Two vertices with a common vertex in their closed neighbourhoods are at distance at most 2. -/
lemma dist_le_two {a b w : V} (ha : w ∈ cnbhd G a) (hb : w ∈ cnbhd G b) : G.dist a b ≤ 2 := by
  rcases mem_cnbhd.1 ha with h | ha <;> rcases mem_cnbhd.1 hb with h' | hb
  · subst h
    subst h'
    simp
  · subst h
    exact (dist_le hb.symm.toWalk).trans (by simp)
  · subst h'
    exact (dist_le ha.toWalk).trans (by simp)
  · exact (dist_le (ha.toWalk.append hb.symm.toWalk)).trans (by simp)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex that reaches the core is not free. -/
lemma not_free {u c : V} (hc : Core G R c) (h : G.Reachable u c) : ¬ Free G R u :=
  fun hu => hu c h hc

/-- **Hairs of core leaves** (paper, (d)): `R·L ≤ 3·y(V)`. Only the vertices that reach the core
need to be dominated. -/
theorem card_L_le (hG : G.IsAcyclic) (hR : 1 ≤ R) (y : V → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hyd : ∀ u, ¬ Free G R u → Dom G y u) :
    (R : ℝ) * #(univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1) ≤ 3 * ∑ v, y v := by
  classical
  set L := univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1 with hL
  have key : ∀ c ∈ L, ∃ (x : V) (q : G.Walk c x), q.IsPath ∧ q.length = R ∧
      ∀ j, 1 ≤ j → j ≤ R → Proj G R (q.getVert j) c := by
    intro c hc
    rw [hL, mem_filter] at hc
    refine exists_hair_path hG hR hc.2.1 fun u₁ u₂ h₁ h₂ hc₁ hc₂ => ?_
    exact card_le_one.1 hc.2.2 u₁ (mem_knbr.2 ⟨h₁, hc₁⟩) u₂ (mem_knbr.2 ⟨h₂, hc₂⟩)
  choose x q hq hql hqP using key
  set I : Finset ({c // c ∈ L} × ℕ) := L.attach ×ˢ Icc 1 R with hIdef
  set f : {c // c ∈ L} × ℕ → V := fun i => (q i.1.1 i.1.2).getVert i.2 with hf
  have hI : #I = #L * R := by simp [hIdef, card_product]
  have hm : ∀ w, #(I.filter fun i => w ∈ cnbhd G (f i)) ≤ 3 := by
    intro w
    have hproj : ∀ i ∈ I.filter (fun i => w ∈ cnbhd G (f i)), Proj G R w i.1.1 := by
      intro i hi
      rw [mem_filter, hIdef, mem_product, mem_Icc] at hi
      obtain ⟨⟨-, hj1, hjR⟩, hw⟩ := hi
      have hP := hqP i.1.1 i.1.2 i.2 hj1 hjR
      rw [hf] at hw
      rcases mem_cnbhd.1 hw with h | hadj
      · rw [h]
        exact hP
      · refine proj_of_adj hG hR hP (fun h => ?_) hadj
        have := (hq i.1.1 i.1.2).getVert_injOn (show i.2 ≤ (q i.1.1 i.1.2).length by
          rw [hql]; exact hjR) (show 0 ≤ (q i.1.1 i.1.2).length by omega)
          (h.trans (Walk.getVert_zero _).symm)
        omega
    refine card_le_three _ fun i hi i' hi' => ?_
    have he : i.1 = i'.1 := Subtype.ext (proj_unique hG hR (hproj i hi) (hproj i' hi'))
    refine ⟨he, ?_⟩
    obtain ⟨a, j⟩ := i
    obtain ⟨a', j'⟩ := i'
    simp only at he
    subst he
    rw [mem_filter, hIdef, mem_product, mem_Icc] at hi hi'
    have hd := dist_le_two hi'.2 hi.2
    rw [hf] at hd
    simp only at hd
    by_contra hlt
    push Not at hlt
    have hlen := hql a.1 a.2
    have := dist_getVert hG (hq a.1 a.2) (i := j') (k := j - j') (by omega)
    rw [show j' + (j - j') = j by omega] at this
    omega
  have hd : ∀ i ∈ I, Dom G y (f i) := by
    intro i hi
    rw [hIdef, mem_product, mem_Icc] at hi
    have hP := hqP i.1.1 i.1.2 i.2 hi.2.1 hi.2.2
    exact hyd _ (not_free hP.1 hP.reachable)
  have h := card_le_of_mult I f y hy hd 3 hm
  rw [hI] at h
  push_cast at h
  linarith

/-- **The core is a forest.** The degrees inside a set of vertices of a forest sum to at most
twice its size. -/
lemma forest_deg (hG : G.IsAcyclic) (K : Finset V) :
    ∑ v ∈ K, #((G.neighborFinset v).filter (· ∈ K)) ≤ 2 * #K := by
  classical
  set H := G.induce (K : Set V) with hH
  have hHa : H.IsAcyclic := hG.induce _
  have h1 := hHa.ncard_edgeSet_add_card_connectedComponent
  have hcard : Nat.card (K : Set V) = #K := by simp
  have h2 : H.edgeSet.ncard = #H.edgeFinset := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have h3 := H.sum_degrees_eq_twice_card_edges
  have h5 : ∑ v : (K : Set V), H.degree v =
      ∑ v ∈ K, #((G.neighborFinset v).filter (· ∈ K)) := by
    rw [← sum_coe_sort K]
    refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ => mem_coe) _ _ fun v => ?_
    rw [← card_neighborFinset_eq_degree, ← card_map (Function.Embedding.subtype _)]
    congr 1
    ext w
    simp only [mem_map, mem_neighborFinset, Function.Embedding.coe_subtype, mem_filter,
      Equiv.subtypeEquivRight_apply_coe]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.2⟩
    · rintro ⟨ha, hw⟩
      exact ⟨⟨w, hw⟩, ha, rfl⟩
  omega

/-- **Branch vertices.** There are at most `3L` of them, with at most `6L` core neighbours in
total. -/
lemma branch_count (hG : G.IsAcyclic) :
    #(univ.filter (IsBr G R)) ≤ 3 * #(univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1) ∧
      ∑ b ∈ univ.filter (IsBr G R), #(knbr G R b) ≤
        6 * #(univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1) := by
  classical
  set K := univ.filter (Core G R) with hK
  have hF : ∑ v ∈ K, #(knbr G R v) ≤ 2 * #K := by
    have he : ∀ v ∈ K, #(knbr G R v) = #((G.neighborFinset v).filter (· ∈ K)) := fun v _ => by
      congr 1
      ext w
      simp [mem_knbr, hK, mem_neighborFinset]
    rw [sum_congr rfl he]
    exact forest_deg hG K
  have eBr : univ.filter (IsBr G R) = K.filter fun v => ¬ IsP G R v := by
    ext v; simp [hK, IsBr]
  have eL : univ.filter (fun v => Core G R v ∧ #(knbr G R v) ≤ 1) =
      K.filter fun v => #(knbr G R v) ≤ 1 := by
    ext v; simp [hK]
  have hP : ∀ v ∈ K, (IsP G R v ↔ 1 ≤ #(knbr G R v) ∧ #(knbr G R v) ≤ 2) := fun v hv =>
    ⟨fun h => h.2, fun h => ⟨(mem_filter.1 hv).2, h⟩⟩
  have hi : ∀ v ∈ K, (if ¬ IsP G R v then 1 else 0) + 2 ≤
      #(knbr G R v) + 3 * (if #(knbr G R v) ≤ 1 then 1 else 0) := by
    intro v hv
    have h := hP v hv
    by_cases h1 : IsP G R v
    · have := h.1 h1
      split_ifs <;> omega
    · have : ¬ (1 ≤ #(knbr G R v) ∧ #(knbr G R v) ≤ 2) := fun h' => h1 (h.2 h')
      split_ifs <;> omega
  have hii : ∀ v ∈ K, (if ¬ IsP G R v then #(knbr G R v) else 0) + 6 ≤
      3 * #(knbr G R v) + 6 * (if #(knbr G R v) ≤ 1 then 1 else 0) := by
    intro v hv
    have h := hP v hv
    by_cases h1 : IsP G R v
    · have := h.1 h1
      split_ifs <;> omega
    · have : ¬ (1 ≤ #(knbr G R v) ∧ #(knbr G R v) ≤ 2) := fun h' => h1 (h.2 h')
      split_ifs <;> omega
  have s1 := sum_le_sum hi
  have s2 := sum_le_sum hii
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, ← card_filter,
    ← card_filter] at s1
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, smul_eq_mul,
    ← sum_filter, ← card_filter] at s2
  rw [eBr, eL]
  constructor <;> omega

omit [DecidableEq V] in
/-- **Edges between core paths and branch vertices**, counted at the P-ends, are at most the core
degrees of the branch vertices. -/
lemma pbr_count :
    ∑ e ∈ univ.filter (IsP G R), #((knbr G R e).filter fun b => ¬ IsP G R b) ≤
      ∑ b ∈ univ.filter (IsBr G R), #(knbr G R b) := by
  classical
  have h1 : ∀ e, (knbr G R e).filter (fun b => ¬ IsP G R b) =
      (univ.filter (IsBr G R)).filter (G.Adj e) := by
    intro e
    ext b
    simp only [mem_filter, mem_knbr, mem_univ, true_and, IsBr]
    tauto
  simp_rw [h1, card_filter]
  rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  rw [← card_filter]
  refine card_le_card fun e he => ?_
  simp only [mem_filter, mem_univ, true_and] at he
  exact mem_knbr.2 ⟨he.2.symm, he.1.1⟩

omit [DecidableEq V] in
/-- The P-vertices next to a branch vertex. -/
lemma adjbr_count :
    #(univ.filter fun e => IsP G R e ∧ ∃ b, G.Adj e b ∧ IsBr G R b) ≤
      ∑ e ∈ univ.filter (IsP G R), #((knbr G R e).filter fun b => ¬ IsP G R b) := by
  classical
  rw [show univ.filter (fun e => IsP G R e ∧ ∃ b, G.Adj e b ∧ IsBr G R b) =
      (univ.filter (IsP G R)).filter (fun e => ∃ b, G.Adj e b ∧ IsBr G R b) by ext; simp,
    card_filter]
  refine sum_le_sum fun e _ => ?_
  split_ifs with h
  · obtain ⟨b, hadj, hb⟩ := h
    exact card_pos.2 ⟨b, mem_filter.2 ⟨mem_knbr.2 ⟨hadj, hb.1⟩, hb.2⟩⟩
  · exact Nat.zero_le _

omit [DecidableEq V] in
/-- The missing directions at the ends of the core paths. -/
lemma slots_count :
    ∑ e ∈ univ.filter (IsP G R), slots G R e ≤
      #(univ.filter fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) +
        ∑ e ∈ univ.filter (IsP G R), #((knbr G R e).filter fun b => ¬ IsP G R b) := by
  classical
  rw [show univ.filter (fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) =
      (univ.filter (IsP G R)).filter (fun v => #(knbr G R v) ≤ 1) by ext; simp,
    card_filter, ← sum_add_distrib]
  refine sum_le_sum fun e he => ?_
  have hP := (mem_filter.1 he).2
  have hsplit : #(pnbr G R e) + #((knbr G R e).filter fun b => ¬ IsP G R b) =
      #(knbr G R e) := by
    rw [← card_filter_add_card_filter_not (s := knbr G R e) (IsP G R)]
    congr 2
    ext b
    simp only [mem_pnbr, mem_filter, mem_knbr]
    exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  unfold slots
  have := hP.2.1
  have := hP.2.2
  split_ifs <;> omega

/-- **Core paths.** `|P| ≤ 3y(V) + #P₁ + #(P next to Br)`, where `P₁` are the P-vertices with one
core neighbour. -/
theorem card_P_le (hG : G.IsAcyclic) (hR : 1 ≤ R) (y : V → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hyd : ∀ u, ¬ Free G R u → Dom G y u) :
    (#(univ.filter (IsP G R)) : ℝ) ≤ 3 * ∑ v, y v +
      #(univ.filter fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) +
        #(univ.filter fun e => IsP G R e ∧ ∃ b, G.Adj e b ∧ IsBr G R b) := by
  classical
  set I := univ.filter fun z => IsP G R z ∧ ¬ #(knbr G R z) ≤ 1 ∧
    ¬ ∃ b, G.Adj z b ∧ IsBr G R b with hIdef
  have hsub : univ.filter (IsP G R) ⊆ I ∪ univ.filter (fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) ∪
      univ.filter (fun e => IsP G R e ∧ ∃ b, G.Adj e b ∧ IsBr G R b) := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and, mem_union, hIdef] at hz ⊢
    tauto
  have hI : (#I : ℝ) ≤ 3 * ∑ v, y v := by
    refine card_le_of_mult I id y hy (fun z hz => hyd z ?_) 3 fun w => ?_
    · simp only [hIdef, mem_filter, mem_univ, true_and] at hz
      exact not_free hz.1.1 (Reachable.refl z)
    by_cases hw : Core G R w
    · by_cases hwP : IsP G R w
      · calc #(I.filter fun z => w ∈ cnbhd G (id z)) ≤ #(insert w (knbr G R w)) := by
              refine card_le_card fun z hz => ?_
              simp only [mem_filter, hIdef, mem_univ, true_and, id] at hz
              rcases mem_cnbhd.1 hz.2 with h | h
              · exact h ▸ mem_insert_self _ _
              · exact mem_insert_of_mem (mem_knbr.2 ⟨h.symm, hz.1.1.1⟩)
          _ ≤ #(knbr G R w) + 1 := card_insert_le _ _
          _ ≤ 3 := by have := hwP.2.2; omega
      · refine le_trans (le_of_eq (card_eq_zero.2 ?_)) (by norm_num)
        ext z
        simp only [mem_filter, hIdef, mem_univ, true_and, id, notMem_empty, iff_false, not_and]
        intro hzP hz
        rcases mem_cnbhd.1 hz with h | h
        · exact hwP (h ▸ hzP.1)
        · exact hzP.2.2 ⟨w, h, hw, hwP⟩
    · refine (card_le_one.2 fun a ha b hb => ?_).trans (by norm_num)
      simp only [mem_filter, hIdef, mem_univ, true_and, id] at ha hb
      have hpa : Proj G R w a := by
        rcases mem_cnbhd.1 ha.2 with h | h
        · exact absurd (h ▸ ha.1.1.1) hw
        · exact proj_of_nbr ha.1.1.1 h hw
      have hpb : Proj G R w b := by
        rcases mem_cnbhd.1 hb.2 with h | h
        · exact absurd (h ▸ hb.1.1.1) hw
        · exact proj_of_nbr hb.1.1.1 h hw
      exact proj_unique hG hR hpa hpb
  have hc : (#(univ.filter (IsP G R)) : ℝ) ≤ #I +
      #(univ.filter fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) +
        #(univ.filter fun e => IsP G R e ∧ ∃ b, G.Adj e b ∧ IsBr G R b) := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  linarith

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma hairs_empty : hairs G R (∅ : Finset V) = ∅ := by
  ext v
  simp [mem_hairs]

omit [DecidableRel G.Adj] in
lemma sum_card_filter_comm {ι : Type*} [Fintype ι] (X : ι → Finset V) (p : V → Prop)
    [DecidablePred p] :
    ∑ i, #((X i).filter p) = ∑ z ∈ univ.filter p, #(univ.filter fun i => z ∈ X i) := by
  simp only [card_eq_sum_ones]
  exact sum_comm' fun i z => by simp [and_comm]

omit [DecidableEq V] in
lemma isP_of_mem_wX_centre {z u : V} (h : z ∈ wX G R (.inl u)) : IsP G R z := by
  simp only [wX] at h
  split_ifs at h
  · exact (mem_pball.1 h).isP_end
  · exact absurd h (notMem_empty z)

omit [DecidableEq V] in
lemma isP_of_mem_wX_prefix {z : V} {q : V × Fin 2 × Fin R} (h : z ∈ wX G R (.inr (.inl q))) :
    IsP G R z := by
  obtain ⟨e, s, t⟩ := q
  simp only [wX] at h
  split_ifs at h
  · exact (mem_pball.1 h).isP_end
  · exact absurd h (notMem_empty z)

/-- The P-ball windows that contain a P-vertex number exactly `2R+1`. -/
lemma count_windows (hG : G.IsAcyclic) (hR : 1 ≤ R) {z : V} (hz : IsP G R z) :
    #(univ.filter fun u => z ∈ wX G R (.inl u)) +
      #(univ.filter fun q : V × Fin 2 × Fin R => z ∈ wX G R (.inr (.inl q))) = 2 * R + 1 := by
  have h1 : univ.filter (fun u => z ∈ wX G R (.inl u)) = pball G R z R := by
    ext u
    rw [mem_filter, ← mem_wU_centre hG hR hz]
    simp only [mem_univ, true_and, wU]
    exact (mem_hairs_core hG hR hz.1).symm
  have h2 : univ.filter (fun q : V × Fin 2 × Fin R => z ∈ wX G R (.inr (.inl q))) =
      univ.filter (fun q => z ∈ wU G R (.inr (.inl q))) := by
    ext q
    rw [mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    exact (mem_hairs_core hG hR hz.1).symm
  rw [h1, h2, card_prefix hG hR hz]
  exact cover_count hG hz hR

/-- **The boundary count.** For every `y ≥ 0` that dominates the vertices that reach the core,
the windows have total weighted boundary at most `(72/R)·y(V)`. -/
theorem sum_wt_wB_le (hG : G.IsAcyclic) (hR : 1 ≤ R) (y : V → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hyd : ∀ u, ¬ Free G R u → Dom G y u) : ∑ i, wt G R i * #(wB G R i) ≤ 72 / R * ∑ v, y v := by
  set AB := univ.filter fun z => IsP G R z ∧ ∃ b, G.Adj z b ∧ IsBr G R b with hAB
  set Pn := univ.filter (IsP G R) with hPn
  set S := ∑ e ∈ Pn, slots G R e with hS
  -- the windows around P-balls
  have hcu : ∀ u : V, #(wB G R (.inl u)) ≤
      #((wX G R (.inl u)).filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b) +
        2 * (if IsP G R u then 1 else 0) := by
    intro u
    by_cases hu : IsP G R u
    · have hX : wX G R (.inl u) = pball G R u R := by simp [wX, hu]
      have hU : wU G R (.inl u) = hairs G R (pball G R u R) := by simp only [wU]; rw [hX]
      rw [hX]
      simpa [hu] using card_wB_pball hG hR hu R hU
    · have hU : wU G R (.inl u) = ∅ := by
        simp only [wU, wX, hu, ↓reduceIte]
        exact hairs_empty
      simp [wB, hU]
  have hcq : ∀ q : V × Fin 2 × Fin R, #(wB G R (.inr (.inl q))) ≤
      #((wX G R (.inr (.inl q))).filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b) +
        2 * (if IsP G R q.1 ∧ (q.2.1 : ℕ) < slots G R q.1 then 1 else 0) := by
    rintro ⟨e, s, t⟩
    by_cases hq : IsP G R e ∧ (s : ℕ) < slots G R e
    · have hX : wX G R (.inr (.inl (e, s, t))) = pball G R e (R - 1 - t) := by simp [wX, hq]
      have hU : wU G R (.inr (.inl (e, s, t))) = hairs G R (pball G R e (R - 1 - t)) := by
        simp only [wU]; rw [hX]
      rw [hX]
      simpa [hq] using card_wB_pball hG hR hq.1 (R - 1 - t) hU
    · have hU : wU G R (.inr (.inl (e, s, t))) = ∅ := by
        simp only [wU, wX, hq, ↓reduceIte]
        exact hairs_empty
      simp [wB, hU, hq]
  have hvalid : ∑ q : V × Fin 2 × Fin R,
      (if IsP G R q.1 ∧ (q.2.1 : ℕ) < slots G R q.1 then 1 else 0) = R * S := by
    rw [hS, mul_sum, ← Fintype.sum_ite_mem (s := Pn), Fintype.sum_prod_type]
    refine sum_congr rfl fun e _ => ?_
    rw [Fintype.sum_prod_type]
    by_cases he : IsP G R e
    · have hcnt := count_st (slots G R e) R R
      rw [min_eq_right (by unfold slots; omega), min_self] at hcnt
      simp only [he, true_and, hPn, mem_filter, mem_univ, ↓reduceIte]
      rw [mul_comm, ← hcnt]
      refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
      simp [t.isLt]
    · simp [he, hPn]
  have hswap : ∑ u : V, #((wX G R (.inl u)).filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b) +
      ∑ q : V × Fin 2 × Fin R,
        #((wX G R (.inr (.inl q))).filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b) =
      (2 * R + 1) * #AB := by
    rw [sum_card_filter_comm (fun u => wX G R (.inl u)),
      sum_card_filter_comm (fun q => wX G R (.inr (.inl q))), ← sum_add_distrib]
    rw [hAB, show univ.filter (fun z => IsP G R z ∧ ∃ b, G.Adj z b ∧ IsBr G R b) =
      (univ.filter fun z => ∃ b, G.Adj z b ∧ IsBr G R b).filter (IsP G R) by
        ext; simp [and_comm], card_filter, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : IsP G R z
    · simp only [hz, ↓reduceIte, mul_one]
      exact count_windows hG hR hz
    · simp only [hz, ↓reduceIte, mul_zero]
      have e1 : univ.filter (fun u => z ∈ wX G R (.inl u)) = ∅ :=
        filter_eq_empty_iff.2 fun u _ h => hz (isP_of_mem_wX_centre h)
      have e2 : univ.filter (fun q : V × Fin 2 × Fin R => z ∈ wX G R (.inr (.inl q))) = ∅ :=
        filter_eq_empty_iff.2 fun q _ h => hz (isP_of_mem_wX_prefix h)
      simp [e1, e2]
  have hX : (∑ u : V, #(wB G R (.inl u))) + ∑ q : V × Fin 2 × Fin R, #(wB G R (.inr (.inl q)))
      ≤ (2 * R + 1) * #AB + 2 * #Pn + 2 * (R * S) := by
    have h1 := sum_le_sum fun u (_ : u ∈ (univ : Finset V)) => hcu u
    have h2 := sum_le_sum fun q (_ : q ∈ (univ : Finset (V × Fin 2 × Fin R))) => hcq q
    rw [sum_add_distrib, ← mul_sum] at h1 h2
    rw [hvalid] at h2
    have h3 : ∑ u : V, (if IsP G R u then 1 else 0) = #Pn := by rw [hPn, card_filter]
    rw [h3] at h1
    omega
  have hbr : ∀ b : V, #(wB G R (.inr (.inr (.inl b)))) ≤ if IsBr G R b then 1 else 0 := by
    intro b
    by_cases hb : IsBr G R b
    · simp only [hb, ↓reduceIte]
      exact (card_le_card (wB_branch hG hR b)).trans (card_singleton b).le
    · have hU : wU G R (.inr (.inr (.inl b))) = ∅ := by
        simp only [wU, wX, hb, ↓reduceIte]
        exact hairs_empty
      simp [wB, hU]
  have hBs : ∑ b : V, #(wB G R (.inr (.inr (.inl b)))) ≤ #(univ.filter (IsBr G R)) := by
    rw [card_filter]
    exact sum_le_sum fun b _ => hbr b
  -- the sum over the windows
  have hT : ∑ i, wt G R i * #(wB G R i) =
      (((∑ u : V, #(wB G R (.inl u))) + ∑ q : V × Fin 2 × Fin R, #(wB G R (.inr (.inl q))) : ℕ)
        : ℝ) / (2 * R + 1) + ((∑ b : V, #(wB G R (.inr (.inr (.inl b)))) : ℕ) : ℝ) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [wt, wB_free, card_empty, Nat.cast_zero, mul_zero, sum_const_zero, add_zero,
      one_mul]
    push_cast
    rw [← mul_sum, ← mul_sum]
    ring
  -- the counts
  obtain ⟨hBr3, hA6⟩ := branch_count (R := R) hG
  have hM := pbr_count (G := G) (R := R)
  have hAB' := adjbr_count (G := G) (R := R)
  have hS' := slots_count (G := G) (R := R)
  have hP' := card_P_le hG hR y hy hyd
  have hL' := card_L_le hG hR y hy hyd
  have hP1 : #(univ.filter fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) ≤
      #(univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1) :=
    card_le_card fun v hv => by
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      exact ⟨hv.1.1, hv.2⟩
  set Lc := #(univ.filter fun v => Core G R v ∧ #(knbr G R v) ≤ 1)
  set Y := ∑ v, y v
  have hY : 0 ≤ Y := sum_nonneg fun v _ => hy v
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hr0 : (0 : ℝ) < R := by linarith
  have hd : (0 : ℝ) < 2 * R + 1 := by linarith
  have cAB : (#AB : ℝ) ≤ 6 * Lc := by exact_mod_cast hAB'.trans (hM.trans hA6)
  have cS : (S : ℝ) ≤ 7 * Lc := by exact_mod_cast hS'.trans (by omega)
  have cBr : (#(univ.filter (IsBr G R)) : ℝ) ≤ 3 * Lc := by exact_mod_cast hBr3
  have cP : (#Pn : ℝ) ≤ 3 * Y + 7 * Lc := by
    have h1 : (#(univ.filter fun v => IsP G R v ∧ #(knbr G R v) ≤ 1) : ℝ) ≤ Lc := by
      exact_mod_cast hP1
    linarith
  have cX : (((∑ u : V, #(wB G R (.inl u))) + ∑ q : V × Fin 2 × Fin R,
      #(wB G R (.inr (.inl q))) : ℕ) : ℝ) ≤ (2 * R + 1) * #AB + 2 * #Pn + 2 * (R * S) := by
    exact_mod_cast hX
  have cB : ((∑ b : V, #(wB G R (.inr (.inr (.inl b)))) : ℕ) : ℝ) ≤
      #(univ.filter (IsBr G R)) := by exact_mod_cast hBs
  rw [hT, div_mul_eq_mul_div, le_div_iff₀ hr0]
  set Z := (((∑ u : V, #(wB G R (.inl u))) + ∑ q : V × Fin 2 × Fin R,
      #(wB G R (.inr (.inl q))) : ℕ) : ℝ)
  have hZ : Z / (2 * R + 1) * R ≤ R * #AB + #Pn + R * S := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left cX hr0.le, (Nat.cast_nonneg #Pn : (0 : ℝ) ≤ #Pn),
      (Nat.cast_nonneg S : (0 : ℝ) ≤ S)]
  have hL0 : (0 : ℝ) ≤ Lc := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left cAB hr0.le, mul_le_mul_of_nonneg_left cS hr0.le,
    mul_le_mul_of_nonneg_left cB hr0.le, mul_le_mul_of_nonneg_left cBr hr0.le,
    mul_le_mul_of_nonneg_right hr hL0]

end Forest

end Op4
