import Op4.ForestCount

/-!
# Forests, randomized part of Theorem `thm:forests`

The randomized algorithm on a finite forest `G`, as in the paper.
* Input, from [14] in the README (hypotheses): a set `D` and stars `d : V → V` with
  `d u ∈ D ∩ N[u]` and `d = id` on `D`. The bound `#D ≤ c₀ γ(G)` enters only in
  `forest_rand_approx`.
* `quot G d`: the contraction of the stars, a forest (`quot_acyclic`).
* Coins: i.i.d. real values with an atomless law `μ` (`coins V μ`), for example uniform on
  `[0,1]`. Every vertex draws one; only those in P-balls are read. Ties have probability zero
  (`ties_null`) and are broken by a fixed index (`key`).
* Anchor of a core-path vertex `u`: the vertex of smallest value in the P-ball
  `pball (quot G d) R u R` (`amin`).
* Cuts (`cutSet`): the core edges at a branch vertex, and the core-path edges whose ends have
  different anchors. Clusters (`cl`): the components of `quot G d` minus the cut edges; these are
  the clusters of the paper (`cl_shape`, `cl_core_path`). Every cluster `W` outputs a fixed minimum subset of `V_W`
  that dominates `V_W` (`mdsIn`, `randOut`).

Results.
* `prob_anchor_ne`: adjacent core-path vertices get different anchors with probability at most
  `2/(R+2)`. If their balls differ, the balls differ in at most two vertices and together have at
  least `R + 2` (`card_pball_sdiff_le`, `card_union_ge`), and the anchors can differ only if the
  smallest value lies in the difference (`measure_no_SM_le`).
* `card_outC_le` (integral repair): for every set `C` of cut edges, the output has at most
  `#D* + 2#C` vertices, for every dominating set `D*`.
* `forest_rand`: the output always dominates, its size is integrable, and its expectation is at
  most `#D* + 16#D/R`. With `#E ≤ #D`, `(R+1)L ≤ #D` and at most `6L` branch edges, the expected
  number of cut edges is at most `8#D/R`. `forest_rand_approx`: if `#D ≤ c₀γ` and `R ≥ 16c₀/ε`,
  the expectation is at most `(1+ε)γ`.
* `cluster_radius`: every cluster lies within distance `2R` of one vertex of `quot G d`.
* `randOut_local`, `randOut_local_G`: whether `v` is in the output depends only on the coins within
  distance `5R` of `d v` in `quot G d`, hence within distance `15R+1` of `v` in `G`.

## Not formalized
The LOCAL model on general graphs: that the core, the clusters and the outputs are computed from
neighbourhoods of radius `O(R)` in `G` (only the dependence on the coins is formalized, in
`randOut_local_G`), and the computation of `D` in `O(1)` rounds [14]. The minimum dominating set
of a cluster is a fixed choice, not the lexicographically first one.
-/

namespace Op4

namespace ForestRand

open SimpleGraph Finset MeasureTheory

section Prob

variable {V : Type*}

/-- The law of the coins: i.i.d. values with law `μ`, one per vertex. -/
noncomputable abbrev coins (V : Type*) [Fintype V] (μ : Measure ℝ) : Measure (V → ℝ) :=
  Measure.pi fun _ : V => μ

/-- `s` is the strict minimum of the coins on `S`. -/
def SM (S : Finset V) (s : V) : Set (V → ℝ) := {c | ∀ y ∈ S, y ≠ s → c s < c y}

lemma measurableSet_SM (S : Finset V) (s : V) : MeasurableSet (SM S s) := by
  have : SM S s = ⋂ y ∈ S, {c : V → ℝ | y ≠ s → c s < c y} := by
    ext c; simp [SM]
  rw [this]
  refine Finset.measurableSet_biInter S fun y _ => ?_
  by_cases h : y = s
  · simp [h]
  · simpa [h] using measurableSet_lt (measurable_pi_apply s) (measurable_pi_apply y)

lemma SM_disjoint {S : Finset V} : (S : Set V).PairwiseDisjoint (SM S) := by
  intro s hs t ht hst
  rw [Function.onFun, Set.disjoint_left]
  intro c h1 h2
  have := h1 t ht (Ne.symm hst)
  have := h2 s hs hst
  linarith

lemma swap_mem [DecidableEq V] {S : Finset V} {s t y : V} (hs : s ∈ S) (ht : t ∈ S) (hy : y ∈ S) :
    Equiv.swap s t y ∈ S := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

variable [Fintype V] [DecidableEq V] (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Ties have probability zero. -/
lemma ties_null {a b : V} (hab : a ≠ b) : coins V μ {c | c a = c b} = 0 := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (fun i : V => i = a)
  have hba : ¬ b = a := fun h => hab h.symm
  set T : Set (((i : {i // i = a}) → ℝ) × ((i : {i // ¬ i = a}) → ℝ)) :=
    {z | z.1 ⟨a, rfl⟩ = z.2 ⟨b, hba⟩} with hT
  have hpre : {c : V → ℝ | c a = c b} =
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => ℝ) (fun i : V => i = a) ⁻¹' T := by
    ext c; rfl
  rw [coins, hpre, hp.measure_preimage_equiv]
  have hTm : MeasurableSet T :=
    measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_fst)
      ((measurable_pi_apply _).comp measurable_snd)
  rw [Measure.prod_apply hTm]
  have h0 : ∀ x : (i : {i // i = a}) → ℝ,
      (Measure.pi fun _ : {i // ¬ i = a} => μ) (Prod.mk x ⁻¹' T) = 0 := by
    intro x
    rw [← Measure.pi_hyperplane (fun _ : {i // ¬ i = a} => μ) ⟨b, hba⟩ (x ⟨a, rfl⟩)]
    congr 1
    ext g
    simp [hT, eq_comm]
  simp [h0]

omit [NullSingletonClass μ] in
/-- **Exchangeability.** Every vertex of `S` is the strict minimum with the same probability. -/
lemma measure_SM_eq {S : Finset V} {s t : V} (hs : s ∈ S) (ht : t ∈ S) :
    coins V μ (SM S s) = coins V μ (SM S t) := by
  have h := measurePreserving_arrowCongr' (fun _ : V => μ) (fun _ : V => μ) (Equiv.swap s t)
    (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id μ)
  rw [coins, ← h.measure_preimage_equiv (SM S s)]
  congr 1
  ext c
  have hc : (MeasurableEquiv.arrowCongr' (Equiv.swap s t) (MeasurableEquiv.refl ℝ)) c =
      fun y => c (Equiv.swap s t y) := rfl
  simp only [Set.mem_preimage, hc, SM, Set.mem_ofPred_eq, Equiv.swap_apply_left]
  constructor
  · intro h' y hy hyt
    have := h' (Equiv.swap s t y) (swap_mem hs ht hy) (fun h'' => hyt (by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h''; exact h''))
    rwa [Equiv.swap_apply_self] at this
  · intro h' y hy hys
    exact h' _ (swap_mem hs ht hy) (fun h'' => hys (by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h''; exact h''))

/-- Almost surely some vertex of `S` is the strict minimum. -/
lemma measure_iUnion_SM {S : Finset V} (hS : S.Nonempty) :
    coins V μ (⋃ s ∈ S, SM S s) = 1 := by
  have hm : MeasurableSet (⋃ s ∈ S, SM S s) :=
    Finset.measurableSet_biUnion S fun s _ => measurableSet_SM S s
  rw [← prob_compl_eq_zero_iff hm]
  refine measure_mono_null (t := ⋃ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2),
    {c : V → ℝ | c p.1 = c p.2}) ?_ ?_
  · intro c hc
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hc
    obtain ⟨s, hsS, hmin⟩ := S.exists_min_image c hS
    have hns := hc s hsS
    simp only [SM, Set.mem_ofPred_eq, not_forall, not_lt] at hns
    obtain ⟨y, hy, hys, hle⟩ := hns
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_filter, mem_product]
    exact ⟨(s, y), ⟨⟨hsS, hy⟩, Ne.symm hys⟩, le_antisymm (hmin y hy) hle⟩
  · refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun p hp => ?_
    exact ties_null μ (mem_filter.1 hp).2

/-- Every vertex of `S` is the strict minimum with probability `1/#S`. -/
lemma measure_SM {S : Finset V} {s : V} (hs : s ∈ S) :
    coins V μ (SM S s) = (#S : ENNReal)⁻¹ := by
  have h1 := measure_iUnion_SM μ ⟨s, hs⟩
  rw [measure_biUnion_finset SM_disjoint fun t _ => measurableSet_SM S t] at h1
  rw [sum_congr rfl fun t ht => measure_SM_eq μ ht hs, sum_const, nsmul_eq_mul] at h1
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h1)

/-- **Strict minima.** The strict minimum of `S` misses `S \ T` with probability at most
`#T/#S`. -/
lemma measure_no_SM_le {S T : Finset V} (hS : S.Nonempty) (hTS : T ⊆ S) :
    coins V μ {c | ¬ ∃ s ∈ S \ T, c ∈ SM S s} ≤ (#T : ENNReal) / #S := by
  calc coins V μ {c | ¬ ∃ s ∈ S \ T, c ∈ SM S s}
      ≤ coins V μ ((⋃ s ∈ S, SM S s)ᶜ ∪ ⋃ s ∈ T, SM S s) := by
        refine measure_mono fun c hc => ?_
        simp only [Set.mem_ofPred_eq, not_exists, not_and, mem_sdiff] at hc
        by_cases h : ∃ s ∈ S, c ∈ SM S s
        · obtain ⟨s, hsS, hs⟩ := h
          by_cases hsT : s ∈ T
          · exact Or.inr (Set.mem_biUnion hsT hs)
          · exact absurd hs (hc s ⟨hsS, hsT⟩)
        · left
          simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
          exact fun s hs h' => h ⟨s, hs, h'⟩
    _ ≤ coins V μ (⋃ s ∈ S, SM S s)ᶜ + coins V μ (⋃ s ∈ T, SM S s) := measure_union_le _ _
    _ ≤ 0 + ∑ s ∈ T, coins V μ (SM S s) := by
        gcongr
        · exact le_of_eq ((prob_compl_eq_zero_iff (Finset.measurableSet_biUnion S fun s _ =>
            measurableSet_SM S s)).2 (measure_iUnion_SM μ hS))
        · exact measure_biUnion_finset_le T _
    _ = (#T : ENNReal) / #S := by
        rw [zero_add, sum_congr rfl fun t ht => measure_SM μ (hTS ht), sum_const, nsmul_eq_mul,
          div_eq_mul_inv]

end Prob


section Anchor

variable {V : Type*} [Fintype V]

/-- A fixed injective index of the vertices; it breaks ties between coins. -/
noncomputable def idx (V : Type*) [Fintype V] (x : V) : ℕ := (Fintype.equivFin V x : ℕ)

lemma idx_inj : Function.Injective (idx V) := fun _ _ h =>
  (Fintype.equivFin V).injective (Fin.ext h)

/-- The key of a vertex: its coin, ties broken by the index. -/
noncomputable def key (c : V → ℝ) (x : V) : ℝ ×ₗ ℕ := toLex (c x, idx V x)

lemma key_le_iff (c : V → ℝ) (x y : V) :
    key c x ≤ key c y ↔ c x < c y ∨ c x = c y ∧ idx V x ≤ idx V y :=
  Prod.Lex.toLex_le_toLex

lemma key_inj (c : V → ℝ) : Function.Injective (key c) := fun x y h => by
  have := congrArg (fun z => (ofLex z).2) h
  exact idx_inj this

/-- The anchor: the vertex of `B` with the smallest key (`u` if `B` is empty). -/
noncomputable def amin (B : Finset V) (u : V) (c : V → ℝ) : V :=
  if h : B.Nonempty then (B.exists_min_image (key c) h).choose else u

lemma amin_spec {B : Finset V} (hB : B.Nonempty) (u : V) (c : V → ℝ) :
    amin B u c ∈ B ∧ ∀ y ∈ B, key c (amin B u c) ≤ key c y := by
  unfold amin
  rw [dite_eq_left hB]
  exact (B.exists_min_image (key c) hB).choose_spec

lemma amin_eq_iff {B : Finset V} (hB : B.Nonempty) (u : V) (c : V → ℝ) (x : V) :
    amin B u c = x ↔ x ∈ B ∧ ∀ y ∈ B, key c x ≤ key c y := by
  constructor
  · rintro rfl
    exact amin_spec hB u c
  · rintro ⟨hx, hmin⟩
    obtain ⟨ha, hamin⟩ := amin_spec hB u c
    exact key_inj c (le_antisymm (hamin x hx) (hmin _ ha))

lemma amin_congr {B : Finset V} (hB : B.Nonempty) (u v : V) (c : V → ℝ) :
    amin B u c = amin B v c := by
  unfold amin
  rw [dite_eq_left hB, dite_eq_left hB]

lemma measurableSet_amin_eq (B : Finset V) (u x : V) :
    MeasurableSet {c : V → ℝ | amin B u c = x} := by
  by_cases hB : B.Nonempty
  · have : {c : V → ℝ | amin B u c = x} = {_c | x ∈ B} ∩
        ⋂ y ∈ B, {c : V → ℝ | c x < c y ∨ c x = c y ∧ idx V x ≤ idx V y} := by
      ext c
      simp only [Set.mem_ofPred_eq, amin_eq_iff hB, key_le_iff, Set.mem_inter_iff,
        Set.mem_iInter]
    rw [this]
    refine (MeasurableSet.const _).inter (Finset.measurableSet_biInter B fun y _ => ?_)
    exact (measurableSet_lt (measurable_pi_apply x) (measurable_pi_apply y)).union
      ((measurableSet_eq_fun (measurable_pi_apply x) (measurable_pi_apply y)).inter
        (MeasurableSet.const _))
  · have : {c : V → ℝ | amin B u c = x} = {_c | u = x} := by
      ext c
      simp [amin, hB]
    rw [this]
    exact MeasurableSet.const _

/-- A strict minimum of the coins on a superset of `B` that lies in `B` is the anchor. -/
lemma amin_of_SM {B S : Finset V} {s : V} (hs : s ∈ B) (hBS : B ⊆ S) {c : V → ℝ}
    (hc : c ∈ SM S s) (u : V) : amin B u c = s := by
  rw [amin_eq_iff ⟨s, hs⟩]
  refine ⟨hs, fun y hy => ?_⟩
  by_cases hys : y = s
  · rw [hys]
  · exact (key_le_iff c s y).2 (Or.inl (hc y (hBS hy) hys))

/-- The anchor vector for the balls `B`. -/
noncomputable def avec (B : V → Finset V) (c : V → ℝ) : V → V := fun u => amin (B u) u c

lemma measurableSet_avec_eq (B : V → Finset V) (a : V → V) :
    MeasurableSet {c | avec B c = a} := by
  have : {c | avec B c = a} = ⋂ u, {c | amin (B u) u c = a u} := by
    ext c
    simp [avec, funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun u => measurableSet_amin_eq _ _ _

/-- Every event decided by the anchor vector is measurable. -/
lemma measurableSet_avec [DecidableEq V] (B : V → Finset V) (Q : (V → V) → Prop) :
    MeasurableSet {c | Q (avec B c)} := by
  have : {c | Q (avec B c)} = ⋃ a ∈ {a | Q a}, {c | avec B c = a} := by
    ext c
    simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_avec_eq B a

lemma measurable_avec [DecidableEq V] (B : V → Finset V) {β : Type*} [MeasurableSpace β]
    (g : (V → V) → β) : Measurable fun c => g (avec B c) :=
  fun s _ => measurableSet_avec B (fun a => g a ∈ s)

end Anchor

section Balls

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj] {R : ℕ}

omit [DecidableEq V] in
/-- A vertex of the P-ball of `u` outside the P-ball of a P-neighbour `v` is the end of a P-path
of length exactly `R` that does not start towards `v`. -/
lemma pball_sdiff (hH : H.IsAcyclic) (hR : 1 ≤ R) {u v x : V} (hv : v ∈ pnbr H R u)
    (hx : x ∈ pball H R u R) (hxv : x ∉ pball H R v R) :
    ∃ p : H.Walk u x, p.IsPath ∧ (∀ y ∈ p.support, IsP H R y) ∧ p.length = R ∧ p.snd ≠ v := by
  rw [mem_pball] at hx hxv
  obtain ⟨p, hp, hpP, hpl⟩ := hx
  have hdist : H.dist u x = p.length := dist_eq_length hH hp
  have hlen : p.length = R := by
    by_contra hne
    have hlt : H.dist x u < R := by rw [dist_comm, hdist]; omega
    exact hxv (inPBall_of_adj hH (InPBall.symm ⟨p, hp, hpP, hpl⟩) hlt hv).symm
  refine ⟨p, hp, hpP, hlen, fun hs => hxv ?_⟩
  have hpn : ¬ p.Nil := fun hn => by
    have := hn.length_eq_zero
    omega
  refine ⟨p.tail.copy hs rfl, by rw [Walk.isPath_copy]; exact hp.tail, fun y hy => hpP y ?_, ?_⟩
  · rw [Walk.support_copy, Walk.support_tail_of_not_nil p hpn] at hy
    exact List.mem_of_mem_tail hy
  · have := Walk.length_tail_add_one hpn
    rw [Walk.length_copy]
    omega

/-- At most one vertex of the P-ball of `u` is outside the P-ball of a P-neighbour. -/
lemma card_pball_sdiff_le (hH : H.IsAcyclic) (hR : 1 ≤ R) {u v : V} (hu : IsP H R u)
    (hv : v ∈ pnbr H R u) : #(pball H R u R \ pball H R v R) ≤ 1 := by
  rw [card_le_one]
  intro x hx x' hx'
  rw [mem_sdiff] at hx hx'
  obtain ⟨p, hp, hpP, hpl, hps⟩ := pball_sdiff hH hR hv hx.1 hx.2
  obtain ⟨q, hq, hqP, hql, hqs⟩ := pball_sdiff hH hR hv hx'.1 hx'.2
  have hpn : ¬ p.Nil := fun hn => by have := hn.length_eq_zero; omega
  have hqn : ¬ q.Nil := fun hn => by have := hn.length_eq_zero; omega
  have hp1 : p.snd ∈ pnbr H R u :=
    mem_pnbr.2 ⟨p.adj_snd hpn, hpP _ (p.getVert_mem_support 1)⟩
  have hq1 : q.snd ∈ pnbr H R u :=
    mem_pnbr.2 ⟨q.adj_snd hqn, hqP _ (q.getVert_mem_support 1)⟩
  have he : p.snd = q.snd := eq_of_mem_pnbr hu hv hp1 hq1 (Ne.symm hps) (Ne.symm hqs)
  exact pray_unique hR ⟨p, hp, hpP, hpl, rfl⟩ ⟨q, hq, hqP, hql, he.symm⟩

/-- If the P-ball of `u` sticks out of the P-ball of a P-neighbour `v`, the two balls together
have at least `R + 2` vertices. -/
lemma card_union_ge (hH : H.IsAcyclic) (hR : 1 ≤ R) {u v : V} (hv : v ∈ pnbr H R u) {x : V}
    (hx : x ∈ pball H R u R) (hxv : x ∉ pball H R v R) :
    R + 2 ≤ #(pball H R u R ∪ pball H R v R) := by
  classical
  obtain ⟨p, hp, hpP, hpl, hps⟩ := pball_sdiff hH hR hv hx hxv
  have hsub : insert v p.support.toFinset ⊆ pball H R u R ∪ pball H R v R := by
    intro y hy
    rw [mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · exact mem_union_right _ (mem_pball.2 (inPBall_self (mem_pnbr.1 hv).2 R))
    · refine mem_union_left _ (mem_pball.2 ⟨p.takeUntil y hy, hp.takeUntil hy,
        fun z hz => hpP z (p.support_takeUntil_subset_support hy hz), ?_⟩)
      have := p.length_takeUntil_le_length hy
      omega
  have hvn : v ∉ p.support := by
    intro hvp
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hvp
    have h1 := dist_eq_length hH (hp.take n)
    rw [Walk.take_length, hn, dist_eq_one_iff_adj.2 (mem_pnbr.1 hv).1] at h1
    have hn1 : n = 1 := by omega
    exact hps (by rw [Walk.snd, ← hn, hn1])
  have hcard : #(insert v p.support.toFinset) = R + 2 := by
    rw [card_insert_of_notMem (by rwa [List.mem_toFinset]),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support, hpl]
  rw [← hcard]
  exact card_le_card hsub

end Balls

section CutProb

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj] {R : ℕ}
  (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- **Cut probability.** Adjacent P-vertices get different anchors with probability at most
`2/(R+2)`. -/
lemma prob_anchor_ne (hH : H.IsAcyclic) (hR : 1 ≤ R) {u v : V} (hu : IsP H R u)
    (hv : v ∈ pnbr H R u) :
    coins V μ {c | amin (pball H R u R) u c ≠ amin (pball H R v R) v c} ≤
      (2 : ENNReal) / ((R + 2 : ℕ) : ENNReal) := by
  have hvP : IsP H R v := (mem_pnbr.1 hv).2
  have hu' : u ∈ pnbr H R v := mem_pnbr.2 ⟨(mem_pnbr.1 hv).1.symm, hu⟩
  have huB : u ∈ pball H R u R := mem_pball.2 (inPBall_self hu R)
  by_cases hB : pball H R u R = pball H R v R
  · have : {c | amin (pball H R u R) u c ≠ amin (pball H R v R) v c} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [← hB]
      exact amin_congr ⟨u, huB⟩ u v c
    rw [this, measure_empty]
    exact zero_le
  have hTS : pball H R u R \ pball H R v R ∪ pball H R v R \ pball H R u R ⊆
      pball H R u R ∪ pball H R v R :=
    union_subset_union sdiff_subset sdiff_subset
  have hT : #(pball H R u R \ pball H R v R ∪ pball H R v R \ pball H R u R) ≤ 2 :=
    (card_union_le _ _).trans (add_le_add (card_pball_sdiff_le hH hR hu hv)
      (card_pball_sdiff_le hH hR hvP hu'))
  have hS : R + 2 ≤ #(pball H R u R ∪ pball H R v R) := by
    by_cases h : ∃ x ∈ pball H R u R, x ∉ pball H R v R
    · obtain ⟨x, hx, hxv⟩ := h
      exact card_union_ge hH hR hv hx hxv
    · have h' : ∃ x ∈ pball H R v R, x ∉ pball H R u R := by
        by_contra h'
        push Not at h h'
        exact hB (Finset.Subset.antisymm h h')
      obtain ⟨x, hx, hxu⟩ := h'
      rw [union_comm]
      exact card_union_ge hH hR hu' hx hxu
  have hSn : (pball H R u R ∪ pball H R v R).Nonempty := ⟨u, mem_union_left _ huB⟩
  calc coins V μ {c | amin (pball H R u R) u c ≠ amin (pball H R v R) v c}
      ≤ coins V μ {c | ¬ ∃ s ∈ (pball H R u R ∪ pball H R v R) \
          (pball H R u R \ pball H R v R ∪ pball H R v R \ pball H R u R),
          c ∈ SM (pball H R u R ∪ pball H R v R) s} := by
        refine measure_mono fun c hc => ?_
        simp only [Set.mem_ofPred_eq] at hc ⊢
        rintro ⟨s, hs, hsm⟩
        have hs' : s ∈ pball H R u R ∧ s ∈ pball H R v R := by
          simp only [mem_sdiff, mem_union] at hs
          tauto
        exact hc ((amin_of_SM hs'.1 subset_union_left hsm u).trans
          (amin_of_SM hs'.2 subset_union_right hsm v).symm)
    _ ≤ (#(pball H R u R \ pball H R v R ∪ pball H R v R \ pball H R u R) : ENNReal) /
          #(pball H R u R ∪ pball H R v R) := measure_no_SM_le μ hSn hTS
    _ ≤ (2 : ENNReal) / ((R + 2 : ℕ) : ENNReal) :=
        ENNReal.div_le_div (by exact_mod_cast hT) (by exact_mod_cast hS)

end CutProb

section Clusters

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A fixed minimum subset of `U` that dominates every vertex of `U`: the integral repair inside
a cluster. -/
noncomputable def mdsIn (U : Finset V) : Finset V :=
  ((U.powerset.filter fun X => ∀ u ∈ U, ∃ w ∈ X, w ∈ cnbhd G u).exists_min_image card
    ⟨U, mem_filter.2 ⟨mem_powerset_self U, fun u hu => ⟨u, hu, mem_cnbhd.2 (Or.inl rfl)⟩⟩⟩).choose

lemma mdsIn_spec (U : Finset V) :
    mdsIn G U ⊆ U ∧ (∀ u ∈ U, ∃ w ∈ mdsIn G U, w ∈ cnbhd G u) ∧
      ∀ X ⊆ U, (∀ u ∈ U, ∃ w ∈ X, w ∈ cnbhd G u) → #(mdsIn G U) ≤ #X := by
  obtain ⟨h1, h2⟩ := ((U.powerset.filter fun X => ∀ u ∈ U, ∃ w ∈ X, w ∈ cnbhd G u).exists_min_image
    card ⟨U, mem_filter.2 ⟨mem_powerset_self U,
      fun u hu => ⟨u, hu, mem_cnbhd.2 (Or.inl rfl)⟩⟩⟩).choose_spec
  rw [mem_filter, mem_powerset] at h1
  exact ⟨h1.1, h1.2, fun X hX hXd => h2 X (mem_filter.2 ⟨mem_powerset.2 hX, hXd⟩)⟩

variable (H : SimpleGraph V) (d : V → V) (C : Finset (Sym2 V))

/-- The cluster of `a`: its component in `H` minus the cut edges. -/
noncomputable def cl (a : V) : Finset V := comp (H.deleteEdges (C : Set (Sym2 V))) a

/-- The vertices of `G` whose star lies in `W`. -/
def VW (W : Finset V) : Finset V := univ.filter fun v => d v ∈ W

/-- The output: every cluster `W` outputs `mdsIn G (VW d W)`. -/
noncomputable def outC : Finset V :=
  (univ.image fun u => cl H C (d u)).biUnion fun W => mdsIn G (VW d W)

open Classical in
/-- The boundary `∂W`: the vertices of `W` with an `H`-neighbour outside `W`. -/
noncomputable def bdry (W : Finset V) : Finset V :=
  univ.filter fun a => d a = a ∧ a ∈ W ∧ ∃ b, H.Adj a b ∧ b ∉ W

open Classical in
/-- All boundary vertices of all clusters. -/
noncomputable def Bd : Finset V := univ.filter fun a => ∃ b, H.Adj a b ∧ b ∉ cl H C a

lemma mem_bdry {W : Finset V} {a : V} :
    a ∈ bdry H d W ↔ d a = a ∧ a ∈ W ∧ ∃ b, H.Adj a b ∧ b ∉ W := by
  simp [bdry]

lemma mem_Bd {a : V} : a ∈ Bd H C ↔ ∃ b, H.Adj a b ∧ b ∉ cl H C a := by
  simp [Bd]

omit [DecidableEq V] in
lemma mem_cl_iff {x y : V} : y ∈ cl H C x ↔ cl H C y = cl H C x :=
  ⟨comp_eq, fun h => h ▸ mem_comp.2 (Reachable.refl _)⟩

/-- **The output dominates.** -/
lemma outC_dom (u : V) : ∃ w ∈ outC G H d C, w ∈ cnbhd G u := by
  have hu : u ∈ VW d (cl H C (d u)) := by
    simp only [VW, mem_filter, mem_univ, true_and]
    exact mem_comp.2 (Reachable.refl _)
  obtain ⟨w, hw, hwu⟩ := (mdsIn_spec G _).2.1 u hu
  exact ⟨w, mem_biUnion.2 ⟨_, mem_image_of_mem _ (mem_univ u), hw⟩, hwu⟩

variable {G H d}

/-- **Integral repair** (paper, `eq:repair`). Inside any `W`, the minimum dominating set of `V_W`
is at most the part of `D*` in `V_W` plus `∂W`. -/
lemma card_mdsIn_le (hd : ∀ u, d u = u ∨ G.Adj u (d u)) (hdd : ∀ u, d (d u) = d u)
    (hHG : ∀ u w, G.Adj u w → d u ≠ d w → H.Adj (d u) (d w))
    {Ds : Finset V} (hDs : ∀ u, ∃ w ∈ Ds, w ∈ cnbhd G u) (W : Finset V) :
    #(mdsIn G (VW d W)) ≤ #(Ds.filter fun v => d v ∈ W) + #(bdry H d W) := by
  refine ((mdsIn_spec G _).2.2 _ (union_subset (fun v hv => ?_) (fun a ha => ?_))
    (fun u hu => ?_)).trans (card_union_le _ _)
  · simp only [VW, mem_filter, mem_univ, true_and] at hv ⊢
    exact hv.2
  · rw [mem_bdry] at ha
    simp only [VW, mem_filter, mem_univ, true_and]
    rw [ha.1]
    exact ha.2.1
  · simp only [VW, mem_filter, mem_univ, true_and] at hu
    obtain ⟨w, hw, hwu⟩ := hDs u
    by_cases hwW : d w ∈ W
    · exact ⟨w, mem_union_left _ (mem_filter.2 ⟨hw, hwW⟩), hwu⟩
    · have hne : w ≠ u := fun h => hwW (h ▸ hu)
      have hadj : G.Adj u w := (mem_cnbhd.1 hwu).resolve_left hne
      have hdne : d u ≠ d w := fun h => hwW (h ▸ hu)
      refine ⟨d u, mem_union_right _
        ((mem_bdry H d).2 ⟨hdd u, hu, d w, hHG u w hadj hdne, hwW⟩), ?_⟩
      rcases hd u with h | h
      · exact mem_cnbhd.2 (Or.inl h)
      · exact mem_cnbhd.2 (Or.inr h)

/-- **Cut edges.** Every cut edge puts at most two vertices into the boundaries. -/
lemma card_Bd_le : #(Bd H C) ≤ 2 * #C := by
  classical
  let f : V → Sym2 V := fun a =>
    if h : ∃ b, H.Adj a b ∧ b ∉ cl H C a then s(a, h.choose) else s(a, a)
  have hfa : ∀ a, a ∈ f a := fun a => by
    simp only [f]
    split_ifs <;> exact Sym2.mem_mk_left _ _
  refine card_le_mul_card_image_of_maps_to (f := f) (fun a ha => ?_) 2 (fun e _ => ?_)
  · rw [mem_Bd] at ha
    have hf : f a = s(a, ha.choose) := by
      simp only [f]
      rw [dite_eq_left ha]
    rw [hf]
    obtain ⟨hab, hbn⟩ := ha.choose_spec
    by_contra hC
    exact hbn (mem_comp.2 (Adj.reachable ((deleteEdges_adj).2 ⟨hab, by simpa using hC⟩)))
  · induction e using Sym2.ind with
    | h p q =>
      refine (card_le_card (t := {p, q}) fun a ha => ?_).trans
        ((card_insert_le _ _).trans (by simp))
      rw [mem_filter] at ha
      have := hfa a
      rw [ha.2, Sym2.mem_iff] at this
      rcases this with rfl | rfl <;> simp

/-- **Size of the output.** For every cut set `C`, the output has at most `#D* + 2#C` vertices. -/
lemma card_outC_le (hd : ∀ u, d u = u ∨ G.Adj u (d u)) (hdd : ∀ u, d (d u) = d u)
    (hHG : ∀ u w, G.Adj u w → d u ≠ d w → H.Adj (d u) (d w))
    (hHd : ∀ a b, H.Adj a b → d a = a)
    {Ds : Finset V} (hDs : ∀ u, ∃ w ∈ Ds, w ∈ cnbhd G u) :
    #(outC G H d C) ≤ #Ds + 2 * #C := by
  have h1 : #(outC G H d C) ≤ ∑ W ∈ univ.image (fun u => cl H C (d u)),
      (#(Ds.filter fun v => d v ∈ W) + #(bdry H d W)) :=
    card_biUnion_le.trans (sum_le_sum fun W _ => card_mdsIn_le hd hdd hHG hDs W)
  have h2 : ∑ W ∈ univ.image (fun u => cl H C (d u)), #(Ds.filter fun v => d v ∈ W) = #Ds := by
    rw [card_eq_sum_card_fiberwise (f := fun v => cl H C (d v))
      (t := univ.image (fun u => cl H C (d u)))
      (by intro v _; exact mem_image_of_mem _ (mem_univ v))]
    refine sum_congr rfl fun W hW => ?_
    obtain ⟨u, -, rfl⟩ := mem_image.1 hW
    congr 1
    exact filter_congr fun v _ => mem_cl_iff H C
  have h3 : ∑ W ∈ univ.image (fun u => cl H C (d u)), #(bdry H d W) ≤ #(Bd H C) := by
    rw [card_eq_sum_card_fiberwise (f := fun a => cl H C a) (s := Bd H C)
      (t := univ.image (fun u => cl H C (d u))) ?_]
    · refine sum_le_sum fun W hW => card_le_card fun a ha => ?_
      obtain ⟨u, -, rfl⟩ := mem_image.1 hW
      obtain ⟨-, haW, b, hab, hbW⟩ := (mem_bdry H d).1 ha
      have hcl : cl H C a = cl H C (d u) := (mem_cl_iff H C).1 haW
      rw [mem_filter, mem_Bd]
      exact ⟨⟨b, hab, by rwa [hcl]⟩, hcl⟩
    · intro a ha
      obtain ⟨b, hab, -⟩ := (mem_Bd H C).1 ha
      exact mem_image.2 ⟨a, mem_univ a, by rw [hHd a b hab]⟩
  have h4 := card_Bd_le (H := H) C
  rw [sum_add_distrib, h2] at h1
  omega

end Clusters

section Count

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj] {R : ℕ}

open scoped Classical

/-- A forest whose edges lie in `D` has at most `#D` edges. -/
lemma card_edgeFinset_le (hH : H.IsAcyclic) {D : Finset V} (hHD : ∀ a b, H.Adj a b → a ∈ D) :
    #H.edgeFinset ≤ #D := by
  have h1 := H.sum_degrees_eq_twice_card_edges
  have h0 : ∀ v ∈ univ, v ∉ D → H.degree v = 0 := fun v _ hv => by
    rw [← card_neighborFinset_eq_degree, card_eq_zero, eq_empty_iff_forall_notMem]
    intro w hw
    rw [mem_neighborFinset] at hw
    exact hv (hHD v w hw)
  have h2 : ∑ v, H.degree v = ∑ v ∈ D, #((H.neighborFinset v).filter (· ∈ D)) := by
    rw [← sum_subset (subset_univ D) h0]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_neighborFinset_eq_degree, filter_true_of_mem fun w hw => ?_]
    rw [mem_neighborFinset] at hw
    exact hHD w v hw.symm
  have h3 := forest_deg hH D
  omega

/-- **Hairs of core leaves.** `(R + 1)·L ≤ #D`. -/
lemma card_L_mul_le (hH : H.IsAcyclic) (hR : 1 ≤ R) {D : Finset V}
    (hHD : ∀ a b, H.Adj a b → a ∈ D) :
    (R + 1) * #(univ.filter fun v => Core H R v ∧ #(knbr H R v) ≤ 1) ≤ #D := by
  set Ls := univ.filter fun v => Core H R v ∧ #(knbr H R v) ≤ 1 with hLs
  have hx : ∀ c ∈ Ls, ∃ X : Finset V, #X = R + 1 ∧ X ⊆ D ∧ ∀ y ∈ X, Proj H R y c := by
    intro c hc
    rw [hLs, mem_filter] at hc
    obtain ⟨-, hcC, hc1⟩ := hc
    have hdeg : ∀ u₁ u₂, H.Adj c u₁ → H.Adj c u₂ → Core H R u₁ → Core H R u₂ → u₁ = u₂ :=
      fun u₁ u₂ h1 h2 hc1' hc2' =>
        card_le_one.1 hc1 u₁ (mem_knbr.2 ⟨h1, hc1'⟩) u₂ (mem_knbr.2 ⟨h2, hc2'⟩)
    obtain ⟨x, q, hq, hql, hqP⟩ := exists_hair_path hH hR hcC hdeg
    refine ⟨q.support.toFinset, ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [List.toFinset_card_of_nodup hq.support_nodup, Walk.length_support, hql]
    · rw [List.mem_toFinset] at hy
      obtain ⟨n, rfl, hn⟩ := Walk.mem_support_iff_exists_getVert.1 hy
      rcases Nat.lt_or_ge n q.length with h | h
      · exact hHD _ _ (q.adj_getVert_succ h)
      · have := q.adj_getVert_succ (i := n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega] at this
        exact hHD _ _ this.symm
    · rw [List.mem_toFinset] at hy
      obtain ⟨n, rfl, hn⟩ := Walk.mem_support_iff_exists_getVert.1 hy
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [Walk.getVert_zero]
        exact proj_self hcC
      · exact hqP n hn0 (by omega)
  choose! X hX using hx
  have hdisj : (Ls : Set V).PairwiseDisjoint X := by
    intro c hc c' hc' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    exact hne (proj_unique hH hR ((hX c hc).2.2 y hy) ((hX c' hc').2.2 y hy'))
  have hsub : Ls.biUnion X ⊆ D := biUnion_subset.2 fun c hc => (hX c hc).2.1
  have := card_le_card hsub
  rw [card_biUnion hdisj, sum_congr rfl fun c hc => (hX c hc).1, sum_const, smul_eq_mul] at this
  linarith

/-- The core edges at branch vertices. -/
noncomputable def brE (H : SimpleGraph V) [DecidableRel H.Adj] (R : ℕ) : Finset (Sym2 V) :=
  H.edgeFinset.filter fun e => ∃ x y, e = s(x, y) ∧ H.Adj x y ∧ Core H R x ∧ Core H R y ∧
    (IsBr H R x ∨ IsBr H R y)

/-- **Branch edges.** There are at most `6L` core edges at branch vertices. -/
lemma card_brE_le (hH : H.IsAcyclic) :
    #(brE H R) ≤ 6 * #(univ.filter fun v => Core H R v ∧ #(knbr H R v) ≤ 1) := by
  have hsub : brE H R ⊆
      (univ.filter (IsBr H R)).biUnion fun b => (knbr H R b).image fun y => s(b, y) := by
    intro e he
    simp only [brE, mem_filter] at he
    obtain ⟨-, x, y, rfl, hxy, hx, hy, hb⟩ := he
    rw [mem_biUnion]
    rcases hb with hb | hb
    · exact ⟨x, mem_filter.2 ⟨mem_univ _, hb⟩, mem_image.2 ⟨y, mem_knbr.2 ⟨hxy, hy⟩, rfl⟩⟩
    · exact ⟨y, mem_filter.2 ⟨mem_univ _, hb⟩,
        mem_image.2 ⟨x, mem_knbr.2 ⟨hxy.symm, hx⟩, Sym2.eq_swap⟩⟩
  calc #(brE H R) ≤ ∑ b ∈ univ.filter (IsBr H R), #((knbr H R b).image fun y => s(b, y)) :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ b ∈ univ.filter (IsBr H R), #(knbr H R b) := sum_le_sum fun b _ => card_image_le
    _ ≤ _ := (branch_count hH).2

end Count

section Contract

variable {V : Type*} (G : SimpleGraph V) (d : V → V)

/-- The contraction of the stars `d⁻¹(a)`. -/
def quot : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ u w, d u = a ∧ d w = b ∧ G.Adj u w
  symm := ⟨fun _ _ h => by
    obtain ⟨h, u, w, hu, hw, huw⟩ := h
    exact ⟨Ne.symm h, w, u, hw, hu, huw.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G d}

lemma quot_adj_of {u w : V} (h : G.Adj u w) (hne : d u ≠ d w) : (quot G d).Adj (d u) (d w) :=
  ⟨hne, u, w, rfl, rfl, h⟩

lemma quot_adj_fix (hdd : ∀ u, d (d u) = d u) {a b : V} (h : (quot G d).Adj a b) : d a = a := by
  obtain ⟨-, u, w, rfl, -, -⟩ := h
  exact hdd u

/-- **The contraction of a forest is a forest.** -/
lemma quot_acyclic (hG : G.IsAcyclic) (hd : ∀ u, d u = u ∨ G.Adj u (d u))
    (hdd : ∀ u, d (d u) = d u) : (quot G d).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [isBridge_iff]
  intro hr
  obtain ⟨hne, u, w, rfl, rfl, huw⟩ := hab
  have hstar : ∀ x, (G.deleteEdges {s(u, w)}).Reachable x (d x) := by
    intro x
    rcases hd x with h | h
    · rw [h]
    · refine Adj.reachable ((deleteEdges_adj).2 ⟨h, fun he => ?_⟩)
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at he
      rcases he with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · exact hne (by rw [← h2, hdd])
      · exact hne (by rw [← h2, hdd])
  have hlift : ∀ a' b', ((quot G d).deleteEdges {s(d u, d w)}).Adj a' b' →
      (G.deleteEdges {s(u, w)}).Reachable a' b' := by
    intro a' b' h
    rw [deleteEdges_adj] at h
    obtain ⟨⟨-, u', w', rfl, rfl, huw'⟩, hnot⟩ := h
    refine ((hstar u').symm.trans ?_).trans (hstar w')
    refine Adj.reachable ((deleteEdges_adj).2 ⟨huw', fun he => hnot ?_⟩)
    rw [Set.mem_singleton_iff] at he ⊢
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  have key : ∀ {x y : V} (p : ((quot G d).deleteEdges {s(d u, d w)}).Walk x y),
      (G.deleteEdges {s(u, w)}).Reachable x y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hlift _ _ h).trans ih
  obtain ⟨p⟩ := hr
  have : (G.deleteEdges {s(u, w)}).Reachable u w := ((hstar u).trans (key p)).trans (hstar w).symm
  rw [isAcyclic_iff_forall_adj_isBridge] at hG
  exact (isBridge_iff.1 (hG huw)) this

end Contract

section Main

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable instance quotDecRel (G : SimpleGraph V) (d : V → V) :
    DecidableRel (quot G d).Adj :=
  Classical.decRel _

variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → V) (R : ℕ)

/-- The P-balls of radius `R` in the contracted forest. -/
noncomputable def balls (u : V) : Finset V := pball (quot G d) R u R

open Classical in
/-- The cut edges for the anchor vector `a`: core edges at a branch vertex, and edges of core
paths whose ends have different anchors. -/
noncomputable def cutSet (a : V → V) : Finset (Sym2 V) :=
  (quot G d).edgeFinset.filter fun e => ∃ x y, e = s(x, y) ∧ (quot G d).Adj x y ∧
    Core (quot G d) R x ∧ Core (quot G d) R y ∧
      (IsBr (quot G d) R x ∨ IsBr (quot G d) R y ∨ a x ≠ a y)

/-- **The randomized algorithm.** The output for the coins `c`: every cluster `W` outputs a fixed
minimum subset of `V_W` that dominates `V_W`. -/
noncomputable def randOut (c : V → ℝ) : Finset V :=
  outC G (quot G d) d (cutSet G d R (avec (balls G d R) c))

/-- `e` is an edge of a core path whose ends have different anchors. -/
def AnE (H : SimpleGraph V) [DecidableRel H.Adj] (a : V → V) (e : Sym2 V) : Prop :=
  ∃ x y, e = s(x, y) ∧ H.Adj x y ∧ IsP H R x ∧ IsP H R y ∧ a x ≠ a y

open Classical in
/-- The edges of core paths whose ends have different anchors. -/
noncomputable def anE (H : SimpleGraph V) [DecidableRel H.Adj] (a : V → V) : Finset (Sym2 V) :=
  H.edgeFinset.filter (AnE R H a)

variable {G d R}

omit [DecidableRel G.Adj] in
lemma cutSet_subset (a : V → V) :
    cutSet G d R a ⊆ brE (quot G d) R ∪ anE R (quot G d) a := by
  intro e he
  simp only [cutSet, mem_filter] at he
  obtain ⟨heE, x, y, rfl, hxy, hx, hy, h⟩ := he
  by_cases hb : IsBr (quot G d) R x ∨ IsBr (quot G d) R y
  · refine mem_union_left _ ?_
    simp only [brE, mem_filter]
    exact ⟨heE, x, y, rfl, hxy, hx, hy, hb⟩
  · have h' : a x ≠ a y := by tauto
    push Not at hb
    have hxP : IsP (quot G d) R x := by
      by_contra hn
      exact hb.1 ⟨hx, hn⟩
    have hyP : IsP (quot G d) R y := by
      by_contra hn
      exact hb.2 ⟨hy, hn⟩
    refine mem_union_right _ ?_
    simp only [anE, mem_filter]
    exact ⟨heE, x, y, rfl, hxy, hxP, hyP, h'⟩

/-- **The randomized algorithm always outputs a dominating set.** -/
theorem randOut_dom (c : V → ℝ) (u : V) : ∃ w ∈ randOut G d R c, w ∈ cnbhd G u :=
  outC_dom G _ d _ u

/-- The pointwise size bound: `#out ≤ #D* + 2(#brE + #anE)`. -/
lemma card_randOut_le {D : Finset V} (hD : ∀ u, d u ∈ D) (hd : ∀ u, d u = u ∨ G.Adj u (d u))
    (hDd : ∀ a ∈ D, d a = a) {Ds : Finset V} (hDs : ∀ u, ∃ w ∈ Ds, w ∈ cnbhd G u) (c : V → ℝ) :
    #(randOut G d R c) ≤
      #Ds + 2 * (#(brE (quot G d) R) + #(anE R (quot G d) (avec (balls G d R) c))) := by
  have hdd : ∀ u, d (d u) = d u := fun u => hDd _ (hD u)
  have h1 := card_outC_le (C := cutSet G d R (avec (balls G d R) c)) hd hdd
    (fun u w h hne => quot_adj_of h hne) (fun a b h => quot_adj_fix hdd h) hDs
  have h2 := (card_le_card (cutSet_subset (G := G) (d := d) (R := R)
    (avec (balls G d R) c))).trans (card_union_le _ _)
  unfold randOut
  omega

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [DecidableRel G.Adj] in
/-- Every edge is a cut edge of a core path with probability at most `2/(R+2)`. -/
lemma prob_AnE_le (hH : (quot G d).IsAcyclic) (hR : 1 ≤ R) (e : Sym2 V) :
    (coins V μ).real {c | AnE R (quot G d) (avec (balls G d R) c) e} ≤ 2 / (R + 2) := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : (quot G d).Adj x y ∧ IsP (quot G d) R x ∧ IsP (quot G d) R y
    · have hsub : {c | AnE R (quot G d) (avec (balls G d R) c) s(x, y)} ⊆
          {c | amin (pball (quot G d) R x R) x c ≠ amin (pball (quot G d) R y R) y c} := by
        intro c hc
        obtain ⟨x', y', he, -, -, -, hne⟩ := hc
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hne
        · exact Ne.symm hne
      have h1 := (measure_mono hsub).trans
        (prob_anchor_ne μ hH hR hxy.2.1 (mem_pnbr.2 ⟨hxy.1, hxy.2.2⟩))
      rw [measureReal_def]
      calc _ ≤ ((2 : ENNReal) / ((R + 2 : ℕ) : ENNReal)).toReal :=
            ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp)) h1
        _ = 2 / (R + 2) := by
            rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
            simp
    · have : {c | AnE R (quot G d) (avec (balls G d R) c) s(x, y)} = ∅ := by
        ext c
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', y', he, hadj, hx', hy', -⟩
        apply hxy
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hadj, hx', hy'⟩
        · exact ⟨hadj.symm, hy', hx'⟩
      rw [this, measureReal_empty]
      positivity

/-- **Theorem `thm:forests`, randomized part.** On a forest `G`, with a set `D` and stars
`d : V → V` as in the paper (`d u ∈ D ∩ N[u]`, `d = id` on `D`), and i.i.d. atomless coins, the
randomized algorithm always outputs a dominating set, its size is integrable, and its expected
size is at most `#D* + 16 #D / R` for every dominating set `D*`. -/
theorem forest_rand (hG : G.IsAcyclic) {D : Finset V} (hD : ∀ u, d u ∈ D)
    (hd : ∀ u, d u = u ∨ G.Adj u (d u)) (hDd : ∀ a ∈ D, d a = a) (hR : 1 ≤ R) :
    (∀ c u, ∃ w ∈ randOut G d R c, w ∈ cnbhd G u) ∧
      Integrable (fun c => (#(randOut G d R c) : ℝ)) (coins V μ) ∧
      ∀ Ds : Finset V, (∀ u, ∃ w ∈ Ds, w ∈ cnbhd G u) →
        ∫ c, (#(randOut G d R c) : ℝ) ∂(coins V μ) ≤ #Ds + 16 * #D / R := by
  have hdd : ∀ u, d (d u) = d u := fun u => hDd _ (hD u)
  have hH : (quot G d).IsAcyclic := quot_acyclic hG hd hdd
  have hHD : ∀ a b, (quot G d).Adj a b → a ∈ D := fun a b h => by
    obtain ⟨-, u, w, rfl, -, -⟩ := h
    exact hD u
  have hF : Integrable (fun c => (#(randOut G d R c) : ℝ)) (coins V μ) := by
    refine Integrable.of_bound ?_ (Fintype.card V) (ae_of_all _ fun c => ?_)
    · exact (measurable_avec (balls G d R)
        (fun a => (#(outC G (quot G d) d (cutSet G d R a)) : ℝ))).aestronglyMeasurable
    · rw [Real.norm_natCast]
      exact_mod_cast card_le_univ _
  refine ⟨randOut_dom, hF, fun Ds hDs => ?_⟩
  set E := (quot G d).edgeFinset with hE
  have hev : ∀ e, MeasurableSet {c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e} :=
    fun e => measurableSet_avec (balls G d R) (fun a => AnE R (quot G d) a e)
  set K : ℝ := #Ds + 2 * #(brE (quot G d) R) with hK
  have hI : ∀ e, Integrable
      ({c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e}.indicator 1) (coins V μ) :=
    fun e => (integrable_const (1 : ℝ)).indicator (hev e)
  have hInd : Integrable (fun c => ∑ e ∈ E,
      {c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e}.indicator 1 c) (coins V μ) :=
    integrable_finsetSum _ fun e _ => hI e
  have hpt : ∀ c, (#(randOut G d R c) : ℝ) ≤ K + 2 * ∑ e ∈ E,
      {c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e}.indicator 1 c := by
    intro c
    have h1 := card_randOut_le (R := R) hD hd hDd hDs c
    have h2 : ((#(anE R (quot G d) (avec (balls G d R) c)) : ℕ) : ℝ) = ∑ e ∈ E,
        {c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e}.indicator 1 c := by
      rw [anE, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun e _ => ?_
      by_cases h : AnE R (quot G d) (avec (balls G d R) c) e <;> simp [h]
    rw [hK, ← h2]
    have h1' : ((#(randOut G d R c) : ℕ) : ℝ) ≤ ((#Ds + 2 * (#(brE (quot G d) R) +
        #(anE R (quot G d) (avec (balls G d R) c))) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    linarith
  have hint : ∫ c, (#(randOut G d R c) : ℝ) ∂(coins V μ) ≤
      K + 2 * ∑ e ∈ E, (coins V μ).real {c | AnE R (quot G d) (avec (balls G d R) c) e} := by
    refine (integral_mono hF ((integrable_const K).add (hInd.const_mul 2)) hpt).trans (le_of_eq ?_)
    show ∫ c, (K + 2 * ∑ e ∈ E,
      {c : V → ℝ | AnE R (quot G d) (avec (balls G d R) c) e}.indicator 1 c) ∂(coins V μ) = _
    rw [integral_add (integrable_const K) (hInd.const_mul 2), integral_const_mul,
      integral_finsetSum _ fun e _ => hI e]
    simp only [integral_const, probReal_univ, one_smul]
    congr 2
    exact sum_congr rfl fun e _ => integral_indicator_one (hev e)
  have hsum : ∑ e ∈ E, (coins V μ).real {c | AnE R (quot G d) (avec (balls G d R) c) e} ≤
      #E * (2 / (R + 2)) := by
    calc _ ≤ ∑ e ∈ E, (2 / ((R : ℝ) + 2)) := sum_le_sum fun e _ => prob_AnE_le μ hH hR e
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hEle : (#E : ℝ) ≤ #D := by exact_mod_cast card_edgeFinset_le hH hHD
  have hbr := card_brE_le (R := R) hH
  have hL := card_L_mul_le hH hR hHD
  have hbrR : (#(brE (quot G d) R) : ℝ) * R ≤ 6 * #D := by
    have : #(brE (quot G d) R) * R ≤ 6 * #D := by
      have h1 := Nat.mul_le_mul_right R hbr
      nlinarith [hL]
    exact_mod_cast this
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hq : 2 / ((R : ℝ) + 2) * R ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hfin : 2 * (#(brE (quot G d) R) : ℝ) + 2 * (#E * (2 / (R + 2))) ≤ 16 * #D / R := by
    rw [le_div_iff₀ hRpos]
    have : (#E : ℝ) * (2 / (R + 2)) * R ≤ 2 * #D := by
      rw [mul_assoc]
      nlinarith [Nat.cast_nonneg (α := ℝ) #E]
    nlinarith
  rw [hK] at hint
  linarith

/-- **Corollary: `(1 + ε)`-approximation.** If `#D ≤ c₀ γ(G)` (the dominating set of [14] in the
README) and `R ≥ 16 c₀ / ε`, the expected size of the output is at most `(1 + ε)#D*` for every
dominating set `D*`, in particular at most `(1 + ε)γ(G)`. -/
theorem forest_rand_approx (hG : G.IsAcyclic) {D : Finset V} (hD : ∀ u, d u ∈ D)
    (hd : ∀ u, d u = u ∨ G.Adj u (d u)) (hDd : ∀ a ∈ D, d a = a) (hR : 1 ≤ R) {c₀ ε : ℝ}
    (hε : 0 < ε) (hc₀ : ∀ X : Finset V, (∀ u, ∃ w ∈ X, w ∈ cnbhd G u) → (#D : ℝ) ≤ c₀ * #X)
    (hRε : 16 * c₀ / ε ≤ R) (Ds : Finset V) (hDs : ∀ u, ∃ w ∈ Ds, w ∈ cnbhd G u) :
    ∫ c, (#(randOut G d R c) : ℝ) ∂(coins V μ) ≤ (1 + ε) * #Ds := by
  have h := (forest_rand μ hG hD hd hDd hR).2.2 Ds hDs
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h1 := hc₀ Ds hDs
  have h2 : 16 * c₀ ≤ ε * R := by
    rw [div_le_iff₀ hε] at hRε
    linarith
  have h3 : 16 * (#D : ℝ) / R ≤ ε * #Ds := by
    rw [div_le_iff₀ hRpos]
    have hDs0 : (0 : ℝ) ≤ #Ds := Nat.cast_nonneg _
    nlinarith
  linarith

end Main

section Radius

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj] {R : ℕ}

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
/-- If only core edges are cut, a vertex reaches its projection without crossing a cut edge. -/
lemma reach_proj {C : Finset (Sym2 V)}
    (hC : ∀ x y, s(x, y) ∈ C → Core H R x ∧ Core H R y) {v p : V} (h : Proj H R v p) :
    (H.deleteEdges (C : Set (Sym2 V))).Reachable v p := by
  obtain ⟨-, w, -, hw⟩ := h
  induction w with
  | nil => rfl
  | cons hadj w' ih =>
    have hw1 : ∀ x ∈ w'.support, Core H R x → x = _ := fun x hx hxc =>
      hw x (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx) hxc
    refine Reachable.trans (Adj.reachable ((deleteEdges_adj).2 ⟨hadj, fun hm => ?_⟩)) (ih hw1)
    obtain ⟨h1, h2⟩ := hC _ _ (by simpa using hm)
    exact hadj.ne ((hw _ (Walk.start_mem_support _) h1).trans
      (hw1 _ w'.start_mem_support h2).symm)

omit [DecidableEq V] in
/-- Two core vertices of the same cluster are equal, or they are P-vertices with the same anchor:
the uncut core edges join P-vertices with equal anchors. -/
lemma same_anchor {C : Finset (Sym2 V)} {a : V → V}
    (hC : ∀ x y, H.Adj x y → Core H R x → Core H R y → s(x, y) ∉ C →
      IsP H R x ∧ IsP H R y ∧ a x = a y)
    (hH : H.IsAcyclic) (hR : 1 ≤ R) {x y : V} (hx : Core H R x) (hy : Core H R y)
    (hr : (H.deleteEdges (C : Set (Sym2 V))).Reachable x y) :
    x = y ∨ (IsP H R x ∧ IsP H R y ∧ a x = a y) := by
  obtain ⟨q, hq⟩ := hr.exists_isPath
  have hcore : ∀ v ∈ q.support, Core H R v := by
    intro v hv
    have hq' := hq.mapLe (deleteEdges_le (C : Set (Sym2 V)))
    have hv' : v ∈ (q.mapLe (deleteEdges_le (C : Set (Sym2 V)))).support := by
      rwa [Walk.support_mapLe_eq_support]
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hv'
    exact core_convex hH hR hx hy hq' hi
  clear hq hx hy hr
  induction q with
  | nil => exact Or.inl rfl
  | cons hadj q' ih =>
    have h1 := hcore _ (Walk.start_mem_support _)
    have h2 := hcore _ (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ q'.start_mem_support)
    rw [deleteEdges_adj] at hadj
    obtain ⟨hPu, hPv, hav⟩ := hC _ _ hadj.1 h1 h2 (by simpa using hadj.2)
    rcases ih (fun z hz => hcore z (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz))
      with h | ⟨-, hPw, hvw⟩
    · subst h
      exact Or.inr ⟨hPu, hPv, hav⟩
    · exact Or.inr ⟨hPu, hPw, hav.trans hvw⟩

omit [DecidableEq V] in
/-- The anchor of a P-vertex is within distance `R`. -/
lemma dist_amin_le {x : V} (hx : IsP H R x) (c : V → ℝ) :
    H.Reachable (amin (pball H R x R) x c) x ∧ H.dist (amin (pball H R x R) x c) x ≤ R := by
  have h := (amin_spec ⟨x, mem_pball.2 (inPBall_self hx R)⟩ x c).1
  obtain ⟨p, -, -, hpl⟩ := mem_pball.1 h
  rw [SimpleGraph.dist_comm]
  exact ⟨p.reachable.symm, (dist_le p).trans hpl⟩

end Radius

section ClusterRadius

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : V → V} {R : ℕ}

omit [DecidableRel G.Adj] in
lemma core_of_mem_cutSet {a : V → V} {x y : V} (h : s(x, y) ∈ cutSet G d R a) :
    Core (quot G d) R x ∧ Core (quot G d) R y := by
  simp only [cutSet, mem_filter] at h
  obtain ⟨-, x', y', he, -, hx, hy, -⟩ := h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hx, hy⟩
  · exact ⟨hy, hx⟩

omit [DecidableRel G.Adj] in
lemma not_cut {a : V → V} {x y : V} (hxy : (quot G d).Adj x y) (hx : Core (quot G d) R x)
    (hy : Core (quot G d) R y) (h : s(x, y) ∉ cutSet G d R a) :
    IsP (quot G d) R x ∧ IsP (quot G d) R y ∧ a x = a y := by
  have hP : ¬ (IsBr (quot G d) R x ∨ IsBr (quot G d) R y ∨ a x ≠ a y) := fun hb => h (by
    simp only [cutSet, mem_filter]
    exact ⟨by simpa using hxy, x, y, rfl, hxy, hx, hy, hb⟩)
  push Not at hP
  refine ⟨?_, ?_, hP.2.2⟩
  · by_contra hn
    exact hP.1 ⟨hx, hn⟩
  · by_contra hn
    exact hP.2.1 ⟨hy, hn⟩

omit [DecidableRel G.Adj] in
/-- **Cluster radius.** Every cluster lies within distance `2R` (in the contracted forest) of a
single vertex: the common anchor of its core vertices, its branch vertex, or any of its vertices if
it misses the core. -/
theorem cluster_radius (hH : (quot G d).IsAcyclic) (hR : 1 ≤ R) (c : V → ℝ) (v : V) :
    ∃ z, ∀ b ∈ cl (quot G d) (cutSet G d R (avec (balls G d R) c)) v,
      (quot G d).Reachable z b ∧ (quot G d).dist z b ≤ 2 * R := by
  classical
  have hC1 : ∀ x y, s(x, y) ∈ cutSet G d R (avec (balls G d R) c) →
      Core (quot G d) R x ∧ Core (quot G d) R y := fun x y h => core_of_mem_cutSet h
  have hC2 : ∀ x y, (quot G d).Adj x y → Core (quot G d) R x → Core (quot G d) R y →
      s(x, y) ∉ cutSet G d R (avec (balls G d R) c) →
      IsP (quot G d) R x ∧ IsP (quot G d) R y ∧
        avec (balls G d R) c x = avec (balls G d R) c y :=
    fun x y hxy hx hy h => not_cut hxy hx hy h
  by_cases hK : ∃ k, Core (quot G d) R k ∧ (quot G d).Reachable v k
  · obtain ⟨k, hk, hvk⟩ := hK
    obtain ⟨p, hp⟩ := exists_proj hk hvk
    have hvp := reach_proj hC1 hp
    refine ⟨if IsP (quot G d) R p then avec (balls G d R) c p else p, fun b hb => ?_⟩
    have hvb := mem_comp.1 hb
    obtain ⟨pb, hpb⟩ := exists_proj hk ((hvb.mono (deleteEdges_le _)).symm.trans hvk)
    have hdb : (quot G d).dist pb b ≤ R := by
      rw [SimpleGraph.dist_comm]
      exact proj_dist_le hH hR hpb
    have hrb : (quot G d).Reachable pb b := hpb.reachable.symm
    rcases same_anchor hC2 hH hR hp.1 hpb.1 ((hvp.symm.trans hvb).trans (reach_proj hC1 hpb))
      with h | ⟨hPp, hPpb, hapb⟩
    · subst h
      split_ifs with hPp
      · obtain ⟨hz1, hz2⟩ := dist_amin_le hPp c
        have := hrb.dist_triangle_right (avec (balls G d R) c p)
        simp only [avec, balls] at this ⊢
        exact ⟨hz1.trans hrb, by omega⟩
      · exact ⟨hrb, by omega⟩
    · simp only [hPp, ↓reduceIte]
      rw [hapb]
      obtain ⟨hz1, hz2⟩ := dist_amin_le hPpb c
      have := hrb.dist_triangle_right (avec (balls G d R) c pb)
      simp only [avec, balls] at this ⊢
      exact ⟨hz1.trans hrb, by omega⟩
  · push Not at hK
    refine ⟨v, fun b hb => ?_⟩
    have hr := (mem_comp.1 hb).mono (deleteEdges_le _)
    exact ⟨hr, (dist_lt_of_no_core hH hR (fun k hr hk => hK k hk hr) hr).le.trans (by omega)⟩

end ClusterRadius

section Locality

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The anchor depends only on the coins in the ball. -/
lemma amin_congr_coins {B : Finset V} {c c' : V → ℝ} (h : ∀ y ∈ B, c y = c' y) (u : V) :
    amin B u c = amin B u c' := by
  by_cases hB : B.Nonempty
  · obtain ⟨hm, hmin⟩ := amin_spec hB u c
    rw [eq_comm, amin_eq_iff hB u c']
    have hk : ∀ y ∈ B, key c' y = key c y := fun y hy => by
      unfold key
      rw [h y hy]
    refine ⟨hm, fun y hy => ?_⟩
    rw [hk _ hm, hk y hy]
    exact hmin y hy
  · simp [amin, hB]

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V} {R : ℕ}

omit [DecidableRel G.Adj] in
lemma mem_cutSet {a : V → V} {x y : V} :
    s(x, y) ∈ cutSet G d R a ↔ (quot G d).Adj x y ∧ Core (quot G d) R x ∧
      Core (quot G d) R y ∧ (IsBr (quot G d) R x ∨ IsBr (quot G d) R y ∨ a x ≠ a y) := by
  simp only [cutSet, mem_filter]
  constructor
  · rintro ⟨-, x', y', he, hxy, hx, hy, hb⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxy, hx, hy, hb⟩
    · refine ⟨hxy.symm, hy, hx, ?_⟩
      rcases hb with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Ne.symm h))
  · rintro ⟨hxy, hx, hy, hb⟩
    exact ⟨by simpa using hxy, x, y, rfl, hxy, hx, hy, hb⟩

lemma mem_outC_iff {H : SimpleGraph V} {C : Finset (Sym2 V)} {v : V} :
    v ∈ outC G H d C ↔ v ∈ mdsIn G (VW d (cl H C (d v))) := by
  constructor
  · intro hv
    obtain ⟨W, hW, hvW⟩ := mem_biUnion.1 hv
    obtain ⟨u, -, rfl⟩ := mem_image.1 hW
    have h1 := (mdsIn_spec G _).1 hvW
    simp only [VW, mem_filter, mem_univ, true_and] at h1
    rwa [(mem_cl_iff H C).1 h1]
  · intro hv
    exact mem_biUnion.2 ⟨_, mem_image_of_mem _ (mem_univ v), hv⟩

omit [DecidableRel G.Adj] in
/-- If the coins agree within distance `5R` of `v`, the cluster of `v` for the first coins is
contained in its cluster for the second coins. -/
lemma cl_subset (hH : (quot G d).IsAcyclic) (hR : 1 ≤ R) {c c' : V → ℝ} {v : V}
    (hcc : ∀ x, (quot G d).Reachable v x → (quot G d).dist v x ≤ 5 * R → c x = c' x) :
    cl (quot G d) (cutSet G d R (avec (balls G d R) c)) v ⊆
      cl (quot G d) (cutSet G d R (avec (balls G d R) c')) v := by
  obtain ⟨z, hz⟩ := cluster_radius hH hR c v
  have hvv : v ∈ cl (quot G d) (cutSet G d R (avec (balls G d R) c)) v :=
    mem_comp.2 (Reachable.refl _)
  have hnear : ∀ b ∈ cl (quot G d) (cutSet G d R (avec (balls G d R) c)) v,
      (quot G d).Reachable v b ∧ (quot G d).dist v b ≤ 4 * R := by
    intro b hb
    obtain ⟨hzb, hzb'⟩ := hz b hb
    obtain ⟨hzv, hzv'⟩ := hz v hvv
    have h1 := hzv.symm.dist_triangle_left b
    have h2 : (quot G d).dist v z = (quot G d).dist z v := SimpleGraph.dist_comm
    exact ⟨hzv.symm.trans hzb, by omega⟩
  have hanc : ∀ x, (quot G d).Reachable v x → (quot G d).dist v x ≤ 4 * R →
      avec (balls G d R) c x = avec (balls G d R) c' x := by
    intro x hx hdx
    refine amin_congr_coins (fun y hy => ?_) x
    obtain ⟨p, -, -, hpl⟩ := mem_pball.1 hy
    have h1 := hx.dist_triangle_left y
    have h2 := dist_le p
    exact hcc y (hx.trans p.reachable) (by omega)
  have key : ∀ {x b : V}
      (q : ((quot G d).deleteEdges (cutSet G d R (avec (balls G d R) c) : Set (Sym2 V))).Walk x b),
      (∀ y ∈ q.support, (quot G d).Reachable v y ∧ (quot G d).dist v y ≤ 4 * R) →
      ((quot G d).deleteEdges (cutSet G d R (avec (balls G d R) c') : Set (Sym2 V))).Reachable
        x b := by
    intro x b q hq
    induction q with
    | nil => rfl
    | cons hadj q' ih =>
      have hx := hq _ (Walk.start_mem_support _)
      have hx1 := hq _ (by
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ q'.start_mem_support)
      rw [deleteEdges_adj] at hadj
      refine Reachable.trans (Adj.reachable ((deleteEdges_adj).2 ⟨hadj.1, fun hm => hadj.2 ?_⟩))
        (ih fun y hy => hq y (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hy))
      rw [mem_coe, mem_cutSet] at hm ⊢
      rwa [hanc _ hx.1 hx.2, hanc _ hx1.1 hx1.2]
  intro b hb
  obtain ⟨q⟩ := mem_comp.1 hb
  refine mem_comp.2 (key q fun y hy => hnear y (mem_comp.2 ⟨q.takeUntil y hy⟩))

/-- **Locality of the coins.** Whether `v` is in the output depends only on the coins within
distance `5R` of `d v` in the contracted forest. -/
theorem randOut_local (hH : (quot G d).IsAcyclic) (hR : 1 ≤ R) {c c' : V → ℝ} {v : V}
    (hcc : ∀ x, (quot G d).Reachable (d v) x → (quot G d).dist (d v) x ≤ 5 * R → c x = c' x) :
    v ∈ randOut G d R c ↔ v ∈ randOut G d R c' := by
  have heq := Subset.antisymm (cl_subset hH hR hcc)
    (cl_subset hH hR (c := c') (c' := c) fun x hx hd => (hcc x hx hd).symm)
  unfold randOut
  rw [mem_outC_iff, mem_outC_iff, heq]

end Locality

section Shape

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : V → V} {R : ℕ}

open Classical in
/-- **The clusters are those of the paper.** A cluster that meets the core consists of the hairs
of its core vertices; a cluster that misses the core is a whole component of the contracted
forest. -/
theorem cl_shape (a : V → V) (v : V) :
    ((∃ k, Core (quot G d) R k ∧ (quot G d).Reachable v k) →
      cl (quot G d) (cutSet G d R a) v =
        hairs (quot G d) R ((cl (quot G d) (cutSet G d R a) v).filter (Core (quot G d) R))) ∧
    ((¬ ∃ k, Core (quot G d) R k ∧ (quot G d).Reachable v k) →
      cl (quot G d) (cutSet G d R a) v = comp (quot G d) v) := by
  have hC1 : ∀ x y, s(x, y) ∈ cutSet G d R a → Core (quot G d) R x ∧ Core (quot G d) R y :=
    fun x y h => core_of_mem_cutSet h
  constructor
  · rintro ⟨k, hk, hvk⟩
    ext b
    rw [mem_hairs]
    constructor
    · intro hb
      have hvb := mem_comp.1 hb
      obtain ⟨pb, hpb⟩ := exists_proj hk ((hvb.mono (deleteEdges_le _)).symm.trans hvk)
      exact ⟨pb, mem_filter.2 ⟨mem_comp.2 (hvb.trans (reach_proj hC1 hpb)), hpb.1⟩, hpb⟩
    · rintro ⟨c, hc, hbc⟩
      rw [mem_filter] at hc
      exact mem_comp.2 ((mem_comp.1 hc.1).trans (reach_proj hC1 hbc).symm)
  · intro hK
    push Not at hK
    ext b
    constructor
    · intro hb
      exact mem_comp.2 ((mem_comp.1 hb).mono (deleteEdges_le _))
    · intro hb
      obtain ⟨q⟩ := mem_comp.1 hb
      suffices h : ∀ {x y : V} (q : (quot G d).Walk x y), (quot G d).Reachable v x →
          ((quot G d).deleteEdges (cutSet G d R a : Set (Sym2 V))).Reachable x y from
        mem_comp.2 (h q (Reachable.refl _))
      intro x y q hx
      induction q with
      | nil => rfl
      | cons hadj q' ih =>
        refine (Adj.reachable ((deleteEdges_adj).2 ⟨hadj, fun hm => ?_⟩)).trans
          (ih (hx.trans hadj.reachable))
        exact hK _ (hC1 _ _ (by simpa using hm)).1 hx

omit [Fintype V] [DecidableEq V] in
/-- The core vertices of a cluster are joined inside the core: in a forest, the path between two
core vertices of a cluster avoids the cut edges and consists of core vertices. So the core part of a
cluster is a component of `H[K]` minus the cut edges, as in the paper. -/
theorem cl_core_path {H : SimpleGraph V} (hH : H.IsAcyclic) (hR : 1 ≤ R) {C : Set (Sym2 V)}
    {x y : V} (hx : Core H R x) (hy : Core H R y) (hr : (H.deleteEdges C).Reachable x y) :
    ∃ q : (H.deleteEdges C).Walk x y, q.IsPath ∧ ∀ z ∈ q.support, Core H R z := by
  obtain ⟨q, hq⟩ := hr.exists_isPath
  refine ⟨q, hq, fun z hz => ?_⟩
  have hz' : z ∈ (q.mapLe (deleteEdges_le C)).support := by
    rwa [Walk.support_mapLe_eq_support]
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hz'
  exact core_convex hH hR hx hy (hq.mapLe (deleteEdges_le C)) hi

end Shape

section LocalG

open Forest

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : V → V} {R : ℕ}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A walk of length `k` in the contracted forest gives a walk of length at most `3k` in `G`. -/
lemma quot_reach_dist (hd : ∀ u, d u = u ∨ G.Adj u (d u)) {a x : V} (q : (quot G d).Walk a x) :
    G.Reachable a x ∧ G.dist a x ≤ 3 * q.length := by
  have hs : ∀ y, G.Reachable (d y) y ∧ G.dist (d y) y ≤ 1 := fun y => by
    rcases hd y with h | h
    · rw [h]
      simp
    · exact ⟨h.symm.reachable, (dist_eq_one_iff_adj.2 h.symm).le⟩
  induction q with
  | nil => simp
  | @cons a' b' x' hadj q' ih =>
    rw [Walk.length_cons]
    obtain ⟨h4, h4'⟩ := ih
    obtain ⟨-, u, w, rfl, rfl, huw⟩ := hadj
    obtain ⟨h1, h1'⟩ := hs u
    obtain ⟨h3, h3'⟩ := hs w
    have t1 := h1.dist_triangle_left x'
    have t2 := huw.reachable.dist_triangle_left x'
    have t3 := h3.symm.dist_triangle_left x'
    have e2 : G.dist u w = 1 := dist_eq_one_iff_adj.2 huw
    have e3 : G.dist w (d w) = G.dist (d w) w := SimpleGraph.dist_comm
    exact ⟨h1.trans (huw.reachable.trans (h3.symm.trans h4)), by omega⟩

/-- **Locality of the coins in `G`.** Whether `v` is in the output depends only on the coins
within distance `15R + 1` of `v` in `G`. -/
theorem randOut_local_G (hG : G.IsAcyclic) {D : Finset V} (hD : ∀ u, d u ∈ D)
    (hd : ∀ u, d u = u ∨ G.Adj u (d u)) (hDd : ∀ a ∈ D, d a = a) (hR : 1 ≤ R) {c c' : V → ℝ}
    {v : V} (hcc : ∀ x, G.Reachable v x → G.dist v x ≤ 15 * R + 1 → c x = c' x) :
    v ∈ randOut G d R c ↔ v ∈ randOut G d R c' := by
  have hdd : ∀ u, d (d u) = d u := fun u => hDd _ (hD u)
  refine randOut_local (quot_acyclic hG hd hdd) hR fun x hx hdx => hcc x ?_ ?_
  · obtain ⟨q, -⟩ := hx.exists_walk_length_eq_dist
    have hvd : G.Reachable v (d v) := by
      rcases hd v with h | h
      · rw [h]
      · exact h.reachable
    exact hvd.trans (quot_reach_dist hd q).1
  · obtain ⟨q, hq⟩ := hx.exists_walk_length_eq_dist
    obtain ⟨h1, h2⟩ := quot_reach_dist hd q
    have hvd : G.Reachable v (d v) ∧ G.dist v (d v) ≤ 1 := by
      rcases hd v with h | h
      · rw [h]
        simp
      · exact ⟨h.reachable, (dist_eq_one_iff_adj.2 h).le⟩
    have t := hvd.1.dist_triangle_left x
    rw [hq] at h2
    omega

end LocalG

end ForestRand

end Op4
