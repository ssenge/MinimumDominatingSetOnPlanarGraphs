import Op4.ForestLocal

/-!
# Corollary `cor:dichotomy`, first part: without long paths, exact domination is local

Let no path of `G` have `k` vertices (`NoPath G k`). Then every component has diameter below `k`,
so in `k` rounds every vertex sees its component. The algorithm takes a fixed minimum dominating
set of each component, which depends only on the component and its closed neighbourhoods
(`mdsOf`), and every vertex outputs its own membership (`out`).
* `exact_min`: the output is a minimum dominating set of `G`.
* `exact_local`: if `G` and `G'` have no path on `k` vertices and agree within distance `k` of `v`
  (`Forest.Agree`), the outputs at `v` are equal. So the output is computed in `k` rounds.
* `exact_on`: as in `Op4.ForestMain`, the identifiers that are not nodes are isolated vertices;
  on the node set the output is a minimum dominating set of the nodes.
A minor-closed class that excludes `P_k` is closed under subgraphs, so its graphs satisfy
`NoPath G k`; Mathlib has no minor-closed classes, so this step is not stated.
-/

open Finset SimpleGraph

namespace Op4

namespace Exact

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No path of `G` has `k` vertices. -/
def NoPath (G : SimpleGraph V) (k : ℕ) : Prop := ∀ x y (p : G.Walk x y), p.IsPath → p.length + 1 < k

/-- `D` dominates `S` with the closed neighbourhoods `nb`. -/
def DomBy (S : Finset V) (nb : V → Finset V) (D : Finset V) : Prop := ∀ u ∈ S, ∃ w ∈ D, w ∈ nb u

instance (S : Finset V) (nb : V → Finset V) (D : Finset V) : Decidable (DomBy S nb D) := by
  unfold DomBy; infer_instance

/-- A fixed minimum dominating set of `S` inside `S`. It depends on `S` and `nb` only. -/
noncomputable def mdsOf (S : Finset V) (nb : V → Finset V) : Finset V :=
  if h : (S.powerset.filter (DomBy S nb)).Nonempty then (exists_min_image _ card h).choose else ∅

lemma mdsOf_spec {S : Finset V} {nb : V → Finset V} (hS : ∀ u ∈ S, u ∈ nb u) :
    mdsOf S nb ⊆ S ∧ DomBy S nb (mdsOf S nb) ∧
      ∀ D ⊆ S, DomBy S nb D → #(mdsOf S nb) ≤ #D := by
  have hne : (S.powerset.filter (DomBy S nb)).Nonempty :=
    ⟨S, mem_filter.2 ⟨mem_powerset_self S, fun u hu => ⟨u, hu, hS u hu⟩⟩⟩
  have h := (exists_min_image _ card hne).choose_spec
  unfold mdsOf
  rw [dite_eq_left hne]
  obtain ⟨h1, h2⟩ := h
  rw [mem_filter, mem_powerset] at h1
  exact ⟨h1.1, h1.2, fun D hD hd => h2 D (mem_filter.2 ⟨mem_powerset.2 hD, hd⟩)⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- The component of `v`. -/
noncomputable def comp (v : V) : Finset V := univ.filter (G.Reachable v)

/-- The closed neighbourhoods of the vertices of the component of `v`. -/
noncomputable def nbC (v : V) : V → Finset V := fun u => if u ∈ comp G v then cnbhd G u else ∅

/-- **The output** at `v`: membership in the fixed minimum dominating set of its component. -/
noncomputable def out (v : V) : Prop := v ∈ mdsOf (comp G v) (nbC G v)

open Classical in
/-- The output as a set. -/
noncomputable def outSet : Finset V := univ.filter (out G)

variable {G}

lemma mem_comp {v u : V} : u ∈ comp G v ↔ G.Reachable v u := by
  simp [comp]

lemma comp_eq {v u : V} (h : G.Reachable v u) : comp G u = comp G v := by
  ext w
  rw [mem_comp, mem_comp]
  exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

lemma comp_eq_iff {v u : V} : comp G u = comp G v ↔ G.Reachable v u := by
  refine ⟨fun h => ?_, comp_eq⟩
  have : u ∈ comp G u := mem_comp.2 (Reachable.refl u)
  rw [h, mem_comp] at this
  exact this

lemma nbC_eq {v u : V} (h : G.Reachable v u) : nbC G u = nbC G v := by
  unfold nbC
  rw [comp_eq h]

lemma cnbhd_sub_comp {v u : V} (hu : u ∈ comp G v) : cnbhd G u ⊆ comp G v := by
  intro w hw
  simp only [cnbhd, mem_insert, mem_neighborFinset] at hw
  rcases hw with rfl | h
  · exact hu
  · exact mem_comp.2 ((mem_comp.1 hu).trans h.reachable)

lemma spec (v : V) :
    mdsOf (comp G v) (nbC G v) ⊆ comp G v ∧ DomBy (comp G v) (nbC G v) (mdsOf (comp G v) (nbC G v)) ∧
      ∀ D ⊆ comp G v, DomBy (comp G v) (nbC G v) D → #(mdsOf (comp G v) (nbC G v)) ≤ #D :=
  mdsOf_spec fun u hu => by simp only [nbC, hu, ↓reduceIte]; exact mem_insert_self u _

/-- On the component of `v`, the output is the fixed minimum dominating set of the component. -/
lemma outSet_filter (v : V) :
    (outSet G).filter (fun u => comp G u = comp G v) = mdsOf (comp G v) (nbC G v) := by
  ext u
  simp only [outSet, out, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    have hr := comp_eq_iff.1 h2
    rwa [comp_eq hr, nbC_eq hr] at h1
  · intro hu
    have hr := mem_comp.1 ((spec v).1 hu)
    rw [comp_eq hr, nbC_eq hr]
    exact ⟨hu, rfl⟩

/-- **The output is a minimum dominating set of `G`.** -/
theorem exact_min : DomBy univ (cnbhd G) (outSet G) ∧
    ∀ D, DomBy univ (cnbhd G) D → #(outSet G) ≤ #D := by
  refine ⟨fun u _ => ?_, fun D hD => ?_⟩
  · have hu : u ∈ comp G u := mem_comp.2 (Reachable.refl u)
    obtain ⟨w, hw, hwu⟩ := (spec u).2.1 u hu
    simp only [nbC, hu, ↓reduceIte] at hwu
    refine ⟨w, ?_, hwu⟩
    rw [← outSet_filter u] at hw
    exact (mem_filter.1 hw).1
  · have hmap : ∀ x ∈ (univ : Finset V), comp G x ∈ univ.image (comp G) :=
      fun x _ => mem_image_of_mem _ (mem_univ x)
    rw [card_eq_sum_card_fiberwise (fun x _ => hmap x (mem_univ x)),
      card_eq_sum_card_fiberwise (s := D) (fun x _ => hmap x (mem_univ x))]
    refine sum_le_sum fun b hb => ?_
    obtain ⟨v, -, rfl⟩ := mem_image.1 hb
    rw [outSet_filter v]
    refine (spec v).2.2 _ (fun u hu => ?_) (fun u hu => ?_)
    · have := (mem_filter.1 hu).2
      exact mem_comp.2 (comp_eq_iff.1 this)
    · obtain ⟨w, hw, hwu⟩ := hD u (mem_univ u)
      refine ⟨w, mem_filter.2 ⟨hw, ?_⟩, by simp only [nbC, hu, ↓reduceIte]; exact hwu⟩
      exact comp_eq (mem_comp.1 (cnbhd_sub_comp hu hwu))

variable {G' : SimpleGraph V} [DecidableRel G'.Adj] {k : ℕ}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Without paths on `k` vertices, every vertex reachable from `v` is reached by a walk of length
below `k`. -/
lemma short_walk (hG : NoPath G k) {v u : V} (h : G.Reachable v u) :
    ∃ p : G.Walk v u, p.length < k := by
  classical
  obtain ⟨p⟩ := h
  refine ⟨p.bypass, ?_⟩
  have := hG v u p.bypass p.bypass_isPath
  omega

lemma comp_eq_of_agree (hG : NoPath G k) (hG' : NoPath G' k) {v : V} (h : Forest.Agree G G' v k) :
    comp G v = comp G' v := by
  ext u
  rw [mem_comp, mem_comp]
  constructor
  · intro hr
    obtain ⟨p, hp⟩ := short_walk hG hr
    obtain ⟨q, -⟩ := h.walk p hp.le
    exact ⟨q⟩
  · intro hr
    obtain ⟨p, hp⟩ := short_walk hG' hr
    obtain ⟨q, -⟩ := h.walk_back p hp.le
    exact ⟨q⟩

/-- **Locality.** If `G` and `G'` have no path on `k` vertices and agree within distance `k` of
`v`, the outputs at `v` are equal. -/
theorem exact_local (hG : NoPath G k) (hG' : NoPath G' k) {v : V} (h : Forest.Agree G G' v k) :
    out G v ↔ out G' v := by
  have hc := comp_eq_of_agree hG hG' h
  have hn : nbC G v = nbC G' v := by
    funext u
    unfold nbC
    rw [← hc]
    by_cases hu : u ∈ comp G v
    · simp only [hu, ↓reduceIte]
      obtain ⟨p, hp⟩ := short_walk hG (mem_comp.1 hu)
      have hadj := h u ⟨p, hp⟩
      ext w
      simp only [cnbhd, mem_insert, mem_neighborFinset]
      rw [hadj w]
    · simp only [hu, ↓reduceIte]
  unfold out
  rw [hc, hn]

/-- **On a network.** Let `V` be the identifier space and let all edges of `G` lie inside the node
set `S`. On `S` the output is a minimum dominating set of the nodes. -/
theorem exact_on (S : Finset V) (hS : ∀ u w, G.Adj u w → u ∈ S) :
    (∀ u ∈ S, ∃ w ∈ outSet G ∩ S, w ∈ cnbhd G u) ∧
      ∀ D ⊆ S, (∀ u ∈ S, ∃ w ∈ D, w ∈ cnbhd G u) → #(outSet G ∩ S) ≤ #D := by
  obtain ⟨hdom, hmin⟩ := exact_min (G := G)
  have hsub : ∀ u ∈ S, cnbhd G u ⊆ S := fun u hu w hw => by
    simp only [cnbhd, mem_insert, mem_neighborFinset] at hw
    rcases hw with rfl | h
    · exact hu
    · exact hS w u h.symm
  -- the identifiers outside `S` are isolated, so they belong to the output
  have hout : ∀ u, u ∉ S → u ∈ outSet G := fun u hu => by
    obtain ⟨w, hw, hwu⟩ := hdom u (mem_univ u)
    have : w = u := by
      simp only [cnbhd, mem_insert, mem_neighborFinset] at hwu
      rcases hwu with h | h
      · exact h
      · exact absurd (hS u w h) hu
    rwa [this] at hw
  refine ⟨fun u hu => ?_, fun D hD hd => ?_⟩
  · obtain ⟨w, hw, hwu⟩ := hdom u (mem_univ u)
    exact ⟨w, mem_inter.2 ⟨hw, hsub u hu hwu⟩, hwu⟩
  · have h1 : #(outSet G) ≤ #(D ∪ Sᶜ) := hmin _ fun u _ => by
      by_cases hu : u ∈ S
      · obtain ⟨w, hw, hwu⟩ := hd u hu
        exact ⟨w, mem_union_left _ hw, hwu⟩
      · exact ⟨u, mem_union_right _ (mem_compl.2 hu), mem_insert_self u _⟩
    have h2 : #(D ∪ Sᶜ) ≤ #D + #Sᶜ := card_union_le _ _
    have h3 : #(outSet G) = #(outSet G ∩ S) + #Sᶜ := by
      have e : outSet G ∩ Sᶜ = Sᶜ := inter_eq_right.2 fun u hu => hout u (mem_compl.1 hu)
      rw [← card_inter_add_card_sdiff (outSet G) S, sdiff_eq_inter_compl, e]
    omega

end Exact

end Op4
