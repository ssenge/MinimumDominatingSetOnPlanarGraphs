import Op4.ForestBasic

/-!
# Core and hairs of a forest

The core of Theorem `thm:forests`, defined in `G` itself. A *high path* from `v` towards a
neighbour `u` is a path of length `R` that starts with the edge `vu`. The core consists of the
vertices with high paths towards two distinct neighbours.
* `core_mid`: an inner vertex of a path is in the core if, on both sides, the path is long enough
  or ends in the core. Special cases: `core_of_path` and `core_convex` (paper, (a)).
* `Proj u c`: `c` is the only core vertex on a path from `u` to `c`. It is unique
  (`proj_unique`), it exists as soon as `u` reaches the core (`exists_proj`), every path from `u`
  to the core passes through it (`proj_mem_support`), and `dist u c ≤ R` (`proj_dist_le`, paper,
  (b)). The *hair* of `c` is `{u | Proj u c}`. A neighbour of a non-core vertex of a hair lies in
  the same hair (`proj_of_adj`).
* `dist_lt_of_no_core` (paper, (c)): if `u` reaches no core vertex, every vertex it reaches is at
  distance less than `2R`.
* `exists_hair_path` (paper, (d)): a core vertex with at most one core neighbour has a high path
  whose other vertices lie in its hair.
-/

namespace Op4

namespace Forest

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A path of length `R` from `v` whose second vertex is `u`. -/
def HighPath (G : SimpleGraph V) (R : ℕ) (v u : V) : Prop :=
  ∃ (x : V) (p : G.Walk v x), p.IsPath ∧ p.length = R ∧ p.snd = u

/-- `v` is in the core: it has high paths towards two distinct neighbours. -/
def Core (G : SimpleGraph V) (R : ℕ) (v : V) : Prop :=
  ∃ u₁ u₂, u₁ ≠ u₂ ∧ HighPath G R v u₁ ∧ HighPath G R v u₂

/-- `c` is the projection of `u` onto the core. -/
def Proj (G : SimpleGraph V) (R : ℕ) (u c : V) : Prop :=
  Core G R c ∧ ∃ p : G.Walk u c, p.IsPath ∧ ∀ x ∈ p.support, Core G R x → x = c

/-- A path from `v` of length at least `R` gives a high path towards its second vertex. -/
lemma highPath_of_long {R : ℕ} (hR : 1 ≤ R) {v x : V} {p : G.Walk v x} (hp : p.IsPath)
    (hl : R ≤ p.length) : HighPath G R v p.snd := by
  refine ⟨_, p.take R, hp.take R, by rw [Walk.take_length]; omega, ?_⟩
  rw [Walk.snd, Walk.take_getVert]
  congr 1
  omega

/-- A high path starts with an edge. -/
lemma HighPath.adj {R : ℕ} (hR : 1 ≤ R) {v u : V} (h : HighPath G R v u) : G.Adj v u := by
  obtain ⟨x, p, -, hl, rfl⟩ := h
  exact Walk.adj_snd (by rw [Walk.not_nil_iff_lt_length]; omega)

/-- If a path from `z` arrives at `v` from a vertex other than `u`, and `v` has a high path
towards `u`, then `z` has a high path towards the second vertex of the path. -/
lemma highPath_through (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {z v u : V} {p : G.Walk z v}
    (hp : p.IsPath) (hpn : ¬ p.Nil) (hu : HighPath G R v u) (hne : p.penultimate ≠ u) :
    HighPath G R z p.snd := by
  obtain ⟨x, q, hq, hql, hqs⟩ := hu
  have hpq : (p.append q).IsPath := append_isPath hG hp hq (Or.inr (Or.inr (hqs ▸ hne)))
  have h := highPath_of_long hR hpq (by rw [Walk.length_append]; omega)
  rwa [Walk.snd, Walk.getVert_append',
    ite_eq_left (show 1 ≤ p.length from Walk.not_nil_iff_lt_length.1 hpn)] at h

/-- A core vertex has a high path from every path that arrives at it. -/
lemma highPath_through_core (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {z v : V} {p : G.Walk z v}
    (hp : p.IsPath) (hpn : ¬ p.Nil) (hv : Core G R v) : HighPath G R z p.snd := by
  obtain ⟨u₁, u₂, hne, h₁, h₂⟩ := hv
  by_cases h : p.penultimate = u₁
  · exact highPath_through hG hR hp hpn h₂ fun h' => hne (h.symm.trans h')
  · exact highPath_through hG hR hp hpn h₁ h

lemma back_snd {u v : V} (p : G.Walk u v) {i : ℕ} (hi0 : 0 < i) (hi : i ≤ p.length) :
    (p.take i).reverse.snd = p.getVert (i - 1) := by
  rw [Walk.snd, Walk.getVert_reverse, Walk.take_getVert, Walk.take_length]
  congr 1
  omega

lemma fwd_snd {u v : V} (p : G.Walk u v) (i : ℕ) : (p.drop i).snd = p.getVert (i + 1) := by
  rw [Walk.snd, Walk.drop_getVert]

/-- **Inner core vertices.** The vertex at index `i` of a path is in the core if on each side the
path either has length at least `R` or ends in a core vertex. -/
lemma core_mid (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi0 : 0 < i) (hil : i < p.length) (hA : R ≤ i ∨ Core G R a)
    (hB : i + R ≤ p.length ∨ Core G R b) : Core G R (p.getVert i) := by
  have hq : (p.take i).reverse.IsPath := (hp.take i).reverse
  have hqn : ¬ (p.take i).reverse.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_reverse, Walk.take_length]; omega
  have hr : (p.drop i).IsPath := hp.drop i
  have hrn : ¬ (p.drop i).Nil := by rw [Walk.not_nil_iff_lt_length, Walk.drop_length]; omega
  have h1 : HighPath G R (p.getVert i) (p.getVert (i - 1)) := by
    rw [← back_snd p hi0 hil.le]
    rcases hA with hA | hA
    · exact highPath_of_long hR hq (by rw [Walk.length_reverse, Walk.take_length]; omega)
    · exact highPath_through_core hG hR hq hqn hA
  have h2 : HighPath G R (p.getVert i) (p.getVert (i + 1)) := by
    rw [← fwd_snd p i]
    rcases hB with hB | hB
    · exact highPath_of_long hR hr (by rw [Walk.drop_length]; omega)
    · exact highPath_through_core hG hR hr hrn hB
  refine ⟨_, _, fun h => ?_, h1, h2⟩
  have := hp.getVert_injOn (show i - 1 ≤ p.length by omega) (show i + 1 ≤ p.length by omega) h
  omega

/-- The vertex at index `i` of a path with `R ≤ i` and `i + R ≤ length` is in the core. -/
lemma core_of_path (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (h1 : R ≤ i) (h2 : i + R ≤ p.length) : Core G R (p.getVert i) :=
  core_mid hG hR hp (by omega) (by omega) (Or.inl h1) (Or.inl h2)

/-- **Convexity** (paper, (a)). Every vertex of a path between two core vertices is in the core. -/
lemma core_convex (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {a b : V} (ha : Core G R a)
    (hb : Core G R b) {p : G.Walk a b} (hp : p.IsPath) {i : ℕ} (hi : i ≤ p.length) :
    Core G R (p.getVert i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rwa [Walk.getVert_zero]
  rcases eq_or_lt_of_le hi with rfl | hil
  · rwa [Walk.getVert_length]
  exact core_mid hG hR hp hi0 hil (Or.inr ha) (Or.inr hb)

/-- A path that is not trivial does not visit its end before the last step. -/
lemma getVert_ne_end {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ} (hi : i < p.length) :
    p.getVert i ≠ v := by
  intro h
  have := hp.getVert_injOn (show i ≤ p.length by omega) (show p.length ≤ p.length from le_rfl)
    (h.trans (Walk.getVert_length p).symm)
  omega

/-- Every path from `u` to a core vertex passes through the projection of `u`. -/
lemma proj_mem_support (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u c c' : V} (hc : Proj G R u c)
    (hc' : Core G R c') {q : G.Walk u c'} (hq : q.IsPath) : c ∈ q.support := by
  classical
  obtain ⟨hcc, p, hp, hpc⟩ := hc
  set r := (p.reverse.append q).bypass with hr_def
  have hr : r.IsPath := Walk.bypass_isPath _
  have hpr : (p.append r).IsPath := by
    refine append_isPath hG hp hr ?_
    by_cases hpn : p.Nil
    · exact Or.inl hpn
    by_cases hrn : r.Nil
    · exact Or.inr (Or.inl hrn)
    refine Or.inr (Or.inr fun h => ?_)
    have h1 : Core G R r.snd :=
      core_convex hG hR hcc hc' hr (Walk.not_nil_iff_lt_length.1 hrn)
    have h2 : p.penultimate ≠ c :=
      getVert_ne_end hp (by have := Walk.not_nil_iff_lt_length.1 hpn; omega)
    exact h2 (hpc _ (Walk.getVert_mem_support _ _) (h ▸ h1))
  rw [← path_eq hG hpr hq, Walk.mem_support_append_iff]
  exact Or.inl p.end_mem_support

/-- The projection is unique. -/
lemma proj_unique (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u c c' : V} (h : Proj G R u c)
    (h' : Proj G R u c') : c = c' := by
  obtain ⟨hc', p', hp', hpc'⟩ := h'
  exact hpc' c (proj_mem_support hG hR h hc' hp') h.1

/-- A vertex that reaches the core has a projection. -/
lemma exists_proj {R : ℕ} {u c₀ : V} (hc₀ : Core G R c₀) (hr : G.Reachable u c₀) :
    ∃ c, Proj G R u c := by
  classical
  have hex : ∃ n, ∃ c, ∃ p : G.Walk u c, p.IsPath ∧ p.length = n ∧ Core G R c := by
    obtain ⟨p, hp, _⟩ := hr.exists_path_of_dist
    exact ⟨_, c₀, p, hp, rfl, hc₀⟩
  obtain ⟨c, p, hp, hpl, hc⟩ := Nat.find_spec hex
  refine ⟨c, hc, p, hp, fun x hx hxc => ?_⟩
  by_contra hne
  have hlt : (p.takeUntil x hx).length < Nat.find hex := by
    rw [← hpl]; exact Walk.length_takeUntil_lt_length hx hne
  exact Nat.find_min hex hlt ⟨x, p.takeUntil x hx, hp.takeUntil hx, rfl, hxc⟩

/-- A projection path has length at most `R` (paper, (b)). -/
lemma proj_length_le (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u c : V} (hc : Core G R c)
    {p : G.Walk u c} (hp : p.IsPath) (hpc : ∀ x ∈ p.support, Core G R x → x = c) :
    p.length ≤ R := by
  by_contra hlen
  push Not at hlen
  have hz : Core G R (p.getVert R) :=
    core_mid hG hR hp (by omega) hlen (Or.inl le_rfl) (Or.inr hc)
  exact getVert_ne_end hp hlen (hpc _ (Walk.getVert_mem_support _ _) hz)

/-- The distance to the projection is at most `R` (paper, (b)). -/
lemma proj_dist_le (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u c : V} (h : Proj G R u c) :
    G.dist u c ≤ R := by
  obtain ⟨hc, p, hp, hpc⟩ := h
  rw [dist_eq_length hG hp]
  exact proj_length_le hG hR hc hp hpc

/-- **Hairs are closed.** A neighbour of a non-core vertex of the hair of `c` lies in the hair. -/
lemma proj_of_adj (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u c w : V} (h : Proj G R u c)
    (huc : u ≠ c) (hadj : G.Adj u w) : Proj G R w c := by
  obtain ⟨hc, p, hp, hpc⟩ := h
  have hpn : ¬ p.Nil := fun hn => huc hn.eq
  have hu : ¬ Core G R u := fun h' => huc (hpc u p.start_mem_support h')
  by_cases hw : p.snd = w
  · refine ⟨hc, p.tail.copy hw rfl, by rw [Walk.isPath_copy]; exact hp.tail, fun x hx hxc => ?_⟩
    rw [Walk.support_copy, Walk.support_tail_of_not_nil p hpn] at hx
    exact hpc x (List.mem_of_mem_tail hx) hxc
  · have he : hadj.symm.toWalk.IsPath := hadj.symm.isPath_toWalk
    have hq : (hadj.symm.toWalk.append p).IsPath := by
      refine append_isPath hG he hp (Or.inr (Or.inr ?_))
      simp only [Walk.penultimate, Adj.toWalk, Walk.length_cons, Walk.length_nil]
      exact fun h' => hw h'.symm
    refine ⟨hc, _, hq, fun x hx hxc => ?_⟩
    rw [Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · refine proj_unique hG hR ⟨hxc, hadj.toWalk, hadj.isPath_toWalk, fun y hy hyc => ?_⟩
          ⟨hc, p, hp, hpc⟩
        simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact absurd hyc hu
        · rfl
      · exact absurd hxc hu
    · exact hpc x hx hxc

/-- **Core-free components are small** (paper, (c)). -/
lemma dist_lt_of_no_core (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {u x : V}
    (hno : ∀ c, G.Reachable u c → ¬ Core G R c) (hx : G.Reachable u x) : G.dist u x < 2 * R := by
  by_contra hlen
  push Not at hlen
  obtain ⟨p, hp, hpl⟩ := hx.exists_path_of_dist
  have hz := core_of_path hG hR hp (i := R) le_rfl (by omega)
  exact hno _ ⟨p.take R⟩ hz

/-- **Hairs of core leaves** (paper, (d)). A core vertex with at most one core neighbour has a
high path whose vertices other than the start lie in its hair. -/
lemma exists_hair_path (hG : G.IsAcyclic) {R : ℕ} (hR : 1 ≤ R) {c : V} (hc : Core G R c)
    (hdeg : ∀ u₁ u₂, G.Adj c u₁ → G.Adj c u₂ → Core G R u₁ → Core G R u₂ → u₁ = u₂) :
    ∃ (x : V) (q : G.Walk c x), q.IsPath ∧ q.length = R ∧
      ∀ j, 1 ≤ j → j ≤ R → Proj G R (q.getVert j) c := by
  obtain ⟨u₁, u₂, hne, h₁, h₂⟩ := hc
  -- one of the two directions is not in the core
  have key : ∀ u, HighPath G R c u → ¬ Core G R u →
      ∃ (x : V) (q : G.Walk c x), q.IsPath ∧ q.length = R ∧
        ∀ j, 1 ≤ j → j ≤ R → Proj G R (q.getVert j) c := by
    intro u ⟨x, q, hq, hql, hqs⟩ hu
    refine ⟨x, q, hq, hql, fun j hj1 hjR => ?_⟩
    have hcore : ∀ k, 1 ≤ k → k ≤ R → ¬ Core G R (q.getVert k) := by
      intro k hk1 hkR hk
      have hqk : (q.take k).IsPath := hq.take k
      have := core_convex hG hR ⟨u₁, u₂, hne, h₁, h₂⟩ hk hqk
        (show 1 ≤ (q.take k).length by rw [Walk.take_length]; omega)
      rw [Walk.take_getVert, show k ⊓ 1 = 1 by omega] at this
      exact hu (hqs ▸ this)
    refine ⟨⟨u₁, u₂, hne, h₁, h₂⟩, (q.take j).reverse, (hq.take j).reverse, fun y hy hyc => ?_⟩
    rw [Walk.support_reverse, List.mem_reverse, Walk.mem_support_iff_exists_getVert] at hy
    obtain ⟨n, rfl, hn⟩ := hy
    rw [Walk.take_getVert] at hyc ⊢
    rw [Walk.take_length] at hn
    rcases Nat.eq_zero_or_pos (j ⊓ n) with h0 | h0
    · rw [h0, Walk.getVert_zero]
    · exact absurd hyc (hcore _ h0 (by omega))
  by_cases hc₁ : Core G R u₁
  · by_cases hc₂ : Core G R u₂
    · exact absurd (hdeg u₁ u₂ (h₁.adj hR) (h₂.adj hR) hc₁ hc₂) hne
    · exact key u₂ h₂ hc₂
  · exact key u₁ h₁ hc₁

end Forest

end Op4
