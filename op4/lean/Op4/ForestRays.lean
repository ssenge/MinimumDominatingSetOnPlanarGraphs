import Op4.ForestCore

/-!
# Core paths of a forest

The core vertices with one or two core neighbours (`IsP`) form the core paths of Theorem
`thm:forests`. The other core vertices are the branch vertices (`IsBr`). A *P-path* is a path
whose vertices are all P-vertices.
* `pray_unique`: a P-path from `c` is determined by its length and its second vertex. So a P-vertex
  `c` has one ray in each of its at most two P-directions (`ray`); capped at `k`, the ray towards
  `w` has length `rlen c w k`.
* `sum_pball`: the P-ball `pball c k`, the set of ends of P-paths of length at most `k` from `c`,
  consists of `c` and these rays.
* `slots e = 2 - #(P-neighbours of e)` counts the missing directions at `e`. Along a ray it is `0`
  before the last vertex, and `1` at the last vertex if the ray stops before `k` (`slots_ray_lt`,
  `slots_ray_last`).
* `cover_count`, the cover identity: `#(pball c k) + ∑_{e ∈ pball c k} slots e·(k - d(c,e)) = 2k+1`.
  On the line through `c`, extended by `slots e` virtual rays at every end `e`, it counts the
  positions within distance `k` of `c`.
* `card_psphere_le`: at most two vertices of `pball c k` are at distance exactly `k ≥ 1` from `c`.
-/

namespace Op4

namespace Forest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {R : ℕ}

open Classical in
/-- The core neighbours of `v`. -/
noncomputable def knbr (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : Finset V :=
  (G.neighborFinset v).filter (Core G R)

/-- A core vertex with one or two core neighbours. -/
def IsP (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : Prop :=
  Core G R v ∧ 1 ≤ #(knbr G R v) ∧ #(knbr G R v) ≤ 2

/-- A branch vertex: a core vertex with no core neighbour or with at least three. -/
def IsBr (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : Prop :=
  Core G R v ∧ ¬ IsP G R v

open Classical in
/-- The P-neighbours of `v`. -/
noncomputable def pnbr (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : Finset V :=
  (G.neighborFinset v).filter (IsP G R)

/-- The number of missing P-directions at `v`. -/
noncomputable def slots (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (v : V) : ℕ :=
  2 - #(pnbr G R v)

lemma mem_knbr {v u : V} : u ∈ knbr G R v ↔ G.Adj v u ∧ Core G R u := by
  simp [knbr]

lemma mem_pnbr {v u : V} : u ∈ pnbr G R v ↔ G.Adj v u ∧ IsP G R u := by
  simp [pnbr]

lemma pnbr_subset_knbr (v : V) : pnbr G R v ⊆ knbr G R v := fun u hu => by
  rw [mem_pnbr] at hu
  exact mem_knbr.2 ⟨hu.1, hu.2.1⟩

lemma card_pnbr_le {v : V} (h : IsP G R v) : #(pnbr G R v) ≤ 2 :=
  (card_le_card (pnbr_subset_knbr v)).trans h.2.2

/-- A P-vertex has at most two P-neighbours. -/
lemma eq_of_mem_pnbr {z a b c : V} (hz : IsP G R z) (ha : a ∈ pnbr G R z) (hb : b ∈ pnbr G R z)
    (hc : c ∈ pnbr G R z) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  by_contra hbc
  have := two_lt_card_iff.2 ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  have := card_pnbr_le hz
  omega

/-- A P-ray: a P-path from `c` to `x` of length `k` whose second vertex is `w`. -/
def PRay (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (c w : V) (k : ℕ) (x : V) : Prop :=
  ∃ p : G.Walk c x, p.IsPath ∧ (∀ y ∈ p.support, IsP G R y) ∧ p.length = k ∧ p.snd = w

/-- Two P-paths from `c` with the same second vertex agree as long as both go on. -/
lemma ppath_agree {c x x' : V} {p : G.Walk c x} {q : G.Walk c x'} (hp : p.IsPath)
    (hq : q.IsPath) (hpP : ∀ y ∈ p.support, IsP G R y) (hqP : ∀ y ∈ q.support, IsP G R y)
    (hs : p.snd = q.snd) : ∀ i, i + 1 ≤ p.length → i + 1 ≤ q.length →
      p.getVert i = q.getVert i ∧ p.getVert (i + 1) = q.getVert (i + 1) := by
  intro i
  induction i with
  | zero =>
    intro _ _
    exact ⟨by rw [Walk.getVert_zero, Walk.getVert_zero], hs⟩
  | succ i ih =>
    intro hp1 hq1
    obtain ⟨h0, h1⟩ := ih (by omega) (by omega)
    refine ⟨h1, ?_⟩
    have hz : IsP G R (p.getVert (i + 1)) := hpP _ (Walk.getVert_mem_support _ _)
    have ha : p.getVert i ∈ pnbr G R (p.getVert (i + 1)) :=
      mem_pnbr.2 ⟨(p.adj_getVert_succ (by omega)).symm, hpP _ (Walk.getVert_mem_support _ _)⟩
    have hb : p.getVert (i + 1 + 1) ∈ pnbr G R (p.getVert (i + 1)) :=
      mem_pnbr.2 ⟨p.adj_getVert_succ (by omega), hpP _ (Walk.getVert_mem_support _ _)⟩
    have hc : q.getVert (i + 1 + 1) ∈ pnbr G R (p.getVert (i + 1)) := by
      rw [h1]
      exact mem_pnbr.2 ⟨q.adj_getVert_succ (by omega), hqP _ (Walk.getVert_mem_support _ _)⟩
    have hab : p.getVert i ≠ p.getVert (i + 1 + 1) := fun h => by
      have := hp.getVert_injOn (show i ≤ p.length by omega) (show i + 1 + 1 ≤ p.length by omega) h
      omega
    have hac : p.getVert i ≠ q.getVert (i + 1 + 1) := fun h => by
      rw [h0] at h
      have := hq.getVert_injOn (show i ≤ q.length by omega) (show i + 1 + 1 ≤ q.length by omega) h
      omega
    exact eq_of_mem_pnbr hz ha hb hc hab hac

/-- A P-ray is determined by its start, its second vertex and its length. -/
lemma pray_unique {c w x x' : V} {k : ℕ} (hk : 1 ≤ k) (h : PRay G R c w k x)
    (h' : PRay G R c w k x') : x = x' := by
  obtain ⟨p, hp, hpP, hpl, hps⟩ := h
  obtain ⟨q, hq, hqP, hql, hqs⟩ := h'
  have h := (ppath_agree hp hq hpP hqP (hps.trans hqs.symm) (k - 1) (by omega) (by omega)).2
  have e1 : p.getVert k = x := by rw [← hpl, Walk.getVert_length]
  have e2 : q.getVert k = x' := by rw [← hql, Walk.getVert_length]
  rwa [show k - 1 + 1 = k by omega, e1, e2] at h

/-- In a forest, the end of a P-ray determines its second vertex and its length. -/
lemma pray_inj (hG : G.IsAcyclic) {c w w' x : V} {j j' : ℕ} (h : PRay G R c w j x)
    (h' : PRay G R c w' j' x) : w = w' ∧ j = j' := by
  obtain ⟨p, hp, -, rfl, rfl⟩ := h
  obtain ⟨p', hp', -, rfl, rfl⟩ := h'
  rw [path_eq hG hp hp']
  exact ⟨rfl, rfl⟩

/-- The initial segments of a P-path are P-rays. -/
lemma pray_getVert {c x : V} {p : G.Walk c x} (hp : p.IsPath) (hpP : ∀ y ∈ p.support, IsP G R y)
    {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ p.length) : PRay G R c p.snd j (p.getVert j) := by
  refine ⟨p.take j, hp.take j, fun y hy => hpP y ?_, by rw [Walk.take_length]; omega, ?_⟩
  · rw [Walk.support_take] at hy
    exact List.mem_of_mem_take hy
  · rw [Walk.snd, Walk.take_getVert]
    congr 1
    omega

/-- A P-ray can be shortened. -/
lemma pray_le {c w x : V} {k : ℕ} (h : PRay G R c w k x) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ y, PRay G R c w j y := by
  obtain ⟨p, hp, hpP, hpl, rfl⟩ := h
  exact ⟨_, pray_getVert hp hpP hj (by omega)⟩

/-- A P-path extended by a P-neighbour of its end that is not its penultimate vertex. -/
lemma pray_concat (hG : G.IsAcyclic) {c x z : V} {p : G.Walk c x} (hp : p.IsPath)
    (hpP : ∀ y ∈ p.support, IsP G R y) (hpn : ¬ p.Nil) (hz : z ∈ pnbr G R x)
    (hne : z ≠ p.penultimate) : PRay G R c p.snd (p.length + 1) z := by
  obtain ⟨hadj, hzP⟩ := mem_pnbr.1 hz
  have hzs : z ∉ p.support := fun h => hne (hG.eq_penultimate_of_adj_end hp hadj h)
  refine ⟨p.concat hadj, hp.concat hzs hadj, fun y hy => ?_, Walk.length_concat _ _, ?_⟩
  · rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hpP y hy
    · exact hzP
  · rw [Walk.snd, Walk.concat_eq_append, Walk.getVert_append',
      ite_eq_left (show 1 ≤ p.length from Walk.not_nil_iff_lt_length.1 hpn)]

lemma pray_one {c w : V} (hc : IsP G R c) (hw : w ∈ pnbr G R c) : PRay G R c w 1 w := by
  obtain ⟨hadj, hwP⟩ := mem_pnbr.1 hw
  refine ⟨hadj.toWalk, hadj.isPath_toWalk, fun y hy => ?_, rfl, rfl⟩
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with rfl | rfl
  · exact hc
  · exact hwP

open Classical in
/-- The length of the ray from `c` towards `w`, capped at `k`. -/
noncomputable def rlen (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (c w : V) (k : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ∃ x, PRay G R c w j x) k

open Classical in
/-- The vertex at distance `j` on the ray from `c` towards `w`. -/
noncomputable def ray (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (c w : V) (j : ℕ) : V :=
  if h : ∃ x, PRay G R c w j x then h.choose else c

lemma ray_spec {c w : V} {j : ℕ} (h : ∃ x, PRay G R c w j x) :
    PRay G R c w j (ray G R c w j) := by
  unfold ray
  rw [dite_eq_left h]
  exact h.choose_spec

lemma rlen_le {c w : V} {k : ℕ} : rlen G R c w k ≤ k := by
  classical
  exact Nat.findGreatest_le k

lemma one_le_rlen {c w : V} (hc : IsP G R c) (hw : w ∈ pnbr G R c) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ rlen G R c w k := by
  classical
  unfold rlen
  exact Nat.le_findGreatest hk ⟨w, pray_one hc hw⟩

lemma ray_pray {c w : V} (hc : IsP G R c) (hw : w ∈ pnbr G R c) {k j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ rlen G R c w k) : PRay G R c w j (ray G R c w j) := by
  have hk : 1 ≤ k := le_trans (le_trans hj hjk) rlen_le
  have hx : ∃ x, PRay G R c w (rlen G R c w k) x := by
    classical
    unfold rlen
    exact Nat.findGreatest_spec (P := fun j => ∃ x, PRay G R c w j x) hk ⟨w, pray_one hc hw⟩
  obtain ⟨x, hx⟩ := hx
  exact ray_spec (pray_le hx hj hjk)

lemma not_pray_of_rlen_lt {c w : V} {k j : ℕ} (h1 : rlen G R c w k < j) (h2 : j ≤ k) :
    ¬ ∃ x, PRay G R c w j x := by
  classical
  unfold rlen at h1
  exact Nat.findGreatest_is_greatest h1 h2

/-- `x` is the end of a P-path of length at most `k` from `c`. -/
def InPBall (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (c : V) (k : ℕ) (x : V) : Prop :=
  ∃ p : G.Walk c x, p.IsPath ∧ (∀ y ∈ p.support, IsP G R y) ∧ p.length ≤ k

open Classical in
/-- The P-ball of radius `k` around `c`. -/
noncomputable def pball (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (c : V) (k : ℕ) :
    Finset V :=
  univ.filter (InPBall G R c k)

lemma mem_pball {c x : V} {k : ℕ} : x ∈ pball G R c k ↔ InPBall G R c k x := by
  simp [pball]

lemma InPBall.symm {c x : V} {k : ℕ} (h : InPBall G R c k x) : InPBall G R x k c := by
  obtain ⟨p, hp, hpP, hpl⟩ := h
  refine ⟨p.reverse, hp.reverse, fun y hy => hpP y ?_, by rwa [Walk.length_reverse]⟩
  rwa [Walk.support_reverse, List.mem_reverse] at hy

lemma InPBall.isP_start {c x : V} {k : ℕ} (h : InPBall G R c k x) : IsP G R c := by
  obtain ⟨p, -, hpP, -⟩ := h
  exact hpP c p.start_mem_support

lemma InPBall.isP_end {c x : V} {k : ℕ} (h : InPBall G R c k x) : IsP G R x := by
  obtain ⟨p, -, hpP, -⟩ := h
  exact hpP x p.end_mem_support

lemma inPBall_self {c : V} (hc : IsP G R c) (k : ℕ) : InPBall G R c k c :=
  ⟨Walk.nil, Walk.IsPath.nil, fun y hy => by
    rw [Walk.support_nil, List.mem_singleton] at hy
    exact hy ▸ hc, by simp⟩

/-- In a forest, a smaller P-ball is cut out by the distance. -/
lemma inPBall_iff_dist (hG : G.IsAcyclic) {c x : V} {k K : ℕ} (hkK : k ≤ K) :
    InPBall G R c k x ↔ InPBall G R c K x ∧ G.dist c x ≤ k := by
  constructor
  · rintro ⟨p, hp, hpP, hpl⟩
    exact ⟨⟨p, hp, hpP, by omega⟩, by rw [dist_eq_length hG hp]; exact hpl⟩
  · rintro ⟨⟨p, hp, hpP, -⟩, hd⟩
    exact ⟨p, hp, hpP, by rw [← dist_eq_length hG hp]; exact hd⟩

/-- The P-ball consists of the start and the rays. -/
lemma pball_eq [DecidableEq V] {c : V} (hc : IsP G R c) (k : ℕ) :
    pball G R c k = insert c (((pnbr G R c).sigma fun w => Icc 1 (rlen G R c w k)).image
      fun q => ray G R c q.1 q.2) := by
  ext x
  rw [mem_pball, mem_insert, mem_image]
  constructor
  · rintro ⟨p, hp, hpP, hpl⟩
    by_cases hpn : p.Nil
    · exact Or.inl hpn.eq.symm
    right
    have h1 : 1 ≤ p.length := Walk.not_nil_iff_lt_length.1 hpn
    have hw : p.snd ∈ pnbr G R c :=
      mem_pnbr.2 ⟨Walk.adj_snd hpn, hpP _ (Walk.getVert_mem_support _ _)⟩
    have hray : PRay G R c p.snd p.length x := ⟨p, hp, hpP, rfl, rfl⟩
    have hle : p.length ≤ rlen G R c p.snd k := by
      classical
      unfold rlen
      exact Nat.le_findGreatest hpl ⟨x, hray⟩
    exact ⟨⟨p.snd, p.length⟩, mem_sigma.2 ⟨hw, mem_Icc.2 ⟨h1, hle⟩⟩,
      pray_unique h1 (ray_pray hc hw h1 hle) hray⟩
  · rintro (rfl | ⟨⟨w, j⟩, hq, rfl⟩)
    · exact inPBall_self hc k
    · rw [mem_sigma, mem_Icc] at hq
      obtain ⟨p, hp, hpP, hpl, -⟩ := ray_pray hc hq.1 hq.2.1 hq.2.2
      exact ⟨p, hp, hpP, by rw [hpl]; exact le_trans hq.2.2 rlen_le⟩

lemma ray_injOn (hG : G.IsAcyclic) {c : V} (hc : IsP G R c) (k : ℕ) :
    Set.InjOn (fun q : (Σ _ : V, ℕ) => ray G R c q.1 q.2)
      ↑((pnbr G R c).sigma fun w => Icc 1 (rlen G R c w k)) := by
  rintro ⟨w, j⟩ hq ⟨w', j'⟩ hq' h
  rw [mem_coe, mem_sigma, mem_Icc] at hq hq'
  have hx := ray_pray hc hq.1 hq.2.1 hq.2.2
  have hx' := ray_pray hc hq'.1 hq'.2.1 hq'.2.2
  simp only at h
  rw [← h] at hx'
  obtain ⟨rfl, rfl⟩ := pray_inj hG hx hx'
  rfl

/-- **Sums over a P-ball.** -/
lemma sum_pball (hG : G.IsAcyclic) {c : V} (hc : IsP G R c) (k : ℕ) (g : V → ℕ) :
    ∑ x ∈ pball G R c k, g x =
      g c + ∑ w ∈ pnbr G R c, ∑ j ∈ Icc 1 (rlen G R c w k), g (ray G R c w j) := by
  classical
  have hnot : c ∉ ((pnbr G R c).sigma fun w => Icc 1 (rlen G R c w k)).image
      fun q => ray G R c q.1 q.2 := by
    rw [mem_image]
    rintro ⟨⟨w, j⟩, hq, hx⟩
    rw [mem_sigma, mem_Icc] at hq
    obtain ⟨p, hp, -, hpl, -⟩ := ray_pray hc hq.1 hq.2.1 hq.2.2
    exact getVert_ne_end hp (i := 0) (by omega) (by rw [Walk.getVert_zero]; exact hx.symm)
  rw [pball_eq hc k, sum_insert hnot, sum_image (ray_injOn hG hc k), sum_sigma]

/-- Before the last vertex of a ray, both P-directions are used. -/
lemma slots_ray_lt {c w : V} (hc : IsP G R c) (hw : w ∈ pnbr G R c) {k j : ℕ} (hj : 1 ≤ j)
    (hjl : j < rlen G R c w k) : slots G R (ray G R c w j) = 0 := by
  classical
  obtain ⟨p, hp, hpP, hpl, hps⟩ := ray_pray hc hw (j := j + 1) (by omega) hjl
  have hrj : ray G R c w j = p.getVert j :=
    pray_unique hj (ray_pray hc hw hj hjl.le) (by
      have := pray_getVert hp hpP hj (by omega)
      rwa [hps] at this)
  have ha : p.getVert (j - 1) ∈ pnbr G R (p.getVert j) := by
    have := p.adj_getVert_succ (show j - 1 < p.length by omega)
    rw [show j - 1 + 1 = j by omega] at this
    exact mem_pnbr.2 ⟨this.symm, hpP _ (Walk.getVert_mem_support _ _)⟩
  have hb : p.getVert (j + 1) ∈ pnbr G R (p.getVert j) :=
    mem_pnbr.2 ⟨p.adj_getVert_succ (by omega), hpP _ (Walk.getVert_mem_support _ _)⟩
  have hab : p.getVert (j - 1) ≠ p.getVert (j + 1) := fun h => by
    have := hp.getVert_injOn (show j - 1 ≤ p.length by omega) (show j + 1 ≤ p.length by omega) h
    omega
  have h2 : 2 ≤ #(pnbr G R (p.getVert j)) := by
    have := card_le_card (show {p.getVert (j - 1), p.getVert (j + 1)} ⊆ pnbr G R (p.getVert j) by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)
    rwa [card_pair hab] at this
  rw [slots, hrj]
  omega

/-- A ray that stops before `k` stops at a vertex with one missing direction. -/
lemma slots_ray_last (hG : G.IsAcyclic) {c w : V} (hc : IsP G R c) (hw : w ∈ pnbr G R c)
    {k : ℕ} (hlt : rlen G R c w k < k) : slots G R (ray G R c w (rlen G R c w k)) = 1 := by
  classical
  have h1 : 1 ≤ rlen G R c w k := one_le_rlen hc hw (by omega)
  obtain ⟨p, hp, hpP, hpl, hps⟩ := ray_pray hc hw h1 le_rfl
  have hpn : ¬ p.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
  have hsub : ∀ z ∈ pnbr G R (ray G R c w (rlen G R c w k)), z = p.penultimate := by
    intro z hz
    by_contra hne
    have := pray_concat hG hp hpP hpn hz hne
    rw [hpl, hps] at this
    exact not_pray_of_rlen_lt (Nat.lt_succ_self _) (by omega) ⟨z, this⟩
  have hmem : p.penultimate ∈ pnbr G R (ray G R c w (rlen G R c w k)) :=
    mem_pnbr.2 ⟨(Walk.adj_penultimate hpn).symm, hpP _ (Walk.getVert_mem_support _ _)⟩
  rw [slots, eq_singleton_iff_unique_mem.2 ⟨hmem, hsub⟩, card_singleton]

/-- **The cover identity.** -/
theorem cover_count (hG : G.IsAcyclic) {c : V} (hc : IsP G R c) {k : ℕ} (hk : 1 ≤ k) :
    #(pball G R c k) + ∑ e ∈ pball G R c k, slots G R e * (k - G.dist c e) = 2 * k + 1 := by
  rw [card_eq_sum_ones, sum_pball hG hc k (fun _ => 1),
    sum_pball hG hc k (fun e => slots G R e * (k - G.dist c e))]
  have hray : ∀ w ∈ pnbr G R c, ∑ j ∈ Icc 1 (rlen G R c w k),
      slots G R (ray G R c w j) * (k - G.dist c (ray G R c w j)) = k - rlen G R c w k := by
    intro w hw
    have hl1 := one_le_rlen hc hw hk
    have hlk : rlen G R c w k ≤ k := rlen_le
    have hd : ∀ j ∈ Icc 1 (rlen G R c w k), G.dist c (ray G R c w j) = j := by
      intro j hj
      rw [mem_Icc] at hj
      obtain ⟨p, hp, -, hpl, -⟩ := ray_pray hc hw hj.1 hj.2
      rw [dist_eq_length hG hp, hpl]
    rw [sum_congr rfl fun j hj => by rw [hd j hj]]
    rw [sum_eq_single_of_mem (rlen G R c w k) (mem_Icc.2 ⟨hl1, le_rfl⟩) fun j hj hne => by
      rw [mem_Icc] at hj
      rw [slots_ray_lt hc hw hj.1 (lt_of_le_of_ne hj.2 hne), zero_mul]]
    rcases lt_or_eq_of_le hlk with hlt | heq
    · rw [slots_ray_last hG hc hw hlt, one_mul]
    · simp [heq]
  rw [sum_congr rfl hray]
  simp only [sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel,
    SimpleGraph.dist_self, Nat.sub_zero]
  have hsum : ∑ w ∈ pnbr G R c, rlen G R c w k + ∑ w ∈ pnbr G R c, (k - rlen G R c w k) =
      #(pnbr G R c) * k := by
    rw [← sum_add_distrib, sum_congr rfl fun w _ => Nat.add_sub_cancel' rlen_le, sum_const,
      smul_eq_mul]
  have hs : slots G R c * k + #(pnbr G R c) * k = 2 * k := by
    rw [slots, ← add_mul, Nat.sub_add_cancel (card_pnbr_le hc)]
  linarith

/-- At most two vertices of a P-ball are at the largest distance. -/
lemma card_psphere_le (hG : G.IsAcyclic) {c : V} (hc : IsP G R c) {k : ℕ} (hk : 1 ≤ k) :
    #((pball G R c k).filter fun x => G.dist c x = k) ≤ 2 := by
  classical
  have hsub : (pball G R c k).filter (fun x => G.dist c x = k) ⊆
      (pnbr G R c).image fun w => ray G R c w k := by
    intro x hx
    rw [mem_filter, mem_pball] at hx
    obtain ⟨⟨p, hp, hpP, -⟩, hd⟩ := hx
    rw [dist_eq_length hG hp] at hd
    have hpn : ¬ p.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
    have hw : p.snd ∈ pnbr G R c :=
      mem_pnbr.2 ⟨Walk.adj_snd hpn, hpP _ (Walk.getVert_mem_support _ _)⟩
    have hray : PRay G R c p.snd k x := ⟨p, hp, hpP, hd, rfl⟩
    exact mem_image.2 ⟨p.snd, hw, pray_unique hk (ray_spec ⟨x, hray⟩) hray⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_pnbr_le hc))

end Forest

end Op4
