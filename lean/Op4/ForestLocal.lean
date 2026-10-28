import Op4.ForestMain

/-!
# Theorem `thm:forests`, deterministic fractional part: locality

`Agree G G' v T`: every vertex that a walk of length `< T` from `v` reaches in `G` has the same
neighbours in `G` and `G'`. This is what `v` learns in `T` rounds of the LOCAL model, and the
relation is symmetric (`Agree.symm`). If two forests agree near `v` with `T = 7R`, then
`forestSol G R v = forestSol G' R v` (`forest_local`): the output at `v` is computed in `7R`
rounds.

Every predicate that a window uses is decided within a bounded radius: high paths and the core
within `R`, core neighbours and P- and branch vertices within `R + 1`, slots within `R + 2`, P-balls
of radius `k` within `k + R + 1`, and projections within `2R`, since a projection path has length
at most `R`. A core-free component has all its vertices within `2R` of each other. The vertices of
a window that contains `v` are within `4R` of `v` (`window`).
-/

namespace Op4

namespace Forest

open SimpleGraph Finset

variable {V : Type*} {G G' : SimpleGraph V}

/-- `G` and `G'` agree on the vertices that a walk of length `< T` from `v` reaches in `G`. -/
def Agree (G G' : SimpleGraph V) (v : V) (T : ℕ) : Prop :=
  ∀ x, (∃ p : G.Walk v x, p.length < T) → ∀ y, (G.Adj x y ↔ G'.Adj x y)

/-- Walks with the same support have the same length. -/
lemma walk_length_eq {H H' : SimpleGraph V} {u x : V} {p : H.Walk u x} {q : H'.Walk u x}
    (h : q.support = p.support) : q.length = p.length := by
  have := congrArg List.length h
  rw [Walk.length_support, Walk.length_support] at this
  omega

lemma walk_isPath_iff {H H' : SimpleGraph V} {u x : V} {p : H.Walk u x} {q : H'.Walk u x}
    (h : q.support = p.support) : q.IsPath ↔ p.IsPath := by
  rw [Walk.isPath_def, Walk.isPath_def, h]

lemma walk_getVert_eq {H H' : SimpleGraph V} {u x : V} {p : H.Walk u x} {q : H'.Walk u x}
    (h : q.support = p.support) (n : ℕ) : q.getVert n = p.getVert n := by
  have hl := walk_length_eq h
  by_cases hn : n ≤ p.length
  · have h1 := p.getVert_eq_support_getElem? hn
    have h2 := q.getVert_eq_support_getElem? (by omega : n ≤ q.length)
    rw [h] at h2
    exact Option.some_injective _ (h2.trans h1.symm)
  · push Not at hn
    rw [q.getVert_of_length_le (i := n) (by omega), p.getVert_of_length_le hn.le]

namespace Agree

variable {v w : V} {T T' : ℕ}

lemma shift (h : Agree G G' v T) (q : G.Walk v w) (hq : q.length + T' ≤ T) :
    Agree G G' w T' := by
  rintro x ⟨p, hp⟩ y
  exact h x ⟨q.append p, by rw [Walk.length_append]; omega⟩ y

lemma adj (h : Agree G G' v T) (hT : 1 ≤ T) (y : V) : G.Adj v y ↔ G'.Adj v y :=
  h v ⟨Walk.nil, by rw [Walk.length_nil]; omega⟩ y

lemma shift_adj (h : Agree G G' v T) (hvw : G.Adj v w) (hT : T' + 1 ≤ T) : Agree G G' w T' :=
  h.shift (Walk.cons hvw Walk.nil) (by simp only [Walk.length_cons, Walk.length_nil]; omega)

/-- A walk of length at most `T` from `v` in `G'` is a walk in `G`. -/
lemma walk_back {x : V} (p : G'.Walk v x) (h : Agree G G' v T) (hl : p.length ≤ T) :
    ∃ q : G.Walk v x, q.support = p.support := by
  induction p generalizing T with
  | nil => exact ⟨Walk.nil, rfl⟩
  | @cons a b c hab p ih =>
    rw [Walk.length_cons] at hl
    have hadj : G.Adj a b := (h.adj (by omega) b).2 hab
    obtain ⟨q, hq⟩ := ih (T := T - 1) (h.shift_adj hadj (by omega)) (by omega)
    exact ⟨Walk.cons hadj q, by rw [Walk.support_cons, Walk.support_cons, hq]⟩

/-- **The relation is symmetric.** -/
lemma symm (h : Agree G G' v T) : Agree G' G v T := by
  rintro x ⟨p, hp⟩ y
  obtain ⟨q, hq⟩ := h.walk_back p hp.le
  exact (h x ⟨q, by rw [walk_length_eq hq]; exact hp⟩ y).symm

/-- A walk of length at most `T` from `v` in `G` is a walk in `G'`. -/
lemma walk {x : V} (p : G.Walk v x) (h : Agree G G' v T) (hl : p.length ≤ T) :
    ∃ q : G'.Walk v x, q.support = p.support :=
  h.symm.walk_back p hl

lemma shift' (h : Agree G G' v T) (q : G'.Walk v w) (hq : q.length + T' ≤ T) :
    Agree G G' w T' :=
  (h.symm.shift q hq).symm

variable {R : ℕ}

lemma highPath (h : Agree G G' v T) (hT : R ≤ T) {u : V} (hp : HighPath G R v u) :
    HighPath G' R v u := by
  obtain ⟨x, p, hp, hl, hs⟩ := hp
  obtain ⟨q, hq⟩ := h.walk p (by omega)
  exact ⟨x, q, (walk_isPath_iff hq).2 hp, (walk_length_eq hq).trans hl,
    (walk_getVert_eq hq 1).trans hs⟩

lemma core_iff (h : Agree G G' v T) (hT : R ≤ T) : Core G R v ↔ Core G' R v := by
  have e : ∀ u, HighPath G R v u ↔ HighPath G' R v u := fun u =>
    ⟨h.highPath hT, h.symm.highPath hT⟩
  simp only [Core, e]

/-- Projections are decided within `2R`, on forests. -/
lemma proj (hG : G.IsAcyclic) (hR : 1 ≤ R) (h : Agree G G' v T) (hT : 2 * R ≤ T) {c : V}
    (hp : Proj G R v c) : Proj G' R v c := by
  classical
  obtain ⟨hc, p, hp, hpc⟩ := hp
  have hl := proj_length_le hG hR hc hp hpc
  obtain ⟨q, hq⟩ := h.walk p (by omega)
  have hcore : ∀ y (hy : y ∈ p.support), Core G R y ↔ Core G' R y := fun y hy =>
    (h.shift (p.takeUntil y hy) (T' := R)
      (by have := p.length_takeUntil_le_length hy; omega)).core_iff le_rfl
  refine ⟨(hcore c p.end_mem_support).1 hc, q, (walk_isPath_iff hq).2 hp, fun y hy hy' => ?_⟩
  rw [hq] at hy
  exact hpc y hy ((hcore y hy).2 hy')

lemma proj_iff (hG : G.IsAcyclic) (hG' : G'.IsAcyclic) (hR : 1 ≤ R) (h : Agree G G' v T)
    (hT : 2 * R ≤ T) {c : V} : Proj G R v c ↔ Proj G' R v c :=
  ⟨h.proj hG hR hT, h.symm.proj hG' hR hT⟩

variable [Fintype V] [DecidableRel G.Adj] [DecidableRel G'.Adj]

lemma knbr_eq (h : Agree G G' v T) (hT : R + 1 ≤ T) : knbr G R v = knbr G' R v := by
  ext u
  rw [mem_knbr, mem_knbr, ← h.adj (by omega) u]
  exact and_congr_right fun hvu => (h.shift_adj hvu (T' := R) hT).core_iff le_rfl

lemma isP_iff (h : Agree G G' v T) (hT : R + 1 ≤ T) : IsP G R v ↔ IsP G' R v := by
  unfold IsP
  rw [h.core_iff (R := R) (by omega), h.knbr_eq hT]

lemma isBr_iff (h : Agree G G' v T) (hT : R + 1 ≤ T) : IsBr G R v ↔ IsBr G' R v := by
  unfold IsBr
  rw [h.core_iff (R := R) (by omega), h.isP_iff hT]

lemma slots_eq (h : Agree G G' v T) (hT : R + 2 ≤ T) : slots G R v = slots G' R v := by
  have : pnbr G R v = pnbr G' R v := by
    ext u
    rw [mem_pnbr, mem_pnbr, ← h.adj (by omega) u]
    exact and_congr_right fun hvu => (h.shift_adj hvu (T' := R + 1) (by omega)).isP_iff le_rfl
  unfold slots
  rw [this]

lemma inPBall (h : Agree G G' v T) {k : ℕ} (hT : k + R + 1 ≤ T) {x : V}
    (hx : InPBall G R v k x) : InPBall G' R v k x := by
  classical
  obtain ⟨p, hp, hP, hl⟩ := hx
  obtain ⟨q, hq⟩ := h.walk p (by omega)
  refine ⟨q, (walk_isPath_iff hq).2 hp, fun y hy => ?_, (walk_length_eq hq).trans_le hl⟩
  rw [hq] at hy
  exact ((h.shift (p.takeUntil y hy) (T' := R + 1)
    (by have := p.length_takeUntil_le_length hy; omega)).isP_iff le_rfl).1 (hP y hy)

lemma pball_eq (h : Agree G G' v T) {k : ℕ} (hT : k + R + 1 ≤ T) :
    pball G R v k = pball G' R v k := by
  ext x
  rw [mem_pball, mem_pball]
  exact ⟨h.inPBall hT, h.symm.inPBall hT⟩

omit [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- The union of the hairs of a set `X` near `v` is decided near `v`. -/
lemma hairs_eq (hG : G.IsAcyclic) (hG' : G'.IsAcyclic) (hR : 1 ≤ R) (h : Agree G G' v T)
    {X : Finset V} {d : ℕ} (hX : ∀ c ∈ X, ∃ q : G.Walk v c, q.length ≤ d)
    (hT : d + 3 * R ≤ T) : hairs G R X = hairs G' R X := by
  ext w
  rw [mem_hairs, mem_hairs]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  obtain ⟨q, hq⟩ := hX c hc
  constructor
  · rintro ⟨hcc, p, hp, hpc⟩
    have hl := proj_length_le hG hR hcc hp hpc
    exact (h.shift (q.append p.reverse) (T' := 2 * R)
      (by rw [Walk.length_append, Walk.length_reverse]; omega)).proj hG hR le_rfl
      ⟨hcc, p, hp, hpc⟩
  · rintro ⟨hcc, p, hp, hpc⟩
    have hl := proj_length_le hG' hR hcc hp hpc
    exact ((h.shift q (T' := T - d) (by omega)).shift' p.reverse (T' := 2 * R)
      (by rw [Walk.length_reverse]; omega)).symm.proj hG' hR le_rfl ⟨hcc, p, hp, hpc⟩

end Agree

variable {R : ℕ}

/-- A vertex of the hair of `c` is within `R` of `c`. -/
lemma walk_of_proj (hG : G.IsAcyclic) (hR : 1 ≤ R) {w c : V} (h : Proj G R w c) :
    ∃ p : G.Walk w c, p.length ≤ R :=
  let ⟨hc, p, hp, hpc⟩ := h
  ⟨p, proj_length_le hG hR hc hp hpc⟩

variable [Fintype V] [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- A vertex of the P-ball of radius `k` around `u` is within `k` of `u`. -/
lemma walk_of_pball {u c : V} {k : ℕ} (h : c ∈ pball G R u k) : ∃ p : G.Walk u c, p.length ≤ k :=
  let ⟨p, _, _, hl⟩ := mem_pball.1 h
  ⟨p, hl⟩

/-- A window made of the hairs of a P-ball that contains `v`. -/
lemma pball_window (hG : G.IsAcyclic) (hG' : G'.IsAcyclic) (hR : 1 ≤ R) {v u : V} {k : ℕ}
    (hk : k ≤ R) (h : Agree G G' v (7 * R)) (hv : v ∈ hairs G R (pball G R u k)) :
    Agree G G' u (5 * R) ∧ hairs G R (pball G R u k) = hairs G' R (pball G' R u k) ∧
      ∀ w ∈ hairs G R (pball G R u k), ∃ q : G.Walk v w, q.length ≤ 4 * R := by
  obtain ⟨c, hc, hvc⟩ := mem_hairs.1 hv
  obtain ⟨p, hp⟩ := walk_of_proj hG hR hvc
  obtain ⟨r, hr⟩ := walk_of_pball hc
  have hvu : (p.append r.reverse).length ≤ 2 * R := by
    simp only [Walk.length_append, Walk.length_reverse]; omega
  have hu := h.shift (p.append r.reverse) (T' := 5 * R) (by omega)
  refine ⟨hu, ?_, fun w hw => ?_⟩
  · rw [← hu.pball_eq (R := R) (k := k) (by omega)]
    exact hu.hairs_eq hG hG' hR (fun c hc => walk_of_pball hc) (by omega)
  · obtain ⟨c', hc', hwc⟩ := mem_hairs.1 hw
    obtain ⟨p', hp'⟩ := walk_of_proj hG hR hwc
    obtain ⟨r', hr'⟩ := walk_of_pball hc'
    refine ⟨(p.append r.reverse).append (r'.append p'.reverse), ?_⟩
    simp only [Walk.length_append, Walk.length_reverse]
    omega

omit [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- A core-free component that contains `v`. -/
lemma free_window (hG : G.IsAcyclic) (hR : 1 ≤ R) {v u : V} (h : Agree G G' v (7 * R))
    (hu : Free G R u) (huv : G.Reachable u v) :
    Free G' R u ∧ comp G u = comp G' u ∧ ∀ w ∈ comp G u, ∃ q : G.Walk v w, q.length ≤ 4 * R := by
  have hno : ∀ c, G.Reachable v c → ¬ Core G R c := fun c hc => hu c (huv.trans hc)
  have hnear : ∀ x, G.Reachable v x → ∃ q : G.Walk v x, q.length < 2 * R := fun x hx => by
    obtain ⟨q, _, hq⟩ := hx.exists_path_of_dist
    exact ⟨q, by rw [hq]; exact dist_lt_of_no_core hG hR hno hx⟩
  have hback : ∀ a x (p : G'.Walk a x), G.Reachable v a → G.Reachable v x := by
    intro a x p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      intro ha
      obtain ⟨q, hq⟩ := hnear a ha
      exact ih (ha.trans ((h a ⟨q, by omega⟩ b).2 hab).reachable)
  have hreach : ∀ x, G.Reachable v x ↔ G'.Reachable v x := fun x =>
    ⟨fun hx => by
      obtain ⟨q, hq⟩ := hnear x hx
      obtain ⟨q', _⟩ := h.walk q (by omega)
      exact ⟨q'⟩,
     fun ⟨p⟩ => hback v x p (Reachable.refl v)⟩
  have hvu' : G'.Reachable v u := (hreach u).1 huv.symm
  refine ⟨fun c hc hcc => ?_, ?_, fun w hw => ?_⟩
  · have hvc := (hreach c).2 (hvu'.trans hc)
    obtain ⟨q, hq⟩ := hnear c hvc
    exact hno c hvc (((h.shift q (T' := R) (by omega)).core_iff le_rfl).2 hcc)
  · ext x
    rw [mem_comp, mem_comp]
    exact ⟨fun hx => hvu'.symm.trans ((hreach x).1 (huv.symm.trans hx)),
      fun hx => huv.trans ((hreach x).2 (hvu'.trans hx))⟩
  · obtain ⟨q, hq⟩ := hnear w (huv.symm.trans (mem_comp.1 hw))
    exact ⟨q, by omega⟩

/-- **A window that contains `v` is decided near `v`.** It is the same window in both forests,
with the same weight, and its vertices are within `4R` of `v`. -/
lemma window (hG : G.IsAcyclic) (hG' : G'.IsAcyclic) (hR : 1 ≤ R) {v : V}
    (h : Agree G G' v (7 * R)) {i : WIdx V R} (hv : v ∈ wU G R i) :
    wU G R i = wU G' R i ∧ wt G R i = wt G' R i ∧
      ∀ w ∈ wU G R i, ∃ q : G.Walk v w, q.length ≤ 4 * R := by
  rcases i with u | ⟨e, s, t⟩ | b | u
  · by_cases hu : IsP G R u
    · have e1 : wU G R (.inl u) = hairs G R (pball G R u R) := by
        simp only [wU, wX, hu, ↓reduceIte]
      rw [e1] at hv ⊢
      obtain ⟨hA, he, hn⟩ := pball_window hG hG' hR le_rfl h hv
      have e2 : wU G' R (.inl u) = hairs G' R (pball G' R u R) := by
        simp only [wU, wX, (hA.isP_iff (R := R) (by omega)).1 hu, ↓reduceIte]
      exact ⟨he.trans e2.symm, rfl, hn⟩
    · simp [wU, wX, hu, mem_hairs] at hv
  · by_cases hu : IsP G R e ∧ (s : ℕ) < slots G R e
    · have e1 : wU G R (.inr (.inl (e, s, t))) = hairs G R (pball G R e (R - 1 - t)) := by
        simp only [wU, wX, hu, and_self, ↓reduceIte]
      rw [e1] at hv ⊢
      obtain ⟨hA, he, hn⟩ := pball_window hG hG' hR (by omega) h hv
      have hu' : IsP G' R e ∧ (s : ℕ) < slots G' R e :=
        ⟨(hA.isP_iff (R := R) (by omega)).1 hu.1, hA.slots_eq (R := R) (by omega) ▸ hu.2⟩
      have e2 : wU G' R (.inr (.inl (e, s, t))) = hairs G' R (pball G' R e (R - 1 - t)) := by
        simp only [wU, wX, hu', and_self, ↓reduceIte]
      exact ⟨he.trans e2.symm, rfl, hn⟩
    · simp [wU, wX, hu, mem_hairs] at hv
  · by_cases hb : IsBr G R b
    · have e1 : wU G R (.inr (.inr (.inl b))) = hairs G R {b} := by
        simp only [wU, wX, hb, ↓reduceIte]
      rw [e1] at hv ⊢
      have hvb : Proj G R v b := by simpa [mem_hairs] using hv
      obtain ⟨p, hp⟩ := walk_of_proj hG hR hvb
      have hA := h.shift p (T' := 6 * R) (by omega)
      have e2 : wU G' R (.inr (.inr (.inl b))) = hairs G' R {b} := by
        simp only [wU, wX, (hA.isBr_iff (R := R) (by omega)).1 hb, ↓reduceIte]
      have hX : ∀ c ∈ ({b} : Finset V), ∃ q : G.Walk b c, q.length ≤ 0 := fun c hc => by
        rw [mem_singleton.1 hc]
        exact ⟨Walk.nil, le_rfl⟩
      refine ⟨(hA.hairs_eq hG hG' hR hX (by omega)).trans e2.symm, rfl, fun w hw => ?_⟩
      have hwb : Proj G R w b := by simpa [mem_hairs] using hw
      obtain ⟨p', hp'⟩ := walk_of_proj hG hR hwb
      refine ⟨p.append p'.reverse, ?_⟩
      simp only [Walk.length_append, Walk.length_reverse]
      omega
    · simp [wU, wX, hb, mem_hairs] at hv
  · by_cases hu : Free G R u
    · have e1 : wU G R (.inr (.inr (.inr u))) = comp G u := by simp only [wU, hu, ↓reduceIte]
      rw [e1] at hv ⊢
      obtain ⟨hu', hc, hn⟩ := free_window hG hR h hu (mem_comp.1 hv)
      have e2 : wU G' R (.inr (.inr (.inr u))) = comp G' u := by simp only [wU, hu', ↓reduceIte]
      exact ⟨e2 ▸ hc, by simp only [wt, hc], hn⟩
    · simp [wU, hu] at hv

variable [DecidableEq V]

lemma wnb_eq {v : V} {T : ℕ} (h : Agree G G' v T) {i : WIdx V R} (hU : wU G R i = wU G' R i)
    (hn : ∀ w ∈ wU G R i, ∃ q : G.Walk v w, q.length + 1 ≤ T) : wnb G R i = wnb G' R i := by
  funext w
  by_cases hw : w ∈ wU G R i
  · have hw' : w ∈ wU G' R i := hU ▸ hw
    obtain ⟨q, hq⟩ := hn w hw
    have hA := h.shift q hq
    simp only [wnb, hw, hw', ↓reduceIte, cnbhd]
    congr 1
    ext y
    rw [mem_neighborFinset, mem_neighborFinset]
    exact hA.adj le_rfl y
  · have hw' : w ∉ wU G' R i := hU ▸ hw
    simp only [wnb, hw, hw', ↓reduceIte]

/-- **Theorem `thm:forests`, deterministic fractional part: locality.** On two forests that agree
on the vertices at distance less than `7R` from `v`, the outputs at `v` are equal. So
`forestSol G R` is computed in `7R` rounds of the LOCAL model. -/
theorem forest_local (hG : G.IsAcyclic) (hG' : G'.IsAcyclic) (hR : 1 ≤ R) {v : V}
    (h : Agree G G' v (7 * R)) : forestSol G R v = forestSol G' R v := by
  unfold forestSol
  refine sum_congr rfl fun i _ => ?_
  by_cases hv : v ∈ wU G R i
  · obtain ⟨hU, hwt, hn⟩ := window hG hG' hR h hv
    have hn' : ∀ w ∈ wU G R i, ∃ q : G.Walk v w, q.length + 1 ≤ 7 * R := fun w hw =>
      (hn w hw).imp fun q hq => by omega
    rw [hwt, wnb_eq h hU hn', hU]
  · by_cases hv' : v ∈ wU G' R i
    · obtain ⟨hU, hwt, hn⟩ := window hG' hG hR h.symm hv'
      have hn' : ∀ w ∈ wU G' R i, ∃ q : G'.Walk v w, q.length + 1 ≤ 7 * R := fun w hw =>
        (hn w hw).imp fun q hq => by omega
      rw [hwt, wnb_eq h.symm hU hn', hU]
    · rw [(locOpt_isOpt (G := G) i).1.2.1 v hv, (locOpt_isOpt (G := G') i).1.2.1 v hv',
        mul_zero, mul_zero]

/-- **Corollary: `(1 + ε)`-approximation.** For `0 < ε ≤ 1` and `R = ⌈72/ε⌉`, `forestSol G R` is a
fractional dominating set of weight at most `(1 + ε)·y(V)` for every fractional dominating set `y`,
and `7R ≤ 511/ε`, so by `forest_local` it is computed in at most `511/ε` rounds. -/
theorem forest_frac_approx (hG : G.IsAcyclic) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ u, Dom G (forestSol G ⌈72 / ε⌉₊) u) ∧
      (∀ y : V → ℝ, (∀ v, 0 ≤ y v) → (∀ u, Dom G y u) →
        ∑ v, forestSol G ⌈72 / ε⌉₊ v ≤ (1 + ε) * ∑ v, y v) ∧
      ((7 * ⌈72 / ε⌉₊ : ℕ) : ℝ) ≤ 511 / ε := by
  set R := ⌈72 / ε⌉₊
  have hR72 : 72 / ε ≤ R := Nat.le_ceil _
  have h72 : (72 : ℝ) ≤ 72 / ε := by rw [le_div_iff₀ hε]; linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hR1 : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    rw [h0, Nat.cast_zero] at hRpos
    exact lt_irrefl _ hRpos)
  obtain ⟨-, hdom, hb⟩ := forest_frac hG hR1
  refine ⟨hdom, fun y hy hyd => ?_, ?_⟩
  · have hsum : 0 ≤ ∑ v, y v := sum_nonneg fun v _ => hy v
    have hle : 72 / (R : ℝ) ≤ ε := by
      rw [div_le_iff₀ hRpos]
      rw [div_le_iff₀ hε] at hR72
      linarith
    calc ∑ v, forestSol G R v ≤ (1 + 72 / R) * ∑ v, y v := hb y hy hyd
      _ ≤ (1 + ε) * ∑ v, y v := mul_le_mul_of_nonneg_right (by linarith) hsum
  · have hceil : (R : ℝ) < 72 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h7 : (7 : ℝ) ≤ 7 / ε := by rw [le_div_iff₀ hε]; linarith
    push_cast
    calc (7 : ℝ) * R ≤ 7 * (72 / ε + 1) := by linarith
      _ = 504 / ε + 7 := by ring
      _ ≤ 504 / ε + 7 / ε := by linarith
      _ = 511 / ε := by ring

end Forest

end Op4
