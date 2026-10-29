import Op4.Kkn
import Op4.Table

/-!
# The Apollonian network: a limit for join-only analyses of the rule

The first item of Section `sec:limits`. Start from `K₄` and insert a vertex into every face, `t`
times (`apo t`). With unit weights the join gain of the rule is the number of parts that join a
star (`joined`), and its expectation is `∑_v (1-p)(1-(1-p)^{d_v})` (`E_joins` in `Kkn.lean`).

* The construction: a face at level `j` has an address `(f, w)` with `f` a face of `K₄` and
  `w : Fin j → Fin 3`; the child `k` of a face replaces its corner `k` by the vertex inserted into
  it (`corners`). The vertex inserted at level `j` has degree `3·2^{t-j-1}`, and the four vertices
  of `K₄` have degree `3·2^t` (`apo_degree`).
* For `t = 10` there are `118100` vertices (`apo_card`) and `354294` edges (`apo_edges`).
* `apo_join_le`: for every `p ≤ 1` the expected join gain is at most `0.17402·|E|`.
* `apo_join_three_eighths`: at `p = 3/8` it lies in `[0.171605, 0.171615)·|E|`, so it is `0.17161`
  to five decimals, against `φ(3/8) ∈ [0.170285, 0.170295)` (`phiP_three_eighths`).
* `apo_optimal`, `apo_kappa`: no lower bound `φ·|E|` on the expected join gain, for any `p`, has
  `φ > 0.17402`, and the exponent for `φ ≤ 0.17402` is above `5.74`.

That the network is planar is taken as given.
-/

open Finset SimpleGraph

namespace Op4

namespace Apollonian

/-! ### The construction -/

/-- All vertices: the four vertices of `K₄`, and the vertex inserted into the face `(f, w)` at
level `j`. -/
abbrev Vert := Fin 4 ⊕ (Σ j : ℕ, Fin 4 × (Fin j → Fin 3))

/-- The level at which a vertex is inserted, plus one; `0` for the vertices of `K₄`. -/
def birth : Vert → ℕ
  | .inl _ => 0
  | .inr x => x.1 + 1

/-- The corners of the face `(f, w)` at level `j`. The face `f` of `K₄` has the three vertices
other than `f`, and the child `k` of a face replaces its corner `k` by the vertex inserted into
the face. -/
def corners : (j : ℕ) → Fin 4 → (Fin j → Fin 3) → Fin 3 → Vert
  | 0, f, _ => fun k => .inl (f.succAbove k)
  | j + 1, f, w => Function.update (corners j f (Fin.tail w)) (w 0) (.inr ⟨j, f, Fin.tail w⟩)

lemma corners_cons (j : ℕ) (f : Fin 4) (k : Fin 3) (w : Fin j → Fin 3) :
    corners (j + 1) f (Fin.cons k w) = Function.update (corners j f w) k (.inr ⟨j, f, w⟩) := by
  simp only [corners, Fin.tail_cons, Fin.cons_zero]

lemma birth_corners : ∀ (j : ℕ) (f : Fin 4) (w : Fin j → Fin 3) (k : Fin 3),
    birth (corners j f w k) ≤ j
  | 0, f, w, k => by simp [corners, birth]
  | j + 1, f, w, k => by
    simp only [corners, Function.update_apply]
    split_ifs
    · simp [birth]
    · exact (birth_corners j f (Fin.tail w) k).trans (Nat.le_succ j)

lemma corners_injective : ∀ (j : ℕ) (f : Fin 4) (w : Fin j → Fin 3),
    Function.Injective (corners j f w)
  | 0, f, w => fun a b h => Fin.succAbove_right_injective (Sum.inl_injective h)
  | j + 1, f, w => by
    intro a b h
    simp only [corners, Function.update_apply] at h
    have hb := birth_corners j f (Fin.tail w)
    split_ifs at h with ha hb'
    · rw [ha, hb']
    · have := hb b; rw [← h] at this; simp [birth] at this
    · have := hb a; rw [h] at this; simp [birth] at this
    · exact corners_injective j f (Fin.tail w) h

/-- The number of faces at level `j` that have `v` as a corner. -/
def cnt (j : ℕ) (v : Vert) : ℕ :=
  ∑ g : Fin 4 × (Fin j → Fin 3), if ∃ k, corners j g.1 g.2 k = v then 1 else 0

lemma sum_children (j : ℕ) (f : Fin 4) (w : Fin j → Fin 3) (v : Vert) :
    ∑ k : Fin 3, (if ∃ k', corners (j + 1) f (Fin.cons k w) k' = v then 1 else 0) =
      2 * (if ∃ k', corners j f w k' = v then 1 else 0) +
        (if v = .inr ⟨j, f, w⟩ then 3 else 0) := by
  simp only [corners_cons]
  by_cases hv : v = .inr ⟨j, f, w⟩
  · subst hv
    have h1 : ¬ ∃ k', corners j f w k' = .inr ⟨j, f, w⟩ := by
      rintro ⟨k', hk'⟩
      have := birth_corners j f w k'
      rw [hk'] at this
      simp [birth] at this
    have h2 : ∀ k : Fin 3, ∃ k', Function.update (corners j f w) k (.inr ⟨j, f, w⟩) k' =
        .inr ⟨j, f, w⟩ := fun k => ⟨k, Function.update_self _ _ _⟩
    simp [h1, h2]
  · by_cases h : ∃ k', corners j f w k' = v
    · obtain ⟨k0, hk0⟩ := h
      have key : ∀ k : Fin 3, (∃ k', Function.update (corners j f w) k (.inr ⟨j, f, w⟩) k' = v) ↔
          k ≠ k0 := by
        intro k
        constructor
        · rintro ⟨k', hk'⟩ rfl
          rw [Function.update_apply] at hk'
          split_ifs at hk' with hk
          · exact hv hk'.symm
          · exact hk (corners_injective j f w (hk'.trans hk0.symm))
        · intro hk
          exact ⟨k0, by rw [Function.update_of_ne (Ne.symm hk)]; exact hk0⟩
      simp only [key, hv, show ∃ k', corners j f w k' = v from ⟨k0, hk0⟩, ↓reduceIte, add_zero]
      fin_cases k0 <;> simp [Fin.sum_univ_three]
    · have key : ∀ k : Fin 3,
          ¬ ∃ k', Function.update (corners j f w) k (.inr ⟨j, f, w⟩) k' = v := by
        rintro k ⟨k', hk'⟩
        rw [Function.update_apply] at hk'
        split_ifs at hk'
        · exact hv hk'.symm
        · exact h ⟨k', hk'⟩
      simp [key, h, hv]

lemma sum_level (j : ℕ) (v : Vert) :
    (∑ g : Fin 4 × (Fin j → Fin 3), if v = .inr ⟨j, g.1, g.2⟩ then 1 else 0) =
      if birth v = j + 1 then 1 else 0 := by
  rcases v with a | ⟨j', f0, w0⟩
  · simp [birth]
  · by_cases hj : j' = j
    · subst hj
      simp only [birth, ↓reduceIte]
      rw [Finset.sum_eq_single (f0, w0)]
      · simp
      · rintro ⟨f, w⟩ _ hne
        have : ¬ (Sum.inr ⟨j', f0, w0⟩ : Vert) = .inr ⟨j', f, w⟩ := by
          intro h
          simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
          exact hne h.symm
        simp only [this, ↓reduceIte]
      · simp
    · have : ∀ g : Fin 4 × (Fin j → Fin 3), ¬ (Sum.inr ⟨j', f0, w0⟩ : Vert) = .inr ⟨j, g.1, g.2⟩ := by
        intro g h
        simp only [Sum.inr.injEq, Sigma.mk.injEq] at h
        exact hj h.1
      simp only [this, ↓reduceIte, sum_const_zero]
      simp [birth, hj]

lemma sum_cons {M : Type*} [AddCommMonoid M] (j : ℕ) (F : (Fin (j + 1) → Fin 3) → M) :
    ∑ w, F w = ∑ w : Fin j → Fin 3, ∑ k : Fin 3, F (Fin.cons k w) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma cnt_succ (j : ℕ) (v : Vert) :
    cnt (j + 1) v = 2 * cnt j v + 3 * (if birth v = j + 1 then 1 else 0) := by
  rw [← sum_level j v]
  unfold cnt
  simp only [Fintype.sum_prod_type, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun f _ => ?_
  rw [sum_cons]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_children]
  split_ifs <;> simp

lemma cnt_zero (v : Vert) : cnt 0 v = if birth v = 0 then 3 else 0 := by
  rcases v with a | ⟨j', f0, w0⟩
  · simp only [cnt, corners, Sum.inl.injEq, birth, ↓reduceIte]
    rw [Fintype.sum_prod_type]
    simp only [Finset.univ_unique, sum_singleton]
    fin_cases a <;> decide
  · simp [cnt, corners, birth]

/-- **The faces at level `j` with corner `v`**: `3·2^{j-b}` if `v` exists at level `j`. -/
lemma cnt_eq (j : ℕ) (v : Vert) :
    cnt j v = if birth v ≤ j then 3 * 2 ^ (j - birth v) else 0 := by
  induction j with
  | zero =>
    rw [cnt_zero]
    by_cases h : birth v = 0 <;> simp [h]
  | succ j ih =>
    rw [cnt_succ, ih]
    by_cases h1 : birth v ≤ j
    · simp only [h1, show birth v ≤ j + 1 by omega, show ¬ birth v = j + 1 by omega, ↓reduceIte]
      rw [show j + 1 - birth v = (j - birth v) + 1 by omega, pow_succ]
      ring
    · by_cases h2 : birth v = j + 1
      · simp [h2]
      · simp only [h1, h2, show ¬ birth v ≤ j + 1 by omega, ↓reduceIte]

/-! ### The network after `t` steps -/

/-- The vertices after `t` steps. -/
abbrev VT (t : ℕ) := Fin 4 ⊕ (Σ j : Fin t, Fin 4 × (Fin j → Fin 3))

def emb {t : ℕ} : VT t → Vert
  | .inl a => .inl a
  | .inr ⟨j, g⟩ => .inr ⟨j.val, g⟩

lemma emb_injective (t : ℕ) : Function.Injective (emb (t := t)) := by
  rintro (a | ⟨j, f, w⟩) (b | ⟨j', f', w'⟩) h <;> simp only [emb, reduceCtorEq, Sum.inl.injEq,
    Sum.inr.injEq] at h
  · rw [h]
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
    have hj : j = j' := Fin.ext h1
    subst hj
    rw [heq_eq_eq] at h2
    rw [h2]

lemma birth_emb_le {t : ℕ} (v : VT t) : birth (emb v) ≤ t := by
  rcases v with a | ⟨j, g⟩
  · simp [emb, birth]
  · simp only [emb, birth]; omega

lemma exists_emb {t : ℕ} (x : Vert) (hx : birth x ≤ t) : ∃ v : VT t, emb v = x := by
  rcases x with a | ⟨j, f, w⟩
  · exact ⟨.inl a, rfl⟩
  · exact ⟨.inr ⟨⟨j, by simp only [birth] at hx; omega⟩, f, w⟩, rfl⟩

/-- `x` has the neighbour `y` with `birth y ≤ birth x`: the other vertices of `K₄`, or a corner of
the face into which `x` was inserted. -/
def R : Vert → Vert → Prop
  | .inl a, .inl b => a ≠ b
  | .inl _, .inr _ => False
  | .inr ⟨j, f, w⟩, y => ∃ k, corners j f w k = y

lemma R_ne {x y : Vert} (h : R x y) : x ≠ y := by
  rcases x with a | ⟨j, f, w⟩
  · rcases y with b | y
    · intro h'; exact h (Sum.inl_injective h')
    · exact h.elim
  · rintro rfl
    obtain ⟨k, hk⟩ := h
    have := birth_corners j f w k
    rw [hk] at this
    simp [birth] at this

/-- The Apollonian network after `t` steps. -/
def apo (t : ℕ) : SimpleGraph (VT t) := (SimpleGraph.fromRel R).comap emb

lemma apo_adj {t : ℕ} (u v : VT t) : (apo t).Adj u v ↔
    R (emb u) (emb v) ∨ ∃ j g, v = .inr ⟨j, g⟩ ∧ ∃ k, corners j g.1 g.2 k = emb u := by
  simp only [apo, comap_adj, fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · rcases v with b | ⟨j, f, w⟩
      · rcases u with a | ⟨j', f', w'⟩
        · exact Or.inl (Ne.symm h)
        · exact h.elim
      · exact Or.inr ⟨j, (f, w), rfl, h⟩
  · rintro (h | ⟨j, g, rfl, h⟩)
    · exact ⟨R_ne h, Or.inl h⟩
    · exact ⟨(R_ne (show R (emb (Sum.inr ⟨j, g⟩ : VT t)) (emb u) from h)).symm, Or.inr h⟩

open Classical in
lemma card_R {t : ℕ} (u : VT t) :
    (∑ v : VT t, if R (emb u) (emb v) then 1 else 0) = 3 := by
  rcases u with a | ⟨j0, f0, w0⟩
  · rw [Fintype.sum_sum_type]
    simp only [emb, R]
    fin_cases a <;> simp [Fin.sum_univ_four]
  · set S : Finset Vert := univ.image (corners j0 f0 w0)
    have hS : #S = 3 := by
      rw [card_image_of_injective _ (corners_injective _ _ _)]; rfl
    have hmap : (univ.filter fun v : VT t => R (emb (.inr ⟨j0, f0, w0⟩ : VT t)) (emb v)).map
        ⟨emb, emb_injective t⟩ = S := by
      ext x
      simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, S,
        mem_image]
      constructor
      · rintro ⟨v, ⟨k, hk⟩, rfl⟩; exact ⟨k, hk⟩
      · rintro ⟨k, rfl⟩
        obtain ⟨v, hv⟩ := exists_emb (t := t) (corners j0 f0 w0 k)
          ((birth_corners _ _ _ k).trans (by omega))
        exact ⟨v, (⟨k, hv.symm⟩ : ∃ k', corners j0 f0 w0 k' = emb v), hv⟩
    have h := congrArg Finset.card hmap
    rw [card_map, card_filter, hS] at h
    exact h

lemma geom_sum (t b : ℕ) (hb : b ≤ t) :
    3 + ∑ j ∈ range t, (if b ≤ j then 3 * 2 ^ (j - b) else 0) = 3 * 2 ^ (t - b) := by
  induction t with
  | zero => simp [show b = 0 by omega]
  | succ t ih =>
    by_cases hbt : b ≤ t
    · rw [sum_range_succ, ← add_assoc, ih hbt]
      simp only [hbt, ↓reduceIte]
      rw [show t + 1 - b = (t - b) + 1 by omega, pow_succ]
      ring
    · have hb' : b = t + 1 := by omega
      subst hb'
      rw [Finset.sum_eq_zero fun j hj => by
        simp only [mem_range] at hj; simp only [show ¬ t + 1 ≤ j by omega, ↓reduceIte]]
      simp

open Classical in
/-- **Degrees.** A vertex inserted at level `j` has degree `3·2^{t-j-1}`; the vertices of `K₄` have
degree `3·2^t`. -/
theorem apo_degree {t : ℕ} (u : VT t) : (apo t).degree u = 3 * 2 ^ (t - birth (emb u)) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
  have hsplit : ∀ v : VT t, (if (apo t).Adj u v then 1 else 0) =
      (if R (emb u) (emb v) then 1 else 0) +
        (if ∃ j g, v = .inr ⟨j, g⟩ ∧ ∃ k, corners j g.1 g.2 k = emb u then 1 else 0) := by
    intro v
    rw [apo_adj]
    by_cases h1 : R (emb u) (emb v)
    · have h2 : ¬ ∃ j g, v = .inr ⟨j, g⟩ ∧ ∃ k, corners j g.1 g.2 k = emb u := by
        rintro ⟨j, g, rfl, k, hk⟩
        rcases u with a | ⟨j', f', w'⟩
        · exact h1
        · obtain ⟨k', hk'⟩ := h1
          have b1 := birth_corners (↑j) g.1 g.2 k
          have b2 := birth_corners (↑j') f' w' k'
          rw [hk] at b1
          rw [hk'] at b2
          simp only [emb, birth] at b1 b2
          omega
      simp only [h1, h2, true_or, ↓reduceIte]
    · simp only [h1, false_or, ↓reduceIte, zero_add]
  simp only [hsplit, sum_add_distrib, card_R]
  have hup : (∑ v : VT t, if ∃ j g, v = .inr ⟨j, g⟩ ∧ ∃ k, corners j g.1 g.2 k = emb u then 1
      else 0) = ∑ j ∈ range t, cnt j (emb u) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [reduceCtorEq, false_and, exists_false, ↓reduceIte, sum_const_zero, zero_add]
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ => sum_congr rfl fun g _ => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨j', g', h, hk⟩
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      rw [h]; exact hk
    · intro h; exact ⟨j, g, rfl, h⟩
  rw [hup]
  simp only [cnt_eq]
  exact geom_sum t _ (birth_emb_le u)

open Classical in
/-- Sums over the vertices, grouped by the level of insertion. -/
lemma sum_vertices {M : Type*} [AddCommMonoid M] (t : ℕ) (F : ℕ → M) :
    ∑ u : VT t, F ((apo t).degree u) =
      4 • F (3 * 2 ^ t) + ∑ j : Fin t, (4 * 3 ^ (j : ℕ)) • F (3 * 2 ^ (t - (j + 1))) := by
  simp only [apo_degree]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [emb, birth, Nat.sub_zero, sum_const, card_univ, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fun]

/-! ### Ten steps -/

lemma apo_card : Fintype.card (VT 10) = 118100 := by
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp [Fin.sum_univ_succ]

open Classical in
lemma apo_edges : #(apo 10).edgeFinset = 354294 := by
  have h := (apo 10).sum_degrees_eq_twice_card_edges
  have h2 := sum_vertices (M := ℕ) 10 id
  simp only [id] at h2
  rw [h2] at h
  simp [Fin.sum_univ_succ] at h
  omega

/-- The expected join gain on `apo 10` as a polynomial in `s = 1 - p`. -/
noncomputable def joinPoly (s : ℝ) : ℝ :=
  118100 * s - (78732 * s ^ 4 + 26244 * s ^ 7 + 8748 * s ^ 13 + 2916 * s ^ 25 + 972 * s ^ 49 +
    324 * s ^ 97 + 108 * s ^ 193 + 36 * s ^ 385 + 12 * s ^ 769 + 4 * s ^ 1537 + 4 * s ^ 3073)

open Classical in
lemma apo_join_eq (p : ℝ) :
    E p univ (fun C => (#(joined (apo 10) C) : ℝ)) = joinPoly (1 - p) := by
  have e : (fun C => (#(joined (apo 10) C) : ℝ)) =
      fun C => ∑ P, if Joins (apo 10) C P then (1 : ℝ) else 0 := by
    funext C
    rw [joined, card_filter]
    push_cast
    rfl
  rw [e, E_sum]
  simp only [E_joins, card_neighborFinset_eq_degree]
  rw [sum_vertices (M := ℝ) 10 fun d => (1 - p) * (1 - (1 - p) ^ d)]
  simp only [nsmul_eq_mul]
  generalize 1 - p = s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num [joinPoly]
  ring

/-- **`max_s` of the join polynomial.** For `s ≥ 0`, `joinPoly s ≤ 0.17402·354294`; the maximum is
`0.1740118·354294` at `s ≈ 0.67967`. -/
lemma joinPoly_le {s : ℝ} (hs : 0 ≤ s) : joinPoly s ≤ 17402 / 100000 * 354294 := by
  unfold joinPoly
  have hQ : 0 ≤ (41706392782711613983358330840747977320910055993635234656900594645980432364136412348732175266727138665406353889510939381 / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 0 + (3426595543661974809043336345688635800210292216630925299267204068923398827740606882854130343327027279436325174760063 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 1 + (14302340292649614768266569153220901318513983999064097291421632850057916281076734624664676640772152261743120173 / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 2 + (99957094638311275661753899807864404007854427193426814242545901087314086786249780465597889692745540277709 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 3 + (50501936322849711155691416529293410747339000644869544003179344799201634116731565434484585091186087 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 4 + (8083429765100461448871379197859656919076037080532042550949836702882737920136238810823004056859 / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 5 + (9608611721824250412579979302661349022849582362948879184053352769451305921082560420116447 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 6 + (235921895985876675648037029557224557323477079841248033978756025523288590473487177833 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 7 + (173889857514153847253828873317608768029707392464031449499935544432279497639847 / 15625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 8 + (6159904887559769809046840671985320877618876475232014779228252435694358923 / 500000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 9 + (152014379832108663828661383239401700547482039453578469230645102524561 / 12500000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 10 + (2279097553260957796267932509499824719805759755041879777787931397 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 11 + (312700009147961384884516952796633388168329726898731775221 / 625000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 12 + (16869461653584706468971150120710380379947263602856531 / 25000000000000000000000000000000000000000000000000 : ℝ) * s ^ 13 + (22563706255287935815069545943700459420744644263 / 25000000000000000000000000000000000000000000 : ℝ) * s ^ 14 + (2987822859587614906287255778441068971511201 / 2500000000000000000000000000000000000000 : ℝ) * s ^ 15 + (4884433883089693701497713397581945767 / 3125000000000000000000000000000000 : ℝ) * s ^ 16 + (503053499222090954588020565613807 / 250000000000000000000000000000 : ℝ) * s ^ 17 + (3172044621793922814988075509 / 1250000000000000000000000 : ℝ) * s ^ 18 + (15556787959813452680409 / 5000000000000000000 : ℝ) * s ^ 19 + (228887371221525927 / 62500000000000 : ℝ) * s ^ 20 + (10102875125643 / 2500000000 : ℝ) * s ^ 21 + (49547943 / 12500 : ℝ) * s ^ 22 + (2916 / 1 : ℝ) * s ^ 23 := by positivity
  have hrest : 0 ≤ 972 * s ^ 49 + 324 * s ^ 97 + 108 * s ^ 193 + 36 * s ^ 385 + 12 * s ^ 769 +
      4 * s ^ 1537 + 4 * s ^ 3073 := by positivity
  have hrem : 0 ≤ (13256301816026389867317556472103819970662570764520026516486241117348831086512702093252117881144557224551602796672302809 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s + (6278520288566291560762503972344215780842945679132810861278861010071455992628973530483799911916743637356703638155720784942091 / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by positivity
  have key : 17402 / 100000 * 354294 -
      (118100 * s - (78732 * s ^ 4 + 26244 * s ^ 7 + 8748 * s ^ 13 + 2916 * s ^ 25)) =
      (s - 67967 / 100000) ^ 2 * ((41706392782711613983358330840747977320910055993635234656900594645980432364136412348732175266727138665406353889510939381 / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 0 + (3426595543661974809043336345688635800210292216630925299267204068923398827740606882854130343327027279436325174760063 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 1 + (14302340292649614768266569153220901318513983999064097291421632850057916281076734624664676640772152261743120173 / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 2 + (99957094638311275661753899807864404007854427193426814242545901087314086786249780465597889692745540277709 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 3 + (50501936322849711155691416529293410747339000644869544003179344799201634116731565434484585091186087 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 4 + (8083429765100461448871379197859656919076037080532042550949836702882737920136238810823004056859 / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 5 + (9608611721824250412579979302661349022849582362948879184053352769451305921082560420116447 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 6 + (235921895985876675648037029557224557323477079841248033978756025523288590473487177833 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 7 + (173889857514153847253828873317608768029707392464031449499935544432279497639847 / 15625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 8 + (6159904887559769809046840671985320877618876475232014779228252435694358923 / 500000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 9 + (152014379832108663828661383239401700547482039453578469230645102524561 / 12500000000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 10 + (2279097553260957796267932509499824719805759755041879777787931397 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 11 + (312700009147961384884516952796633388168329726898731775221 / 625000000000000000000000000000000000000000000000000000 : ℝ) * s ^ 12 + (16869461653584706468971150120710380379947263602856531 / 25000000000000000000000000000000000000000000000000 : ℝ) * s ^ 13 + (22563706255287935815069545943700459420744644263 / 25000000000000000000000000000000000000000000 : ℝ) * s ^ 14 + (2987822859587614906287255778441068971511201 / 2500000000000000000000000000000000000000 : ℝ) * s ^ 15 + (4884433883089693701497713397581945767 / 3125000000000000000000000000000000 : ℝ) * s ^ 16 + (503053499222090954588020565613807 / 250000000000000000000000000000 : ℝ) * s ^ 17 + (3172044621793922814988075509 / 1250000000000000000000000 : ℝ) * s ^ 18 + (15556787959813452680409 / 5000000000000000000 : ℝ) * s ^ 19 + (228887371221525927 / 62500000000000 : ℝ) * s ^ 20 + (10102875125643 / 2500000000 : ℝ) * s ^ 21 + (49547943 / 12500 : ℝ) * s ^ 22 + (2916 / 1 : ℝ) * s ^ 23) + ((13256301816026389867317556472103819970662570764520026516486241117348831086512702093252117881144557224551602796672302809 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * s + (6278520288566291560762503972344215780842945679132810861278861010071455992628973530483799911916743637356703638155720784942091 / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) := by ring
  have h1 := mul_nonneg (sq_nonneg (s - 67967 / 100000)) hQ
  linarith

open Classical in
/-- **At most `0.17402` for every `p ≤ 1`.** -/
theorem apo_join_le {p : ℝ} (hp1 : p ≤ 1) :
    E p univ (fun C => (#(joined (apo 10) C) : ℝ)) ≤ 17402 / 100000 * #(apo 10).edgeFinset := by
  rw [apo_join_eq, apo_edges]
  push_cast
  exact joinPoly_le (by linarith)

set_option exponentiation.threshold 4000 in
open Classical in
/-- **`0.17161` at `p = 3/8`**, to five decimals. -/
theorem apo_join_three_eighths :
    171605 / 1000000 * (#(apo 10).edgeFinset : ℝ) ≤
        E (3 / 8) univ (fun C => (#(joined (apo 10) C) : ℝ)) ∧
      E (3 / 8) univ (fun C => (#(joined (apo 10) C) : ℝ)) <
        171615 / 1000000 * (#(apo 10).edgeFinset : ℝ) := by
  rw [apo_join_eq, apo_edges]
  unfold joinPoly
  norm_num

/-- The per-level fraction of Theorem `thm:planar` at `p = 3/8`: `0.17029` to five decimals. -/
lemma phiP_three_eighths : 170285 / 1000000 ≤ phiP (3 / 8) ∧ phiP (3 / 8) < 170295 / 1000000 := by
  unfold phiP
  norm_num

open Classical in
/-- **No lower bound above `0.17402`.** If the expected join gain on `apo 10` is at least `φ·|E|`
for some `p ≤ 1`, then `φ ≤ 0.17402`. -/
theorem apo_optimal {φ p : ℝ} (hp1 : p ≤ 1)
    (h : φ * #(apo 10).edgeFinset ≤ E p univ (fun C => (#(joined (apo 10) C) : ℝ))) :
    φ ≤ 17402 / 100000 := by
  have h1 := h.trans (apo_join_le hp1)
  rw [apo_edges] at h1
  push_cast at h1
  nlinarith

set_option exponentiation.threshold 2000 in
/-- The exponent for a per-level fraction `φ ∈ (0, 0.17402]` is above `5.74`. -/
theorem apo_kappa {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 17402 / 100000) :
    574 / 100 < kappa (1 - φ) := by
  have h := lt_kappa_nat (q := 1 - 17402 / 100000) 100000 82598 574 100 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have hm := kappa_mono (q := 1 - 17402 / 100000) (q' := 1 - φ) (by norm_num) (by linarith)
    (by linarith)
  have : ((574 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 574 / 100 := by norm_num
  linarith

end Apollonian

end Op4
