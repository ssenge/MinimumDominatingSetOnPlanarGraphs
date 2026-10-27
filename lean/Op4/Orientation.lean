import Op4.RandomCentres

/-!
# Orientations with bounded out-degree

The orientation theorem of [5] in the README: if every vertex set `S` spans at most `k·|S|`
edges, the edges can be oriented so that every vertex has out-degree at most `k`. The proof is
Hall's theorem: match every edge to one of `k` copies of one of its endpoints. A set `s` of edges
meets `k·|U|` copies, where `U` is the set of their endpoints, and `|s| ≤ k·|U|` is the density
bound for `U`.

* `orientation_of_density`: the orientation, in the form used by `random_centres` and
  `arcs_eq_half_total`.
* `random_centres_density`: `random_centres` with the orientation hypothesis replaced by the density
  bound, `E[gain] ≥ (1-p)(1-(1-p)^k)/k · w(G)`.

The density bound is stated for ordered pairs: `S` contains at most `2k·|S|` ordered pairs
`(P, X)` with `w P X ≠ 0`, that is, at most `k·|S|` edges.
-/

open Finset

namespace Op4

section Orientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordered pairs `(P, X)` of `S` with `w P X ≠ 0`; every edge inside `S` is counted twice. -/
noncomputable def pairsIn (w : V → V → NNReal) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun x => w x.1 x.2 ≠ 0

/-- **Orientation theorem.** If every `S` spans at most `k·|S|` edges, there is an orientation `O`
of the support of `w` with out-degree at most `k`: `X ∈ O P` means that the edge `PX` points from
`P` to `X`, and every edge is oriented exactly once. -/
theorem orientation_of_density (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P)
    (hloop : ∀ P, w P P = 0) (k : ℕ)
    (hden : ∀ S : Finset V, (pairsIn w S).card ≤ 2 * k * S.card) :
    ∃ O : V → Finset V, (∀ P, P ∉ O P) ∧ (∀ P, (O P).card ≤ k) ∧
      (∀ P X, X ∈ O P → w P X ≠ 0) ∧ (∀ P X, w P X ≠ 0 → (X ∈ O P ↔ P ∉ O X)) := by
  classical
  -- a ranking of the vertices, used to name each edge by one ordered pair
  set r : V → ℕ := fun v => (Fintype.equivFin V v : ℕ) with hr
  have hrinj : Function.Injective r := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  have hne : ∀ P X, w P X ≠ 0 → P ≠ X := fun P X h hPX => h (hPX ▸ hloop P)
  -- the edges, as pairs `(P, X)` with `r P < r X`
  set E : Finset (V × V) := univ.filter fun x => w x.1 x.2 ≠ 0 ∧ r x.1 < r x.2 with hE
  have hEmem : ∀ e : E, w e.1.1 e.1.2 ≠ 0 ∧ r e.1.1 < r e.1.2 := fun e => (mem_filter.1 e.2).2
  -- every edge may use one of `k` copies of either endpoint
  set t : E → Finset (V × Fin k) := fun e => ({e.1.1, e.1.2} : Finset V) ×ˢ univ with ht
  have hall : ∀ s : Finset E, s.card ≤ (s.biUnion t).card := by
    intro s
    set U : Finset V := s.biUnion fun e => ({e.1.1, e.1.2} : Finset V) with hU
    have hbu : s.biUnion t = U ×ˢ (univ : Finset (Fin k)) := by
      ext ⟨v, c⟩
      simp [ht, hU]
    rw [hbu, card_product, card_univ, Fintype.card_fin]
    set L := (pairsIn w U).filter fun x => r x.1 < r x.2 with hL
    have h1 : s.card ≤ L.card := by
      refine card_le_card_of_injOn (fun e => e.1) ?_ (fun a _ b _ h => Subtype.ext h)
      intro e he
      have he' : e ∈ s := he
      have hU1 : e.1.1 ∈ U := mem_biUnion.2 ⟨e, he', by simp⟩
      have hU2 : e.1.2 ∈ U := mem_biUnion.2 ⟨e, he', by simp⟩
      simp only [mem_coe, hL, pairsIn, mem_filter, mem_product]
      exact ⟨⟨⟨hU1, hU2⟩, (hEmem e).1⟩, (hEmem e).2⟩
    have h2 : 2 * L.card ≤ (pairsIn w U).card := by
      have hsplit : L.card + ((pairsIn w U).filter fun x => ¬ r x.1 < r x.2).card
          = (pairsIn w U).card := card_filter_add_card_filter_not _
      have hswap : L.card ≤ ((pairsIn w U).filter fun x => ¬ r x.1 < r x.2).card := by
        refine card_le_card_of_injOn Prod.swap ?_ (fun a _ b _ h => Prod.swap_injective h)
        intro x hx
        have hx' : x ∈ L := hx
        simp only [hL, pairsIn, mem_filter, mem_product] at hx'
        simp only [mem_coe, pairsIn, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap]
        exact ⟨⟨⟨hx'.1.1.2, hx'.1.1.1⟩, by rw [hw]; exact hx'.1.2⟩, by omega⟩
      omega
    have h3 : L.card ≤ k * U.card := by
      have := hden U
      exact Nat.le_of_mul_le_mul_left (by rw [← mul_assoc]; omega) (by norm_num : 0 < 2)
    rw [mul_comm]; omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfend : ∀ e : E, (f e).1 = e.1.1 ∨ (f e).1 = e.1.2 := fun e => by
    have := hft e
    simp only [ht, mem_product, mem_insert, mem_singleton] at this
    exact this.1
  -- `P` owns the edges matched to its copies; it orients them away from itself
  set A : V → Finset E := fun P => univ.filter fun e => (f e).1 = P with hA
  set oth : V → E → V := fun P e => if e.1.1 = P then e.1.2 else e.1.1 with hoth
  -- the name of the edge `PX`
  set c : V → V → V × V := fun P X => if r P < r X then (P, X) else (X, P) with hc
  have hcform : ∀ P X, (c P X = (P, X) ∧ r P < r X) ∨ (c P X = (X, P) ∧ ¬ r P < r X) :=
    fun P X => by
      by_cases hlt : r P < r X
      · left; simp [hc, hlt]
      · right; simp [hc, hlt]
  have hcE : ∀ P X, w P X ≠ 0 → c P X ∈ E := fun P X h => by
    have hrne : r P ≠ r X := fun h' => hne P X h (hrinj h')
    rw [hE, mem_filter]
    rcases hcform P X with ⟨h1, hlt⟩ | ⟨h1, hlt⟩
    · rw [h1]; exact ⟨mem_univ _, h, hlt⟩
    · rw [h1]; exact ⟨mem_univ _, by rw [hw]; exact h, show r X < r P by omega⟩
  have hcsymm : ∀ P X, P ≠ X → c X P = c P X := fun P X h => by
    have hrne : r P ≠ r X := fun h' => h (hrinj h')
    rcases hcform P X with ⟨h1, hlt⟩ | ⟨h1, hlt⟩ <;>
      rcases hcform X P with ⟨h2, hlt2⟩ | ⟨h2, hlt2⟩ <;>
      first | omega | rw [h1, h2]
  -- `X ∈ O P` exactly when the edge `PX` is matched to a copy of `P`
  have key : ∀ P X (h : w P X ≠ 0),
      (X ∈ (A P).image (oth P) ↔ (f ⟨c P X, hcE P X h⟩).1 = P) := fun P X h => by
    constructor
    · intro hX
      obtain ⟨e, heA, heo⟩ := mem_image.1 hX
      have hfe : (f e).1 = P := by simpa [hA] using heA
      have hlt := (hEmem e).2
      have hec : e.1 = c P X := by
        by_cases h1 : e.1.1 = P
        · have h2 : e.1.2 = X := by simpa [hoth, h1] using heo
          have hlt' : r P < r X := by rw [← h1, ← h2]; exact hlt
          simp only [hc, hlt', ↓reduceIte]
          exact Prod.ext h1 h2
        · have h2 : e.1.1 = X := by simpa [hoth, h1] using heo
          have h3 : e.1.2 = P := by
            rcases hfend e with h3 | h3
            · exact absurd (h3.symm.trans hfe) h1
            · exact h3.symm.trans hfe
          have hlt' : ¬ r P < r X := by rw [← h2, ← h3]; omega
          simp only [hc, hlt', ↓reduceIte]
          exact Prod.ext h2 h3
      have : e = ⟨c P X, hcE P X h⟩ := Subtype.ext hec
      rw [← this]; exact hfe
    · intro hf
      refine mem_image.2 ⟨⟨c P X, hcE P X h⟩, by simp [hA, hf], ?_⟩
      have hPX := hne P X h
      show (if (c P X).1 = P then (c P X).2 else (c P X).1) = X
      rcases hcform P X with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; simp
      · rw [h1]; simp [Ne.symm hPX]
  refine ⟨fun P => (A P).image (oth P), ?_, ?_, ?_, ?_⟩
  · -- no loops
    intro P hP
    obtain ⟨e, heA, heo⟩ := mem_image.1 hP
    have hlt := (hEmem e).2
    by_cases h1 : e.1.1 = P
    · have h2 : e.1.2 = P := by simpa [hoth, h1] using heo
      rw [h1, h2] at hlt; omega
    · simp [hoth, h1] at heo
  · -- out-degree at most `k`
    intro P
    refine (card_image_le).trans ?_
    calc (A P).card ≤ (univ : Finset (Fin k)).card := by
          refine card_le_card_of_injOn (fun e => (f e).2) (fun e _ => by simp) ?_
          intro a ha b hb hab
          have ha' : (f a).1 = P := by simpa [hA] using ha
          have hb' : (f b).1 = P := by simpa [hA] using hb
          exact hfinj (Prod.ext (ha'.trans hb'.symm) hab)
      _ = k := by simp
  · -- only support edges are oriented
    intro P X hX
    obtain ⟨e, heA, heo⟩ := mem_image.1 hX
    have hfe : (f e).1 = P := by simpa [hA] using heA
    have hwe := (hEmem e).1
    by_cases h1 : e.1.1 = P
    · have h2 : e.1.2 = X := by simpa [hoth, h1] using heo
      rw [← h1, ← h2]; exact hwe
    · have h2 : e.1.1 = X := by simpa [hoth, h1] using heo
      have h3 : e.1.2 = P := by
        rcases hfend e with h3 | h3
        · exact absurd (h3.symm.trans hfe) h1
        · exact h3.symm.trans hfe
      rw [← h2, ← h3, hw]; exact hwe
  · -- every edge is oriented exactly once
    intro P X h
    have h' : w X P ≠ 0 := by rw [hw]; exact h
    have hPX := hne P X h
    rw [key P X h, key X P h',
      show (⟨c X P, hcE X P h'⟩ : E) = ⟨c P X, hcE P X h⟩ from Subtype.ext (hcsymm P X hPX)]
    set e0 : E := ⟨c P X, hcE P X h⟩ with he0
    have hend : (f e0).1 = (c P X).1 ∨ (f e0).1 = (c P X).2 := hfend e0
    have hPorX : (f e0).1 = P ∨ (f e0).1 = X := by
      rcases hcform P X with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hend; exact hend
      · rw [h1] at hend; exact hend.symm
    constructor
    · intro h1 h2; exact hPX (h1.symm.trans h2)
    · intro h1; tauto

/-- **One level for a class of density `k`.** If every vertex set `S` spans at most `k·|S|`
edges of `w`, then `E[gain] ≥ (1-p)(1-(1-p)^k)/k · w(G)`, with `w(G) = Σ_P Σ_X w(P,X) / 2`. -/
theorem random_centres_density {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : V → V → NNReal)
    (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0) {k : ℕ} (hk : 0 < k)
    (hden : ∀ S : Finset V, (pairsIn w S).card ≤ 2 * k * S.card) :
    (1 - p) * (1 - (1 - p) ^ k) / k * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) := by
  obtain ⟨O, hO, hOk, -, hOe⟩ := orientation_of_density w hw hloop k hden
  have h := random_centres hp0 hp1 w O hO hk hOk
  have ha := arcs_eq_half_total w hw O hOe
  rw [show (∑ P, ∑ X, (w P X : ℝ)) / 2 = ∑ P, ∑ X ∈ O P, (w P X : ℝ) by linarith]
  exact h

end Orientation

end Op4
