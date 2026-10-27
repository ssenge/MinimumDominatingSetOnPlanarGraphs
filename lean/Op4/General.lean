import Op4.Sharper

/-!
# The sharper count for classes with edge density `a` and bipartite density `b`

For a class in which every graph has `|E| ≤ a|V|` and every bipartite graph has `|E| ≤ b|V|`,
the planar facts A and B generalize to real thresholds:
* `FactAt t`: `|E| ≤ Σ_v min(d_v, t)` for `t ≥ a`;
* `FactBu u b`: `2|E| ≤ Σ_v min(d_v, u) + b·#(non-isolated vertices)` for `u ≥ 2a`.

`general` turns any pointwise certificate for finitely many such facts into a per-level bound,
through the layer-cake core `sharper_core`. `aonly` is the special case without a bipartite bound:
`E[gain] ≥ (1-p)·min(g(⌊a⌋)/⌊a⌋, g(⌈a⌉)/a)·w(G)` with `g(d) = 1 - (1-p)^d`.

## Hypotheses
As in `Op4.Sharper`, the facts enter as hypotheses here. `Op4.Density` derives them from the two
density bounds (paper, Lemma `lem:factsgen`), and `general_density` needs only these bounds.
-/

open Finset

namespace Op4

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fact `A_t`: `2|E| ≤ 2 Σ_v min(d_v, t)`. -/
def FactAt (t : ℝ) (w : V → V → NNReal) : Prop :=
  ((∑ P, deg w P : ℕ) : ℝ) ≤ 2 * ∑ P, min ((deg w P : ℕ) : ℝ) t

/-- Fact `B_u`: `2|E| ≤ Σ_v min(d_v, u) + b·#(non-isolated vertices)`. -/
def FactBu (u b : ℝ) (w : V → V → NNReal) : Prop :=
  ((∑ P, deg w P : ℕ) : ℝ) ≤ ∑ P, min ((deg w P : ℕ) : ℝ) u
    + b * (((univ.filter fun P => deg w P ≠ 0).card : ℕ) : ℝ)

omit [DecidableEq V] in
/-- **General degree lemma.** A pointwise certificate over the facts `A_{t_i}` and `B_{u_j}` gives
`Σ_P (1 - s^{d_P}) ≥ (Σ α + 2 Σ β)·|E|`. -/
theorem degree_lemma_gen {s b : ℝ} {m l : ℕ} (al t : Fin m → ℝ) (be u : Fin l → ℝ)
    (hal : ∀ i, 0 ≤ al i) (hbe : ∀ j, 0 ≤ be j)
    (hcert : ∀ d : ℕ, ∑ i, al i * min (d : ℝ) (t i)
      + ∑ j, be j * (min (d : ℝ) (u j) + if d = 0 then 0 else b) ≤ 1 - s ^ d)
    (w : V → V → NNReal) (hA : ∀ i, FactAt (t i) w) (hB : ∀ j, FactBu (u j) b w) :
    (∑ i, al i + 2 * ∑ j, be j) * (((∑ P, deg w P : ℕ) : ℝ) / 2) ≤ ∑ P, (1 - s ^ deg w P) := by
  set D : ℝ := ((∑ P, deg w P : ℕ) : ℝ)
  have hcard : (((univ.filter fun P => deg w P ≠ 0).card : ℕ) : ℝ)
      = ∑ P, (if deg w P = 0 then (0 : ℝ) else 1) := by
    rw [card_filter]; push_cast; exact sum_congr rfl fun P _ => by split_ifs <;> simp_all
  have hAi : ∀ i, al i * (D / 2) ≤ al i * ∑ P, min ((deg w P : ℕ) : ℝ) (t i) := fun i =>
    mul_le_mul_of_nonneg_left (by have := hA i; unfold FactAt at this; linarith) (hal i)
  have hBj : ∀ j, be j * D ≤ be j * (∑ P, min ((deg w P : ℕ) : ℝ) (u j)
      + b * ∑ P, (if deg w P = 0 then (0 : ℝ) else 1)) := fun j =>
    mul_le_mul_of_nonneg_left (by have := hB j; unfold FactBu at this; rw [hcard] at this; linarith)
      (hbe j)
  have e1 : ∑ P, ∑ i, al i * min ((deg w P : ℕ) : ℝ) (t i)
      = ∑ i, al i * ∑ P, min ((deg w P : ℕ) : ℝ) (t i) := by
    rw [sum_comm]; exact sum_congr rfl fun i _ => by rw [mul_sum]
  have e2 : ∑ P, ∑ j, be j * (min ((deg w P : ℕ) : ℝ) (u j) + if deg w P = 0 then 0 else b)
      = ∑ j, be j * (∑ P, min ((deg w P : ℕ) : ℝ) (u j)
        + b * ∑ P, (if deg w P = 0 then (0 : ℝ) else 1)) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum (a := b), ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun P _ => by split_ifs <;> ring
  calc (∑ i, al i + 2 * ∑ j, be j) * (D / 2)
      = (∑ i, al i) * (D / 2) + (∑ j, be j) * D := by ring
    _ = ∑ i, al i * (D / 2) + ∑ j, be j * D := by rw [sum_mul, sum_mul]
    _ ≤ ∑ i, al i * ∑ P, min ((deg w P : ℕ) : ℝ) (t i) + ∑ j, be j * (∑ P,
          min ((deg w P : ℕ) : ℝ) (u j) + b * ∑ P, (if deg w P = 0 then (0 : ℝ) else 1)) :=
        add_le_add (sum_le_sum fun i _ => hAi i) (sum_le_sum fun j _ => hBj j)
    _ = ∑ P, (∑ i, al i * min ((deg w P : ℕ) : ℝ) (t i)
          + ∑ j, be j * (min ((deg w P : ℕ) : ℝ) (u j) + if deg w P = 0 then 0 else b)) := by
        rw [sum_add_distrib, e1, e2]
    _ ≤ ∑ P, (1 - s ^ deg w P) := sum_le_sum fun P _ => hcert (deg w P)

/-- **Theorem 2 for a class with densities `a`, `b`.** If every symmetric weighting whose support
lies in that of `w` satisfies the facts, a certificate for `s = 1-p` gives
`E[gain] ≥ (1-p)(Σ α + 2 Σ β)·w(G)`. -/
theorem general {p b : ℝ} {m l : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (al t : Fin m → ℝ) (be u : Fin l → ℝ) (hal : ∀ i, 0 ≤ al i) (hbe : ∀ j, 0 ≤ be j)
    (hcert : ∀ d : ℕ, ∑ i, al i * min (d : ℝ) (t i)
      + ∑ j, be j * (min (d : ℝ) (u j) + if d = 0 then 0 else b) ≤ 1 - (1 - p) ^ d)
    (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (Hcl : ∀ v : V → V → NNReal, (∀ P X, v P X = v X P) → (∀ P X, v P X ≠ 0 → w P X ≠ 0) →
      (∀ i, FactAt (t i) v) ∧ (∀ j, FactBu (u j) b v)) :
    (1 - p) * (∑ i, al i + 2 * ∑ j, be j) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) :=
  sharper_core hp0 hp1 w hw hloop fun v hv hsub =>
    degree_lemma_gen al t be u hal hbe hcert v (Hcl v hv hsub).1 (Hcl v hv hsub).2

/-- `g(d)/d` is non-increasing: `d·(1 - s^n) ≤ n·(1 - s^d)` for `d ≤ n`. -/
lemma g_ratio {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {d n : ℕ} (hd : d ≤ n) :
    (d : ℝ) * (1 - s ^ n) ≤ n * (1 - s ^ d) := by
  induction n, hd using Nat.le_induction with
  | base => exact le_rfl
  | succ n hdn ih =>
    -- 1 - s^d = (1-s) Σ_{i<d} s^i ≥ (1-s)·d·s^n
    have hgeom : (1 - s ^ d) = (∑ i ∈ range d, s ^ i) * (1 - s) := by
      have := geom_sum_mul s d; linarith
    have hsum : (d : ℝ) * s ^ n ≤ ∑ i ∈ range d, s ^ i := by
      have : ∑ i ∈ range d, s ^ n ≤ ∑ i ∈ range d, s ^ i := sum_le_sum fun i hi =>
        pow_le_pow_of_le_one hs0 hs1 (by simp at hi; omega)
      simpa using this
    have h1s : 0 ≤ 1 - s := by linarith
    have hkey : (d : ℝ) * s ^ n * (1 - s) ≤ 1 - s ^ d := by
      rw [hgeom]; exact mul_le_mul_of_nonneg_right hsum h1s
    push_cast
    nlinarith [pow_succ s n]

/-- Certificate without a bipartite bound: `c_a · min(d, a) ≤ g(d)` for every `d`, where
`c_a = min(g(⌊a⌋)/⌊a⌋, g(⌈a⌉)/a)`. -/
theorem cert_aonly {s a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : 1 ≤ a) (d : ℕ) :
    min ((1 - s ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - s ^ ⌈a⌉₊) / a) * min (d : ℝ) a ≤ 1 - s ^ d := by
  have hf1 : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfpos : (0 : ℝ) < ⌊a⌋₊ := by exact_mod_cast hf1
  have hapos : 0 < a := by linarith
  rcases le_or_gt d ⌊a⌋₊ with h | h
  · have hda : (d : ℝ) ≤ a := le_trans (by exact_mod_cast h) (Nat.floor_le hapos.le)
    rw [min_eq_left hda]
    calc min ((1 - s ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - s ^ ⌈a⌉₊) / a) * d
        ≤ (1 - s ^ ⌊a⌋₊) / ⌊a⌋₊ * d :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg d)
      _ ≤ 1 - s ^ d := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hfpos]
          have := g_ratio hs0 hs1 h; linarith
  · have h' : ⌊a⌋₊ + 1 ≤ d := h
    have hda : a ≤ d := by
      have h1 := Nat.lt_floor_add_one a
      have h2 : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast h'
      push_cast at h2; linarith
    rw [min_eq_right hda]
    have hc : ⌈a⌉₊ ≤ d := Nat.ceil_le.mpr hda
    calc min ((1 - s ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - s ^ ⌈a⌉₊) / a) * a
        ≤ (1 - s ^ ⌈a⌉₊) / a * a := mul_le_mul_of_nonneg_right (min_le_right _ _) hapos.le
      _ = 1 - s ^ ⌈a⌉₊ := div_mul_cancel₀ _ hapos.ne'
      _ ≤ 1 - s ^ d := by have := pow_le_pow_of_le_one hs0 hs1 hc; linarith

/-- **Density only.** For a class of density `a ≥ 1`, with no bipartite bound,
`E[gain] ≥ (1-p)·min(g(⌊a⌋)/⌊a⌋, g(⌈a⌉)/a)·w(G)`. For integer `a` this is `f_a(p)` of
`random_centres`; otherwise it is larger than `f_⌈a⌉(p)`. -/
theorem aonly {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha : 1 ≤ a)
    (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (Hcl : ∀ v : V → V → NNReal, (∀ P X, v P X = v X P) → (∀ P X, v P X ≠ 0 → w P X ≠ 0) →
      FactAt a v) :
    (1 - p) * min ((1 - (1 - p) ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - (1 - p) ^ ⌈a⌉₊) / a)
      * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E p univ (gain w) := by
  have hs0 : 0 ≤ 1 - p := by linarith
  have hs1 : 1 - p ≤ 1 := by linarith
  have hc0 : 0 ≤ min ((1 - (1 - p) ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - (1 - p) ^ ⌈a⌉₊) / a) := by
    have h1 : 0 ≤ 1 - (1 - p) ^ ⌊a⌋₊ := by have := pow_le_one₀ hs0 hs1 (n := ⌊a⌋₊); linarith
    have h2 : 0 ≤ 1 - (1 - p) ^ ⌈a⌉₊ := by have := pow_le_one₀ hs0 hs1 (n := ⌈a⌉₊); linarith
    exact le_min (by positivity) (div_nonneg h2 (by linarith))
  have := general (b := 0) (m := 1) (l := 0) hp0 hp1
    ![min ((1 - (1 - p) ^ ⌊a⌋₊) / ⌊a⌋₊) ((1 - (1 - p) ^ ⌈a⌉₊) / a)] ![a] ![] ![]
    (fun i => by fin_cases i; exact hc0) (fun j => j.elim0)
    (fun d => by simpa using cert_aonly hs0 hs1 ha d) w hw hloop
    (fun v hv hsub => ⟨fun i => by fin_cases i; exact Hcl v hv hsub, fun j => j.elim0⟩)
  simpa using this

end General

end Op4
