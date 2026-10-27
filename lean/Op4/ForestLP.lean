import Mathlib

/-!
# Window optima

The fractional problem of a window: minimize `∑ x` over `x ≥ 0` supported on `U` with
`∑_{w ∈ nb u} x w ≥ 1` for every `u ∈ U`. If `u ∈ nb u` for every `u ∈ U`, it has an optimal
solution (`exists_isOpt`): truncating at `1` keeps a solution feasible and does not increase its
weight, and on the box `[0,1]^V` the feasible set is compact. `locOpt U nb` is one fixed optimal
solution. It depends on `U` and `nb` only, which gives the locality of Theorem `thm:forests`.
-/

open Finset

namespace Op4

variable {V : Type*} [Fintype V]

/-- `x` is feasible for the window problem `(U, nb)`. -/
def Feas (U : Finset V) (nb : V → Finset V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ (∀ v, v ∉ U → x v = 0) ∧ ∀ u ∈ U, 1 ≤ ∑ w ∈ nb u, x w

/-- `x` is an optimal solution of the window problem `(U, nb)`. -/
def IsOpt (U : Finset V) (nb : V → Finset V) (x : V → ℝ) : Prop :=
  Feas U nb x ∧ ∀ z, Feas U nb z → ∑ v, x v ≤ ∑ v, z v

omit [Fintype V] in
/-- Truncating a feasible solution at `1` keeps it feasible. -/
lemma feas_min {U : Finset V} {nb : V → Finset V} {z : V → ℝ} (hz : Feas U nb z) :
    Feas U nb (fun v => min (z v) 1) := by
  classical
  obtain ⟨h0, h1, h2⟩ := hz
  refine ⟨fun v => le_min (h0 v) zero_le_one, fun v hv => by simp [h1 v hv], fun u hu => ?_⟩
  by_cases h : ∃ w ∈ nb u, 1 ≤ z w
  · obtain ⟨w, hw, hzw⟩ := h
    calc (1 : ℝ) = min (z w) 1 := (min_eq_right hzw).symm
      _ ≤ ∑ w ∈ nb u, min (z w) 1 :=
          single_le_sum (f := fun w => min (z w) 1) (fun w _ => le_min (h0 w) zero_le_one) hw
  · push Not at h
    calc (1 : ℝ) ≤ ∑ w ∈ nb u, z w := h2 u hu
      _ = ∑ w ∈ nb u, min (z w) 1 := sum_congr rfl fun w hw => (min_eq_left (h w hw).le).symm

/-- **The window problem has an optimal solution.** -/
theorem exists_isOpt (U : Finset V) (nb : V → Finset V) (hU : ∀ u ∈ U, u ∈ nb u) :
    ∃ x, IsOpt U nb x := by
  classical
  set C : Set (V → ℝ) := {x | Feas U nb x ∧ ∀ v, x v ≤ 1} with hCdef
  have hne : C.Nonempty := by
    refine ⟨fun v => if v ∈ U then 1 else 0, ⟨fun v => by dsimp only; split_ifs <;> norm_num,
      fun v hv => by simp [hv], fun u hu => ?_⟩, fun v => by dsimp only; split_ifs <;> norm_num⟩
    calc (1 : ℝ) = (fun v => if v ∈ U then (1 : ℝ) else 0) u := by simp [hu]
      _ ≤ ∑ w ∈ nb u, (fun v => if v ∈ U then (1 : ℝ) else 0) w :=
          single_le_sum (f := fun v => if v ∈ U then (1 : ℝ) else 0)
            (fun w _ => by split_ifs <;> norm_num) (hU u hu)
  have hclosed : IsClosed C := by
    have hC : C = (⋂ v, {x : V → ℝ | 0 ≤ x v}) ∩ (⋂ v, ⋂ (_ : v ∉ U), {x : V → ℝ | x v = 0}) ∩
        (⋂ u, ⋂ (_ : u ∈ U), {x : V → ℝ | 1 ≤ ∑ w ∈ nb u, x w}) ∩ ⋂ v, {x : V → ℝ | x v ≤ 1} := by
      ext x
      simp only [hCdef, Feas, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [hC]
    refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
    · exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
    · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply v) continuous_const
    · exact isClosed_iInter fun u => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_finsetSum _ fun w _ => continuous_apply w)
    · exact isClosed_iInter fun v => isClosed_le (continuous_apply v) continuous_const
  have hcompact : IsCompact C := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      hclosed fun x hx => ?_
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun v => ⟨hx.1.1 v, hx.2 v⟩
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hne
    (continuous_finsetSum _ fun v _ => continuous_apply v).continuousOn
  refine ⟨x, hx.1, fun z hz => ?_⟩
  have hz' : (fun v => min (z v) 1) ∈ C := ⟨feas_min hz, fun v => min_le_right _ _⟩
  calc ∑ v, x v ≤ ∑ v, min (z v) 1 := isMinOn_iff.1 hmin _ hz'
    _ ≤ ∑ v, z v := sum_le_sum fun v _ => min_le_left _ _

open Classical in
/-- A fixed optimal solution of the window problem. -/
noncomputable def locOpt (U : Finset V) (nb : V → Finset V) : V → ℝ :=
  if h : ∃ x, IsOpt U nb x then h.choose else 0

lemma locOpt_spec {U : Finset V} {nb : V → Finset V} (hU : ∀ u ∈ U, u ∈ nb u) :
    IsOpt U nb (locOpt U nb) := by
  have h := exists_isOpt U nb hU
  unfold locOpt
  rw [dite_eq_left h]
  exact h.choose_spec

end Op4
