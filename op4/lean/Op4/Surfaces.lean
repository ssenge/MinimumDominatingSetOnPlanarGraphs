import Op4.Density

/-!
# Certificates behind the surface table

For a surface of Euler genus `e`, Euler's formula bounds the edge density by `a_e` and the bipartite
density by `b_e` (paper, Table `tab:surfaces`). For every row with `e ≥ 3` this file checks the
pointwise certificate of Theorem `thm:general` at the dyadic `p` of the table, turns it into a
per-level bound through `general_density`, and bounds the round exponent from above by the table entry.
Every certificate uses one fact `A_t` with `t = a_e` and one or two facts `B_u` with `u ≥ 2a_e`.

## Taken as given
Euler's formula on surfaces, which gives the density bounds `a_e` and `b_e`. They enter as the
hypotheses `DensityA a_e w` and `DensityB b_e w` (`Op4.Density`).
-/

open Finset

namespace Op4

section Surfaces

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Euler genus 3: `a = 27/8`, `b = 20/9`, `p = 81/256`. -/
theorem cert_genus3 (d : ℕ) :
    3299 / 25000 * min (d : ℝ) (27 / 8) + 1351 / 25000 * (min (d : ℝ) (27 / 4) + if d = 0 then 0 else (20 / 9))
      ≤ 1 - (1 - (81 / 256)) ^ d := by
  rcases Nat.lt_or_ge d 7 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (7 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (27 / 8) = 27 / 8 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) (27 / 4) = 27 / 4 := min_eq_right (by linarith)
    rw [m0, m1, ite_eq_right hd0]
    have : (1 - (81 / 256) : ℝ) ^ d ≤ (1 - (81 / 256)) ^ 7 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 3: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus3 : (27 / 8 : ℝ) ≤ 27 / 8 ∧ 2 * (27 / 8 : ℝ) ≤ 27 / 4 := by
  norm_num

/-- Euler genus 3: the per-level fraction `(1-p)·c` with `c = 6001/25000`. -/
theorem surface_genus3 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (27 / 8) w) (hB : DensityB (20 / 9) w) :
    (1 - (81 / 256)) * (6001 / 25000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (81 / 256) univ (gain w) := by
  have h := general_density (p := (81 / 256)) (a := (27 / 8)) (b := (20 / 9)) (m := 1) (l := 1)
    (by norm_num) (by norm_num)
    ![3299 / 25000] ![27 / 8] ![1351 / 25000] ![27 / 4]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus3 d) w hw hloop hA hB
  have e : (∑ i, (![3299 / 25000] : Fin 1 → ℝ) i + 2 * ∑ j, (![1351 / 25000] : Fin 1 → ℝ) j) = 6001 / 25000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 713 in
/-- Euler genus 3: the round exponent is below 6.13. -/
theorem kappa_genus3 : kappa (1 - (1 - (81 / 256)) * (6001 / 25000)) < 613 / 100 := by
  have hq : (1 : ℝ) / (1 - (1 - (81 / 256)) * (6001 / 25000)) = 256000 / 213993 := by norm_num
  have hN : (3 : ℕ) ^ 100 * 213993 ^ 613 < 256000 ^ 613 := by decide
  have h : (3 : ℝ) ^ 100 < (1 / (1 - (1 - (81 / 256)) * (6001 / 25000))) ^ 613 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 613) (b := 100) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 4: `a = 11/3`, `b = 12/5`, `p = 39/128`. -/
theorem cert_genus4 (d : ℕ) :
    1187 / 10000 * min (d : ℝ) (11 / 3) + 4167 / 100000 * (min (d : ℝ) (22 / 3) + if d = 0 then 0 else (12 / 5)) + 251 / 25000 * (min (d : ℝ) 12 + if d = 0 then 0 else (12 / 5))
      ≤ 1 - (1 - (39 / 128)) ^ d := by
  rcases Nat.lt_or_ge d 12 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (12 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (11 / 3) = 11 / 3 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) (22 / 3) = 22 / 3 := min_eq_right (by linarith)
    have m2 : min (d : ℝ) 12 = 12 := min_eq_right (by linarith)
    rw [m0, m1, m2, ite_eq_right hd0]
    have : (1 - (39 / 128) : ℝ) ^ d ≤ (1 - (39 / 128)) ^ 12 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 4: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus4 : (11 / 3 : ℝ) ≤ 11 / 3 ∧ 2 * (11 / 3 : ℝ) ≤ 22 / 3 ∧ 2 * (11 / 3 : ℝ) ≤ 12 := by
  norm_num

/-- Euler genus 4: the per-level fraction `(1-p)·c` with `c = 5553/25000`. -/
theorem surface_genus4 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (11 / 3) w) (hB : DensityB (12 / 5) w) :
    (1 - (39 / 128)) * (5553 / 25000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (39 / 128) univ (gain w) := by
  have h := general_density (p := (39 / 128)) (a := (11 / 3)) (b := (12 / 5)) (m := 1) (l := 2)
    (by norm_num) (by norm_num)
    ![1187 / 10000] ![11 / 3] ![4167 / 100000, 251 / 25000] ![22 / 3, 12]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus4 d) w hw hloop hA hB
  have e : (∑ i, (![1187 / 10000] : Fin 1 → ℝ) i + 2 * ∑ j, (![4167 / 100000, 251 / 25000] : Fin 2 → ℝ) j) = 5553 / 25000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 231 in
/-- Euler genus 4: the round exponent is below 6.55. -/
theorem kappa_genus4 : kappa (1 - (1 - (39 / 128)) * (5553 / 25000)) < 131 / 20 := by
  have hq : (1 : ℝ) / (1 - (1 - (39 / 128)) * (5553 / 25000)) = 3200000 / 2705783 := by norm_num
  have hN : (3 : ℕ) ^ 20 * 2705783 ^ 131 < 3200000 ^ 131 := by decide
  have h : (3 : ℝ) ^ 20 < (1 / (1 - (1 - (39 / 128)) * (5553 / 25000))) ^ 131 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 131) (b := 20) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 6: `a = 21/5`, `b = 30/11`, `p = 75/256`. -/
theorem cert_genus6 (d : ℕ) :
    11869 / 100000 * min (d : ℝ) (21 / 5) + 1023 / 25000 * (min (d : ℝ) (42 / 5) + if d = 0 then 0 else (30 / 11))
      ≤ 1 - (1 - (75 / 256)) ^ d := by
  rcases Nat.lt_or_ge d 9 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (9 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (21 / 5) = 21 / 5 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) (42 / 5) = 42 / 5 := min_eq_right (by linarith)
    rw [m0, m1, ite_eq_right hd0]
    have : (1 - (75 / 256) : ℝ) ^ d ≤ (1 - (75 / 256)) ^ 9 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 6: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus6 : (21 / 5 : ℝ) ≤ 21 / 5 ∧ 2 * (21 / 5 : ℝ) ≤ 42 / 5 := by
  norm_num

/-- Euler genus 6: the per-level fraction `(1-p)·c` with `c = 20053/100000`. -/
theorem surface_genus6 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (21 / 5) w) (hB : DensityB (30 / 11) w) :
    (1 - (75 / 256)) * (20053 / 100000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (75 / 256) univ (gain w) := by
  have h := general_density (p := (75 / 256)) (a := (21 / 5)) (b := (30 / 11)) (m := 1) (l := 1)
    (by norm_num) (by norm_num)
    ![11869 / 100000] ![21 / 5] ![1023 / 25000] ![42 / 5]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus6 d) w hw hloop hA hB
  have e : (∑ i, (![11869 / 100000] : Fin 1 → ℝ) i + 2 * ∑ j, (![1023 / 25000] : Fin 1 → ℝ) j) = 20053 / 100000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 819 in
/-- Euler genus 6: the round exponent is below 7.19. -/
theorem kappa_genus6 : kappa (1 - (1 - (75 / 256)) * (20053 / 100000)) < 719 / 100 := by
  have hq : (1 : ℝ) / (1 - (1 - (75 / 256)) * (20053 / 100000)) = 25600000 / 21970407 := by norm_num
  have hN : (3 : ℕ) ^ 100 * 21970407 ^ 719 < 25600000 ^ 719 := by decide
  have h : (3 : ℝ) ^ 100 < (1 / (1 - (1 - (75 / 256)) * (20053 / 100000))) ^ 719 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 719) (b := 100) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 8: `a = 51/11`, `b = 3`, `p = 35/128`. -/
theorem cert_genus8 (d : ℕ) :
    109 / 1000 * min (d : ℝ) (51 / 11) + 73 / 2000 * (min (d : ℝ) (102 / 11) + if d = 0 then 0 else 3)
      ≤ 1 - (1 - (35 / 128)) ^ d := by
  rcases Nat.lt_or_ge d 10 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (10 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (51 / 11) = 51 / 11 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) (102 / 11) = 102 / 11 := min_eq_right (by linarith)
    rw [m0, m1, ite_eq_right hd0]
    have : (1 - (35 / 128) : ℝ) ^ d ≤ (1 - (35 / 128)) ^ 10 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 8: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus8 : (51 / 11 : ℝ) ≤ 51 / 11 ∧ 2 * (51 / 11 : ℝ) ≤ 102 / 11 := by
  norm_num

/-- Euler genus 8: the per-level fraction `(1-p)·c` with `c = 91/500`. -/
theorem surface_genus8 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (51 / 11) w) (hB : DensityB 3 w) :
    (1 - (35 / 128)) * (91 / 500) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (35 / 128) univ (gain w) := by
  have h := general_density (p := (35 / 128)) (a := (51 / 11)) (b := 3) (m := 1) (l := 1)
    (by norm_num) (by norm_num)
    ![109 / 1000] ![51 / 11] ![73 / 2000] ![102 / 11]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j; norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus8 d) w hw hloop hA hB
  have e : (∑ i, (![109 / 1000] : Fin 1 → ℝ) i + 2 * ∑ j, (![73 / 2000] : Fin 1 → ℝ) j) = 91 / 500 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 131 in
/-- Euler genus 8: the round exponent is below 7.75. -/
theorem kappa_genus8 : kappa (1 - (1 - (35 / 128)) * (91 / 500)) < 31 / 4 := by
  have hq : (1 : ℝ) / (1 - (1 - (35 / 128)) * (91 / 500)) = 64000 / 55537 := by norm_num
  have hN : (3 : ℕ) ^ 4 * 55537 ^ 31 < 64000 ^ 31 := by decide
  have h : (3 : ℝ) ^ 4 < (1 / (1 - (1 - (35 / 128)) * (91 / 500))) ^ 31 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 31) (b := 4) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 12: `a = 11/2`, `b = 24/7`, `p = 1/4`. -/
theorem cert_genus12 (d : ℕ) :
    10291 / 100000 * min (d : ℝ) (11 / 2) + 1993 / 100000 * (min (d : ℝ) 11 + if d = 0 then 0 else (24 / 7)) + 721 / 100000 * (min (d : ℝ) 15 + if d = 0 then 0 else (24 / 7))
      ≤ 1 - (1 - (1 / 4)) ^ d := by
  rcases Nat.lt_or_ge d 15 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (15 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (11 / 2) = 11 / 2 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) 11 = 11 := min_eq_right (by linarith)
    have m2 : min (d : ℝ) 15 = 15 := min_eq_right (by linarith)
    rw [m0, m1, m2, ite_eq_right hd0]
    have : (1 - (1 / 4) : ℝ) ^ d ≤ (1 - (1 / 4)) ^ 15 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 12: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus12 : (11 / 2 : ℝ) ≤ 11 / 2 ∧ 2 * (11 / 2 : ℝ) ≤ 11 ∧ 2 * (11 / 2 : ℝ) ≤ 15 := by
  norm_num

/-- Euler genus 12: the per-level fraction `(1-p)·c` with `c = 15719/100000`. -/
theorem surface_genus12 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (11 / 2) w) (hB : DensityB (24 / 7) w) :
    (1 - (1 / 4)) * (15719 / 100000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (1 / 4) univ (gain w) := by
  have h := general_density (p := (1 / 4)) (a := (11 / 2)) (b := (24 / 7)) (m := 1) (l := 2)
    (by norm_num) (by norm_num)
    ![10291 / 100000] ![11 / 2] ![1993 / 100000, 721 / 100000] ![11, 15]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus12 d) w hw hloop hA hB
  have e : (∑ i, (![10291 / 100000] : Fin 1 → ℝ) i + 2 * ∑ j, (![1993 / 100000, 721 / 100000] : Fin 2 → ℝ) j) = 15719 / 100000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 319 in
/-- Euler genus 12: the round exponent is below 8.76. -/
theorem kappa_genus12 : kappa (1 - (1 - (1 / 4)) * (15719 / 100000)) < 219 / 25 := by
  have hq : (1 : ℝ) / (1 - (1 - (1 / 4)) * (15719 / 100000)) = 400000 / 352843 := by norm_num
  have hN : (3 : ℕ) ^ 25 * 352843 ^ 219 < 400000 ^ 219 := by decide
  have h : (3 : ℝ) ^ 25 < (1 / (1 - (1 - (1 / 4)) * (15719 / 100000))) ^ 219 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 219) (b := 25) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 20: `a = 33/5`, `b = 70/17`, `p = 59/256`. -/
theorem cert_genus20 (d : ℕ) :
    45877 / 500000 * min (d : ℝ) (33 / 5) + 8409 / 500000 * (min (d : ℝ) (66 / 5) + if d = 0 then 0 else (70 / 17)) + 1071 / 250000 * (min (d : ℝ) 16 + if d = 0 then 0 else (70 / 17))
      ≤ 1 - (1 - (59 / 256)) ^ d := by
  rcases Nat.lt_or_ge d 16 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (16 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (33 / 5) = 33 / 5 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) (66 / 5) = 66 / 5 := min_eq_right (by linarith)
    have m2 : min (d : ℝ) 16 = 16 := min_eq_right (by linarith)
    rw [m0, m1, m2, ite_eq_right hd0]
    have : (1 - (59 / 256) : ℝ) ^ d ≤ (1 - (59 / 256)) ^ 16 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 20: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus20 : (33 / 5 : ℝ) ≤ 33 / 5 ∧ 2 * (33 / 5 : ℝ) ≤ 66 / 5 ∧ 2 * (33 / 5 : ℝ) ≤ 16 := by
  norm_num

/-- Euler genus 20: the per-level fraction `(1-p)·c` with `c = 66979/500000`. -/
theorem surface_genus20 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (33 / 5) w) (hB : DensityB (70 / 17) w) :
    (1 - (59 / 256)) * (66979 / 500000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (59 / 256) univ (gain w) := by
  have h := general_density (p := (59 / 256)) (a := (33 / 5)) (b := (70 / 17)) (m := 1) (l := 2)
    (by norm_num) (by norm_num)
    ![45877 / 500000] ![33 / 5] ![8409 / 500000, 1071 / 250000] ![66 / 5, 16]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus20 d) w hw hloop hA hB
  have e : (∑ i, (![45877 / 500000] : Fin 1 → ℝ) i + 2 * ∑ j, (![8409 / 500000, 1071 / 250000] : Fin 2 → ℝ) j) = 66979 / 500000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 201 in
/-- Euler genus 20: the round exponent is below 10.1. -/
theorem kappa_genus20 : kappa (1 - (1 - (59 / 256)) * (66979 / 500000)) < 101 / 10 := by
  have hq : (1 : ℝ) / (1 - (1 - (59 / 256)) * (66979 / 500000)) = 128000000 / 114805137 := by norm_num
  have hN : (3 : ℕ) ^ 10 * 114805137 ^ 101 < 128000000 ^ 101 := by decide
  have h : (3 : ℝ) ^ 10 < (1 / (1 - (1 - (59 / 256)) * (66979 / 500000))) ^ 101 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 101) (b := 10) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 100: `a = 27/2`, `b = 8`, `p = 5/32`. -/
theorem cert_genus100 (d : ℕ) :
    2843 / 50000 * min (d : ℝ) (27 / 2) + 19 / 4000 * (min (d : ℝ) 27 + if d = 0 then 0 else 8) + 159 / 100000 * (min (d : ℝ) 28 + if d = 0 then 0 else 8)
      ≤ 1 - (1 - (5 / 32)) ^ d := by
  rcases Nat.lt_or_ge d 28 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (28 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (27 / 2) = 27 / 2 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) 27 = 27 := min_eq_right (by linarith)
    have m2 : min (d : ℝ) 28 = 28 := min_eq_right (by linarith)
    rw [m0, m1, m2, ite_eq_right hd0]
    have : (1 - (5 / 32) : ℝ) ^ d ≤ (1 - (5 / 32)) ^ 28 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 100: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus100 : (27 / 2 : ℝ) ≤ 27 / 2 ∧ 2 * (27 / 2 : ℝ) ≤ 27 ∧ 2 * (27 / 2 : ℝ) ≤ 28 := by
  norm_num

/-- Euler genus 100: the per-level fraction `(1-p)·c` with `c = 3477/50000`. -/
theorem surface_genus100 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (27 / 2) w) (hB : DensityB 8 w) :
    (1 - (5 / 32)) * (3477 / 50000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (5 / 32) univ (gain w) := by
  have h := general_density (p := (5 / 32)) (a := (27 / 2)) (b := 8) (m := 1) (l := 2)
    (by norm_num) (by norm_num)
    ![2843 / 50000] ![27 / 2] ![19 / 4000, 159 / 100000] ![27, 28]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus100 d) w hw hloop hA hB
  have e : (∑ i, (![2843 / 50000] : Fin 1 → ℝ) i + 2 * ∑ j, (![19 / 4000, 159 / 100000] : Fin 2 → ℝ) j) = 3477 / 50000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 1917 in
/-- Euler genus 100: the round exponent is below 18.17. -/
theorem kappa_genus100 : kappa (1 - (1 - (5 / 32)) * (3477 / 50000)) < 1817 / 100 := by
  have hq : (1 : ℝ) / (1 - (1 - (5 / 32)) * (3477 / 50000)) = 1600000 / 1506121 := by norm_num
  have hN : (3 : ℕ) ^ 100 * 1506121 ^ 1817 < 1600000 ^ 1817 := by decide
  have h : (3 : ℝ) ^ 100 < (1 / (1 - (1 - (5 / 32)) * (3477 / 50000))) ^ 1817 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 1817) (b := 100) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

/-- Euler genus 200: `a = 37/2`, `b = 11`, `p = 33/256`. -/
theorem cert_genus200 (d : ℕ) :
    44127 / 1000000 * min (d : ℝ) (37 / 2) + 191 / 62500 * (min (d : ℝ) 37 + if d = 0 then 0 else 11) + 321 / 500000 * (min (d : ℝ) 41 + if d = 0 then 0 else 11)
      ≤ 1 - (1 - (33 / 256)) ^ d := by
  rcases Nat.lt_or_ge d 41 with h | h
  · interval_cases d <;> norm_num [min_def]
  · have hd : (41 : ℝ) ≤ d := by exact_mod_cast h
    have hd0 : d ≠ 0 := by omega
    have m0 : min (d : ℝ) (37 / 2) = 37 / 2 := min_eq_right (by linarith)
    have m1 : min (d : ℝ) 37 = 37 := min_eq_right (by linarith)
    have m2 : min (d : ℝ) 41 = 41 := min_eq_right (by linarith)
    rw [m0, m1, m2, ite_eq_right hd0]
    have : (1 - (33 / 256) : ℝ) ^ d ≤ (1 - (33 / 256)) ^ 41 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    norm_num at this ⊢
    linarith

/-- Euler genus 200: the thresholds satisfy `t ≥ a_e` and `u ≥ 2a_e`. -/
theorem thresholds_genus200 : (37 / 2 : ℝ) ≤ 37 / 2 ∧ 2 * (37 / 2 : ℝ) ≤ 37 ∧ 2 * (37 / 2 : ℝ) ≤ 41 := by
  norm_num

/-- Euler genus 200: the per-level fraction `(1-p)·c` with `c = 51523/1000000`. -/
theorem surface_genus200 (w : V → V → NNReal) (hw : ∀ P X, w P X = w X P) (hloop : ∀ P, w P P = 0)
    (hA : DensityA (37 / 2) w) (hB : DensityB 11 w) :
    (1 - (33 / 256)) * (51523 / 1000000) * ((∑ P, ∑ X, (w P X : ℝ)) / 2) ≤ E (33 / 256) univ (gain w) := by
  have h := general_density (p := (33 / 256)) (a := (37 / 2)) (b := 11) (m := 1) (l := 2)
    (by norm_num) (by norm_num)
    ![44127 / 1000000] ![37 / 2] ![191 / 62500, 321 / 500000] ![37, 41]
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i; norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun d => by simpa [Fin.sum_univ_succ, add_assoc] using cert_genus200 d) w hw hloop hA hB
  have e : (∑ i, (![44127 / 1000000] : Fin 1 → ℝ) i + 2 * ∑ j, (![191 / 62500, 321 / 500000] : Fin 2 → ℝ) j) = 51523 / 1000000 := by
    simp; norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 2493 in
/-- Euler genus 200: the round exponent is below 23.93. -/
theorem kappa_genus200 : kappa (1 - (1 - (33 / 256)) * (51523 / 1000000)) < 2393 / 100 := by
  have hq : (1 : ℝ) / (1 - (1 - (33 / 256)) * (51523 / 1000000)) = 256000000 / 244510371 := by norm_num
  have hN : (3 : ℕ) ^ 100 * 244510371 ^ 2393 < 256000000 ^ 2393 := by decide
  have h : (3 : ℝ) ^ 100 < (1 / (1 - (1 - (33 / 256)) * (51523 / 1000000))) ^ 2393 := by
    rw [hq, div_pow, lt_div_iff₀ (by positivity)]; exact_mod_cast hN
  have := kappa_lt (a := 2393) (b := 100) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢; exact this

end Surfaces

end Op4
