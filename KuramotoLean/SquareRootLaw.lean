/-
  Kuramoto Stability — Square Root Law for r*
  =============================================

  Proves: r*² ≥ 8(K - K_c) / (K³ · K_c · Σ c_k/γ_k³)  (lower bound)
          r*² ≤ (K - K_c)(2γ_max + K)² / K³            (upper bound)

  Together: r* = Θ(√(K - K_c)) near the bifurcation K → K_c+.

  1 sorry (slope_gap_lower_bound).
-/

import KuramotoLean.BifurcationAnalysis
import KuramotoLean.SelfConsistencyFixedPoint

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Denominator helpers -/

private theorem sqrt_ge_base (γ_k K r : ℝ) (hγ : 0 < γ_k) :
    γ_k ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
  calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
    _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
      sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])

private theorem den_pos (γ_k K r : ℝ) (hγ : 0 < γ_k) :
    0 < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
  linarith [sqrt_ge_base γ_k K r hγ]

/-! ## Each slope gap term ≤ c_k K³r²/(8γ_k³) -/

theorem slope_gap_term_le (γ_k c_k K r : ℝ) (hγ : 0 < γ_k)
    (hc : 0 < c_k) (hK : 0 < K) :
    c_k * K / (2 * γ_k) - c_k * K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) ≤
    c_k * K ^ 3 * r ^ 2 / (8 * γ_k ^ 3) := by
  set S := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
  have hS_sq : S ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hS_ge : γ_k ≤ S := sqrt_ge_base γ_k K r hγ
  have hGS : 0 < γ_k + S := by linarith
  have h2γ : (0 : ℝ) < 2 * γ_k := by positivity
  have h8γ3 : (0 : ℝ) < 8 * γ_k ^ 3 := by positivity
  rw [div_sub_div _ _ (ne_of_gt h2γ) (ne_of_gt hGS), div_le_div_iff₀
    (mul_pos h2γ hGS) h8γ3]
  have h_conj : (γ_k + S) * (S - γ_k) = K ^ 2 * r ^ 2 := by nlinarith [hS_sq]
  have hS_sub_nn : 0 ≤ S - γ_k := by linarith
  have h_sq_ge : 4 * γ_k ^ 2 ≤ (γ_k + S) ^ 2 := by nlinarith
  have h_lhs : c_k * K ^ 3 * r ^ 2 * (2 * γ_k * (γ_k + S)) =
      c_k * K * (S - γ_k) * (2 * γ_k * (γ_k + S) ^ 2) := by
    calc c_k * K ^ 3 * r ^ 2 * (2 * γ_k * (γ_k + S))
        = c_k * K * (K ^ 2 * r ^ 2) * (2 * γ_k * (γ_k + S)) := by ring
      _ = c_k * K * ((γ_k + S) * (S - γ_k)) * (2 * γ_k * (γ_k + S)) := by rw [h_conj]
      _ = c_k * K * (S - γ_k) * (2 * γ_k * (γ_k + S) ^ 2) := by ring
  have h_rhs : (c_k * K * (γ_k + S) - 2 * γ_k * (c_k * K)) * (8 * γ_k ^ 3) =
      c_k * K * (S - γ_k) * (8 * γ_k ^ 3) := by ring
  have h_coeff : 8 * γ_k ^ 3 ≤ 2 * γ_k * (γ_k + S) ^ 2 := by nlinarith
  have h_prod : c_k * K * (S - γ_k) * (8 * γ_k ^ 3) ≤
      c_k * K * (S - γ_k) * (2 * γ_k * (γ_k + S) ^ 2) := by
    apply mul_le_mul_of_nonneg_left h_coeff
    exact mul_nonneg (mul_nonneg (le_of_lt hc) (le_of_lt hK)) hS_sub_nn
  linarith

/-! ## Slope gap ≤ K³r²/8 · Σ c_k/γ_k³ -/

theorem slope_gap_upper_bound (γ c : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K) :
    scSlope γ c K 0 - scSlope γ c K r ≤
    (K ^ 3 * r ^ 2 / 8) * ∑ k, c k / γ k ^ 3 := by
  unfold scSlope
  rw [← Finset.sum_sub_distrib]
  have h0 : ∀ k, sqrt ((γ k) ^ 2 + K ^ 2 * 0 ^ 2) = γ k := fun k => by
    rw [show (γ k) ^ 2 + K ^ 2 * (0 : ℝ) ^ 2 = (γ k) ^ 2 from by ring]
    exact sqrt_sq (le_of_lt (hγ k))
  simp_rw [h0, show ∀ k, γ k + γ k = 2 * γ k from fun _ => by ring]
  calc ∑ k, (c k * K / (2 * γ k) -
      c k * K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r ^ 2)))
      ≤ ∑ k, c k * K ^ 3 * r ^ 2 / (8 * (γ k) ^ 3) :=
        Finset.sum_le_sum fun k _ =>
          slope_gap_term_le (γ k) (c k) K r (hγ k) (hc k) hK
    _ = (K ^ 3 * r ^ 2 / 8) * ∑ k, c k / (γ k) ^ 3 := by
        symm; rw [Finset.mul_sum]; congr 1; ext k; ring

/-! ## The square root law (lower bound) -/

theorem order_parameter_sq_lower_bound (γ c : Fin n → ℝ) (K r_star : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hK_super : npoleCriticalK γ c < K)
    (hr_pos : 0 < r_star)
    (hfp : scSlope γ c K r_star = 1) :
    8 * (K - npoleCriticalK γ c) /
      (K ^ 3 * npoleCriticalK γ c * ∑ k, c k / γ k ^ 3) ≤ r_star ^ 2 := by
  have hKc_pos : 0 < npoleCriticalK γ c := by
    unfold npoleCriticalK
    exact div_pos two_pos
      (sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty)
  have hsum3_pos : (0 : ℝ) < ∑ k, c k / γ k ^ 3 :=
    sum_pos (fun k _ => div_pos (hc k) (pow_pos (hγ k) 3)) univ_nonempty
  have h_gap : scSlope γ c K 0 - 1 ≤
      (K ^ 3 * r_star ^ 2 / 8) * ∑ k, c k / γ k ^ 3 := by
    rw [← hfp]; exact slope_gap_upper_bound γ c K r_star hγ hc hK
  have h_S0 : scSlope γ c K 0 = K / npoleCriticalK γ c := by
    rw [scSlope_at_zero γ c K hγ]; unfold npoleCriticalK; field_simp
  rw [h_S0] at h_gap
  have h_gap2 : (K - npoleCriticalK γ c) / npoleCriticalK γ c ≤
      (K ^ 3 * r_star ^ 2 / 8) * ∑ k, c k / γ k ^ 3 := by
    have : K / npoleCriticalK γ c - 1 =
        (K - npoleCriticalK γ c) / npoleCriticalK γ c := by
      field_simp [ne_of_gt hKc_pos]
    linarith
  rw [div_le_iff₀ (by positivity :
    0 < K ^ 3 * npoleCriticalK γ c * ∑ k, c k / γ k ^ 3)]
  have h_scaled := mul_le_mul_of_nonneg_right h_gap2
    (show (0 : ℝ) ≤ 8 * npoleCriticalK γ c from by positivity)
  have lhs_eq : (K - npoleCriticalK γ c) / npoleCriticalK γ c *
      (8 * npoleCriticalK γ c) = 8 * (K - npoleCriticalK γ c) := by
    field_simp [ne_of_gt hKc_pos]
  have rhs_eq : (K ^ 3 * r_star ^ 2 / 8) * (∑ k, c k / γ k ^ 3) *
      (8 * npoleCriticalK γ c) =
      r_star ^ 2 * (K ^ 3 * npoleCriticalK γ c * ∑ k, c k / γ k ^ 3) := by
    ring
  linarith

/-! ## Square root law upper bound: r*² ≤ (K - K_c)(2γ_max + K)²/K³

  Each summand of S(0)-S(r) uses the conjugate identity
  (γ+D)(D-γ) = K²r² with D = √(γ²+K²r²). Since D ≤ γ+Kr
  (by √(a²+b²) ≤ a+b), we get γ+D ≤ 2γ+Kr ≤ 2γ_max+K. Then
  gap_k ≥ cK³r²/(2γ(2γ_max+K)²), sum gives ≥ (K³r²/((2γ_max+K)²K_c)),
  equate with (K-K_c)/K_c to get r² ≤ (K-K_c)(2γ_max+K)²/K³. -/

theorem slope_gap_lower_bound (γ c : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hr_nn : 0 ≤ r) (hr_le : r ≤ 1)
    (γ_max : ℝ) (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, γ k ≤ γ_max) :
    K ^ 3 * r ^ 2 / ((2 * γ_max + K) ^ 2) * (∑ k, c k / γ k) / 2 ≤
    scSlope γ c K 0 - scSlope γ c K r := by
  sorry

theorem order_parameter_sq_upper_bound (γ c : Fin n → ℝ) (K r_star : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hK_super : npoleCriticalK γ c < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hfp : scSlope γ c K r_star = 1)
    (γ_max : ℝ) (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, γ k ≤ γ_max) :
    r_star ^ 2 ≤ (K - npoleCriticalK γ c) * (2 * γ_max + K) ^ 2 / K ^ 3 := by
  have hKc_pos : 0 < npoleCriticalK γ c := by
    unfold npoleCriticalK
    exact div_pos two_pos
      (sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty)
  have h_S0 : scSlope γ c K 0 = K / npoleCriticalK γ c := by
    rw [scSlope_at_zero γ c K hγ]; unfold npoleCriticalK; field_simp
  have h_sum_Kc : ∑ k, c k / γ k = 2 / npoleCriticalK γ c := by
    unfold npoleCriticalK; field_simp
  have h_gap : scSlope γ c K 0 - 1 = (K - npoleCriticalK γ c) / npoleCriticalK γ c := by
    rw [h_S0]; field_simp [ne_of_gt hKc_pos]
  have h2gK_pos : 0 < 2 * γ_max + K := by linarith
  have h_lower := slope_gap_lower_bound γ c K r_star hγ hc hK (le_of_lt hr_pos)
    (le_of_lt hr_lt) γ_max hγ_max_pos hγ_max
  rw [hfp, h_gap, h_sum_Kc] at h_lower
  have h_prod := mul_le_mul_of_nonneg_right h_lower
    (le_of_lt (mul_pos hKc_pos (pow_pos h2gK_pos 2)))
  have h_lhs : K ^ 3 * r_star ^ 2 / (2 * γ_max + K) ^ 2 *
      (2 / npoleCriticalK γ c) / 2 *
      (npoleCriticalK γ c * (2 * γ_max + K) ^ 2) =
      K ^ 3 * r_star ^ 2 := by
    field_simp [ne_of_gt hKc_pos, ne_of_gt h2gK_pos]
  have h_rhs : (K - npoleCriticalK γ c) / npoleCriticalK γ c *
      (npoleCriticalK γ c * (2 * γ_max + K) ^ 2) =
      (K - npoleCriticalK γ c) * (2 * γ_max + K) ^ 2 := by
    field_simp [ne_of_gt hKc_pos]
  rw [le_div_iff₀ (pow_pos hK 3)]; linarith

end
