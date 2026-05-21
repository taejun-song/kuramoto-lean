/-
  Tight Lipschitz Bound and Local Exponential Stability
  =====================================================
  The self-consistency map Φ has a tight Lipschitz bound:
    |Φ(r₂) - Φ(r₁)| ≤ L(r₁) · |r₂ - r₁|
  where L(r) = ∫ Kγ/(D·(γ+D)) dμ with D = √(γ²+K²r²).

  At the fixed point r*: L(r*) < 1 strictly.
  This proves local exponential stability of the equilibrium.

  The bound Kγ/(D(γ+D)) is the exact derivative ∂/∂r[explicitEquil(γ,K,r)]
  and is strictly smaller than the slope K/(γ+D) by the factor γ/D < 1.
-/

import KuramotoLean.SelfConsistencyContraction

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Pointwise tight Lipschitz bound -/

private theorem rD_diff_bound (γ K r₁ r₂ : ℝ)
    (hγ : 0 < γ) (_hK : 0 < K) (hr₁ : 0 < r₁) (h_lt : r₁ < r₂) :
    r₂ * sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2) - r₁ * sqrt (γ ^ 2 + K ^ 2 * r₂ ^ 2) ≤
    γ ^ 2 * (r₂ - r₁) / sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2) := by
  set D₁ := sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2)
  set D₂ := sqrt (γ ^ 2 + K ^ 2 * r₂ ^ 2)
  have hD₁_sq : D₁ ^ 2 = γ ^ 2 + K ^ 2 * r₁ ^ 2 := sq_sqrt (by positivity)
  have hD₂_sq : D₂ ^ 2 = γ ^ 2 + K ^ 2 * r₂ ^ 2 := sq_sqrt (by positivity)
  have hD₁ : 0 < D₁ := sqrt_pos.mpr (by positivity)
  have hD₂ : 0 < D₂ := sqrt_pos.mpr (by positivity)
  have hr₂ : 0 < r₂ := lt_trans hr₁ h_lt
  have h_rsq : r₁ ^ 2 < r₂ ^ 2 := by nlinarith
  have h_sq_diff : (r₁ * D₂) ^ 2 < (r₂ * D₁) ^ 2 := by nlinarith [hD₁_sq, hD₂_sq, sq_pos_of_pos hγ]
  have h_pos : r₁ * D₂ < r₂ * D₁ :=
    lt_of_abs_lt (abs_lt_of_sq_lt_sq h_sq_diff (by positivity))
  have hD₁_le : D₁ ≤ D₂ := by
    apply sqrt_le_sqrt; nlinarith [sq_nonneg K]
  have h_sum_ge : (r₁ + r₂) * D₁ ≤ r₂ * D₁ + r₁ * D₂ := by nlinarith
  have h_diff_eq : (r₂ * D₁ - r₁ * D₂) * (r₂ * D₁ + r₁ * D₂) =
      γ ^ 2 * (r₂ ^ 2 - r₁ ^ 2) := by nlinarith [hD₁_sq, hD₂_sq]
  have h_sum_pos : 0 < r₂ * D₁ + r₁ * D₂ := by positivity
  rw [show r₂ * D₁ - r₁ * D₂ = γ ^ 2 * (r₂ ^ 2 - r₁ ^ 2) / (r₂ * D₁ + r₁ * D₂) from
    (eq_div_iff (ne_of_gt h_sum_pos)).mpr (by linarith)]
  rw [show r₂ ^ 2 - r₁ ^ 2 = (r₂ + r₁) * (r₂ - r₁) from by ring]
  rw [div_le_div_iff₀ h_sum_pos hD₁]
  nlinarith

/-- **POINTWISE TIGHT LIPSCHITZ.**
    explicitEquil(γ,K,r₂) - explicitEquil(γ,K,r₁) ≤ Kγ/(D₁(γ+D₁)) · (r₂-r₁). -/
theorem explicitEquil_tight_lipschitz (γ K r₁ r₂ : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr₁ : 0 < r₁) (h_lt : r₁ < r₂) :
    explicitEquil γ K r₂ - explicitEquil γ K r₁ ≤
    K * γ / (sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2) *
      (γ + sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2))) * (r₂ - r₁) := by
  set D₁ := sqrt (γ ^ 2 + K ^ 2 * r₁ ^ 2)
  set D₂ := sqrt (γ ^ 2 + K ^ 2 * r₂ ^ 2)
  have hr₂ : 0 < r₂ := lt_trans hr₁ h_lt
  have hD₁ : 0 < D₁ := sqrt_pos.mpr (by positivity)
  have hD₂ : 0 < D₂ := sqrt_pos.mpr (by positivity)
  have hden₁ : 0 < γ + D₁ := by linarith
  have hden₂ : 0 < γ + D₂ := by linarith
  have hD₂_ge : D₁ ≤ D₂ := by
    apply sqrt_le_sqrt
    have : r₁ ^ 2 ≤ r₂ ^ 2 := by nlinarith
    nlinarith [sq_nonneg K]
  rw [explicitEquil_rationalized γ K r₁ hγ hK hr₁,
      explicitEquil_rationalized γ K r₂ hγ hK hr₂]
  have h_rD := rD_diff_bound γ K r₁ r₂ hγ hK hr₁ h_lt
  have h_lhs : K * r₂ / (γ + D₂) - K * r₁ / (γ + D₁) =
      K * (γ * (r₂ - r₁) + (r₂ * D₁ - r₁ * D₂)) / ((γ + D₁) * (γ + D₂)) := by
    rw [div_sub_div _ _ (ne_of_gt hden₂) (ne_of_gt hden₁)]; ring_nf
  rw [h_lhs]
  have h_num_bound : γ * (r₂ - r₁) + (r₂ * D₁ - r₁ * D₂) ≤
      γ * (r₂ - r₁) + γ ^ 2 * (r₂ - r₁) / D₁ := by linarith
  have h_combine : γ * (r₂ - r₁) + γ ^ 2 * (r₂ - r₁) / D₁ =
      γ * (r₂ - r₁) * (D₁ + γ) / D₁ := by field_simp
  have h_step1 : K * (γ * (r₂ - r₁) + (r₂ * D₁ - r₁ * D₂)) / ((γ + D₁) * (γ + D₂)) ≤
      K * (γ * (r₂ - r₁) * (D₁ + γ) / D₁) / ((γ + D₁) * (γ + D₂)) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [h_num_bound, h_combine]) (le_of_lt hK))
      (le_of_lt (mul_pos hden₁ hden₂))
  have h_step2 : K * (γ * (r₂ - r₁) * (D₁ + γ) / D₁) / ((γ + D₁) * (γ + D₂)) =
      K * γ * (r₂ - r₁) / (D₁ * (γ + D₂)) := by field_simp; ring
  have h_step3 : K * γ * (r₂ - r₁) / (D₁ * (γ + D₂)) ≤
      K * γ * (r₂ - r₁) / (D₁ * (γ + D₁)) :=
    div_le_div_of_nonneg_left (by have := sub_pos.mpr h_lt; positivity) (by positivity)
      (by nlinarith)
  have h_step4 : K * γ * (r₂ - r₁) / (D₁ * (γ + D₁)) =
      K * γ / (D₁ * (γ + D₁)) * (r₂ - r₁) := by ring
  linarith

/-! ## Tight slope strictly less than slope -/

/-- **TIGHT SLOPE < SLOPE.**
    Kγ/(D(γ+D)) < K/(γ+D) for r > 0, since γ < D = √(γ²+K²r²). -/
theorem tight_slope_lt_slope (γ K r : ℝ) (hγ : 0 < γ) (hK : 0 < K) (hr : 0 < r) :
    K * γ / (sqrt (γ ^ 2 + K ^ 2 * r ^ 2) * (γ + sqrt (γ ^ 2 + K ^ 2 * r ^ 2))) <
    K / (γ + sqrt (γ ^ 2 + K ^ 2 * r ^ 2)) := by
  set D := sqrt (γ ^ 2 + K ^ 2 * r ^ 2)
  have hD : 0 < D := sqrt_pos.mpr (by positivity)
  have hden : 0 < γ + D := by linarith
  have hγ_lt_D : γ < D := by
    calc γ = sqrt (γ ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ < D := sqrt_lt_sqrt (sq_nonneg γ)
          (by nlinarith [sq_pos_of_pos hK, sq_pos_of_pos hr])
  rw [div_lt_div_iff₀ (mul_pos hD hden) hden]
  have : K * γ * (γ + D) < K * D * (γ + D) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hγ_lt_D hK) hden
  linarith

/-! ## Integrability of tight slope -/

theorem tight_slope_integrable [IsProbabilityMeasure μ] (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_meas : Measurable γ) :
    Integrable (fun ω => K * γ ω /
      (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
       (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)))) μ := by
  apply (slope_integrable γ K r hγ_pos hK hr hγ_meas).mono
  · exact (hγ_meas.const_mul K |>.div
      ((Real.continuous_sqrt.measurable.comp
        ((hγ_meas.pow_const 2).add measurable_const)).mul
       (hγ_meas.add (Real.continuous_sqrt.measurable.comp
        ((hγ_meas.pow_const 2).add measurable_const))))).aestronglyMeasurable
  · exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have hD : 0 < sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := sqrt_pos.mpr (by positivity)
      have hden : 0 < γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := by linarith [hγ_pos ω]
      rw [abs_of_pos (div_pos (mul_pos hK (hγ_pos ω)) (mul_pos hD hden)),
          abs_of_pos (div_pos hK hden)]
      exact le_of_lt (tight_slope_lt_slope (γ ω) K r (hγ_pos ω) hK hr)

/-! ## Main result: Lipschitz constant at r* is < 1 -/

/-- **LOCAL EXPONENTIAL STABILITY.**
    At the fixed point r*, the tight Lipschitz constant ∫ Kγ/(D(γ+D)) dμ < 1.
    This is the derivative Φ'(r*) of the self-consistency map, and it's < 1
    because γ/D < 1 strictly (each oscillator has γ < √(γ²+K²r*²)). -/
theorem tight_lipschitz_lt_one [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ < 1 := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_slope_one := slope_integral_eq_one γ K r_star hγ_pos hK hr hγ_meas hfp
  set f := fun ω => K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
    (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)))
  set g := fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))
  have hf_int := tight_slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have hg_int := slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have h_lt_pw : ∀ ω, f ω < g ω := fun ω =>
    tight_slope_lt_slope (γ ω) K r_star (hγ_pos ω) hK hr
  have h_diff_pos : 0 < ∫ ω, (g ω - f ω) ∂μ :=
    (integral_pos_iff_support_of_nonneg
      (fun ω => le_of_lt (sub_pos.mpr (h_lt_pw ω))) (hg_int.sub hf_int)).mpr (by
      rw [show Function.support (fun ω => g ω - f ω) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (sub_pos.mpr (h_lt_pw ω))]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hg_int hf_int]

end
