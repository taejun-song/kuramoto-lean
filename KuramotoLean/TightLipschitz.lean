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
import KuramotoLean.IterationConvergence
import KuramotoLean.CriticalExponent

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

/-! ## Spectral gap identity -/

/-- **SPECTRAL GAP IDENTITY.**
    The gap between the slope and the tight slope equals K³r²/(D(γ+D)²). -/
theorem spectral_gap_pointwise (γ K r : ℝ) (hγ : 0 < γ) (hK : 0 < K) (hr : 0 < r) :
    K / (γ + sqrt (γ ^ 2 + K ^ 2 * r ^ 2)) -
    K * γ / (sqrt (γ ^ 2 + K ^ 2 * r ^ 2) * (γ + sqrt (γ ^ 2 + K ^ 2 * r ^ 2))) =
    K ^ 3 * r ^ 2 / (sqrt (γ ^ 2 + K ^ 2 * r ^ 2) *
      (γ + sqrt (γ ^ 2 + K ^ 2 * r ^ 2)) ^ 2) := by
  set D := sqrt (γ ^ 2 + K ^ 2 * r ^ 2)
  have hD : 0 < D := sqrt_pos.mpr (by positivity)
  have hD_sq : D ^ 2 = γ ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hden : 0 < γ + D := by linarith
  field_simp
  nlinarith [hD_sq, sq_nonneg γ, sq_nonneg K, sq_nonneg r, sq_nonneg D,
    mul_pos hK hr, sq_pos_of_pos hD, sq_pos_of_pos hden]

/-- **SPECTRAL GAP = ∫ K³r²/(D(γ+D)²) dμ.**
    At the fixed point, 1 - λ(r*) = ∫ K³r*²/(D(γ+D)²) dμ > 0. -/
theorem spectral_gap_integral [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ =
    ∫ ω, K ^ 3 * r_star ^ 2 / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2) ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_slope_one := slope_integral_eq_one γ K r_star hγ_pos hK hr hγ_meas hfp
  have hf_int := tight_slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have hg_int := slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  rw [← h_slope_one, ← integral_sub hg_int hf_int]
  congr 1; ext ω
  exact spectral_gap_pointwise (γ ω) K r_star (hγ_pos ω) hK hr

/-- **SPECTRAL GAP LOWER BOUND.**
    1 - λ(r*) ≥ K³r*²/(D_max(γ_max+D_max)²) where D_max = √(γ_max²+K²r*²). -/
theorem spectral_gap_lower_bound [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    K ^ 3 * r_star ^ 2 / (sqrt (γ_max ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ_max + sqrt (γ_max ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2) ≤
    1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ := by
  have hγ_meas := measurable_of_Iic hγ_level
  rw [spectral_gap_integral γ K r_star hγ_pos hK hr hγ_level hfp]
  have hg_int := slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have hf_int := tight_slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have h_gap_int : Integrable (fun ω => K ^ 3 * r_star ^ 2 /
      (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2)) μ := by
    convert hg_int.sub hf_int using 1; ext ω
    exact (spectral_gap_pointwise (γ ω) K r_star (hγ_pos ω) hK hr).symm
  set D_max := sqrt (γ_max ^ 2 + K ^ 2 * r_star ^ 2)
  have hD_max : 0 < D_max := sqrt_pos.mpr (by positivity)
  have hden_max : 0 < γ_max + D_max := by linarith
  calc K ^ 3 * r_star ^ 2 / (D_max * (γ_max + D_max) ^ 2)
      = ∫ _ : Ω, K ^ 3 * r_star ^ 2 / (D_max * (γ_max + D_max) ^ 2) ∂μ := by
        rw [integral_const]; simp
    _ ≤ ∫ ω, K ^ 3 * r_star ^ 2 / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
          (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2) ∂μ := by
        apply integral_mono (integrable_const _) h_gap_int
        intro ω
        have hD_ω : 0 < sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) := sqrt_pos.mpr (by positivity)
        have hden_ω : 0 < γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) :=
          by linarith [hγ_pos ω]
        have hγ_sq : (γ ω) ^ 2 ≤ γ_max ^ 2 := by nlinarith [hγ_max ω, hγ_pos ω]
        have hD_le : sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) ≤ D_max :=
          sqrt_le_sqrt (by linarith)
        have hden_le : γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) ≤ γ_max + D_max :=
          add_le_add (hγ_max ω) hD_le
        apply div_le_div_of_nonneg_left (by positivity : 0 ≤ K ^ 3 * r_star ^ 2)
          (mul_pos hD_ω (sq_pos_of_pos hden_ω))
        exact mul_le_mul hD_le (sq_le_sq' (by linarith) hden_le) (sq_nonneg _) (le_of_lt hD_max)

/-- **SPECTRAL GAP UPPER BOUND.**
    1 - λ(r*) ≤ K³r*²/(D_min(γ_min+D_min)²) — gap vanishes as r* → 0. -/
theorem spectral_gap_upper_bound [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_min : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ ω, γ_min ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ ≤
    K ^ 3 * r_star ^ 2 / (sqrt (γ_min ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ_min + sqrt (γ_min ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2) := by
  have hγ_meas := measurable_of_Iic hγ_level
  rw [spectral_gap_integral γ K r_star hγ_pos hK hr hγ_level hfp]
  have hg_int := slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have hf_int := tight_slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have h_gap_int : Integrable (fun ω => K ^ 3 * r_star ^ 2 /
      (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2)) μ := by
    convert hg_int.sub hf_int using 1; ext ω
    exact (spectral_gap_pointwise (γ ω) K r_star (hγ_pos ω) hK hr).symm
  set D_min := sqrt (γ_min ^ 2 + K ^ 2 * r_star ^ 2)
  have hD_min : 0 < D_min := sqrt_pos.mpr (by positivity)
  have hden_min : 0 < γ_min + D_min := by linarith
  calc ∫ ω, K ^ 3 * r_star ^ 2 / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) ^ 2) ∂μ
      ≤ ∫ _ : Ω, K ^ 3 * r_star ^ 2 / (D_min * (γ_min + D_min) ^ 2) ∂μ := by
        apply integral_mono h_gap_int (integrable_const _)
        intro ω
        have hD_ω : 0 < sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) :=
          sqrt_pos.mpr (by positivity)
        have hden_ω : 0 < γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) :=
          by linarith [hγ_pos ω]
        have hγ_sq : γ_min ^ 2 ≤ (γ ω) ^ 2 := by nlinarith [hγ_min ω, hγ_min_pos]
        have hD_ge : D_min ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) :=
          sqrt_le_sqrt (by linarith)
        have hden_ge : γ_min + D_min ≤ γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) :=
          add_le_add (hγ_min ω) hD_ge
        apply div_le_div_of_nonneg_left (by positivity : 0 ≤ K ^ 3 * r_star ^ 2)
          (mul_pos hD_min (sq_pos_of_pos hden_min))
        exact mul_le_mul hD_ge (sq_le_sq' (by linarith) hden_ge)
          (sq_nonneg _) (le_of_lt hD_ω)
    _ = K ^ 3 * r_star ^ 2 / (D_min * (γ_min + D_min) ^ 2) := by
        rw [integral_const]; simp

/-- **CRITICAL SLOWING DOWN.**
    1 - λ(r*) ≤ (K-Kc)(2γ_max+K)²/(4γ_min³).
    The spectral gap vanishes linearly at K = Kc. -/
theorem critical_slowing_down [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_min γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ ω, γ_min ≤ γ ω)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ ≤
    (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / (4 * γ_min ^ 3) := by
  have h_gap := spectral_gap_upper_bound γ K r_star γ_min hγ_pos hK hr_pos
    hγ_min_pos hγ_min hγ_level hfp
  have h_rstar := rstar_le_sqrt_gap γ K r_star γ_max hγ_pos hK hr_pos hr_lt
    hγ_max_pos hγ_max hγ_level h_inv_int h_inv_pos h_super hfp
  set D_min := sqrt (γ_min ^ 2 + K ^ 2 * r_star ^ 2)
  have hD_min : 0 < D_min := sqrt_pos.mpr (by positivity)
  have hD_min_ge : γ_min ≤ D_min := by
    calc γ_min = sqrt (γ_min ^ 2) := (sqrt_sq (le_of_lt hγ_min_pos)).symm
      _ ≤ D_min := sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r_star)])
  have hden_min : 0 < γ_min + D_min := by linarith
  have h_rstar_sq : r_star ^ 2 ≤
      (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3 := by
    have h_nn : 0 ≤ (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3 := by
      apply div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
    have := sq_le_sq' (by linarith [hr_pos]) h_rstar
    rwa [sq_sqrt h_nn] at this
  calc 1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ
      ≤ K ^ 3 * r_star ^ 2 / (D_min * (γ_min + D_min) ^ 2) := h_gap
    _ ≤ K ^ 3 * r_star ^ 2 / (γ_min * (2 * γ_min) ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos hγ_min_pos (sq_pos_of_pos (by linarith)))
        exact mul_le_mul hD_min_ge (sq_le_sq' (by linarith) (by linarith))
          (sq_nonneg _) (le_of_lt hD_min)
    _ = K ^ 3 * r_star ^ 2 / (4 * γ_min ^ 3) := by ring
    _ ≤ K ^ 3 * ((K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3) /
        (4 * γ_min ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h_rstar_sq (by positivity)
    _ = (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / (4 * γ_min ^ 3) := by
        field_simp

/-- **CONTRACTION RATE UPPER BOUND.**
    λ(r) ≤ E[γ]/(Kr²) — convergence accelerates with stronger coupling. -/
theorem contraction_rate_upper [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_int_γ : Integrable γ μ) :
    ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) ∂μ ≤
    (∫ ω, γ ω ∂μ) / (K * r ^ 2) := by
  have hγ_meas := measurable_of_Iic hγ_level
  have hf_int := tight_slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have h_pw : ∀ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) ≤ γ ω / (K * r ^ 2) := by
    intro ω
    have hD : 0 < sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := sqrt_pos.mpr (by positivity)
    have hden : 0 < γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
      by linarith [hγ_pos ω]
    have hDsq : (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ^ 2 =
        (γ ω) ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
    rw [div_le_div_iff₀ (mul_pos hD hden) (by positivity : 0 < K * r ^ 2)]
    nlinarith [hγ_pos ω, sq_nonneg (γ ω)]
  have h_rw : ∀ ω, γ ω / (K * r ^ 2) = γ ω * (1 / (K * r ^ 2)) := fun ω => by ring
  calc ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) ∂μ
      ≤ ∫ ω, γ ω / (K * r ^ 2) ∂μ := integral_mono hf_int (h_int_γ.div_const _) h_pw
    _ = ∫ ω, γ ω * (1 / (K * r ^ 2)) ∂μ := by congr 1; ext ω; exact h_rw ω
    _ = (∫ ω, γ ω ∂μ) * (1 / (K * r ^ 2)) := integral_mul_const _ _
    _ = (∫ ω, γ ω ∂μ) / (K * r ^ 2) := by ring

/-- **LINEAR BOUND: Φ(r) ≤ (K/Kc) · r.**
    The self-consistency map is bounded by K/Kc times r.
    Subcritical (K < Kc): immediate contraction.
    Supercritical (K > Kc): constraint on Φ growth. -/
theorem sc_map_linear_bound [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ ≤ K / continuumKc γ μ * r := by
  have hγ_meas := measurable_of_Iic hγ_level
  have h_pw : ∀ ω, explicitEquil (γ ω) K r ≤ K * r / (2 * γ ω) := by
    intro ω
    rw [explicitEquil_rationalized (γ ω) K r (hγ_pos ω) hK hr]
    have hD : 0 < sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := sqrt_pos.mpr (by positivity)
    have hD_ge : γ ω ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := by
      calc γ ω = sqrt ((γ ω) ^ 2) := (sqrt_sq (le_of_lt (hγ_pos ω))).symm
        _ ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
          sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
    apply div_le_div_of_nonneg_left (by positivity : 0 ≤ K * r)
      (by linarith [hγ_pos ω]) (by linarith)
  have hg_int : Integrable (fun ω => K * r / (2 * γ ω)) μ := by
    have : (fun ω => K * r / (2 * γ ω)) = fun ω => (K * r / 2) * (1 / γ ω) :=
      funext fun ω => by ring
    rw [this]; exact h_inv_int.const_mul _
  have hf_int : Integrable (fun ω => explicitEquil (γ ω) K r) μ :=
    hg_int.mono
      (by have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
            unfold explicitEquil; apply Continuous.div_const
            exact continuous_neg.add (Real.continuous_sqrt.comp
              ((continuous_pow 2).add continuous_const))
          exact (hc.measurable.comp hγ_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg (le_of_lt (explicitEquil_pos (γ ω) K r (hγ_pos ω) hK hr))]
        rw [abs_of_nonneg (le_of_lt (div_pos (by positivity) (by linarith [hγ_pos ω])))]
        exact h_pw ω)
  have h_rw : (fun ω => K * r / (2 * γ ω)) = fun ω => (1 / γ ω) * (K * r / 2) :=
    funext fun ω => by ring
  calc ∫ ω, explicitEquil (γ ω) K r ∂μ
      ≤ ∫ ω, K * r / (2 * γ ω) ∂μ := integral_mono hf_int hg_int h_pw
    _ = ∫ ω, (1 / γ ω) * (K * r / 2) ∂μ := by rw [h_rw]
    _ = (∫ ω, (1 / γ ω) ∂μ) * (K * r / 2) := integral_mul_const _ _
    _ = K / continuumKc γ μ * r := by unfold continuumKc; field_simp

/-- **SUBCRITICAL EXPONENTIAL DECAY.**
    For K < Kc: Φⁿ(r₀) ≤ (K/Kc)ⁿ · r₀ → 0.
    The incoherent state is exponentially stable with rate K/Kc. -/
theorem subcritical_geometric_decay [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr₀ : 0 < r₀)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    ∀ n, scMapIter γ K μ n r₀ ≤ (K / continuumKc γ μ) ^ n * r₀ := by
  intro n
  induction n with
  | zero => simp [scMapIter]
  | succ n ih =>
    have h_pos_n := scMapIter_pos (μ := μ) γ K hγ_pos hK hγ_level r₀ hr₀ n
    calc scMapIter γ K μ (n + 1) r₀
        = ∫ ω, explicitEquil (γ ω) K (scMapIter γ K μ n r₀) ∂μ := rfl
      _ ≤ K / continuumKc γ μ * scMapIter γ K μ n r₀ :=
          sc_map_linear_bound γ K _ hγ_pos hK h_pos_n hγ_level h_inv_int h_inv_pos
      _ ≤ K / continuumKc γ μ * ((K / continuumKc γ μ) ^ n * r₀) :=
          mul_le_mul_of_nonneg_left ih (by
            have hKc : 0 < continuumKc γ μ := by unfold continuumKc; positivity
            exact le_of_lt (div_pos hK hKc))
      _ = (K / continuumKc γ μ) ^ (n + 1) * r₀ := by ring

/-! ## Geometric convergence of Picard iteration -/

private theorem equil_integrable' [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_meas : Measurable γ) :
    Integrable (fun ω => explicitEquil (γ ω) K r) μ :=
  (integrable_const (1 : ℝ)).mono
    (by have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
          unfold explicitEquil; apply Continuous.div_const
          exact continuous_neg.add (Real.continuous_sqrt.comp
            ((continuous_pow 2).add continuous_const))
        exact (hc.measurable.comp hγ_meas).aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, norm_one]
      exact le_of_lt (abs_lt.mpr
        ⟨by linarith [explicitEquil_pos (γ ω) K r (hγ_pos ω) hK hr],
         explicitEquil_lt_one (γ ω) K r (hγ_pos ω) hK hr⟩))

/-- **ONE-STEP TIGHT CONTRACTION (above r*).**
    Φ(r) - r* ≤ λ(r*) · (r - r*) for r > r*, where λ(r*) < 1. -/
theorem sc_map_tight_contraction_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r) (hr_star : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_above : r_star < r) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ - r_star ≤
    (∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ) * (r - r_star) := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hInt_r := equil_integrable' γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have hInt_rs := equil_integrable' γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ)
  have hL_int := tight_slope_integrable γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ)
  have h_pw : ∀ ω, explicitEquil (γ ω) K r - explicitEquil (γ ω) K r_star ≤
      K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) * (r - r_star) :=
    fun ω => explicitEquil_tight_lipschitz (γ ω) K r_star r (hγ_pos ω) hK hr_star h_above
  have h_ineq : ∫ ω, (explicitEquil (γ ω) K r - explicitEquil (γ ω) K r_star) ∂μ ≤
      ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) * (r - r_star) ∂μ :=
    integral_mono (hInt_r.sub hInt_rs) (hL_int.mul_const _) h_pw
  rw [integral_sub hInt_r hInt_rs, integral_mul_const] at h_ineq
  linarith

/-- **GEOMETRIC CONVERGENCE (above r*).**
    For r₀ > r*, the Picard iterates satisfy
    rₙ - r* ≤ λ(r*)ⁿ · (r₀ - r*) with λ(r*) < 1. -/
theorem scMapIter_geometric_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_above : r_star < r₀) :
    let cRate := ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ
    ∀ n, scMapIter γ K μ n r₀ - r_star ≤ cRate ^ n * (r₀ - r_star) := by
  intro cRate n
  have hfp' : scMap γ K r_star μ = r_star := hfp
  have h_above_n := scMapIter_above_rstar γ K r₀ r_star hγ_pos hK hγ_level
    hr₀ hr_star hfp' (le_of_lt h_above)
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_pw_pos : ∀ ω, 0 < K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) := fun ω =>
    div_pos (mul_pos hK (hγ_pos ω))
      (mul_pos (sqrt_pos.mpr (by positivity))
        (by linarith [hγ_pos ω,
          sqrt_pos.mpr (show 0 < (γ ω) ^ 2 + K ^ 2 * r_star ^ 2 by positivity)]))
  have hcRate_pos : 0 < cRate :=
    (integral_pos_iff_support_of_nonneg (fun ω => le_of_lt (h_pw_pos ω))
      (tight_slope_integrable γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ))).mpr (by
      rw [show Function.support (fun ω => K * γ ω /
          (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
          (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)))) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (h_pw_pos ω)]
      rw [measure_univ]; exact one_pos)
  induction n with
  | zero => simp [scMapIter]
  | succ n ih =>
    rcases eq_or_lt_of_le (h_above_n n) with h_eq | h_gt
    · have : scMapIter γ K μ (n + 1) r₀ = r_star := by
        change scMap γ K (scMapIter γ K μ n r₀) μ = r_star
        rw [← h_eq]; exact hfp'
      linarith [mul_nonneg (pow_nonneg (le_of_lt hcRate_pos) (n + 1))
        (le_of_lt (sub_pos.mpr h_above))]
    · have h_pos_n := scMapIter_pos (μ := μ) γ K hγ_pos hK hγ_level r₀ hr₀ n
      calc scMapIter γ K μ (n + 1) r₀ - r_star
          = ∫ ω, explicitEquil (γ ω) K (scMapIter γ K μ n r₀) ∂μ - r_star := rfl
        _ ≤ cRate * (scMapIter γ K μ n r₀ - r_star) :=
            sc_map_tight_contraction_above γ K _ r_star
              hγ_pos hK h_pos_n hr_star hγ_level hfp h_gt
        _ ≤ cRate * (cRate ^ n * (r₀ - r_star)) :=
            mul_le_mul_of_nonneg_left ih (le_of_lt hcRate_pos)
        _ = cRate ^ (n + 1) * (r₀ - r_star) := by ring

/-- **CONVERGENCE TO EQUILIBRIUM (above r*).**
    Picard iterates converge to r* in the topological sense. -/
theorem scMapIter_tendsto_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_above : r_star < r₀) :
    Filter.Tendsto (fun n => scMapIter γ K μ n r₀) Filter.atTop (nhds r_star) := by
  have hfp' : scMap γ K r_star μ = r_star := hfp
  have hγ_meas := measurable_of_Iic hγ_level
  set cRate := ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
    (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ
  have hcRate_lt := tight_lipschitz_lt_one γ K r_star hγ_pos hK hr_star hγ_level hfp
  have hcRate_nn : 0 ≤ cRate := by
    apply integral_nonneg; intro ω
    exact le_of_lt (div_pos (mul_pos hK (hγ_pos ω))
      (mul_pos (sqrt_pos.mpr (by positivity))
        (by linarith [hγ_pos ω,
          sqrt_pos.mpr (show 0 < (γ ω) ^ 2 + K ^ 2 * r_star ^ 2 by positivity)])))
  have h_geom := scMapIter_geometric_above γ K r₀ r_star hγ_pos hK hr₀ hr_star
    hγ_level hfp h_above
  have h_above_n := scMapIter_above_rstar γ K r₀ r_star hγ_pos hK hγ_level
    hr₀ hr_star hfp' (le_of_lt h_above)
  have h_pow_tend : Filter.Tendsto (fun n => cRate ^ n * (r₀ - r_star))
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hcRate_nn hcRate_lt
    have h2 : Filter.Tendsto (fun _ : ℕ => r₀ - r_star) Filter.atTop (nhds (r₀ - r_star)) :=
      tendsto_const_nhds
    have h3 := h1.mul h2
    simp only [zero_mul] at h3; exact h3
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (h_above_n n)
  · intro a ha
    have h_gap := sub_pos.mpr ha
    have := (tendsto_order.mp h_pow_tend).2 (a - r_star) h_gap
    exact this.mono fun n hn => by linarith [h_geom n]

end
