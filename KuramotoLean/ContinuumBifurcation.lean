/-
  Continuum Bifurcation Monotonicity
  ====================================
  The order parameter r* is strictly increasing in coupling K for the
  continuum Kuramoto model. Combined with equilibrium uniqueness, this
  fully characterizes the bifurcation diagram.

  For K₁ < K₂ (both > Kc): r*(K₁) < r*(K₂).

  Also: r* ≥ 1 - 2γ_max/K → 1 as K → ∞ (strong coupling limit).

  0 sorry.
-/

import KuramotoLean.ContinuumEquilibriumUniqueness

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Slope monotonicity in K -/

private theorem slope_mono_K_pointwise (γ_k K₁ K₂ r : ℝ)
    (hγ : 0 < γ_k) (hK₁ : 0 < K₁) (hr : 0 < r) (hK : K₁ < K₂) :
    K₁ / (γ_k + sqrt (γ_k ^ 2 + K₁ ^ 2 * r ^ 2)) <
    K₂ / (γ_k + sqrt (γ_k ^ 2 + K₂ ^ 2 * r ^ 2)) := by
  have hK₂ : 0 < K₂ := lt_trans hK₁ hK
  rw [div_lt_div_iff₀ (slope_den_pos γ_k hγ K₁ r) (slope_den_pos γ_k hγ K₂ r)]
  set D₁ := sqrt (γ_k ^ 2 + K₁ ^ 2 * r ^ 2)
  set D₂ := sqrt (γ_k ^ 2 + K₂ ^ 2 * r ^ 2)
  have hD₁_sq : D₁ ^ 2 = γ_k ^ 2 + K₁ ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hD₂_sq : D₂ ^ 2 = γ_k ^ 2 + K₂ ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hK₂D₁_pos : 0 < K₂ * D₁ := by positivity
  have h_sq_diff : (K₁ * D₂) ^ 2 < (K₂ * D₁) ^ 2 := by
    calc (K₁ * D₂) ^ 2 = K₁ ^ 2 * (γ_k ^ 2 + K₂ ^ 2 * r ^ 2) := by
          rw [mul_pow, hD₂_sq]
      _ < K₂ ^ 2 * (γ_k ^ 2 + K₁ ^ 2 * r ^ 2) := by
          nlinarith [sq_pos_of_pos hγ, sq_lt_sq' (by linarith) hK]
      _ = (K₂ * D₁) ^ 2 := by rw [mul_pow, hD₁_sq]
  nlinarith [lt_of_abs_lt (abs_lt_of_sq_lt_sq h_sq_diff (le_of_lt hK₂D₁_pos))]

private theorem slope_integral_strict_lt [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r₁ r₂ : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_meas : Measurable γ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ < r₂) :
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r₂ ^ 2)) ∂μ <
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r₁ ^ 2)) ∂μ := by
  have h_diff_pos : ∀ ω, (0 : ℝ) <
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r₁ ^ 2)) -
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r₂ ^ 2)) :=
    fun ω => sub_pos.mpr (slope_pointwise_strictAnti (γ ω) K (hγ_pos ω) hK
      (le_of_lt hr₁) h)
  have hf₁ := slope_integrable γ K r₁ hγ_pos hK hr₁ hγ_meas (μ := μ)
  have hf₂ := slope_integrable γ K r₂ hγ_pos hK hr₂ hγ_meas (μ := μ)
  have h_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (h_diff_pos ω)) (hf₁.sub hf₂)).mpr (by
      rw [show Function.support _ = Set.univ from Set.ext fun ω => by
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (h_diff_pos ω)]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hf₁ hf₂]

private theorem slope_integral_eq_one [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_meas : Measurable γ)
    (hfp : ∫ ω, explicitEquil (γ ω) K r ∂μ = r) :
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ = 1 := by
  have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ =
      (∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ) * r := by
    have : (fun ω => explicitEquil (γ ω) K r) =
        fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) * r := by
      ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
    rw [this, integral_mul_const]
  rw [hfp] at h_eq
  exact mul_right_cancel₀ (ne_of_gt hr) (h_eq.symm.trans (one_mul r).symm)

/-! ## r* monotonicity in K -/

theorem continuum_r_star_mono_K [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K₁ K₂ r₁ r₂ : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hfp₁ : ∫ ω, explicitEquil (γ ω) K₁ r₁ ∂μ = r₁)
    (hfp₂ : ∫ ω, explicitEquil (γ ω) K₂ r₂ ∂μ = r₂)
    (hK : K₁ < K₂) :
    r₁ < r₂ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hs₁ := slope_integral_eq_one γ K₁ r₁ hγ_pos hK₁ hr₁ hγ_meas hfp₁
  have hs₂ := slope_integral_eq_one γ K₂ r₂ hγ_pos hK₂ hr₂ hγ_meas hfp₂
  have h_K_slope : ∀ r, 0 < r →
      ∫ ω, K₁ / (γ ω + sqrt ((γ ω) ^ 2 + K₁ ^ 2 * r ^ 2)) ∂μ <
      ∫ ω, K₂ / (γ ω + sqrt ((γ ω) ^ 2 + K₂ ^ 2 * r ^ 2)) ∂μ := by
    intro r hr
    have h_pw : ∀ ω, (0 : ℝ) <
        K₂ / (γ ω + sqrt ((γ ω) ^ 2 + K₂ ^ 2 * r ^ 2)) -
        K₁ / (γ ω + sqrt ((γ ω) ^ 2 + K₁ ^ 2 * r ^ 2)) :=
      fun ω => sub_pos.mpr (slope_mono_K_pointwise (γ ω) K₁ K₂ r
        (hγ_pos ω) hK₁ hr hK)
    have hf₁ := slope_integrable γ K₁ r hγ_pos hK₁ hr hγ_meas (μ := μ)
    have hf₂ := slope_integrable γ K₂ r hγ_pos hK₂ hr hγ_meas (μ := μ)
    have h_pos := (integral_pos_iff_support_of_nonneg
      (fun ω => le_of_lt (h_pw ω)) (hf₂.sub hf₁)).mpr (by
        rw [show Function.support _ = Set.univ from Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (h_pw ω)]
        rw [measure_univ]; exact one_pos)
    linarith [integral_sub hf₂ hf₁]
  by_contra h_not
  push Not at h_not
  rcases eq_or_lt_of_le h_not with heq | hlt
  · rw [heq] at hs₂
    linarith [h_K_slope r₁ hr₁]
  · have h1 := h_K_slope r₂ hr₂
    have h3 := slope_integral_strict_lt (μ := μ) γ K₁ r₂ r₁ hγ_pos hK₁ hγ_meas hr₂ hr₁ hlt
    linarith

/-! ## Strong coupling lower bound -/

theorem continuum_r_star_lower_strong [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    1 - 2 * γ_max / K ≤ r_star := by
  set q := K * r_star / (2 * γ_max + K * r_star)
  have hden : (0 : ℝ) < 2 * γ_max + K * r_star := by positivity
  have h_each : ∀ ω, q ≤ explicitEquil (γ ω) K r_star :=
    fun ω => explicitEquil_lower_from_gamma_max (γ ω) K r_star γ_max
      (hγ_pos ω) hK hr (hγ_max ω)
  have hInt_r : Integrable (fun ω => explicitEquil (γ ω) K r_star) μ :=
    (integrable_const (1 : ℝ)).mono
      (by have hγ_meas := measurable_of_Iic hγ_level
          have hc : Continuous (fun x : ℝ => explicitEquil x K r_star) := by
            unfold explicitEquil; apply Continuous.div_const
            exact continuous_neg.add (Real.continuous_sqrt.comp
              ((continuous_pow 2).add continuous_const))
          exact (hc.measurable.comp hγ_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, norm_one]
        exact explicitEquil_abs_le_one (γ ω) K r_star (hγ_pos ω) hK)
  have h_int := integral_mono (integrable_const q) hInt_r h_each
  simp only [integral_const, smul_eq_mul, probReal_univ] at h_int
  have h_lb : q ≤ r_star := by linarith [h_int]
  rw [show q = K * r_star / (2 * γ_max + K * r_star) from rfl, div_le_iff₀ hden] at h_lb
  have h_key : K * (1 - r_star) ≤ 2 * γ_max := by nlinarith
  linarith [(le_div_iff₀ hK).mpr (by linarith : (1 - r_star) * K ≤ 2 * γ_max)]

end
