/-
  Quantitative Contraction Rate
  ==============================
  The self-consistency map Φ has a quantitative contraction factor:

    |Φ(r) - r*| ≤ λ · |r - r*|  for r in [δ, 1-δ]

  where λ < 1 depends on K, Kc, and the distribution.

  The key bound: for r between r₁ and r₂ (both positive),
    Φ(r₂) - Φ(r₁) ≤ (r₂ - r₁) · max_slope

  where max_slope = sup_r ∈ [r₁,r₂] Φ'(r).

  Since Φ'(r) = ∫ Kγ/(D(γ+D)) dμ < 1 (where D = √(γ²+K²r²)),
  we get contraction. The bound Φ'(r) ≤ K/(2γ_min) · something.

  For the quantitative version, we use:
    Φ(r) = r · S(r) where S is strictly decreasing
    |Φ(r) - r*| = |r·S(r) - r*·1| ≤ |r-r*|·S(r) + r*·|S(r)-1|

  But a cleaner approach: use the mean value theorem character
  of the difference quotient for the slope function.

-/

import KuramotoLean.SelfConsistencyContraction

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Quantitative contraction via slope bounds -/

/-- **Upper bound on slope integral.**
    For r ≥ r_min > 0: the slope integral is at most K/(2γ_min). -/
theorem slope_integral_upper [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_min_le : ∀ ω, γ_min ≤ γ ω) :
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ ≤ K / (2 * γ_min) := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_pw : ∀ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ≤ K / (2 * γ_min) := by
    intro ω
    have hγ_ω : γ_min ≤ γ ω := hγ_min_le ω
    have hS_ge : γ ω ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := by
      calc γ ω = sqrt ((γ ω) ^ 2) := (sqrt_sq (le_of_lt (hγ_pos ω))).symm
        _ ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
          sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
    have hden_ge : 2 * γ_min ≤ γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := by linarith
    exact div_le_div_of_nonneg_left (le_of_lt hK) (by positivity) hden_ge
  have hf_int := slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  calc ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ
      ≤ ∫ _ : Ω, K / (2 * γ_min) ∂μ := integral_mono hf_int (integrable_const _) h_pw
    _ = K / (2 * γ_min) := by simp

/-- **Lower bound on slope integral (supercritical).**
    For K > Kc: the slope integral at r = 0 would be K/Kc > 1.
    For r bounded away from 0: can bound from below. -/
theorem slope_integral_lower [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max) :
    K / (γ_max + sqrt (γ_max ^ 2 + K ^ 2 * r ^ 2)) ≤
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_pw : ∀ ω, K / (γ_max + sqrt (γ_max ^ 2 + K ^ 2 * r ^ 2)) ≤
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) := by
    intro ω
    apply div_le_div_of_nonneg_left (le_of_lt hK) (slope_den_pos (γ ω) (hγ_pos ω) K r)
    have h1 : γ ω ≤ γ_max := hγ_max ω
    have h2 : sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) ≤ sqrt (γ_max ^ 2 + K ^ 2 * r ^ 2) := by
      apply sqrt_le_sqrt
      have : γ ω ^ 2 ≤ γ_max ^ 2 :=
        sq_le_sq' (by linarith [hγ_pos ω, hγ_max_pos]) h1
      linarith
    linarith
  have hf_int := slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  calc K / (γ_max + sqrt (γ_max ^ 2 + K ^ 2 * r ^ 2))
      = ∫ _ : Ω, K / (γ_max + sqrt (γ_max ^ 2 + K ^ 2 * r ^ 2)) ∂μ := by simp
    _ ≤ ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ :=
        integral_mono (integrable_const _) hf_int h_pw

/-! ## Explicit contraction factor -/

/-- **QUANTITATIVE CONTRACTION.**
    If K/(2γ_min) < 1, the self-consistency map Φ(r) ≤ λr with λ = K/(2γ_min). -/
theorem sc_map_quantitative_contraction [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r)
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_min_le : ∀ ω, γ_min ≤ γ ω) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ ≤ K / (2 * γ_min) * r := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ =
      (∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ) * r := by
    have : (fun ω => explicitEquil (γ ω) K r) =
        fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) * r := by
      ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
    rw [this, integral_mul_const]
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right
    (slope_integral_upper γ K r hγ_pos hK hr hγ_level γ_min hγ_min hγ_min_le) (le_of_lt hr)

/-- **SUBCRITICAL NO-FIXED-POINT from contraction.**
    If K/(2γ_min) < 1, then the map Φ has no positive fixed point.
    This gives an explicit sufficient condition for incoherence. -/
theorem no_fixed_point_from_contraction [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r)
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_min_le : ∀ ω, γ_min ≤ γ ω)
    (h_sub : K / (2 * γ_min) < 1) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ < r := by
  have h_bound := sc_map_quantitative_contraction (μ := μ) γ K r hγ_pos hK hγ_level
    hr γ_min hγ_min hγ_min_le
  calc ∫ ω, explicitEquil (γ ω) K r ∂μ
      ≤ K / (2 * γ_min) * r := h_bound
    _ < 1 * r := mul_lt_mul_of_pos_right h_sub hr
    _ = r := one_mul r

end
