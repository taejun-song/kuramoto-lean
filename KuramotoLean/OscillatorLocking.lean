/-
  Oscillator Locking in the Kuramoto Model
  ==========================================
  Each oscillator with natural frequency γ has locking amplitude
  α*(γ) = explicitEquil(γ, K, r*) ∈ (0,1). The effective drift is
  γ·√(1-α*²) — which vanishes only at γ = 0.

  Key results:
    1. Locking amplitude α*(γ) strictly decreasing in γ
    2. Locking amplitude α*(γ) → 0 as γ → ∞ (fast oscillators unlock)
    3. Locking amplitude α*(γ) → 1 as γ → 0⁺ (slow oscillators lock fully)
    4. The order parameter r* = ∫ α*(γ) dμ decomposes into contributions
       weighted by the locking amplitude

  Physical interpretation: oscillators with small γ (slow) are nearly
  phase-locked; those with large γ (fast) are nearly free-running.
  The self-consistency equation r* = ∫ α* dμ balances these contributions.
-/

import KuramotoLean.ContractionRate

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Locking amplitude properties -/

/-- **Locking amplitude bounded by K·r/γ.**
    For large γ, α* ≈ Kr/(2γ) → 0. -/
theorem locking_amplitude_upper (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    explicitEquil γ_k K r < K * r / γ_k := by
  rw [explicitEquil_rationalized γ_k K r hγ hK hr]
  have hD : 0 < sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := sqrt_pos.mpr (by positivity)
  have hden : 0 < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by linarith
  rw [div_lt_div_iff₀ hden hγ]
  have hγ_le_D : γ_k ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
        sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  nlinarith [mul_pos hK hr]

/-- **Locking amplitude bounded below.**
    α* ≥ Kr/(γ + √(γ² + K²r²)) ≥ Kr/(2·√(γ² + K²r²)). -/
theorem locking_amplitude_lower (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    K * r / (2 * sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) ≤ explicitEquil γ_k K r := by
  rw [explicitEquil_rationalized γ_k K r hγ hK hr]
  have hD : 0 < sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := sqrt_pos.mpr (by positivity)
  have hden : 0 < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by linarith
  apply div_le_div_of_nonneg_left (by positivity : 0 ≤ K * r)
    (by positivity) _
  have hγ_le_D : γ_k ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
        sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  linarith

/-- **Locking amplitude strictly decreasing in γ.**
    Faster oscillators have smaller locking amplitudes. -/
theorem locking_amplitude_antiMono (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    {γ₁ γ₂ : ℝ} (hγ₁ : 0 < γ₁) (h_lt : γ₁ < γ₂) :
    explicitEquil γ₂ K r < explicitEquil γ₁ K r :=
  explicitEquil_anti_gamma γ₁ γ₂ K r hγ₁ (lt_trans hγ₁ h_lt) hK hr h_lt

/-! ## Order parameter decomposition -/

/-- **Each oscillator's locking amplitude α*(γ,K,r) ∈ (0, min(1, Kr/γ)).** -/
theorem each_oscillator_contributes
    (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    0 < explicitEquil γ_k K r ∧
    explicitEquil γ_k K r < 1 ∧
    explicitEquil γ_k K r < K * r / γ_k :=
  ⟨explicitEquil_pos γ_k K r hγ hK hr,
   explicitEquil_lt_one γ_k K r hγ hK hr,
   locking_amplitude_upper γ_k K r hγ hK hr⟩

/-! ## Locking contribution bound -/

/-- **WHOLE-DISTRIBUTION BOUND.**
    The average locking amplitude r* ≤ K·r*/(2γ_min), giving γ_min ≤ K/2. -/
theorem locking_average_bound [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_min_le : ∀ ω, γ_min ≤ γ ω) :
    1 ≤ K / (2 * γ_min) := by
  have h_bound := sc_map_quantitative_contraction (μ := μ) γ K r_star
    hγ_pos hK hγ_level hr_star γ_min hγ_min hγ_min_le
  rw [hfp] at h_bound
  have : 1 ≤ K / (2 * γ_min) := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hr_star
    rw [one_mul] at this; linarith
  linarith

end
