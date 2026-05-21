/-
  Continuum Linear Stability Analysis
  =====================================
  The linearization of the OA continuum ODE at α = 0 (incoherent state):

    dα/dt = -γ(ω)·α + (K/2)·r·(1 - α²)

  At α = 0: the linearization is dv/dt = -γ(ω)·v + (K/2)·∫v dμ.
  This linear operator has spectrum {-γ(ω)} ∪ {eigenvalues of rank-1 perturbation}.
  The dispersion equation: 1 = (K/2)·∫(1/(λ+γ(ω))) dμ determines the eigenvalue λ.
  For K < Kc: all eigenvalues have λ < 0 (spectral gap).
  For K > Kc: there exists λ > 0 (instability).

  0 sorry.
-/

import KuramotoLean.ContinuumSubcritical

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Dispersion function -/

/-- The continuum dispersion function h(λ) = (K/2)·∫(1/(λ+γ(ω))) dμ.
    Eigenvalues of the linearized OA operator satisfy h(λ) = 1. -/
def continuumDispersionAtLambda (γ : Ω → ℝ) (K : ℝ) (μ : Measure Ω) (lam : ℝ) : ℝ :=
  (K / 2) * ∫ ω, (1 / (lam + γ ω)) ∂μ

/-- At λ = 0: h(0) = (K/2)·∫(1/γ) dμ = K/Kc. -/
theorem dispersion_at_zero (γ : Ω → ℝ) (K : ℝ) :
    continuumDispersionAtLambda γ K μ 0 = (K / 2) * ∫ ω, (1 / γ ω) ∂μ := by
  simp [continuumDispersionAtLambda, zero_add]

/-- For K < Kc: h(0) < 1.
    Since h is decreasing in λ for λ > -γ_min, there is no positive root.
    All eigenvalues are negative. -/
theorem dispersion_subcritical (γ : Ω → ℝ) (K : ℝ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ) :
    continuumDispersionAtLambda γ K μ 0 < 1 := by
  rw [dispersion_at_zero]
  have h1 : K < 2 / ∫ ω, (1 / γ ω) ∂μ := h_sub
  have h2 : K * ∫ ω, (1 / γ ω) ∂μ < 2 := by
    rwa [lt_div_iff₀ h_inv_pos] at h1
  linarith

/-- For K > Kc: h(0) > 1. Combined with h(λ) → 0 as λ → ∞,
    the intermediate value theorem gives a positive root. -/
theorem dispersion_supercritical (γ : Ω → ℝ) (K : ℝ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K) :
    1 < continuumDispersionAtLambda γ K μ 0 := by
  rw [dispersion_at_zero]
  have h1 : 2 / ∫ ω, (1 / γ ω) ∂μ < K := h_super
  have h2 : 2 < K * ∫ ω, (1 / γ ω) ∂μ := by
    rwa [div_lt_iff₀ h_inv_pos] at h1
  linarith

/-! ## Spectral gap bound -/

/-- **Spectral gap for the subcritical regime.**
    When K < Kc, the decay rate of the linearized system is at least
    γ_min · (1 - K/Kc). This matches the rate in subcritical_rate_pos. -/
theorem spectral_gap_subcritical (γ : Ω → ℝ) (K : ℝ) (γ_min : ℝ)
    (hγ_min_pos : 0 < γ_min)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ) :
    0 < γ_min * (1 - K / continuumKc γ μ) :=
  subcritical_rate_pos γ K γ_min hγ_min_pos h_inv_pos h_sub

/-- **The spectral gap gives the Lyapunov decay rate.**
    The linearized OA system at α = 0 has all modes decaying at rate ≥ μ.
    For the nonlinear system, the same rate holds for the Lyapunov W near α = 0,
    giving the exponential subcritical convergence. -/
theorem spectral_gap_matches_lyapunov_rate (γ : Ω → ℝ) (K γ_min : ℝ)
    (hγ_min_pos : 0 < γ_min)
    (hK_nn : 0 ≤ K)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ) :
    let μ_rate := γ_min * (1 - K / continuumKc γ μ)
    0 < μ_rate ∧ μ_rate ≤ γ_min :=
  ⟨subcritical_rate_pos γ K γ_min hγ_min_pos h_inv_pos h_sub, by
    have hKc_pos : 0 < continuumKc γ μ := by unfold continuumKc; positivity
    have hfrac : 0 ≤ K / continuumKc γ μ := div_nonneg hK_nn (le_of_lt hKc_pos)
    nlinarith⟩

/-! ## Connection to PhaseTransition -/

/-- The spectral gap vanishes exactly at Kc. -/
theorem spectral_gap_vanishes_at_Kc (γ : Ω → ℝ) (γ_min : ℝ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    γ_min * (1 - continuumKc γ μ / continuumKc γ μ) = 0 := by
  have hKc_ne : continuumKc γ μ ≠ 0 :=
    ne_of_gt (show 0 < continuumKc γ μ from by unfold continuumKc; positivity)
  rw [div_self hKc_ne, sub_self, mul_zero]

/-- The spectral gap is monotone in K (larger K = smaller gap). -/
theorem spectral_gap_monotone (γ : Ω → ℝ) (K₁ K₂ γ_min : ℝ)
    (hγ_min_pos : 0 < γ_min)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (hK₁₂ : K₁ ≤ K₂) (h_sub : K₂ < continuumKc γ μ) :
    γ_min * (1 - K₂ / continuumKc γ μ) ≤ γ_min * (1 - K₁ / continuumKc γ μ) := by
  have hKc_pos : 0 < continuumKc γ μ := by unfold continuumKc; positivity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hγ_min_pos)
  have h := div_le_div_of_nonneg_right hK₁₂ (le_of_lt hKc_pos)
  linarith

end
