/-
  LorentzianContinuumConvergence.lean
  ====================================
  Connecting file: lorentzian_explicit_tendsto → V∞ → 0.

  KEY IDEA: The Lorentzian ODE r(t) → r* is proved in LorentzianExistence.lean
  via the explicit Bernoulli closed form. The per-ω Gronwall + DCT argument in
  LorentzianPointwiseConv.lean then gives V∞(t) = ∫(α-α*)² dμ → 0 once we
  supply the r(t) → r* fact and ODE data for the per-ω OA flow.

  MAIN RESULT: lorentzian_continuum_V_inf_tendsto
    Given a probability measure μ on Ω with γ(ω) > 0 a.e., equilibrium α*,
    and OA flow data with forcing r(t) = lorentzian_explicit K γ₀ r₀:
      V∞(t) = ∫ (α(ω,t) - α*(ω))² dμ → 0

  0 sorry.
-/

import KuramotoLean.LorentzianExistence
import KuramotoLean.LorentzianPointwiseConv

open MeasureTheory Real Set Filter Topology

noncomputable section

/-- **Lorentzian continuum convergence.**
    For the Lorentzian scalar order parameter r(t) = lorentzian_explicit K γ₀ r₀,
    the continuum Lyapunov V∞(t) = ∫(α(ω,t) - α*(ω))² dμ → 0.

    Combines:
    - lorentzian_explicit_tendsto: r(t) → r* = √(1 - 2γ₀/K)
    - V_inf_tendsto_zero_from_r: per-ω Gronwall + DCT (exp 281)

    Hypotheses required beyond the Lorentzian ODE parameters:
    - μ: a probability measure on Ω
    - γ(ω) > 0 a.e.: satisfied for the Lorentzian since |ω| > 0 Lebesgue-a.e.
    - α*(ω): equilibrium satisfying γ(ω)·α*(ω) = (K/2)·r*·(1 - α*(ω)²)
    - OA flow data: existence + boundedness + measurability of α(ω,t) -/
theorem lorentzian_continuum_V_inf_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ)
    (K γ₀ r₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hγ_ae_pos : ∀ᵐ ω ∂μ, 0 < γ ω)
    (α_star : Ω → ℝ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω =
        (K / 2) * Real.sqrt (1 - 2 * γ₀ / K) * (1 - (α_star ω) ^ 2))
    (hα_star_pos : ∀ ω, 0 < α_star ω)
    (hα_star_lt : ∀ ω, α_star ω < 1)
    (α : Ω → ℝ → ℝ)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_ode : ∀ ω t, 0 < t →
        HasDerivAt (α ω) (oaScalarRHS (γ ω) K (lorentzian_explicit K γ₀ r₀) t (α ω t)) t)
    (hα_bdd : ∀ ω t, 0 ≤ t → 0 ≤ α ω t ∧ α ω t ≤ 1)
    (hα_sq_meas : ∀ t, AEStronglyMeasurable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) :=
  V_inf_tendsto_zero_from_r γ K hK hγ_ae_pos α_star
    (Real.sqrt (1 - 2 * γ₀ / K))
    (Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ₀ hK hKγ₀))
    hα_star_pos hα_star_lt hα_star_equil
    (lorentzian_explicit K γ₀ r₀)
    (lorentzian_explicit_tendsto K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt)
    α hα_cont hα_ode hα_bdd hα_sq_meas

end
