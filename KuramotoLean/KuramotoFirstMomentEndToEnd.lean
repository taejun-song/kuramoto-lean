/-
  KuramotoFirstMomentEndToEnd.lean
  =================================
  End-to-end convergence: given K * ∫(1/γ)dμ > 2 and ODE data, there exists
  r_star ∈ (0,1) such that r(t) → r_star.

  Combines:
  - sc_fixed_point_exists_continuum (KuramotoContinuumSCFixedPoint, exp 304):
      K * ∫(1/γ) > 2 → ∃ r_star ∈ (0,1) with r_star = ∫ explicitEquil(γω,K,r_star) dμ
  - kuramoto_first_moment_concrete_v7 (exp 303):
      given r_star + ODE data → r(t) → r_star

  Net change vs v7: drops (r_star : ℝ) (hr_star_pos) (hr_star_sc);
  adds (h_inv_int) (hK_crit); generalizes hα_sq_int to ∀ r_s;
  conclusion is existential: ∃ r_star, r(t) → r_star.

  0 sorry.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV7
import KuramotoLean.KuramotoContinuumSCFixedPoint

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **End-to-end convergence from critical coupling.**

    Given K·∫(1/γ)dμ > 2, ODE and persistence hypotheses, r(t) converges to
    some fixed point r_star ∈ (0,1) of the self-consistency map. -/
theorem kuramoto_first_moment_end_to_end [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (hK_crit : 2 < K * ∫ ω, 1 / γ ω ∂μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    -- Square integrability for all candidate fixed points r_s
    (hα_sq_int : ∀ r_s : ℝ, ∀ t,
        Integrable (fun ω => (α ω t - explicitEquil (γ ω) K r_s) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_star, hr_pos, hr_lt, hr_sc⟩ :=
    sc_fixed_point_exists_continuum γ K hK hγ_pos hγ_level h_inv_int hK_crit
  exact ⟨r_star, hr_pos, hr_lt,
    kuramoto_first_moment_concrete_v7 γ K hK hγ_pos hγ_level hγ_int
      r_star hr_pos hr_sc r α hα_ode h_sc hα_int (hα_sq_int r_star)
      hα_inv α₀_lb hα₀_lb_pos hα_lb hμ_body_pos⟩

end
