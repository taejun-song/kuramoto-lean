/-
  KuramotoFirstMomentEndToEndV2.lean
  ===================================
  End-to-end convergence combining:
  - sc_fixed_point_exists_continuum (exp 304): ∃ r_star from K·∫1/γ > 2
  - kuramoto_first_moment_concrete_v8 (exp 306): drops hα_sq_int via hα_neg

  Vs end-to-end (exp 305): also drops hα_sq_int, uses hα_neg instead.
  Vs V8 (exp 306): adds h_inv_int + hK_crit to eliminate explicit r_star.

  Net signature: no explicit r_star, no hα_sq_int. Existential conclusion.

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV8
import KuramotoLean.KuramotoContinuumSCFixedPoint

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem kuramoto_first_moment_end_to_end_v2 [IsProbabilityMeasure μ]
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
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_star, hr_pos, hr_lt, hr_sc⟩ :=
    sc_fixed_point_exists_continuum γ K hK hγ_pos hγ_level h_inv_int hK_crit
  exact ⟨r_star, hr_pos, hr_lt,
    kuramoto_first_moment_concrete_v8 γ K hK hγ_pos hγ_level hγ_int
      r_star hr_pos hr_sc r α hα_ode h_sc hα_int hα_neg hα_inv
      α₀_lb hα₀_lb_pos hα_lb hμ_body_pos⟩

end
