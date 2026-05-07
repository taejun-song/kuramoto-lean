/-
  KuramotoFirstMomentConcreteV2.lean
  ===================================
  Strengthens KuramotoFirstMomentConcrete (exp 296): replaces the external
  hypothesis `hV_body_cont` with the weaker `hα_cont` (pointwise ContinuousOn
  of α), deriving body Lyapunov continuity internally via V_body_continuousOn_prob.

  This reduces the hypothesis count by 1: the caller no longer needs to supply
  body-Lyapunov continuity — it suffices to know that each trajectory α(ω,·)
  is continuous (which is immediate from ODE regularity for bounded γ).

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcrete
import KuramotoLean.VBodyContinuous

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Concrete convergence without γ_min, with α continuity hypothesis.**

    Same as `kuramoto_first_moment_concrete` (exp 296) but replaces
      `hV_body_cont : ∀ M > 0, ContinuousOn (V_body M) (Ici 0)`
    with the weaker
      `hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0)`,
    from which body Lyapunov continuity is derived via `V_body_continuousOn_prob`.

    This is the "minimal hypothesis" form: the caller does NOT need to separately
    prove continuity of the Lyapunov functional — trajectory continuity suffices. -/
theorem kuramoto_first_moment_concrete_v2 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, 0 < t → |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  have hV_body_cont : ∀ M, 0 < M → ContinuousOn
      (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0) :=
    fun M _ => V_body_continuousOn_prob γ M (hγ_level M) α α_star
      hα_cont hα_inv hα_star_pos hα_star_lt hα_sq_int
  exact kuramoto_first_moment_concrete γ K hK hγ_nn hγ_meas hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hr_bdd hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hV_body_cont hμ_body_pos

end
