/-
  KuramotoFirstMomentConcreteV3.lean
  ===================================
  Strengthens KuramotoFirstMomentConcreteV2 (exp 297): drops `hα_cont`
  (pointwise ContinuousOn of α), deriving it internally from `hα_ode`
  via HasDerivAt.continuousAt.

  Derivation: HasDerivAt (α ω) _ t at every t ≥ 0
    → ContinuousAt (α ω) t  (HasDerivAt.continuousAt)
    → ContinuousWithinAt (α ω) (Ici 0) t  (ContinuousAt.continuousWithinAt)
    → ContinuousOn (α ω) (Ici 0)

  Net reduction vs kuramoto_first_moment_concrete (exp 296):
    - Drops `hV_body_cont`  (replaced by V_body_continuousOn_prob in V2)
    - Drops `hα_cont`       (derived from hα_ode here)

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV2

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Concrete convergence without γ_min, with minimal continuity hypotheses.**

    Drops `hα_cont` from V2: trajectory continuity follows from the ODE
    (HasDerivAt implies ContinuousAt implies ContinuousWithinAt). -/
theorem kuramoto_first_moment_concrete_v3 [IsProbabilityMeasure μ]
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
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  have hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0) :=
    fun ω t ht => (hα_ode ω t (mem_Ici.mp ht)).continuousAt.continuousWithinAt
  exact kuramoto_first_moment_concrete_v2 γ K hK hγ_nn hγ_meas hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hr_bdd hα_ode h_sc hα_int hα_sq_int hα_inv hα_cont
    α₀_lb hα₀_lb_pos hα_lb hμ_body_pos

end
