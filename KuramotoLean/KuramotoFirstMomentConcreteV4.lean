/-
  KuramotoFirstMomentConcreteV4.lean
  ===================================
  Strengthens KuramotoFirstMomentConcreteV3 (exp 298): drops `hγ_meas`
  (AEStronglyMeasurable γ μ), deriving it from `hγ_level` via
  `measurable_of_Iic`.

  Derivation: ∀ M, MeasurableSet {ω | γ ω ≤ M}
    = ∀ M, MeasurableSet (γ ⁻¹' Iic M)  (definitional)
    → Measurable γ  (measurable_of_Iic)
    → AEStronglyMeasurable γ μ  (.aestronglyMeasurable)

  Net reduction vs kuramoto_first_moment_concrete (exp 296):
    - Drops `hV_body_cont`  (→ V_body_continuousOn_prob in V2)
    - Drops `hα_cont`       (→ HasDerivAt.continuousAt in V3)
    - Drops `hγ_meas`       (→ measurable_of_Iic in V4)

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV3

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Concrete convergence without γ_min, with minimal measurability hypotheses.**

    Drops `hγ_meas` from V3: strong measurability of γ follows from the
    assumption that all level sets {γ ≤ M} are measurable (measurable_of_Iic). -/
theorem kuramoto_first_moment_concrete_v4 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
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
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  exact kuramoto_first_moment_concrete_v3 γ K hK hγ_nn hγ_meas hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hr_bdd hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hμ_body_pos

end
