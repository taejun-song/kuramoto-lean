/-
  KuramotoFirstMomentConcreteV6.lean
  ===================================
  Strengthens KuramotoFirstMomentConcreteV5 (exp 301): drops `hr_star_pos`
  (0 < r*), deriving it from:
    hr_star_eq (r* = ∫ α* ∂μ)
    + hα_star_pos (∀ ω, 0 < α* ω)
    + hαs_int (Integrable α*)

  Derivation: r* = ∫ α* ∂μ > 0 because α* > 0 everywhere and
  μ is a probability measure (total mass 1 > 0), so
    support(α*) = univ  →  μ(support(α*)) = 1 > 0
    →  0 < ∫ α* ∂μ  (by integral_pos_iff_support_of_nonneg)

  Net reduction vs kuramoto_first_moment_concrete (exp 296):
    - Drops `hV_body_cont`  (→ V_body_continuousOn_prob in V2)
    - Drops `hα_cont`       (→ HasDerivAt.continuousAt in V3)
    - Drops `hγ_meas`       (→ measurable_of_Iic in V4)
    - Drops `hr_bdd`        (→ r_abs_le_one_from_sc in V5)
    - Drops `hr_star_pos`   (→ integral_pos_iff_support_of_nonneg in V6)

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV5
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real Set Filter Topology Function

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Concrete convergence, 5 hypotheses fewer than base.**

    Drops `hr_star_pos` from V5: r* = ∫ α* ∂μ > 0 because α* > 0 everywhere
    and the support of α* is all of Ω (probability measure → μ(Ω) = 1 > 0). -/
theorem kuramoto_first_moment_concrete_v6 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq,
      integral_pos_iff_support_of_nonneg (fun ω => le_of_lt (hα_star_pos ω)) hαs_int]
    have h_supp : support α_star = Set.univ :=
      eq_univ_of_forall (fun ω => mem_support.mpr (ne_of_gt (hα_star_pos ω)))
    rw [h_supp, measure_univ]
    exact one_pos
  exact kuramoto_first_moment_concrete_v5 γ K hK hγ_nn hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hμ_body_pos

end
