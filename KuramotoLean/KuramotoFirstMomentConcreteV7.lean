/-
  KuramotoFirstMomentConcreteV7.lean
  ===================================
  Strengthens KuramotoFirstMomentConcreteV6 (exp 302): drops the explicit
  equilibrium data (α_star, hα_star_pos, hα_star_lt, hαs_int, hα_star_equil,
  hr_star_eq) by defining α_star internally via the closed-form formula:
    α_star ω := explicitEquil (γ ω) K r_star

  Replaces 6 hypotheses with 3:
    hγ_pos : ∀ ω, 0 < γ ω   (strengthens hγ_nn to strict positivity)
    hr_star_pos : 0 < r_star
    hr_star_sc : r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ

  Internal derivations:
    α_star            := fun ω => explicitEquil (γ ω) K r_star
    hα_star_pos       ← explicitEquil_pos (hγ_pos ω) hK hr_star_pos
    hα_star_lt        ← explicitEquil_lt_one (hγ_pos ω) hK hr_star_pos
    hr_star_eq        := hr_star_sc
    hα_star_equil     ← explicitEquil_solves + unfold componentEquil
    hγ_meas           ← measurable_of_Iic hγ_level
    hαs_meas          ← Continuous (fun x => explicitEquil x K r_star) + hγ_meas
    hαs_int           ← hαs_meas + α_star ∈ (0,1) + integrable_const 1

  Net: drops 6, adds 3 → net drop of 3 hypotheses.
  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV6
import KuramotoLean.EquilibriumFormula
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Concrete convergence: equilibrium data derived from explicitEquil formula.**

    Drops all explicit equilibrium hypotheses from V6 (α_star, hα_star_pos,
    hα_star_lt, hαs_int, hα_star_equil, hr_star_eq). All are derived from the
    closed-form formula α_star ω = explicitEquil (γ ω) K r_star. -/
theorem kuramoto_first_moment_concrete_v7 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r_star : ℝ) (hr_star_pos : 0 < r_star)
    (hr_star_sc : r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - explicitEquil (γ ω) K r_star) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  let α_star : Ω → ℝ := fun ω => explicitEquil (γ ω) K r_star
  have hα_star_pos : ∀ ω, 0 < α_star ω :=
    fun ω => explicitEquil_pos (γ ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hα_star_lt : ∀ ω, α_star ω < 1 :=
    fun ω => explicitEquil_lt_one (γ ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hαs_meas : Measurable α_star := by
    have hc : Continuous (fun x : ℝ => explicitEquil x K r_star) := by
      unfold explicitEquil
      apply Continuous.div_const
      exact continuous_neg.add (Real.continuous_sqrt.comp
        ((continuous_pow 2).add continuous_const))
    exact hc.measurable.comp hγ_meas
  have hαs_int : Integrable α_star μ :=
    (integrable_const (1 : ℝ)).mono hαs_meas.aestronglyMeasurable
      (Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, norm_one, abs_of_pos (hα_star_pos ω)]
        exact le_of_lt (hα_star_lt ω)))
  have hr_star_eq : r_star = ∫ ω, α_star ω ∂μ := hr_star_sc
  have hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2) := by
    intro ω
    have h := explicitEquil_solves (γ ω) K r_star (hγ_pos ω) hK hr_star_pos
    unfold componentEquil at h
    linarith
  exact kuramoto_first_moment_concrete_v6 γ K hK
    (fun ω => le_of_lt (hγ_pos ω)) hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hμ_body_pos

end
