/-
  KuramotoFirstMomentConcreteV8.lean
  ===================================
  Drops `hα_sq_int` from V7 by deriving it internally.

  Replaces `hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - explicitEquil (γ ω) K r_star)^2) μ`
  with `hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0`.

  Derivation: for t ≥ 0, α ω t ∈ (0,1) from hα_inv, and explicitEquil ∈ (0,1),
  so (α ω t - explicitEquil ...)^2 < 1. For t < 0, α ω t = α ω 0 by hα_neg,
  same bound. AEStronglyMeasurability from hα_int + internal α_star measurability.

  Net vs V7: replaces hα_sq_int (technical) with hα_neg (physical extension convention).
  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentConcreteV7
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem kuramoto_first_moment_concrete_v8 [IsProbabilityMeasure μ]
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
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  -- Derive α_star measurability (needed for AEStronglyMeasurable of difference)
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  let α_star : Ω → ℝ := fun ω => explicitEquil (γ ω) K r_star
  have hα_star_pos : ∀ ω, 0 < α_star ω :=
    fun ω => explicitEquil_pos (γ ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hα_star_lt : ∀ ω, α_star ω < 1 :=
    fun ω => explicitEquil_lt_one (γ ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hαs_meas : Measurable α_star := by
    have hc : Continuous (fun x : ℝ => explicitEquil x K r_star) := by
      unfold explicitEquil; apply Continuous.div_const
      exact continuous_neg.add (Real.continuous_sqrt.comp
        ((continuous_pow 2).add continuous_const))
    exact hc.measurable.comp hγ_meas
  have hαs_int : Integrable α_star μ :=
    (integrable_const (1 : ℝ)).mono hαs_meas.aestronglyMeasurable
      (Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, norm_one, abs_of_pos (hα_star_pos ω)]
        exact le_of_lt (hα_star_lt ω)))
  -- Derive hα_sq_int
  have hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - explicitEquil (γ ω) K r_star) ^ 2) μ :=
    fun t => by
      have ha_int : Integrable (fun ω => α ω t - α_star ω) μ := (hα_int t).sub hαs_int
      apply (integrable_const (1 : ℝ)).mono
      · simp_rw [sq]
        exact ha_int.1.mul ha_int.1
      · apply Eventually.of_forall; intro ω
        rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (sq_nonneg _)]
        have ha : 0 < α ω t ∧ α ω t < 1 := by
          by_cases ht : 0 ≤ t
          · exact hα_inv ω t ht
          · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]; exact hα_inv ω 0 le_rfl
        nlinarith [ha.1, ha.2, hα_star_pos ω, hα_star_lt ω]
  exact kuramoto_first_moment_concrete_v7 γ K hK hγ_pos hγ_level hγ_int
    r_star hr_star_pos hr_star_sc r α hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hμ_body_pos

end
