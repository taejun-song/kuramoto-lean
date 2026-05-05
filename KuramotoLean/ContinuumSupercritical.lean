/-
  Kuramoto Stability — Continuum Supercritical Condition
  ======================================================

  From the equilibrium γ·α* = (K/2)r*(1-α*²) with α* ∈ (0,1)
  and self-consistency r* = ∫α* dμ > 0, we derive:
    ∫ α*/(1-α*²) dμ > r*
  This is the continuum K > K_c condition.

  0 sorry.
-/

import KuramotoLean.ContinuumLyapunov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- α*/(1-α*²) > α* when α* ∈ (0,1). -/
theorem alpha_ratio_gt (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    a < a / (1 - a ^ 2) := by
  have h1 : (0 : ℝ) < 1 - a ^ 2 := by nlinarith
  rw [lt_div_iff₀ h1]
  have : 0 < a ^ 2 := by positivity
  nlinarith [sq_nonneg a]

/-- **Supercritical integral.** ∫α*/(1-α*²) > ∫α* = r*. -/
theorem supercritical_integral [IsProbabilityMeasure μ]
    (α_star : Ω → ℝ)
    (hα_pos : ∀ ω, 0 < α_star ω) (hα_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (h_ratio_int : Integrable (fun ω => α_star ω / (1 - (α_star ω) ^ 2)) μ) :
    ∫ ω, α_star ω ∂μ < ∫ ω, α_star ω / (1 - (α_star ω) ^ 2) ∂μ := by
  have h_diff_int : Integrable (fun ω => α_star ω / (1 - (α_star ω) ^ 2) - α_star ω) μ :=
    h_ratio_int.sub hαs_int
  have h_nn : ∀ ω, (0 : ℝ) ≤ α_star ω / (1 - (α_star ω) ^ 2) - α_star ω :=
    fun ω => le_of_lt (by linarith [alpha_ratio_gt (α_star ω) (hα_pos ω) (hα_lt ω)])
  have h_supp : 0 < μ (Function.support (fun ω => α_star ω / (1 - (α_star ω) ^ 2) - α_star ω)) := by
    have h_eq : Function.support (fun ω => α_star ω / (1 - (α_star ω) ^ 2) - α_star ω) = univ := by
      ext ω; simp only [Function.mem_support, mem_univ, iff_true]
      exact ne_of_gt (by linarith [alpha_ratio_gt (α_star ω) (hα_pos ω) (hα_lt ω)] : (0:ℝ) < _)
    rw [h_eq, measure_univ]; exact one_pos
  have h_pos : 0 < ∫ ω, (α_star ω / (1 - (α_star ω) ^ 2) - α_star ω) ∂μ :=
    (integral_pos_iff_support_of_nonneg h_nn h_diff_int).mpr h_supp
  linarith [integral_sub h_ratio_int hαs_int]

end
