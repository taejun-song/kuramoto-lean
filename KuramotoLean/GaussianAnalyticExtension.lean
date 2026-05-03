/-
  Kuramoto Stability — Gaussian Analytic Extension
  =================================================

  Proves that the Gaussian frequency distribution
    g(ω) = exp(-ω² / (2σ²)) / (σ · √(2π))
  admits a complex analytic extension to ALL of ℂ (entire function).

  In particular, it satisfies AnalyticOnNhd ℂ g_ext {z : ℂ | |Im z| < a} for any a > 0.

  Proof: g_ext(z) = exp(-z²/(2σ²)) / C.
    · z ↦ -(z²) is analytic: analyticAt_id.pow 2 + AnalyticAt.neg
    · Dividing by a constant preserves analyticity: AnalyticAt.div_const
    · AnalyticAt.cexp': exp ∘ analytic = analytic

  The Gaussian is transcendental (unlike the rational Lorentzian), but the
  continuum global stability proof works directly without rational approximation.

  0 sorry, 0 axioms.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex Real Set

noncomputable section

/-- The Gaussian frequency distribution: g(ω) = exp(-ω²/(2σ²)) / (σ√(2π)). -/
def gaussianFreqDist (σ ω : ℝ) : ℝ :=
  Real.exp (-(ω ^ 2) / (2 * σ ^ 2)) / (σ * Real.sqrt (2 * Real.pi))

/-- Complex extension of the Gaussian: g_ext(z) = exp(-z²/(2σ²)) / (σ√(2π)). -/
def gaussianFreqDistExt (σ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(z ^ 2) / ((2 * σ ^ 2 : ℝ) : ℂ)) / ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- The complex extension restricts to the real Gaussian on ℝ. -/
theorem gaussianFreqDistExt_real (σ ω : ℝ) :
    gaussianFreqDistExt σ (ω : ℂ) = (gaussianFreqDist σ ω : ℂ) := by
  simp only [gaussianFreqDistExt, gaussianFreqDist, Complex.ofReal_div, Complex.ofReal_exp,
             Complex.ofReal_mul]
  congr 1
  push_cast
  ring

/-- The Gaussian complex extension is analytic at every z ∈ ℂ (it is an entire function).
    Key: AnalyticAt.cexp' applies exp to an analytic inner function. -/
theorem gaussianFreqDistExt_analyticAt (σ : ℝ) (z : ℂ) :
    AnalyticAt ℂ (gaussianFreqDistExt σ) z := by
  unfold gaussianFreqDistExt
  apply AnalyticAt.div_const
  apply AnalyticAt.cexp'
  apply AnalyticAt.div_const
  apply AnalyticAt.neg
  exact analyticAt_id.pow 2

/-- The Gaussian complex extension is analytic on any horizontal strip. -/
theorem gaussianFreqDistExt_analyticOnNhd (σ : ℝ) (a : ℝ) (ha : 0 < a) :
    AnalyticOnNhd ℂ (gaussianFreqDistExt σ) {z : ℂ | |z.im| < a} :=
  fun z _ => gaussianFreqDistExt_analyticAt σ z

end
