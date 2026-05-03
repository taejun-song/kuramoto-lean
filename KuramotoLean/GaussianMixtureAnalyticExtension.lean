/-
  Kuramoto Stability — Gaussian Mixture Analytic Extension
  =========================================================

  A finite weighted sum of Gaussians
    g(ω) = Σ_k aₖ · exp(-ω²/(2σₖ²)) / (σₖ√(2π))
  is an ENTIRE function (sum of entire functions), hence satisfies
  AnalyticOnNhd ℂ g_ext {z | |Im z| < a} for any a > 0.

  Key: since the mixture is entire, any strip width a > 0 works.
  Contrast with Lorentzian mixtures (strip bounded by min γ_k).

  0 sorry, 0 axioms.
-/

import KuramotoLean.GaussianAnalyticExtension
import Mathlib.Analysis.Analytic.Constructions

open Complex Real Set Finset

noncomputable section

/-- A finite weighted sum of Gaussians. -/
def gaussianMixture (n : ℕ) (a σ : Fin n → ℝ) (ω : ℝ) : ℝ :=
  ∑ k : Fin n, a k * gaussianFreqDist (σ k) ω

/-- Complex extension: defined as sum of functions for direct analyticAt_sum use. -/
def gaussianMixtureExt (n : ℕ) (a σ : Fin n → ℝ) : ℂ → ℂ :=
  ∑ k : Fin n, (fun z : ℂ => (a k : ℂ) * gaussianFreqDistExt (σ k) z)

/-- The complex extension restricts to the real mixture on ℝ. -/
theorem gaussianMixtureExt_real (n : ℕ) (a σ : Fin n → ℝ) (ω : ℝ) :
    gaussianMixtureExt n a σ (ω : ℂ) = (gaussianMixture n a σ ω : ℂ) := by
  simp only [gaussianMixtureExt, gaussianMixture, Finset.sum_apply,
             ofReal_sum, ofReal_mul]
  congr 1; ext k
  rw [gaussianFreqDistExt_real]

/-- Each Gaussian component is analytic at every z (it is entire). -/
theorem gaussianMixtureExt_analyticAt (n : ℕ) (a σ : Fin n → ℝ) (z : ℂ) :
    AnalyticAt ℂ (gaussianMixtureExt n a σ) z := by
  unfold gaussianMixtureExt
  apply Finset.univ.analyticAt_sum
  intro k _
  exact analyticAt_const.mul (gaussianFreqDistExt_analyticAt (σ k) z)

/-- A Gaussian mixture is analytic on any horizontal strip (it is entire). -/
theorem gaussianMixtureExt_analyticOnNhd (n : ℕ) (a σ : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    AnalyticOnNhd ℂ (gaussianMixtureExt n a σ) {z : ℂ | |z.im| < s} :=
  fun z _ => gaussianMixtureExt_analyticAt n a σ z

end
