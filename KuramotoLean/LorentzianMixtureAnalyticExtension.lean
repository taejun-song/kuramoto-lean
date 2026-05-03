/-
  Kuramoto Stability — Lorentzian Mixture Analytic Extension
  ==========================================================

  A finite weighted sum of Lorentzians
    g(ω) = Σ_k aₖ · γₖ/π / (ω² + γₖ²)
  is a rational function, hence analytic on the strip {|Im z| < a}
  whenever a ≤ γ k for every component k.

  Since the mixture is itself rational, the rational approximation
  error is ZERO: g_approx n = g for all n. This extends the
  axiom-free result of LorentzianAnalyticExtension to all finite
  Lorentzian mixtures. No Padé/AAK theory needed.

  0 sorry, 0 axiom.
-/

import KuramotoLean.LorentzianAnalyticExtension
import Mathlib.Analysis.Analytic.Constructions

open Complex Real Set Finset

noncomputable section

/-- A finite weighted sum of Lorentzians. -/
def lorentzianMixture (n : ℕ) (a γ : Fin n → ℝ) (ω : ℝ) : ℝ :=
  ∑ k : Fin n, a k * lorentzianFreqDist (γ k) ω

/-- Complex extension: defined as a Finset sum of functions so that
    `analyticAt_sum` applies directly (avoids the fun/sum transposition issue). -/
def lorentzianMixtureExt (n : ℕ) (a γ : Fin n → ℝ) : ℂ → ℂ :=
  ∑ k : Fin n, (fun z : ℂ => (a k : ℂ) * lorentzianFreqDistExt (γ k) z)

/-- The complex extension restricts to the real mixture on ℝ. -/
theorem lorentzianMixtureExt_real (n : ℕ) (a γ : Fin n → ℝ) (ω : ℝ) :
    lorentzianMixtureExt n a γ (ω : ℂ) = (lorentzianMixture n a γ ω : ℂ) := by
  simp only [lorentzianMixtureExt, lorentzianMixture, Finset.sum_apply,
             ofReal_sum, ofReal_mul]
  congr 1; ext k
  rw [lorentzianFreqDistExt_real]

/-- The mixture extension is analytic on {|Im z| < a} when a ≤ γ k for all k. -/
theorem lorentzianMixtureExt_analyticOnNhd
    (n : ℕ) (a_coeff γ : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (hγ_pos : ∀ k, 0 < γ k) (hγ_ge : ∀ k, a ≤ γ k) :
    AnalyticOnNhd ℂ (lorentzianMixtureExt n a_coeff γ) {z : ℂ | |z.im| < a} := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  unfold lorentzianMixtureExt
  apply Finset.univ.analyticAt_sum
  intro k _
  apply analyticAt_const.mul
  exact lorentzianFreqDistExt_analyticOnNhd (γ k) (hγ_pos k) z
    (Set.mem_setOf.mpr (lt_of_lt_of_le hz (hγ_ge k)))

/-- Lorentzian mixtures have axiom-free rational approximations.
    Since the mixture is itself rational, g_approx n = g gives zero error. -/
theorem lorentzian_mixture_rational_approx
    (n : ℕ) (a_coeff γ : Fin n → ℝ) (hγ_pos : ∀ k, 0 < γ k) :
    ∃ (g_approx : ℕ → ℝ → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ m : ℕ, ∀ ω : ℝ,
        |lorentzianMixture n a_coeff γ ω - g_approx m ω| ≤ C * Real.exp (-(c * m)) :=
  ⟨fun _ => lorentzianMixture n a_coeff γ, 1, 1, one_pos, one_pos, fun m ω => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (le_of_lt one_pos) (Real.exp_nonneg _)⟩

end
