/-
  Kuramoto Stability Project — Free-Rotation Amplification Lemma
  ================================================================
  Under free rotation α₀·e^{-iωt} at complex ω = σ - iτ (τ > 0),
  ‖α₀·e^{-iωt}‖ = ‖α₀‖·e^{-τt}.
  For t ≤ 0 this grows as e^{τ|t|} → ∞, so the Z^{a''} norm diverges
  backward unless α₀ = 0.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

open Complex Real

noncomputable section

/-- Re(-i(σ-iτ)t) = -τt. -/
lemma free_rot_re (σ τ t : ℝ) :
    (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * (t : ℂ)).re = -τ * t := by
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_im]
  ring

/-- ‖e^{-i(σ-iτ)t}‖ = e^{-τt}. -/
theorem norm_free_rot (σ τ t : ℝ) :
    ‖Complex.exp (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * (t : ℂ))‖ =
    Real.exp (-τ * t) := by
  rw [Complex.norm_exp, free_rot_re]

/-- ‖α₀·e^{-iωt}‖ = ‖α₀‖·e^{-τt} where ω = σ - iτ. -/
theorem norm_free_rot_product (α₀ : ℂ) (σ τ t : ℝ) :
    ‖α₀ * Complex.exp (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * (t : ℂ))‖ =
    ‖α₀‖ * Real.exp (-τ * t) := by
  rw [norm_mul, norm_free_rot]

/-- For τ > 0 and t ≤ 0: e^{-τt} ≥ 1. -/
theorem amplification_ge_one (τ t : ℝ) (hτ : 0 < τ) (ht : t ≤ 0) :
    (1 : ℝ) ≤ Real.exp (-τ * t) := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- For any M, if t ≤ -M/τ then e^{-τt} ≥ e^M. -/
theorem amplification_unbounded (τ M : ℝ) (hτ : 0 < τ)
    (t : ℝ) (ht : t ≤ -M / τ) :
    Real.exp M ≤ Real.exp (-τ * t) :=
  Real.exp_le_exp.mpr (by
    have : -M / τ * τ = -M := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right ht hτ.le])

/-- **Free-rotation amplification.** ‖α₀·e^{-iωt}‖ ≥ ‖α₀‖·e^M for t ≤ -M/τ. -/
theorem free_rot_diverges (α₀ : ℂ) (σ τ M : ℝ)
    (hτ : 0 < τ) (hα : 0 < ‖α₀‖)
    (t : ℝ) (ht : t ≤ -M / τ) :
    ‖α₀‖ * Real.exp M ≤
    ‖α₀ * Complex.exp (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * (t : ℂ))‖ := by
  rw [norm_free_rot_product]
  exact mul_le_mul_of_nonneg_left (amplification_unbounded τ M hτ t ht) (le_of_lt hα)

end
