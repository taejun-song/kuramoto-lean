/-
  Kuramoto Stability Project — Barrier Lemma (Hypothesis H)
  ==========================================================
  At complex frequency ω = σ - iτ (τ > 0), d/dt|α|²|_{|α|=1} = -2τ < 0.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination

open Complex

noncomputable section

/-- Re(ᾱ(r̄ - rα²)) = (1-|α|²)Re(rα). -/
lemma coupling_factor (α r : ℂ) :
    (starRingEnd ℂ α * (starRingEnd ℂ r - r * α ^ 2)).re =
    (1 - Complex.normSq α) * (r * α).re := by
  simp only [Complex.normSq_apply, sq, starRingEnd_self_apply,
    Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

lemma coupling_vanishes_on_circle (α r : ℂ) (h : Complex.normSq α = 1) :
    (starRingEnd ℂ α * (starRingEnd ℂ r - r * α ^ 2)).re = 0 := by
  rw [coupling_factor, h, sub_self, zero_mul]

/-- 2Re(ᾱ(-i(σ-iτ)α)) = -2τ|α|². -/
lemma rotation_complex (α : ℂ) (σ τ : ℝ) :
    2 * (starRingEnd ℂ α * (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * α)).re =
    -2 * τ * Complex.normSq α := by
  simp only [Complex.normSq_apply, starRingEnd_self_apply,
    Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- **Barrier Lemma.** d/dt|α|²|_{|α|=1} = -2τ.
    Brute-force: expand to real/imag components, then linear_combination. -/
theorem barrier_lemma (α r : ℂ) (K σ τ : ℝ)
    (h : Complex.normSq α = 1) :
    2 * (starRingEnd ℂ α *
      (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * α +
       (K : ℂ) / 2 * (starRingEnd ℂ r - r * α ^ 2))).re = -2 * τ := by
  simp only [Complex.normSq_apply] at h
  simp only [sq, Complex.normSq_apply, starRingEnd_self_apply,
    Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  -- Goal is now a polynomial identity in α.re, α.im, r.re, r.im, K, σ, τ
  -- with hypothesis h : α.re * α.re + α.im * α.im = 1
  -- Coefficient: the expression = -2τ + (α.re²+α.im²-1)*(-2τ - K*(α.re*r.re - α.im*r.im))
  linear_combination
    (-2 * τ - K * (α.re * r.re - α.im * r.im)) * h

/-- d/dt|α|² < 0 on the unit circle when τ > 0. -/
theorem barrier_strict (α r : ℂ) (K σ τ : ℝ) (hτ : 0 < τ)
    (h : Complex.normSq α = 1) :
    2 * (starRingEnd ℂ α *
      (-Complex.I * ((σ : ℂ) - Complex.I * (τ : ℂ)) * α +
       (K : ℂ) / 2 * (starRingEnd ℂ r - r * α ^ 2))).re < 0 := by
  have h1 := barrier_lemma α r K σ τ h
  linarith

end
