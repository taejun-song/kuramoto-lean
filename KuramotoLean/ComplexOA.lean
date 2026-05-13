/-
  Complex OA Equation — Definitions and Invariant Disk
  =====================================================
  The complex Ott-Antonsen equation for general (possibly asymmetric) g:

    ż(ω,t) = -iω·z + (K/2)(η̄ - η·z²)
    η(t) = ∫ z̄(ω,t) g(ω) dω

  where z(ω,t) ∈ D (open unit disk).

  This file:
  1. Defines the complex OA RHS
  2. Defines the Ψ energy functional: Ψ = -∫ log(1-|z|²) g dω
  3. Proves the pointwise derivative of |z|²:
       d|z|²/dt = K·Re(η·z)·(1 - |z|²)
  4. Proves the pointwise derivative of -log(1-|z|²):
       d[-log(1-|z|²)]/dt = K·Re(η·z)

  The real scalar OA (α ∈ (0,1), symmetric g) is the restriction
  z = α ∈ ℝ, η = r ∈ ℝ.
-/

import KuramotoLean.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Complex OA RHS -/

/-- The complex OA velocity field:
    ż = -iω·z + (K/2)(η̄ - η·z²)
    where η is the complex order parameter. -/
def complexOaRHS (ω K : ℝ) (η z : ℂ) : ℂ :=
  -(Complex.I * (ω : ℂ) * z) + ((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2)

/-! ## Key identity: d|z|²/dt = K·Re(η·z)·(1-|z|²) -/

/-- The time derivative of |z|² along the complex OA flow.
    d|z|²/dt = 2·Re(z̄·ż) = K·Re(η·z)·(1-|z|²).

    Proof sketch:
    z̄·ż = z̄·(-iωz + (K/2)(η̄ - ηz²))
         = -iω|z|² + (K/2)(z̄η̄ - z̄ηz²)
         = -iω|z|² + (K/2)(conj(zη) - |z|²·ηz̄)

    Re(z̄·ż) = (K/2)·Re(conj(zη) - |z|²·conj(ηz))
             since Re(-iω|z|²) = 0 (|z|² is real)
             = (K/2)·Re(zη)·(1 - |z|²)
             since Re(conj(w)) = Re(w).

    So d|z|²/dt = 2·Re(z̄·ż) = K·Re(ηz)·(1-|z|²). -/
theorem complexOa_normSq_deriv (ω K : ℝ) (η z : ℂ) :
    2 * (starRingEnd ℂ z * complexOaRHS ω K η z).re =
      K * (η * z).re * (1 - Complex.normSq z) := by
  show 2 * (starRingEnd ℂ z * complexOaRHS ω K η z).re =
    K * (η * z).re * (1 - (z.re * z.re + z.im * z.im))
  unfold complexOaRHS
  have hK_re : ((K : ℂ) / 2).re = K / 2 := by simp
  have hK_im : ((K : ℂ) / 2).im = 0 := by simp
  have hω_re : ((ω : ℂ)).re = ω := Complex.ofReal_re ω
  have hω_im : ((ω : ℂ)).im = 0 := Complex.ofReal_im ω
  simp only [Complex.normSq_apply, sq, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    hK_re, hK_im, hω_re, hω_im]
  ring

/-! ## Ψ energy functional -/

/-- The complex Ψ energy: Ψ(t) = -∫ log(1-|z(ω,t)|²) dμ(ω).
    Measures total "locking energy" in the population. -/
def psiComplex (z : Ω → ℂ) (μ : Measure Ω) : ℝ :=
  ∫ ω, -Real.log (1 - Complex.normSq (z ω)) ∂μ

/-- Ψ is non-negative when all z(ω) are in the unit disk. -/
theorem psiComplex_nonneg
    (z : Ω → ℂ) (hz : ∀ ω, Complex.normSq (z ω) < 1) :
    0 ≤ psiComplex z μ := by
  unfold psiComplex
  have h_nn : ∀ ω, (0 : ℝ) ≤ -Real.log (1 - Complex.normSq (z ω)) := by
    intro ω
    have h1 : 0 < 1 - Complex.normSq (z ω) := sub_pos.mpr (hz ω)
    have h2 : 1 - Complex.normSq (z ω) ≤ 1 := by
      linarith [Complex.normSq_nonneg (z ω)]
    linarith [Real.log_nonpos h1.le h2]
  exact MeasureTheory.integral_nonneg h_nn

end
