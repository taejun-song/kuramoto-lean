/-
  Complex OA Pair Bound — Analysis
  ==================================
  Investigation of whether V'(t) ≤ 0 holds for the complex OA.

  FINDING: The rotation term -iωz in V' does NOT cancel by symmetry.
  It is EVEN under ω ↦ -ω (not odd), so the symmetry integral is
  nonzero. This means the real scalar pair bound does NOT directly
  port to the complex OA.

  The Lyapunov V = ∫|z - z*|²g dω may NOT be antitone for the
  complex OA. A different Lyapunov function is needed.

  HOWEVER: the Ψ energy (dΨ/dt = K|η|² ≥ 0) IS proved and provides
  monotonicity in a different functional. The convergence argument
  for the complex OA requires a different approach than the real case.

  This file documents the gap and provides the Cauchy-Schwarz bound
  which IS valid for complex V.
-/

import KuramotoLean.ComplexOASymmetry

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Cauchy-Schwarz for complex V (this IS valid) -/

/-- |η - η*|² ≤ V = ∫|z - z*|²·g dμ.
    This is the complex Jensen/Cauchy-Schwarz inequality. -/
theorem complex_cauchy_schwarz_bound [IsProbabilityMeasure μ]
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (hg_nn : ∀ ω, 0 ≤ g ω)
    (hV_int : Integrable (fun ω => Complex.normSq (z ω - z_star ω) * g ω) μ) :
    Complex.normSq (∫ ω, starRingEnd ℂ (z ω - z_star ω) * (g ω : ℂ) ∂μ) ≤
    ∫ ω, Complex.normSq (z ω - z_star ω) * g ω ∂μ := by
  sorry

/-! ## V convergence requires a different approach for complex OA -/

/-- **GAP DOCUMENTATION.**
    The L² Lyapunov V = ∫|z-z*|²g is NOT proved antitone for
    complex OA. The rotation term -iωz contributes an EVEN (not odd)
    integrand to V', which does not vanish by symmetry.

    The convergence of the complex OA order parameter |η| → r*
    likely requires one of:
    1. A different Lyapunov function (e.g., the Dietert Ψ-energy
       combined with compactness arguments)
    2. A spectral/hypocoercivity approach (Dietert-Fernandez 2018)
    3. Direct analysis of the coupled (ρ, φ) polar dynamics

    What IS proved:
    - Ψ monotone: dΨ/dt = K|η|² ≥ 0 (ComplexOAEnergy, 0 sorry)
    - Symmetry preserved: z(ω) = conj(z(-ω)) (ComplexOASymmetry, 0 sorry)
    - η ∈ ℝ for symmetric g (ComplexOASymmetry, 0 sorry)

    What is NOT proved:
    - V antitone for complex OA
    - V → 0 for complex OA
    - Direct convergence |η| → r* without V → 0 hypothesis -/
theorem complex_oa_V_not_proved_antitone : True := trivial

end
