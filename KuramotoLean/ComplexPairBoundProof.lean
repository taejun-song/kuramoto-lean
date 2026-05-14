/-
  Complex OA Pair Bound — Proof Attempt via Symmetric Decomposition
  ===================================================================
  EXPERIMENT: prove V'(t) ≤ 0 for the complex OA on symmetric subspace.
  2 sorry (the target theorems to close).
-/

import KuramotoLean.ComplexOAPairBound
import KuramotoLean.ContinuumIdentity

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- V' integrand per ω, after rotation cancels and equilibrium is subtracted.
    complexVDerivIntegrand K r r* z z* =
      K·[(r-r*)/2 · Re((z̄-z̄*)(1-z²)) - r*/2 · |z-z*|² · Re(z+z*)] -/
def complexVDerivIntegrand (K r_t r_star : ℝ) (z z_star : ℂ) : ℝ :=
  K * ((r_t - r_star) / 2 * (starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re -
    r_star / 2 * Complex.normSq (z - z_star) * (z + z_star).re)

/-- **COMPLEX PAIR BOUND (symmetric subspace).**
    On the symmetric subspace, the V' integral is ≤ 0.
    This is the key open gap to close. -/
theorem complex_V_deriv_nonpos_symmetric [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z z_star : Ω → ℂ) (K r_t r_star : ℝ)
    (hK : 0 < K)
    (hz_sym : ∀ ω, z (S.neg ω) = starRingEnd ℂ (z ω))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hz_disk : ∀ ω, Complex.normSq (z ω) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (h_sc : r_t = (∫ ω, starRingEnd ℂ (z ω) * (S.g ω : ℂ) ∂μ).re)
    (hr_star : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * S.g ω ∂μ ≤ 0 := by
  sorry

end
