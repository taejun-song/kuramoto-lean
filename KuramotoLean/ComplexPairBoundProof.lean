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

/-- If the weighted complex OA pair integrand is pointwise nonpositive, then its
    integral is nonpositive. This is the final measure-theoretic step in the
    symmetric complex pair-bound argument. -/
private theorem complex_V_deriv_nonpos_of_pointwise
    (S : SymmetricFreq Ω μ)
    (z z_star : Ω → ℂ) (K r_t r_star : ℝ)
    (h_weighted_nonpos :
      ∀ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * S.g ω ≤ 0) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * S.g ω ∂μ ≤ 0 := by
  exact integral_nonpos h_weighted_nonpos

/-- The remaining algebraic gap in the complex symmetric argument is a
    pointwise weighted sign estimate for the V' integrand.  This isolates the
    exact bridge still needed from the complex pair decomposition and the
    self-consistency identities. -/
private theorem complex_pair_bound_pointwise
    [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z z_star : Ω → ℂ) (K r_t r_star : ℝ)
    (hK : 0 < K)
    (hz_sym : ∀ ω, z (S.neg ω) = starRingEnd ℂ (z ω))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hz_disk : ∀ ω, Complex.normSq (z ω) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (h_sc : r_t = (∫ ω, starRingEnd ℂ (z ω) * (S.g ω : ℂ) ∂μ).re)
    (hr_star : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re) :
    ∀ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * S.g ω ≤ 0 := by
  intro ω
  set A : ℝ :=
    (r_t - r_star) / 2 * (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re -
      r_star / 2 * Complex.normSq (z ω - z_star ω) * (z ω + z_star ω).re
  have hrewrite :
      complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * S.g ω =
        K * (A * S.g ω) := by
    unfold complexVDerivIntegrand
    simp [A, mul_left_comm, mul_comm]
  rw [hrewrite]
  have hcore : A * S.g ω ≤ 0 := by
    -- Remaining gap: the complex symmetric pair decomposition should reduce
    -- this local real-valued quantity to a manifestly nonpositive form.
    sorry
  exact mul_nonpos_of_nonneg_of_nonpos hK.le hcore

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
  exact complex_V_deriv_nonpos_of_pointwise S z z_star K r_t r_star
    (complex_pair_bound_pointwise S z z_star K r_t r_star
      hK hz_sym hz_star_sym hz_disk hz_star_pos h_sc hr_star)

end
