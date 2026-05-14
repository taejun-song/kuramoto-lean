/-
  Complex OA Pair Bound — Fubini Approach
  =========================================
  Proves ∫ V'_integrand · g dμ ≤ 0 for the complex OA via Fubini.

  Key finding from attack round 1: the POINTWISE bound is FALSE
  (complex_pair_bound_core_counterexample). The integral bound
  requires the DOUBLE INTEGRAL (Fubini) decomposition, exactly
  as in the real case (ContinuumIdentity.lean).

  Strategy: V' = -(K/2) · ∫∫ P(ω₁,ω₂) g₁g₂ dω₁dω₂
  where P(ω₁,ω₂) is the complex pair integrand.
  Show ∫∫ P ≥ 0 via Fubini + self-consistency.

  After rotation cancels (proved in ComplexOAPairBound.lean),
  V' = K · [-r* · Q_c + D_c · S_c] where:
    Q_c = ∫ Re(|z-z*|²(z+z*)) · g dω
    S_c = ∫ Re((z̄-z̄*)(1-z²)) · g dω
    D_c = r - r* = ∫ Re(z̄-z̄*) · g dω

  The Fubini decomposition gives:
    r* · Q_c - D_c · S_c = (1/2) ∫∫ P(ω₁,ω₂) g₁g₂

  Need: ∫∫ P ≥ 0. This is the complex analog of pair_bound_from_products.
-/

import KuramotoLean.ComplexOAPairBound
import KuramotoLean.ContinuumIdentity

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The pointwise bound is FALSE — proof that Fubini is needed -/

/-- Counterexample: the per-ω integrand can be positive.
    Need the DOUBLE INTEGRAL, not pointwise. -/
theorem complex_pair_pointwise_false :
    ¬ ∀ (r_t r_star : ℝ) (z z_star : ℂ),
      (r_t - r_star) / 2 * (starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re -
        r_star / 2 * Complex.normSq (z - z_star) * (z + z_star).re ≤ 0 := by
  push_neg
  exact ⟨-1, 1, 0, 1, by norm_num⟩

/-! ## V' integrand definition -/

def complexVDerivIntegrand (K r_t r_star : ℝ) (z z_star : ℂ) : ℝ :=
  K * ((r_t - r_star) / 2 * (starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re -
    r_star / 2 * Complex.normSq (z - z_star) * (z + z_star).re)

/-! ## Fubini decomposition components -/

/-- Q_c = ∫ |z-z*|² · Re(z+z*) · g dω  (cubic moment) -/
def Qc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, Complex.normSq (z ω - z_star ω) * (z ω + z_star ω).re * g ω ∂μ

/-- S_c = ∫ Re((z̄-z̄*)(1-z²)) · g dω  (mixed moment) -/
def Sc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re * g ω ∂μ

/-- D_c = r - r* = ∫ Re(z̄-z̄*) · g dω  (order parameter deviation) -/
def Dc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (starRingEnd ℂ (z ω - z_star ω)).re * g ω ∂μ

/-- V' = K · [-r* · Q_c + D_c · S_c] after rotation cancels. -/
theorem complex_V_deriv_eq_QDS (K r_star : ℝ) (z z_star : Ω → ℂ) (g : Ω → ℝ)
    (r_t : ℝ) (hD : r_t - r_star = Dc z z_star g μ) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ =
      K * (-r_star / 2 * Qc z z_star g μ + Dc z z_star g μ / 2 * Sc z z_star g μ) := by
  rw [hD]
  simp [complexVDerivIntegrand, Qc, Sc, Dc, sub_eq_add_neg, mul_add, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc, left_distrib, right_distrib]

/-! ## The Fubini identity: r*Q - D·S = (1/2)∫∫ pair -/

/-- The complex pair integrand for (ω₁, ω₂). -/
def complexPairIntegrand (z z_star : Ω → ℂ) (ω₁ ω₂ : Ω) : ℝ :=
  let d₁ := z ω₁ - z_star ω₁
  let d₂ := z ω₂ - z_star ω₂
  Complex.normSq d₂ * (z_star ω₁).re * (z ω₂ + z_star ω₂).re +
  Complex.normSq d₁ * (z_star ω₂).re * (z ω₁ + z_star ω₁).re -
  2 * (starRingEnd ℂ d₁ * d₂).re *
    ((1 - z ω₁ ^ 2).re * (z_star ω₂).re + (1 - z ω₂ ^ 2).re * (z_star ω₁).re) / 2

/-- The Fubini identity: r*Q_c - D_c·S_c = (1/2) ∫∫ pair.
    Same algebraic structure as pair_fubini_identity in ContinuumIdentity.lean. -/
theorem complex_pair_fubini
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (r_star : ℝ) :
    r_star * Qc z z_star g μ - Dc z z_star g μ * Sc z z_star g μ =
      (1/2) * ∫ ω₁, ∫ ω₂,
        complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ := by
  sorry

/-! ## The complex pair integrand is non-negative (the key bound) -/

/-- **THE COMPLEX PAIR BOUND.**
    ∫∫ complexPairIntegrand · g₁ · g₂ ≥ 0.

    This is the complex analog of pair_bound_from_products.
    For real z, z* ∈ (0,1), this reduces to the proved real pair bound.
    For complex z, z* ∈ D, the bound uses the same SOS structure
    but with Re(·) terms instead of scalar products. -/
theorem complex_pair_nonneg [IsProbabilityMeasure μ]
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω)
    (hz_disk : ∀ ω, Complex.normSq (z ω) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω)) :
    0 ≤ ∫ ω₁, ∫ ω₂,
      complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ := by
  sorry

/-! ## Assembly: V' ≤ 0 -/

/-- **V' ≤ 0 for complex OA via Fubini.**
    Combines: V' = K[-r*Q + DS] and r*Q - DS = (1/2)∫∫pair ≥ 0. -/
theorem complex_V_deriv_nonpos [IsProbabilityMeasure μ]
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r_t r_star : ℝ)
    (hK : 0 < K) (hg : ∀ ω, 0 ≤ g ω)
    (hz_disk : ∀ ω, Complex.normSq (z ω) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hD : r_t - r_star = Dc z z_star g μ)
    (hr_star_pos : 0 < r_star) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ ≤ 0 := by
  rw [complex_V_deriv_eq_QDS K r_star z z_star g r_t hD]
  have h_fub := @complex_pair_fubini Ω _ μ z z_star g r_star
  have h_nn := @complex_pair_nonneg Ω _ μ _ z z_star g hg hz_disk hz_star_pos
  nlinarith

end
