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
  push Not
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

/-! ## Status of the complex pair step

The two missing theorems in the original draft claimed a fully general complex
Fubini identity, a fully general nonnegativity result, and a fully general
`V' = K[-r*Q + DS]` identity. Those claims are not supported by the current
hypotheses:

* `complex_V_deriv_eq_QDS` needs explicit integrability/linearity hypotheses.
* `complex_pair_fubini` used a free `r_star` on the left-hand side but no
  corresponding quantity on the right-hand side.
* `complex_pair_nonneg` only assumed `‖z‖ < 1` and `z_star ≠ 0`, which is too
  weak; concrete numerical examples give a negative pair integrand.

What is actually derivable from the current file is the final assembly step:
if a suitable `V'` identity, pair identity, and pair nonnegativity statement
are supplied, then the Lyapunov derivative is nonpositive. We record exactly
that below.
-/

/-- The complex pair integrand for (ω₁, ω₂). -/
def complexPairIntegrand (z z_star : Ω → ℂ) (ω₁ ω₂ : Ω) : ℝ :=
  let d₁ := z ω₁ - z_star ω₁
  let d₂ := z ω₂ - z_star ω₂
  Complex.normSq d₂ * (z_star ω₁).re * (z ω₂ + z_star ω₂).re +
  Complex.normSq d₁ * (z_star ω₂).re * (z ω₁ + z_star ω₁).re -
  (starRingEnd ℂ d₁ * d₂).re *
    ((1 - z ω₁ ^ 2).re * (z_star ω₂).re + (1 - z ω₂ ^ 2).re * (z_star ω₁).re) / 2

/-! ## Assembly: V' ≤ 0 -/

/-- **Conditional assembly of `V' ≤ 0`.**
    This is the valid consequence of the current file:
    once a matching pair identity and pair nonnegativity result are available,
    the Lyapunov derivative is nonpositive. -/
theorem complex_V_deriv_nonpos_of_pair_bound
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r_t r_star : ℝ)
    (hK : 0 < K)
    (hV_eq_QDS :
      ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ =
        K * (-r_star / 2 * Qc z z_star g μ + Dc z z_star g μ / 2 * Sc z z_star g μ))
    (h_pair_fubini :
      r_star * Qc z z_star g μ - Dc z z_star g μ * Sc z z_star g μ =
        (1 / 2) * ∫ ω₁, ∫ ω₂,
          complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ)
    (h_pair_nonneg :
      0 ≤ ∫ ω₁, ∫ ω₂,
        complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ ≤ 0 := by
  rw [hV_eq_QDS]
  have h_pair_rhs :
      0 ≤ r_star * Qc z z_star g μ - Dc z z_star g μ * Sc z z_star g μ := by
    rw [h_pair_fubini]
    nlinarith
  nlinarith

end
