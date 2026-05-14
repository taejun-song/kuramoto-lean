/-
  Complex OA Full Chain — Close ALL Hypotheses
  ================================================
  Proves V→0 unconditionally (no h_body_anti, h_body_zero, h_tail
  hypotheses). Derives everything from ODE data.

  3 sorry = 3 targets for the attack loop.
-/

import KuramotoLean.ComplexOAVZero

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- V→0 with NO body/tail hypotheses. Derives all three from ODE data. -/
theorem complex_oa_V_zero_unconditional [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (K : ℝ) (r_star : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hω_level : ∀ M : ℝ, MeasurableSet {ω | |S.ω_freq ω| ≤ M}) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0) := by
  apply complex_oa_V_tendsto_zero S z z_star K r_star hK hr_star_pos
    hz_disk hz_star_pos hz_star_lt hg_nn hg_int hg_norm hz_ode
    hr_star_eq hz_star_equil hV_int hω_level
  -- h_body_anti: body V antitone (bounded ω → bounded rotation → pair bound)
  · intro M hM
    sorry
  -- h_body_zero: body V → 0 (body persistence + Gronwall)
  · intro M hM
    sorry
  -- h_tail: tail integral < ε (|z-z*|² ≤ 4 + tail g → 0)
  · intro ε hε
    sorry

end
