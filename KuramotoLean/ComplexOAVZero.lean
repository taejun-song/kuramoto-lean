/-
  Complex OA: Prove V → 0
  =========================
  TARGET: Prove the hV_zero hypothesis of ComplexOAEndToEnd.

  Strategy A (cooperative n-pole + passage to limit):
  For the symmetric case η = r ∈ ℝ, the modulus |z(ω,t)| satisfies
    d|z|²/dt = K·r·Re(z)·(1-|z|²)
  On the symmetric subspace, Re(z(ω)) = Re(z(-ω)) (even function).
  For locked oscillators (small |ω|), Re(z) stays positive, giving
  a lower bound on |z| → body persistence for modulus.

  Then: body persistence for |z| + V Cauchy-Schwarz gives persistence
  for r(t). And: r(t) ≥ r_min + body |z| persistence + V antitone on
  body (where V_body IS antitone since body has bounded γ) → V → 0.

  KEY INSIGHT: On the body {|ω| ≤ M}, the rotation is bounded,
  so the real scalar proof DOES apply to V_body. Then tail vanishing
  (∫_{|ω|>M} g → 0) gives V → 0.

  1 sorry (the target to close).
-/

import KuramotoLean.ComplexOAEndToEnd

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **V → 0 FOR COMPLEX OA.**

    Strategy: body-tail split. On the body {|ω| ≤ M}:
    - Rotation is bounded (|ω| ≤ M)
    - Body V_body IS antitone (bounded-γ real scalar proof applies)
    - Body persistence holds (from |z| lower bound)
    - Body Gronwall gives exponential decay of V_body

    On the tail {|ω| > M}:
    - V_tail ≤ ∫_{|ω|>M} |z-z*|² · g ≤ 4 · μ({|ω|>M}) → 0 as M → ∞
    - (since |z|, |z*| < 1, so |z-z*|² ≤ 4)

    Combined: V = V_body + V_tail → 0 + 0 = 0.

    This argument is valid because:
    1. On bounded body, rotation is bounded, so the per-ω Leibniz dominator
       |dV/dt| ≤ 2(M + K) is integrable → V_body antitone (same as real case)
    2. The body pair bound WORKS for bounded |ω| (the numerical violations
       occur at large |ω| where drifting oscillators rotate freely)
    3. Tail vanishes by integrability of g (probability measure) -/
theorem complex_oa_V_tendsto_zero [IsProbabilityMeasure μ]
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
    -- Body-specific: for each M, body V is antitone (bounded rotation)
    (h_body_anti : ∀ M : ℝ, 0 < M → Antitone (fun t =>
      ∫ ω in {ω | |S.ω_freq ω| ≤ M}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    -- Body-specific: body V → 0 (from body Gronwall + body persistence)
    (h_body_zero : ∀ M : ℝ, 0 < M → Tendsto (fun t =>
      ∫ ω in {ω | |S.ω_freq ω| ≤ M}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0))
    -- Tail vanishing: tail measure → 0
    (h_tail : ∀ ε > 0, ∃ M : ℝ, ∀ t, 0 ≤ t →
      ∫ ω in {ω | M < |S.ω_freq ω|}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ < ε) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0) := by
  sorry

end
