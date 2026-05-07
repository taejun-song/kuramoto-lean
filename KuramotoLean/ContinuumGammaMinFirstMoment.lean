/-
  ContinuumGammaMinFirstMoment.lean
  ==================================
  Proves r(t) → r* for the continuum OA model when:
    • γ(ω) ≥ γ_min > 0  (uniform positive damping)
    • ∫ γ dμ < ∞        (FIRST MOMENT — weaker than second moment)

  MOTIVATION: KuramotoGammaMinConvergence.lean requires second moment
    hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ
  via the Gronwall/absorbing-ball path (ContinuumSolvedWired6).

  This file uses the LEIBNIZ-FTC PATH via two building blocks:
    1. continuum_v_antitone  (ContinuumSolvedContinuum) — V antitone from first moment
    2. iss_implies_definitive (ContinuumFiniteMoment)   — r → r* from V antitone + Gronwall

  The caller supplies the body Gronwall absorbing radius C(M) and
  combined vanishing C(M) + μ({γ>M}) → 0.

  KEY OBSERVATION: V antitone no longer requires second moment. The
  Leibniz dominator 2γ(ω)+K is integrable (from first moment), so
  leibniz_oa_integrable_gamma applies. The Q-integrability used in
  dV/dt ≤ 0 follows from the equilibrium identity 1/α* = α*+2γ/(Kr*)
  and first moment ∫γdμ < ∞.

  COVERAGE: All distributions with finite first moment + γ_min > 0:
    • Student-t 1 < ν ≤ 2 (second moment infinite, first moment finite)
    • Power-law g(ω) ~ ω^{-(1+α)} with 1 < α ≤ 2 on [γ_min, ∞)
    • Any g with ∫γ g dγ < ∞ and g supported on [γ_min, ∞)

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedContinuum
import KuramotoLean.ContinuumFiniteMoment

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Continuum Kuramoto convergence: γ_min > 0 with first moment only.**

    Combines V antitone (from Leibniz-FTC via `continuum_v_antitone`,
    using first moment ∫γ<∞) with body-tail ISS convergence
    (`iss_implies_definitive`, using body Gronwall + combined vanishing).

    The key advantage over `KuramotoGammaMinConvergence`:
      OLD: requires `hγ_sq_int : Integrable (fun ω => (γ ω)^2) μ` (second moment)
      NEW: requires only `hγ_int : Integrable γ μ` (first moment)

    Caller obligations:
    - `hα_neg`: α(ω,t) = α(ω,0) for t ≤ 0 (Leibniz extension convention)
    - `C M`: body absorbing radius (derivable from body persistence)
    - `h_body_rate`: body exponential decay into C(M) ball
    - `h_combined_vanish`: C(M) + μ({γ>M}) → 0 as M → ∞

    For the canonical choice with initial lower bound α₀_lb > 0:
      C(M) = τ(M)/(α₀_lb · ds(M)) ~ M·μ({γ>M})/(α₀_lb·K·r_star)
    Combined vanishing then follows from first_moment_tail_vanish
    (M·μ({γ>M}) → 0 from ∫γ<∞). -/
theorem kuramoto_gamma_min_first_moment [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- FIRST MOMENT (replaces second moment hγ_sq_int of KuramotoGammaMinConvergence)
    (hγ_int : Integrable γ μ)
    -- Minimum damping (gives strict positivity ∀ ω, 0 < γ ω)
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_lb : ∀ ω, γ_min ≤ γ ω)
    -- Body absorbing radius and Gronwall decay
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_rate : ∀ M : ℝ, 0 < M → ∃ (rate : ℝ), 0 < rate ∧ ∀ t ≥ (0 : ℝ),
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
          (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
            rexp (-rate * t) + C M)
    -- Combined vanishing: C(M) + μ({γ>M}) → 0
    (h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  -- Step 1: strict positivity of γ from lower bound
  have hγ_pos : ∀ ω, 0 < γ ω := fun ω => lt_of_lt_of_le hγ_min (hγ_lb ω)
  -- Step 2: V antitone from first moment (Leibniz-FTC path)
  -- continuum_v_antitone uses integrable γ dominator 2γ+K and Q-integrability
  -- from 1/α* = α* + 2γ/(Kr*) to prove dV/dt ≤ 0, hence V antitone.
  have hV_anti : Antitone (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) :=
    continuum_v_antitone γ K r α α_star r_star hK hγ_pos hγ_int hγ_meas
      hr_cont hr_bdd hr_nn hα_ode hα_cont hα_star_pos hα_star_lt hαs_int
      hr_star_eq hα_star_equil h_sc hα_inv hα_sq_int hα_neg hα_int
  -- Step 3: r → r* from V antitone + body Gronwall + combined vanishing
  exact iss_implies_definitive γ K hK hγ_pos hγ_int α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int
    hα_inv hγ_level hV_anti C hC_nn h_body_rate h_combined_vanish

end
