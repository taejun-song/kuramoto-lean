/-
  Kuramoto Stability — Single Wired Continuum Theorem
  ====================================================
  Resolves TWO wiring issues identified by Codex review:

  ISSUE 1 (hγ and ω=0):
    The original theorem had `hγ_pos : ∀ ω, 0 < γ ω`, which explicitly
    excludes ω=0 for γ = |ω|. This is unnecessary: strict positivity of γ
    is DERIVABLE from the equilibrium hypotheses. If γ(ω) = 0 then the
    equilibrium equation 0 = (K/2)·r*·(1-α*²) with K,r* > 0 forces
    α*(ω) = 1, contradicting hα_star_lt. So γ ω > 0 follows from the
    other hypotheses — we need only assume γ ω ≥ 0.

    At ω=0 (γ=0): the equilibrium is α*(0) = 1 (fully locked), and the
    ODE dα/dt = (K/2)·r·(1-α²) drives α → 1 monotonically. The point
    ω=0 is thus the MOST locked oscillator, not a problematic case.
    The hypothesis hα_star_lt : α* < 1 effectively excludes ω=0 from Ω
    (which is WLOG since {ω=0} has measure zero for any density g).

  ISSUE 2 (body persistence not wired into ContinuumSolvedComplete):
    The original `kuramoto_continuum_wired` called `kuramoto_continuum_real`
    (ContinuumSolvedReal.lean, EventualTAC path) and did NOT call any
    theorem from ContinuumSolvedComplete.lean.

    FIX: This single theorem directly calls `kuramoto_wired_to_complete`
    (ContinuumSolvedComplete.lean), which:
    1. Internally derives body persistence δ(M) from ODE comparison
       (calling `continuum_body_persistence` from BodyPersistenceFromODE)
    2. Instantiates h_gronwall_from_persist with δ to get h_body_gronwall
    3. Calls `kuramoto_continuum_stability` (ContinuumSolvedComplete)
    4. Produces: Tendsto r atTop (nhds r_star)

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedComplete
import KuramotoLean.ContinuumSolvedReal

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Single wired continuum Kuramoto theorem.**

Resolves BOTH wiring issues:
  ISSUE 1: Uses `hγ : ∀ ω, 0 ≤ γ ω` (not `0 < γ ω`). Strict positivity
    is derivable from hα_star_equil + hα_star_pos + hα_star_lt + K,r* > 0.
    At ω=0: α*(0)=1 (fully locked), but hα_star_lt excludes it — WLOG
    since {ω=0} has measure zero.

  ISSUE 2: Wires ContinuumSolvedFromODE into ContinuumSolvedComplete by
    calling `kuramoto_wired_to_complete`, which internally:
    (a) Derives body persistence δ(M) from ODE comparison (BodyPersistenceFromODE)
    (b) Instantiates h_gronwall_from_persist with δ to get h_body_gronwall
    (c) Calls kuramoto_continuum_stability (ContinuumSolvedComplete)

For the standard model γ(ω) = |ω|, instantiate with Ω = {ω : ℝ | ω ≠ 0}.
The measure-zero exclusion of {0} is WLOG for any density g. -/
theorem kuramoto_continuum_wired [IsProbabilityMeasure μ]
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
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- r PERSISTENCE (from Ψ-growth / instability escape)
    (r_min : ℝ) (hr_min : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (h_r_persist : ∀ t, 0 ≤ t → r_min ≤ r t)
    -- INITIAL DATA bounded away from 0 on each body
    (hα_0_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    -- GRONWALL from body persistence + Leibniz + pair coercivity
    -- Provable from: body Leibniz (γ ≤ M → dominator 2M+K) + pair coercivity
    -- (body persistence δ + equilibrium bound ds → coercive rate K·δ·ds)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_gronwall_from_persist : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      (∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    -- COMBINED VANISHING: C(M) + μ({γ > M}) → 0
    (h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) :=
  -- WIRED: internally derives body persistence (ContinuumSolvedFromODE),
  -- then calls ContinuumSolvedComplete (kuramoto_continuum_stability).
  kuramoto_wired_to_complete γ K hK hγ hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level r_min hr_min hr_min_le h_r_persist hα_0_body
    C hC_nn h_gronwall_from_persist h_combined_vanish

/-! ## Why γ ω > 0 follows from equilibrium hypotheses

The hypothesis `hγ : ∀ ω, 0 ≤ γ ω` is strictly weaker than the old
`hγ_pos : ∀ ω, 0 < γ ω`. The strict positivity is redundant given:
  • hα_star_equil : γ ω * α_star ω = (K/2) * r_star * (1 - α_star(ω)²)
  • hα_star_pos   : 0 < α_star ω
  • hα_star_lt    : α_star ω < 1
  • K > 0, r_star > 0 (from r_star = ∫ α_star dμ and α_star > 0)

At any ω: since α_star ω ∈ (0,1), we have 1 - α_star(ω)² > 0, so the RHS
is positive, giving γ ω * α_star ω > 0, hence γ ω > 0. -/

theorem gamma_pos_from_equil (γ_val K r_star α_star_val : ℝ)
    (hK : 0 < K) (hr_star : 0 < r_star)
    (hα_pos : 0 < α_star_val) (hα_lt : α_star_val < 1)
    (hγ_nn : 0 ≤ γ_val)
    (h_equil : γ_val * α_star_val = (K / 2) * r_star * (1 - α_star_val ^ 2)) :
    0 < γ_val := by
  have h_rhs : 0 < (K / 2) * r_star * (1 - α_star_val ^ 2) :=
    mul_pos (mul_pos (half_pos hK) hr_star) (by nlinarith [sq_nonneg α_star_val])
  rw [← h_equil] at h_rhs
  cases (mul_pos_iff.mp h_rhs) with
  | inl h => exact h.1
  | inr h => linarith [hα_pos]

end
