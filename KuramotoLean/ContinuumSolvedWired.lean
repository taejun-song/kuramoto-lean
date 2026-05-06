/-
  Kuramoto Stability — Single Wired Continuum Theorem
  ====================================================
  Resolves TWO wiring issues identified by Codex review:

  ISSUE 1 (hγ and ω=0):
    The old theorem used `hγ_pos : ∀ ω, 0 < γ ω` (strict), which is a
    REDUNDANT hypothesis: strict positivity is already DERIVABLE from the
    equilibrium equation γ·α* = (K/2)·r*·(1-α*²) together with
    `hα_star_lt : α_star ω < 1`.  (If γω = 0 then α*(ω) = 1, contradicting
    hα_star_lt.  Hence `hα_star_lt` already implicitly forces γ > 0.)

    At ω=0: γ(0)=0 forces α*(0)=1 (fully locked), which is the most-locked
    oscillator.  The hypothesis `hα_star_lt : α_star ω < 1` simply means
    ω=0 is not in the type Ω — consistent with using Ω = ℝ\{0} for γ=|ω|.

    FIX: Use `hγ : ∀ ω, 0 ≤ γ ω` (non-negative).  The strict bound
    `0 < γ ω` is provable when needed from `gamma_pos_from_equil`
    (equilibrium equation + hα_star_lt + hα_star_pos), but no downstream
    call requires it explicitly — `continuum_body_persistence` and
    `kuramoto_continuum_stability` both need only 0 ≤ γ ω.

  ISSUE 2 (body persistence not wired into ContinuumSolvedComplete):
    `ContinuumSolvedComplete` (kuramoto_continuum_stability) takes h_body_gronwall
    as an external hypothesis. ContinuumSolvedFromODE proves body persistence
    but was not used to derive h_body_gronwall internally.

    FIX: ONE theorem whose proof:
    (a) Internally calls `continuum_body_persistence` (BodyPersistenceFromODE)
        to derive δ(M) from ODE comparison — no external persistence hypothesis.
    (b) Instantiates `h_gronwall_from_persist` with the derived δ to get
        h_body_gronwall for each body {γ ≤ M}.
    (c) Calls `kuramoto_continuum_stability` (ContinuumSolvedComplete)
        with the derived h_body_gronwall.
    Result: Tendsto r atTop (nhds r_star).

  Remaining open assumptions:
    • h_gronwall_from_persist: the body Gronwall bound (body Leibniz +
      pair coercivity — the single remaining unproved step).
    • h_combined_vanish: C(M) + μ(tail) → 0, which depends on g's decay.

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedComplete

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Single wired continuum Kuramoto theorem** (resolves both wiring issues).

  ISSUE 1 FIX: `hγ : ∀ ω, 0 ≤ γ ω` (non-negative, not strict).
  Strict positivity `0 < γ ω` is DERIVABLE from the equilibrium equation
  plus `hα_star_lt`: if γω = 0 the equilibrium gives α*(ω)=1, contradicting
  hα_star_lt, so `hγ_pos` was a redundant hypothesis.  Using `hγ : 0 ≤ γ ω`
  is the minimal honest hypothesis; downstream calls need only 0 ≤ γ ω.

  ISSUE 2 FIX: proof internally calls `continuum_body_persistence`
  (BodyPersistenceFromODE) to derive δ(M) > 0 on each body {γ ≤ M}, then
  instantiates `h_gronwall_from_persist` with δ(M), then calls
  `kuramoto_continuum_stability` (ContinuumSolvedComplete) directly.
  No external body-persistence hypothesis needed. -/
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
    -- r persistence (from Ψ-growth / instability escape — the only dynamical input
    -- beyond ODE existence; says the system stays supercritical)
    (r_min : ℝ) (hr_min : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (h_r_persist : ∀ t, 0 ≤ t → r_min ≤ r t)
    -- initial body lower bound: initial α bounded away from 0 on each body {γ ≤ M}
    (hα_0_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    -- Gronwall from body persistence:
    --   given δ > 0 uniform on {γ ≤ M}, produces rate and Gronwall bound on V_body.
    --   Provable from: body Leibniz (γ ≤ M bounded → dominator 2M+K) +
    --   pair coercivity (body persistence δ + equilibrium lower bound ds(M)).
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_gronwall_from_persist : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      (∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    -- combined vanishing: C(M) + μ({γ > M}) → 0
    -- depends on decay of g: Gaussian, Student-t ν>2, compact support all satisfy this
    (h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  -- ISSUE 2 FIX step (a): derive body persistence from ODE comparison on each body.
  -- `continuum_body_persistence` (BodyPersistenceFromODE) gives δ(M) > 0 such that
  -- ∀ ω ∈ {γ ≤ M}, ∀ t ≥ 0, δ(M) ≤ α(ω,t). No external persistence hypothesis.
  have h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M := fun M hM => by
    obtain ⟨δ, hδ, hα_lb⟩ := continuum_body_persistence (μ := μ) γ K r α r_min M hK hγ
      hr_min hr_min_le hM h_r_persist hr_bdd
      (fun ω t ht => hα_ode ω t (le_of_lt ht))
      hα_inv hα_cont
      (fun ω hω => (hα_inv ω 0 le_rfl).1)
      (hα_0_body M hM)
    -- ISSUE 2 FIX step (b): instantiate Gronwall with derived δ
    exact h_gronwall_from_persist M hM δ hδ hα_lb
  -- ISSUE 2 FIX step (c): call ContinuumSolvedComplete (kuramoto_continuum_stability_gronwall)
  exact kuramoto_continuum_stability_gronwall γ K hK hγ hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level C hC_nn h_body_gronwall h_combined_vanish

/-! ## ISSUE 1 RESOLVED: γ > 0 is derivable, not assumed

`kuramoto_continuum_wired` uses `hγ : ∀ ω, 0 ≤ γ ω` (minimal hypothesis).
Strict positivity `0 < γ ω` is NOT an independent hypothesis — it follows
from the equilibrium equation plus `hα_star_lt : α_star ω < 1`:
  if γω = 0 then 0 = (K/2)·r*·(1 - α*(ω)²) with K,r* > 0, so α*(ω) = ±1.
  Since α*(ω) > 0 (hα_star_pos), α*(ω) = 1, contradicting hα_star_lt.
Hence the hypothesis bundle already forces γ > 0 wherever it matters.

The following lemma makes this derivation explicit. -/

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
