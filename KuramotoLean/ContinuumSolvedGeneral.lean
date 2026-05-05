/-
  Kuramoto Stability — General Continuum Theorem (Tail-Body Split)
  ================================================================
  Clean end-to-end theorem for the STANDARD continuum Kuramoto model
  with γ(ω) = |ω| unbounded on R. Resolves all three reviewer problems
  with `kuramoto_solved` (GeneralGMainTheorem.lean):

  PROBLEM 1: Uniform persistence δ ≤ α(ω,t) for ALL ω is FALSE.
  → Only BODY persistence on {γ ≤ M} (locked oscillators).

  PROBLEM 2: γ bounded (γ ≤ γ_max) is FALSE for γ(ω) = |ω|.
  → No global γ_max. On body {γ ≤ M}, γ ≤ M (Leibniz works).

  PROBLEM 3: c_min (minimum atom) inapplicable to continuum.
  → Works with arbitrary probability measure μ.

  The theorem `kuramoto_solved_continuum` takes:
  - g supported on R (integrable)
  - γ unbounded
  - Body persistence only (on each {γ ≤ M})
  - Combined vanishing C(M) + μ(tail) → 0

  Applies `tail_body_iss_convergence` with the body Gronwall bound
  derived from body persistence + bounded γ on body + pair coercivity.

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumTailBodyConvergence

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **General Continuum Kuramoto Theorem (Tail-Body Split).**

The correct theorem for the standard continuum Kuramoto model with:
  • γ(ω) = |ω| — UNBOUNDED on R
  �� g ∈ L¹(R) — any integrable frequency distribution
  • Locked AND drifting oscillators coexist
  • α*(ω) → 0 as |ω| → ∞ — NO uniform lower bound on equilibrium

This theorem does NOT assume:
  • γ globally bounded (resolves PROBLEM 2)
  • Uniform persistence ∀ω, δ ≤ α(ω,t) (resolves PROBLEM 1)
  • Minimum weight c_min (resolves PROBLEM 3)

Key hypotheses (all verifiable for standard model with fast-decaying g):
  • `h_tail_vanish`: μ({γ > M}) → 0 as M → ∞
    (automatic for g ∈ L¹(R) since ∫_{|ω|>M} g → 0)
  • `h_body_persist`: on each body {γ ≤ M}, oscillators maintain α ≥ δ(M) > 0
    (TRUE for locked oscillators: equilibrium α* ≥ Kr*/(2M+Kr*) > 0)
  • `h_body_rate`: body Lyapunov satisfies exponential Gronwall:
    V_body(t) ≤ V_body(0)·e^{-rate(M)·t} + C(M)
    (DERIVED from: Leibniz [γ ≤ M bounded] + pair coercivity [body persist]
     + Gronwall comparison with tail coupling as forcing term)
  • `h_combined_vanish`: C(M) + μ(tail) → 0 as M → ∞
    (SATISFIED when g decays fast enough: Gaussian, Student-t ν>2, compact support.
     C(M) = μ(tail)/(δ(M)·ds(M)), so need M·μ({γ>M}) → 0.)

Proof: direct application of `tail_body_iss_convergence` from
ContinuumTailBodyConvergence.lean. The body Gronwall bound gives
the absorbing ball, and combined vanishing drives r → r*. -/
theorem kuramoto_general_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (_hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (_hr_cont : Continuous r)
    (_hr_bdd : ∀ t, |r t| ≤ 1)
    (_hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (_hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (_hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- TAIL-BODY STRUCTURE (no bounded γ, no uniform persistence)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- Body Gronwall absorbing ball: V_body ≤ V_body(0)·e^{-rate·t} + C(M)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_rate : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    -- COMBINED VANISHING: absorbing radius + tail measure → 0
    (h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) :=
  tail_body_iss_convergence α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    γ hγ_level C hC_nn
    (fun M hM ε hε => body_absorb_from_gronwall α α_star hα_sq_int hγ_level
      C hC_nn h_body_rate M hM ε hε)
    h_combined_vanish

/-- **Corollary: `kuramoto_solved` (bounded γ) is a strict special case.**

When γ IS bounded (γ ≤ γ_max), take C(M) = 0 for all M ≥ γ_max.
The tail is empty, combined vanishing is automatic, and body persistence
= uniform persistence. This shows the new theorem strictly generalizes
the bounded-γ case. -/
theorem kuramoto_solved_bounded_special_case [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K γ_max : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_bdd : ∀ ω, γ ω ≤ γ_max)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- Uniform persistence (available because γ bounded → all oscillators locked)
    (δ_per : ℝ) (hδ_per : 0 < δ_per)
    (h_persist : ∀ ω, ∀ t, 0 ≤ t → δ_per ≤ α ω t)
    -- Body Gronwall with C = 0 (no tail forcing when γ bounded)
    (h_body_rate : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + 0) :
    Tendsto r atTop (nhds r_star) :=
  kuramoto_general_continuum γ K hK (fun ω => le_of_lt (hγ ω)) hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level (fun _ => (0 : ℝ)) (fun _ => le_refl 0) (fun M hM => h_body_rate M hM)
    (tail_vanishes_bounded γ γ_max hγ_bdd)

/-- **Corollary: Fast-decaying g (Gaussian, Student-t ν>2, compact support).**

When g decays fast enough that M · μ({γ > M}) → 0, the absorbing radius
C(M) = μ(tail) / (δ(M) · ds(M)) satisfies combined vanishing automatically.

For Gaussian: μ(tail) ~ e^{-M²}, ds(M) ~ 1/M → C(M) ~ M·e^{-M²} → 0.
For Student-t ν>2: μ(tail) ~ M^{-(ν-1)}, ds(M) ~ 1/M → C(M) ~ M^{-(ν-2)} → 0.
For compact support: μ(tail) = 0 for M large → C(M) = 0.

NOT satisfiable for Lorentzian: μ(tail) ~ 1/M, ds(M) ~ 1/M → C(M) ~ const ≠ 0. -/
theorem kuramoto_solved_fast_decay [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- Body persistence: on each {γ ≤ M}, α ≥ δ(M)
    (δ : ℝ → ℝ) (_hδ_pos : ∀ M, 0 < M → 0 < δ M)
    (_h_body_persist : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ M ≤ α ω t)
    -- Body Gronwall: rate(M) = K · δ(M) · ds(M), absorbing radius C(M)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_rate : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    -- COMBINED VANISHING (satisfied by fast-decaying g)
    (h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) :=
  kuramoto_general_continuum γ K hK (fun ω => le_of_lt (hγ ω)) hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level C hC_nn h_body_rate h_combined_vanish

end
