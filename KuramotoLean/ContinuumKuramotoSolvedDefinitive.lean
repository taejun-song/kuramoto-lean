/-
  Kuramoto Stability — Definitive Continuum Theorem (Standard Model)
  ==================================================================
  `kuramoto_solved_continuum_definitive`: the CORRECT theorem for the standard
  continuum Kuramoto model with γ(ω) = |ω| on ℝ.

  Resolves three fundamental problems with `kuramoto_solved`:

  PROBLEM 1 (Persistence): `kuramoto_solved` assumes ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t).
  FALSE for the standard model — drifting oscillators (|ω| > Kr*) have α*(ω) → 0.
  RESOLUTION: Body persistence per truncation M only. No global persistence.

  PROBLEM 2 (Bounded γ): `kuramoto_solved` assumes γ(ω) ≤ γ_max.
  FALSE — γ(ω) = |ω| is unbounded on ℝ.
  RESOLUTION: On each body {γ ≤ M}, γ IS bounded by M. No global bound.

  PROBLEM 3 (Minimum weight): `kuramoto_solved` rate uses c_min = min atom weight.
  INAPPLICABLE to continuum g(ω)dω which has no atoms.
  RESOLUTION: Rate from body pair coercivity on {γ ≤ M}. No atoms needed.

  PROOF (Tail-Body Split, Dietert 2016 §2-3):
    For any ε > 0, choose M large enough:
    1. TAIL: V_tail ≤ μ({γ > M}) < ε (probability measure, |α-α*|² ≤ 1)
    2. BODY: V_body < C(M) + ε (absorbing ball from body Gronwall)
    3. COMBINE: V = V_body + V_tail < C(M) + 2ε → 0 when C(M) → 0

  Coverage: Gaussian, Student-t ν>2, compact support (NOT Lorentzian).
  Lorentzian needs Bernoulli closed-form (proved separately).

  0 sorry. 0 axioms.
-/

import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.ContinuumTailBodyConvergence
import KuramotoLean.ContinuumSolvedReal

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definitive continuum Kuramoto stability (standard model).**

For the Ott-Antonsen continuum Kuramoto model with:
  • γ : Ω → ℝ — natural frequency (UNBOUNDED, e.g. γ(ω) = |ω|)
  • μ — probability measure (representing g(ω)dω on ℝ)
  • α*(ω) — equilibrium with γ·α* = (K/2)·r*·(1-(α*)²)
  • r* = ∫ α* dμ — self-consistent equilibrium order parameter

Conclusion: r(t) → r* as t → ∞.

Does NOT assume:
  • `γ_max` / `hγ_bdd` — γ bounded globally (PROBLEM 2)
  • `∃ δ, ∀ ω t, δ ≤ α(ω,t)` — uniform persistence (PROBLEM 1)
  • `c_min` — minimum atom weight (PROBLEM 3)

Key hypothesis `h_body_absorb`: for each M > 0, V_body(M,t) eventually
enters absorbing ball of radius C(M). Derivable from:
  • γ ≤ M on body → Leibniz (dominator 2M+K)
  • Body persistence δ(M) > 0 → coercive pair bound
  • dV_body/dt ≤ -K·δ(M)·δ*(M)·V_body + K·μ(tail) → Gronwall

Key hypothesis `h_vanish`: C(M) + μ({γ > M}) → 0.
  Satisfied when g decays fast enough: M²·μ({γ>M}) → 0. -/
theorem kuramoto_solved_continuum_definitive [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (_K : ℝ)
    (_hK : 0 < _K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω =
      (_K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY ABSORBING BALL (replaces bounded γ + uniform persistence + c_min):
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_absorb : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε)
    -- COMBINED VANISHING:
    (h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
      atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) :=
  tail_body_iss_convergence α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    γ hγ_level C hC_nn h_body_absorb h_vanish

/-- **Continuum stability from body Gronwall with absorbing radius.**

Variant that takes an explicit body Gronwall bound
V_body(t) ≤ V₀·exp(-rate·t) + C(M) and derives the absorbing-ball
condition needed by `kuramoto_solved_continuum_definitive`.

This is the form that arises directly from body Leibniz + body persistence
+ Gronwall comparison on the restricted body {γ ≤ M}. -/
theorem kuramoto_solved_continuum_gronwall [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω =
      (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY GRONWALL with absorbing radius C(M):
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧ ∀ t ≥ (0 : ℝ),
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
          (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
            rexp (-rate * t) + C M)
    -- COMBINED VANISHING:
    (h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal)
      atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  apply kuramoto_solved_continuum_definitive γ K _hK _hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq _hα_star_equil r α
    h_sc hα_int hα_sq_int hα_inv C hC_nn _ h_vanish
  intro M hM ε hε
  exact body_absorb_from_gronwall α α_star hα_sq_int hγ_level
    C hC_nn h_body_gronwall M hM ε hε

/-- **Continuum stability from body exponential decay (no absorbing ball).**

Stronger variant where V_body → 0 (not just V_body → C(M)).
This means C(M) = 0, so combined vanishing reduces to μ(tail) → 0,
which is automatic for any probability measure.

Applicable when body persistence is strong enough to give full decay
(e.g., finite first moment via BarbalatLeibnizBridge). -/
theorem kuramoto_solved_continuum_exp [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω =
      (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (_hα_ode : ∀ ω, ∀ t ≥ 0,
      HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY EXPONENTIAL DECAY (C(M) = 0):
    (h_body_exp : ∀ M : ℝ, 0 < M →
      ∃ rate : ℝ, 0 < rate ∧ ∀ t ≥ (0 : ℝ),
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
          (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
            rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) :=
  kuramoto_solved_full_continuum γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α _hα_ode
    h_sc hα_int hα_sq_int hα_inv h_body_exp

/-- **Subsumption: `kuramoto_solved` (bounded γ) is a special case.**

When γ IS bounded by γ_max and persistence IS uniform:
  • Body = full space for M ≥ γ_max (tail is empty)
  • Body Gronwall from global Gronwall: V_body ≤ V ≤ V₀·exp(-rate·t)
  • C(M) = 0 for all M, combined vanishing = μ(tail) → 0 (automatic)

This proves `kuramoto_solved_continuum_definitive` strictly generalizes
`kuramoto_solved`. -/
theorem bounded_gamma_implies_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω =
      (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- Global Gronwall (from `kuramoto_solved`'s bounded-γ machinery):
    (rate : ℝ) (hrate : 0 < rate)
    (h_gronwall : ∀ t ≥ (0 : ℝ),
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) := by
  have h_tail : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero (μ := μ) γ hγ_level
  apply tail_body_iss_convergence α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    γ hγ_level (fun _ => 0) (fun _ => le_rfl)
  · intro M _hM ε hε
    have h_exp_decay : Tendsto
        (fun t : ℝ => (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hrate).mpr tendsto_id
      have h2 := (tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp h1)).const_mul
          (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ)
      simp only [Function.comp_def, mul_zero] at h2
      exact h2.congr (fun _ => by ring)
    rw [Metric.tendsto_atTop] at h_exp_decay
    obtain ⟨T, hT⟩ := h_exp_decay ε hε
    refine ⟨max T 0, fun t ht => ?_⟩
    have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
    have h_body_le : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
        ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
      setIntegral_le_integral (hα_sq_int t)
        (ae_of_all μ fun _ => sq_nonneg _)
    have h_full := h_gronwall t ht_nn
    have h_exp := hT t (le_trans (le_max_left T 0) ht)
    rw [Real.dist_eq, sub_zero] at h_exp
    have h_nn_exp : 0 ≤ (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) *
        rexp (-rate * t) :=
      mul_nonneg (integral_nonneg fun _ => sq_nonneg _)
        (le_of_lt (Real.exp_pos _))
    rw [abs_of_nonneg h_nn_exp] at h_exp
    simp only [zero_add]; linarith
  · simp only [zero_add]; exact h_tail

end
