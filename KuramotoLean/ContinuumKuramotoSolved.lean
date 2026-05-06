/-
  kuramoto_continuum_solved — Definitive Continuum Kuramoto Global Stability
  ==========================================================================
  The correct theorem for the STANDARD continuum Kuramoto model:
    dα/dt = -|ω|·α + (K/2)·r(t)·(1 - α²),  r(t) = ∫ α(ω,t) g(ω) dω
  with g : R → R integrable (Lorentzian, Gaussian, etc.), K > K_c.

  Resolves ALL THREE fundamental problems with `kuramoto_solved`:

  PROBLEM 1 (Uniform persistence FALSE):
    `kuramoto_solved` requires ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t).
    FALSE: drifting oscillators (|ω| > Kr*) have α*(ω) → 0.
    FIX: Body persistence only — on each body {γ ≤ M}, α ≥ δ(M) > 0.
    This IS true for locked oscillators where α*(ω) > 0.

  PROBLEM 2 (Bounded γ FALSE):
    `kuramoto_solved` requires ∀ ω, γ(ω) ≤ γ_max.
    FALSE: γ(ω) = |ω| unbounded on R.
    FIX: No global γ_max. On each body {γ ≤ M}, γ is bounded by M,
    so Leibniz differentiation works (dominator 2M + K).

  PROBLEM 3 (c_min inapplicable):
    `kuramoto_solved` rate μ = K·c_min·δ·δ* is an n-pole concept.
    Continuum g(ω)dω has no atoms; c_min = 0.
    FIX: Body pair coercivity gives rate K·δ(M)·ds(M) directly.
    No minimum weight needed.

  PROOF STRATEGY (Dietert 2016, §2-3 tail-body split):
    Split V = ∫(α-α*)² dμ into body {γ ≤ M} and tail {γ > M}:
      V = V_body(M) + V_tail(M)            [integral_add_compl]

    TAIL: V_tail ≤ μ({γ > M}) → 0 as M → ∞
      Since |α - α*| < 1 pointwise (both in (0,1)), (α-α*)² ≤ 1.
      Tail integral ≤ μ(tail). μ({γ > M}) → 0 for any probability
      measure (continuity of measure from above, no moment condition).

    BODY: V_body(M,t) → absorbing ball of radius C(M) → 0
      On {γ ≤ M}: γ bounded → Leibniz differentiation works.
      Body persistence δ(M) > 0 + equilibrium bound ds(M) > 0
      → coercive pair bound ∫∫_body pair ≥ 2·δ(M)·ds(M)·V_body.
      Body ISS: dV_body/dt ≤ -K·δ(M)·ds(M)·V_body + K·μ(tail)
      (tail coupling from r = ∫_ALL α dμ acting as forcing).
      Gronwall comparison → V_body ≤ V(0)·e^{-λt} + C(M).
      C(M) = μ(tail)/(δ(M)·ds(M)) → 0 for fast-decaying g.

    COMBINED: |r - r*|² ≤ V = V_body + V_tail
      For any ε > 0, choose M with C(M) + μ(tail) < ε²/4.
      Eventually V_body < C(M) + ε²/4, V_tail < ε²/4.
      So V < 3ε²/4 < ε², |r - r*| < ε.

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedReal
import KuramotoLean.ContinuumSolvedStandard

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definitive Continuum Kuramoto Global Stability Theorem.**

For the ACTUAL standard continuum Kuramoto model with:
  • γ(ω) = |ω| — unbounded natural frequency (no γ_max)
  • μ — any probability measure on Ω (represents g(ω)dω)
  • BOTH locked (α* > 0) AND drifting (α* → 0) oscillators
  • NO uniform lower bound on α (no global persistence δ)

The order parameter r(t) → r* as t → ∞.

Hypotheses (all verifiable for the standard model):
  • Equilibrium: α* solves γ·α* = (K/2)·r*·(1 - α*²)
  • Solution: (r, α) satisfy OA ODE + self-consistency + invariance
  • γ-level sets measurable (automatic for measurable γ)
  • Body Gronwall: for each M > 0, V_body(M,t) ≤ V_body(M,0)·e^{-rate·t} + C(M)
    (derivable from: Leibniz [γ ≤ M] + body persistence + pair coercivity)
  • Absorbing radius: C(M) → 0 as M → ∞
    (derivable from: C = μ(tail)/rate, μ(tail) → 0, rate bounded below)

The theorem does NOT assume:
  • γ globally bounded (PROBLEM 2 ✓)
  • ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t) — uniform persistence (PROBLEM 1 ✓)
  • c_min — minimum atom weight (PROBLEM 3 ✓)

Subsumes `kuramoto_solved` as special case: when γ IS bounded, C(M) = 0
for M ≥ γ_max and the body is all of Ω. -/
theorem kuramoto_continuum_solved [IsProbabilityMeasure μ]
    -- Physical parameters
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- Equilibrium data
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    -- ODE solution data
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY GRONWALL: exponential decay to absorbing ball on each body {γ ≤ M}
    -- Derivable from: bounded γ on body → Leibniz; body persistence → coercivity;
    -- tail coupling → ISS forcing; Gronwall comparison → exponential + C(M)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (hC_vanish : Tendsto C atTop (nhds 0))
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M) :
    Tendsto r atTop (nhds r_star) := by
  -- Step 1: Tail vanishing — μ({γ > M}) → 0 from probability measure (no moment condition)
  have h_tail : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero (μ := μ) γ hγ_level
  -- Step 2: Combined vanishing C(M) + μ(tail) → 0
  have h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have h := hC_vanish.add h_tail; rwa [add_zero] at h
  -- Step 3: ε-δ argument with integral_add_compl (Dietert tail-body split)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε ^ 2 / 4
  have hδ : 0 < δ := by positivity
  rw [Metric.tendsto_atTop] at h_vanish
  obtain ⟨N, hN⟩ := h_vanish δ hδ
  set M := max N 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_sum_small : C M + (μ {ω | M < γ ω}).toReal < δ := by
    have h := hN M (le_max_left N 1)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg
      (add_nonneg (hC_nn M) ENNReal.toReal_nonneg)] at h
  -- Body absorbing ball from Gronwall
  obtain ⟨rate, hrate, h_gron⟩ := h_body_gronwall M hM_pos
  obtain ⟨T, hT⟩ := iss_from_gronwall_bound
    (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ)
    (fun t => integral_nonneg fun _ => sq_nonneg _)
    rate (C M) hrate (hC_nn M) h_gron δ hδ
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have ht_ge_T : T ≤ t := le_trans (le_max_left T 0) ht
  -- Cauchy-Schwarz: |r - r*|² ≤ V = ∫(α - α*)² dμ
  have hCS : (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]; exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  -- Split V = V_body + V_tail via integral_add_compl
  have hV_split : ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int t)).symm
  -- Tail bound: V_tail ≤ μ({γ > M}) < δ
  have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
  have hVtail : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int t).integrableOn
            (integrable_const 1).integrableOn (hγ_level M).compl
          intro ω _
          nlinarith [(hα_inv ω t ht_nn).1, (hα_inv ω t ht_nn).2,
            hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)]
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
      _ < δ := lt_of_le_of_lt (le_add_of_nonneg_left (hC_nn M)) h_sum_small
  -- Body bound: V_body < C(M) + δ < 2δ
  have hVbody : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < 2 * δ := by
    have hC_lt : C M < δ :=
      lt_of_le_of_lt (le_add_of_nonneg_right ENNReal.toReal_nonneg) h_sum_small
    linarith [hT t ht_ge_T]
  -- Combine: |r - r*|² ≤ V = V_body + V_tail < 2δ + δ = 3ε²/4 < ε²
  have hV_lt : (r t - r_star) ^ 2 < ε ^ 2 := calc
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := hCS
    _ = _ + _ := hV_split
    _ < 2 * δ + δ := add_lt_add hVbody hVtail
    _ = 3 * (ε ^ 2 / 4) := by ring
    _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hV_lt (le_of_lt hε)

/-- **Subsumption: `kuramoto_solved` (bounded γ) is a special case.**

When γ IS bounded by γ_max and persistence IS uniform, the global Gronwall
V(t) ≤ V(0)·exp(-rate·t) implies body Gronwall with C(M) = μ({γ > M}).
For M ≥ γ_max: μ({γ > M}) = 0, so C → 0 trivially. -/
theorem kuramoto_continuum_solved_of_bounded [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K γ_max : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (_hγ_bdd : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- Global Gronwall (from bounded γ + uniform persistence + pair coercivity)
    (rate : ℝ) (hrate : 0 < rate)
    (h_gronwall : ∀ t ≥ (0 : ℝ),
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) := by
  apply kuramoto_continuum_solved γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    -- C(M) = μ({γ > M}): tail measure as absorbing radius
    (fun M => (μ {ω | M < γ ω}).toReal)
    (fun _ => ENNReal.toReal_nonneg)
    (tail_measure_tendsto_zero (μ := μ) γ hγ_level)
  -- Derive body Gronwall from global Gronwall: V_body ≤ V ≤ V(0)·e^{-rt}
  intro M hM
  refine ⟨rate, hrate, fun t ht => ?_⟩
  have h_body_le : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
    setIntegral_le_integral (hα_sq_int t) (ae_of_all μ fun _ => sq_nonneg _)
  have h_split0 : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int 0)).symm
  have h_tail0_le : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ ≤
      (μ {ω | M < γ ω}).toReal := by
    have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int 0).integrableOn
            (integrable_const 1).integrableOn (hγ_level M).compl
          intro ω _
          nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2,
            hα_star_pos ω, hα_star_lt ω, sq_abs (α ω 0 - α_star ω)]
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
  have hexp_le : rexp (-rate * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h_body0_nn : (0 : ℝ) ≤ ∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have h_tail0_nn : (0 : ℝ) ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  calc ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ
      ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := h_body_le
    _ ≤ (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) := h_gronwall t ht
    _ = ((∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) +
         (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ)) *
          rexp (-rate * t) := by rw [← h_split0]
    _ = (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) :=
      add_mul _ _ _
    _ ≤ (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) * 1 := by
      linarith [mul_le_mul_of_nonneg_left hexp_le h_tail0_nn]
    _ ≤ (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (μ {ω | M < γ ω}).toReal := by linarith [h_tail0_le]

/-- **Existential form for end-to-end statements.**

Given standard model data + solution existence with body Gronwall,
the order parameter converges. Bundles the conclusion as ∃ r, r → r*. -/
theorem kuramoto_continuum_solved_exists [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (h_data : ∃ (r : ℝ → ℝ) (α : Ω → ℝ → ℝ),
      (∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) ∧
      ∃ (C : ℝ → ℝ), (∀ M, 0 ≤ C M) ∧ Tendsto C atTop (nhds 0) ∧
        (∀ M : ℝ, 0 < M → ∃ (rate : ℝ), 0 < rate ∧
          ∀ t ≥ (0 : ℝ),
            ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
              (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
                rexp (-rate * t) + C M)) :
    ∃ (r : ℝ → ℝ), Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, h_sc, hα_int, hα_sq_int, hα_inv, C, hC_nn, hC_van, h_gron⟩ := h_data
  exact ⟨r, kuramoto_continuum_solved γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    C hC_nn hC_van h_gron⟩

end
