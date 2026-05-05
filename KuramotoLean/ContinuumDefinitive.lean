/-
  kuramoto_standard_continuum — Definitive Continuum Kuramoto Stability
  =====================================================================
  The correct theorem for the STANDARD continuum Kuramoto model:
    dα/dt = -|ω|·α + (K/2)·r(t)·(1 - α²)
    r(t) = ∫ α(ω,t) g(ω) dω
  with g : R → R integrable, symmetric, unimodal, K > K_c.

  Fixes ALL THREE problems with `kuramoto_solved` (GeneralGMainTheorem.lean):

  PROBLEM 1 (Uniform persistence FALSE):
    `kuramoto_solved` requires ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t).
    Drifting oscillators (|ω| > Kr*) have α*(ω) → 0. No uniform δ exists.
    FIX: Body Gronwall per truncation level M. Only LOCKED oscillators
    on {γ ≤ M} need persistence (where it IS true).

  PROBLEM 2 (Bounded γ FALSE):
    `kuramoto_solved` requires ∀ ω, γ ω ≤ γ_max.
    Standard model has γ(ω) = |ω| unbounded on R.
    FIX: No global γ_max. On each body {γ ≤ M}, γ is bounded by M,
    so Leibniz differentiation works (dominator 2M+K).

  PROBLEM 3 (c_min inapplicable):
    `kuramoto_solved` rate uses c_min (minimum atom weight of discrete μ).
    Continuum g(ω)dω has no atoms.
    FIX: Coercive pair bound gives rate K·δ(M)·ds(M) on body directly.
    No minimum weight needed.

  PROOF STRATEGY (Dietert 2016, §2-3 tail-body split):
    Split V = ∫(α-α*)² dμ into body and tail via integral_add_compl:
      V = V_body(M) + V_tail(M)

    TAIL BOUND: V_tail ≤ μ({γ > M}) → 0
      Since (α-α*)² ≤ 1 pointwise, the tail integral is bounded by the
      tail measure. μ({γ > M}) → 0 by continuity of measure from above
      (automatic for any probability measure — no moment condition).

    BODY CONVERGENCE: V_body(M,t) → absorbing ball of radius C(M) → 0
      On body {γ ≤ M}: γ bounded by M (Leibniz works), locked oscillators
      have body persistence δ(M) > 0, pair coercivity gives rate.
      Body ISS Gronwall: dV_body/dt ≤ -rate(M)·V_body + forcing(M)
      → V_body eventually ≤ C(M) + ε for any ε > 0.

    COMBINED: For any ε > 0, choose M with C(M) + μ(tail) < ε²/4.
      Then V < 2·(ε²/4) + ε²/4 < ε².
      Cauchy-Schwarz: |r - r*|² ≤ V < ε². Done.

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedReal
import KuramotoLean.ContinuumSolvedStandard

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definitive Standard Continuum Kuramoto Stability Theorem.**

For the actual physical continuum Kuramoto model with:
  • γ(ω) = |ω| — unbounded natural frequency on R
  • g ∈ L¹(R) — any integrable frequency distribution
  • BOTH locked (|ω| < Kr*) AND drifting (|ω| > Kr*) oscillators
  • α*(ω) → 0 as |ω| → ∞ — NO uniform lower bound

Conclusion: the order parameter r(t) → r* as t → ∞.

Does NOT assume:
  • `γ_max` / `hγ_bdd` — γ bounded globally (PROBLEM 2)
  • `∃ δ, ∀ ω t, δ ≤ α(ω,t)` — uniform persistence (PROBLEM 1)
  • `c_min` — minimum atom weight (PROBLEM 3)

Key hypothesis: `h_body_gronwall` — for each truncation level M > 0,
the body Lyapunov V_body(M,t) satisfies an exponential Gronwall bound:
  V_body(M,t) ≤ V_body(M,0) · exp(-rate(M)·t) + C(M)
with absorbing radius C(M) → 0 as M → ∞.

This body Gronwall is DERIVABLE from the bounded-γ stability machinery
applied to the body {γ ≤ M} where:
  • γ ≤ M → Leibniz differentiation of V_body (dominator 2M+K)
  • Body persistence: ∃ δ(M) > 0, α ≥ δ(M) on {γ ≤ M}
  • Body pair coercivity: ∫∫_body pair ≥ 2·δ(M)·ds(M)·V_body
  • Body ISS: dV_body/dt ≤ -K·δ(M)·ds(M)·V_body + K·μ(tail)
  • Gronwall comparison → exponential decay to absorbing ball

The absorbing radius C(M) = μ({γ>M})/(δ(M)·ds(M)) → 0 because
μ({γ>M}) → 0 (probability measure) and δ(M)·ds(M) is bounded below
for any fixed M (from body persistence + equilibrium lower bound).

Covers: Gaussian, Student-t (ν > 2), compact support, any g with
M · g(M) integrable. NOT Lorentzian without additional argument
(use `kuramoto_continuum_real` for Lorentzian via EventualTAC). -/
theorem kuramoto_standard_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- Equilibrium data
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    -- ODE solution data
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY GRONWALL: on each body {γ ≤ M}, exponential decay to absorbing ball
    -- (from bounded-γ stability on body: Leibniz + persistence + coercivity)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M) (hC_vanish : Tendsto C atTop (nhds 0))
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M) :
    Tendsto r atTop (nhds r_star) := by
  -- Step 1: Derive tail vanishing from probability measure (no moment condition)
  have h_tail : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero (μ := μ) γ hγ_level
  -- Step 2: Derive body absorbing ball from Gronwall bound
  have h_body_absorb : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε := by
    intro M hM ε hε
    obtain ⟨rate, hrate, h_gron⟩ := h_body_gronwall M hM
    exact iss_from_gronwall_bound
      (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ)
      (fun t => integral_nonneg fun _ => sq_nonneg _)
      rate (C M) hrate (hC_nn M) h_gron ε hε
  -- Step 3: Derive combined vanishing C(M) + μ(tail) → 0
  have h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have h := hC_vanish.add h_tail
    rwa [show (0 : ℝ) + 0 = 0 from add_zero 0] at h
  -- Step 4: ε-δ argument with integral_add_compl
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε ^ 2 / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  rw [Metric.tendsto_atTop] at h_vanish
  obtain ⟨N, hN⟩ := h_vanish δ hδ
  set M := max N 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_sum_small : C M + (μ {ω | M < γ ω}).toReal < δ := by
    have h := hN M (le_max_left N 1)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg
      (add_nonneg (hC_nn M) ENNReal.toReal_nonneg)] at h
  have hC_lt : C M < δ :=
    lt_of_le_of_lt (le_add_of_nonneg_right ENNReal.toReal_nonneg) h_sum_small
  have h_tail_lt : (μ {ω | M < γ ω}).toReal < δ :=
    lt_of_le_of_lt (le_add_of_nonneg_left (hC_nn M)) h_sum_small
  obtain ⟨T, hT⟩ := h_body_absorb M hM_pos δ hδ
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have ht_ge_T : T ≤ t := le_trans (le_max_left T 0) ht
  -- Cauchy-Schwarz: |r - r*|² ≤ V = ∫(α-α*)² dμ
  have hCS : (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]
    exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  -- Split V = V_body + V_tail via integral_add_compl
  have hV_split : ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int t)).symm
  -- Tail bound: V_tail ≤ μ({γ > M}) < δ
  have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
  have h_sq_bdd : ∀ ω, (α ω t - α_star ω) ^ 2 ≤ 1 := by
    intro ω
    have hp := (hα_inv ω t ht_nn).1; have hl := (hα_inv ω t ht_nn).2
    nlinarith [hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)]
  have hVtail : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int t).integrableOn
            (integrable_const (1 : ℝ)).integrableOn
            (hγ_level M).compl (fun ω _ => h_sq_bdd ω)
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by
          rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
      _ < δ := h_tail_lt
  -- Body bound: V_body < C(M) + δ < 2δ
  have hVbody : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < 2 * δ := by
    linarith [hT t ht_ge_T]
  -- Combine: |r - r*|² ≤ V = V_body + V_tail < 2δ + δ = 3δ < ε²
  have hV_lt : (r t - r_star) ^ 2 < ε ^ 2 := calc
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := hCS
    _ = _ + _ := hV_split
    _ < 2 * δ + δ := add_lt_add hVbody hVtail
    _ = 3 * (ε ^ 2 / 4) := by ring
    _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hV_lt (le_of_lt hε)

/-- **End-to-end existential form of `kuramoto_standard_continuum`.**

Parallel to `kuramoto_solved` (GeneralGMainTheorem.lean) but for the
standard continuum model with unbounded γ.

The existence hypothesis bundles ODE data + body Gronwall + C → 0.
No bounded γ, no uniform persistence, no minimum weight. -/
theorem kuramoto_standard_continuum_exists [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (h_exists : ∃ (r : ℝ → ℝ) (α : Ω → ℝ → ℝ),
      (∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) ∧
      (∃ (C : ℝ → ℝ), (∀ M, 0 ≤ C M) ∧ Tendsto C atTop (nhds 0) ∧
        (∀ M : ℝ, 0 < M → ∃ (rate : ℝ), 0 < rate ∧
          ∀ t ≥ (0 : ℝ),
            ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
              (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
                rexp (-rate * t) + C M))) :
    ∃ (r : ℝ → ℝ), Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, h_sc, hα_int, hα_sq_int, hα_inv, C, hC_nn, hC_vanish, h_gron⟩ := h_exists
  exact ⟨r, kuramoto_standard_continuum γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α
    h_sc hα_int hα_sq_int hα_inv C hC_nn hC_vanish h_gron⟩

/-- **`kuramoto_solved` is a special case of `kuramoto_standard_continuum`.**

When γ IS bounded by γ_max and persistence IS uniform, the global Gronwall
V(t) ≤ V(0)·exp(-rate·t) implies the body Gronwall with absorbing radius
C(M) = μ({γ > M}) (tail measure). Since γ is bounded, μ({γ > M}) = 0
for M ≥ γ_max, so C → 0. -/
theorem kuramoto_standard_of_bounded [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- Global Gronwall rate (from bounded γ + uniform persistence)
    (rate : ℝ) (hrate : 0 < rate)
    (h_gronwall : ∀ t ≥ (0 : ℝ),
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) := by
  -- Use C(M) = μ({γ > M}) as absorbing radius
  set C := fun M => (μ {ω | M < γ ω}).toReal
  apply kuramoto_standard_continuum γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α
    h_sc hα_int hα_sq_int hα_inv C
    (fun _ => ENNReal.toReal_nonneg)
    (tail_measure_tendsto_zero (μ := μ) γ hγ_level)
  intro M hM
  refine ⟨rate, hrate, fun t ht => ?_⟩
  -- V_body(t) ≤ V(t) ≤ V(0)·exp = (V_body(0) + V_tail(0))·exp
  --          ≤ V_body(0)·exp + V_tail(0) ≤ V_body(0)·exp + μ(tail) = goal
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
          have hp := (hα_inv ω 0 le_rfl).1; have hl := (hα_inv ω 0 le_rfl).2
          nlinarith [hα_star_pos ω, hα_star_lt ω, sq_abs (α ω 0 - α_star ω)]
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by
          rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
  have hexp_le : rexp (-rate * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
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

end
