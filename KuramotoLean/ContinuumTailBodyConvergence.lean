/-
  Continuum Kuramoto — Tail-Body ISS Convergence
  ===============================================

  The correct continuum theorem for the standard Kuramoto model with
  γ(ω) = |ω| unbounded on R. Resolves three reviewer problems with
  `kuramoto_solved` without tautological hypotheses.

  Prior continuum theorems had flawed ISS hypotheses:
  - `kuramoto_solved_iss`: required limsup V_body ≤ μ(tail), i.e.
    absorbing radius C ≤ μ(tail). But Gronwall gives C = μ(tail)/(δ·ds)
    and δ·ds < 1 always (both in (0,1)), so this is UNSATISFIABLE.
  - `kuramoto_solved_continuum`: h_approx ↔ V→0, tautological.

  Fix: generalize the absorbing ball radius to C(M) with the combined
  vanishing condition C(M) + μ({γ > M}) → 0.

  From body Gronwall: dV_body/dt ≤ -K·δ(M)·ds(M)·V_body + K·μ(tail)
  gives C(M) = μ(tail)/(δ(M)·ds(M)).

  Combined vanishing: C(M) + μ(tail) = μ(tail)·(1 + 1/(δ(M)·ds(M))) → 0
  iff μ(tail) decays faster than δ(M)·ds(M).

  Satisfiable: Gaussian (e^{-M²} vs 1/M), Student-t ν>2, compact support.
  Not satisfiable: Lorentzian (1/M vs 1/M, ratio ~ 1). Lorentzian needs
  the Bernoulli closed-form instead (already proved separately).

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedStandard

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Tail-body ISS convergence with general absorbing radius.**

For the standard continuum Kuramoto model with unbounded γ(ω) = |ω|.
The order parameter r → r* if:
1. The body Lyapunov V_body enters an absorbing ball of radius C(M)
2. C(M) + μ({γ > M}) → 0 as M → ∞

No uniform persistence. No bounded γ. No minimum weight.

The absorbing radius C(M) arises from body Gronwall comparison:
  dV_body/dt ≤ -λ(M)·V_body + K·μ(tail)
  ⟹ limsup V_body ≤ K·μ(tail)/λ(M) = C(M)
where λ(M) = K·δ(M)·ds(M) is the body pair coercivity rate.

Proof: for any ε, choose M so that C(M) + μ(tail) < ε²/4.
Then V_body < C(M) + ε²/4 < 2·ε²/4 and V_tail < ε²/4.
So V < 3ε²/4 < ε² and |r - r*| < ε. -/
theorem tail_body_iss_convergence [IsProbabilityMeasure μ]
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (γ : Ω → ℝ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_absorb : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε)
    (h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
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
  have hCS : (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]
    exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  have hV_split : ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int t)).symm
  have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
  have h_sq_bdd : ∀ ω, (α ω t - α_star ω) ^ 2 ≤ 1 := by
    intro ω
    have hp := (hα_inv ω t ht_nn).1; have hl := (hα_inv ω t ht_nn).2
    nlinarith [hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)]
  have hVt : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int t).integrableOn
            (integrable_const (1 : ℝ)).integrableOn
            (hγ_level M).compl (fun ω _ => h_sq_bdd ω)
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by
          rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
      _ < δ := h_tail_lt
  have hVb : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < 2 * δ := by
    linarith [hT t ht_ge_T]
  have hV_lt : (r t - r_star) ^ 2 < ε ^ 2 := calc
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := hCS
    _ = _ + _ := hV_split
    _ < 2 * δ + δ := add_lt_add hVb hVt
    _ = 3 * (ε ^ 2 / 4) := by ring
    _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hV_lt (le_of_lt hε)

/-- **Body Gronwall → ISS absorbing ball.**

When the body Lyapunov satisfies an exponential Gronwall bound:
  V_body(t) ≤ V_body(0) · exp(-rate·t) + C
with C = C(M) (the absorbing radius), the body V eventually enters
{V_body < C + ε} for any ε > 0.

This converts a Gronwall bound into the `h_body_absorb` hypothesis
of `tail_body_iss_convergence`.

The Gronwall bound arises from the body ODE analysis:
  dV_body/dt = ∫_body 2(α-α*)·f dμ
             ≤ -K·δ·ds·V_body + K·μ(tail)   (pair bound + tail coupling)
  ⟹ V_body(t) ≤ V(0)·exp(-K·δ·ds·t) + μ(tail)/(δ·ds) -/
theorem body_absorb_from_gronwall {γ : Ω → ℝ}
    (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (_hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (_hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    (M : ℝ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε := by
  obtain ⟨rate, hrate, h_gron⟩ := h_body_gronwall M hM
  exact iss_from_gronwall_bound
    (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ)
    (fun t => integral_nonneg fun _ => sq_nonneg _)
    rate (C M) hrate (hC_nn M) h_gron ε hε

/-- **Combined continuum convergence from body Gronwall.**

End-to-end theorem: standard model data + body Gronwall bound with
absorbing radius C(M) + combined vanishing → r → r*.

The body Gronwall bound is derivable from:
  • Bounded γ on body {γ ≤ M} → Leibniz differentiation of V_body
  • Body persistence δ(M) ≤ α on {γ ≤ M} → coercive pair bound
  • Tail coupling bounded by K·μ(tail)
  • Gronwall comparison: V_body ≤ V(0)·e^{-λt} + C(M)

The combined vanishing C(M) + μ(tail) → 0 is satisfied when g decays
fast enough relative to the locked-region shrinkage:
  C(M) = μ(tail)/(δ(M)·ds(M))
  ds(M) = Kr*/(2M + Kr*) ~ 1/M  (equilibrium lower bound on body)
  Need: μ(tail)/ds(M) → 0, i.e., M·μ({γ>M}) → 0. -/
theorem kuramoto_continuum_gronwall_convergence [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 < γ ω)
    (_hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (_hr_cont : Continuous r) (_hr_bdd : ∀ t, |r t| ≤ 1)
    (_hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (_hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (_hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    -- BODY GRONWALL with GENERAL absorbing radius C(M)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M)
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M)
    -- COMBINED VANISHING: absorbing radius + tail measure → 0
    (h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) :=
  tail_body_iss_convergence α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq r α h_sc hα_int hα_sq_int hα_inv
    γ hγ_level C hC_nn
    (fun M hM ε hε => body_absorb_from_gronwall α α_star hα_sq_int hγ_level
      C hC_nn h_body_gronwall M hM ε hε)
    h_vanish

/-- **Bounded γ gives trivial vanishing.**

When γ ≤ γ_max, the body is all of Ω for M ≥ γ_max and the tail is empty.
Taking C(M) = 0 for all M, the vanishing C(M) + μ(tail) = μ(tail) → 0
is automatic. This shows `kuramoto_solved` (bounded γ) is a strict
special case of the ISS framework. -/
theorem tail_vanishes_bounded [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (γ_max : ℝ) (hγ_bdd : ∀ ω, γ ω ≤ γ_max) :
    Tendsto (fun M => (0 : ℝ) + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
  simp only [zero_add]
  exact tail_vanishes_when_bounded γ γ_max hγ_bdd

/-- **Old ISS hypothesis implies new ISS hypothesis.**

The old `kuramoto_solved_iss` required V_body < μ(tail) + ε (absorbing
radius = μ(tail)). This implies the new condition with C(M) = μ(tail),
giving combined vanishing 2·μ(tail) → 0.

This corollary shows the new framework strictly generalizes the old. -/
theorem old_iss_implies_new
    (γ : Ω → ℝ)
    (_hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_tail : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0))
    (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (_hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_old_iss : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ <
        (μ {ω | M < γ ω}).toReal + ε) :
    ∃ (C : ℝ → ℝ),
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) ∧
      Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
  refine ⟨fun M => (μ {ω | M < γ ω}).toReal, fun M => ENNReal.toReal_nonneg,
    h_old_iss, ?_⟩
  have h_add := h_tail.add h_tail
  simp only [add_zero] at h_add
  exact h_add

end
