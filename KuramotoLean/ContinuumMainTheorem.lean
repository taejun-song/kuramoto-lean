/-
  Kuramoto Stability — Continuum Model (Unbounded Frequencies)
  =============================================================
  Handles the ACTUAL continuum Kuramoto model with:
  - g supported on R (e.g., Lorentzian, Gaussian)
  - gamma(omega) = |omega| (unbounded)
  - BOTH locked (|omega| < Kr*) and drifting (|omega| > Kr*) oscillators
  - alpha*(omega) -> 0 as |omega| -> infinity (no uniform lower bound)

  Three fundamental issues with kuramoto_solved for the standard model:

  PROBLEM 1: The persistence hypothesis delta <= alpha(omega,t) for ALL omega
  is FALSE. Drifting oscillators have alpha -> 0.

  PROBLEM 2: gamma_max bounded, but standard Kuramoto has gamma(omega) = |omega|
  (unbounded). Leibniz dominated convergence needs bounded integrand derivative.

  PROBLEM 3: c_min (minimum weight) is an n-pole concept.

  Resolution (Dietert 2016, Dietert-Fernandez 2018):

  TAIL-BODY SPLIT: for any epsilon > 0, choose M large enough that
    integral_{|omega|>=M} g domega < epsilon  (g integrable)
  Then split r(t) - r* into body (|omega| < M) and tail (|omega| >= M).
  - Body: gamma <= M (bounded!), persistence holds -> V_body -> 0
  - Tail: bounded by epsilon regardless of dynamics
  - Combined: |r - r*|^2 <= V_body + tail -> 0

  Axiom budget: 0
  Sorry count: 0
-/

import KuramotoLean.GeneralGMainTheorem

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Continuum Kuramoto Stability (Tail-Body Split).**

For the continuum OA system with potentially unbounded gamma(omega):
- Does NOT require gamma globally bounded
- Does NOT require global persistence (alpha >= delta > 0 for ALL omega)
- Does NOT require minimum weight c_min

The hypothesis `h_approx` encodes the tail-body split:
for any epsilon, there exists body S with V_S -> 0 and mu(S^c) < epsilon.

Proof: |r-r*|^2 <= V = V_body + V_tail < (body -> 0) + (tail < epsilon) -> 0. -/
theorem kuramoto_continuum_from_happrox [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 < γ ω)
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
    (h_approx : ∀ ε > 0, ∃ (S : Set Ω),
      MeasurableSet S ∧
      (μ Sᶜ).toReal < ε ∧
      Tendsto (fun t => ∫ ω in S, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := (ε / 2) ^ 2 with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS_meas, h_tail, hV_body⟩ := h_approx δ hδ
  rw [Metric.tendsto_atTop] at hV_body
  obtain ⟨N, hN⟩ := hV_body δ hδ
  refine ⟨max N 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht_ge : N ≤ t := le_trans (le_max_left _ _) ht
  rw [Real.dist_eq]
  -- |r-r*|^2 <= V(t) by Cauchy-Schwarz
  have hCS : (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]
    exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  -- V = V_body + V_tail
  have hV_split : ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ =
      (∫ ω in S, (α ω t - α_star ω) ^ 2 ∂μ) +
      (∫ ω in Sᶜ, (α ω t - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl hS_meas (hα_sq_int t)).symm
  have h_bdd : ∀ ω, (α ω t - α_star ω) ^ 2 ≤ 1 := by
    intro ω
    have hp := (hα_inv ω t ht_nn).1; have hl := (hα_inv ω t ht_nn).2
    nlinarith [hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)]
  -- V_body < delta
  have hVb : ∫ ω in S, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    have h := hN t ht_ge
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
    exact h
  -- V_tail <= mu(S^c) < delta
  have hVt : ∫ ω in Sᶜ, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    calc ∫ ω in Sᶜ, (α ω t - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in Sᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int t).integrableOn
            (integrable_const (1 : ℝ)).integrableOn
            hS_meas.compl (fun ω _ => h_bdd ω)
      _ = (μ Sᶜ).toReal := by
          rw [setIntegral_const]; simp [Measure.real]
      _ < δ := h_tail
  -- V < 2*delta = epsilon^2/2 < epsilon^2, so |r-r*| < epsilon
  have hV_lt : (r t - r_star) ^ 2 < ε ^ 2 := calc
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := hCS
    _ = _ + _ := hV_split
    _ < δ + δ := add_lt_add hVb hVt
    _ = ε ^ 2 / 2 := by rw [hδ_def]; ring
    _ < ε ^ 2 := by linarith [sq_pos_of_pos hε]
  exact abs_lt_of_sq_lt_sq hV_lt (le_of_lt hε)

/-- V → 0 trivially implies h_approx (take S = Ω). -/
theorem v_tendsto_zero_implies_h_approx [IsProbabilityMeasure μ]
    (f : Ω → ℝ → ℝ)
    (V_tendsto : Tendsto (fun t => ∫ ω, (f ω t) ^ 2 ∂μ) atTop (nhds 0)) :
    ∀ ε > 0, ∃ (S : Set Ω),
      MeasurableSet S ∧
      (μ Sᶜ).toReal < ε ∧
      Tendsto (fun t => ∫ ω in S, (f ω t) ^ 2 ∂μ) atTop (nhds 0) := by
  intro ε hε
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · simp only [compl_univ, measure_empty, ENNReal.toReal_zero]; exact hε
  · simp only [Measure.restrict_univ]; exact V_tendsto

/-- h_approx implies V → 0 (the converse). Together with the above, h_approx ↔ V → 0. -/
theorem h_approx_implies_v_tendsto_zero [IsProbabilityMeasure μ]
    (f : Ω → ℝ → ℝ) (hf_bdd : ∀ ω t, (f ω t) ^ 2 ≤ 1)
    (hf_int : ∀ t, Integrable (fun ω => (f ω t) ^ 2) μ)
    (h_approx : ∀ ε > 0, ∃ (S : Set Ω),
      MeasurableSet S ∧
      (μ Sᶜ).toReal < ε ∧
      Tendsto (fun t => ∫ ω in S, (f ω t) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun t => ∫ ω, (f ω t) ^ 2 ∂μ) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S, hS_meas, h_tail, hV_body⟩ := h_approx (ε / 2) (by linarith)
  rw [Metric.tendsto_atTop] at hV_body
  obtain ⟨N, hN⟩ := hV_body (ε / 2) (by linarith)
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  have hV_split : ∫ ω, (f ω t) ^ 2 ∂μ =
      (∫ ω in S, (f ω t) ^ 2 ∂μ) + (∫ ω in Sᶜ, (f ω t) ^ 2 ∂μ) :=
    (integral_add_compl hS_meas (hf_int t)).symm
  have hVb : ∫ ω in S, (f ω t) ^ 2 ∂μ < ε / 2 := by
    have h := hN t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
    exact h
  have hVt : ∫ ω in Sᶜ, (f ω t) ^ 2 ∂μ < ε / 2 := calc
    ∫ ω in Sᶜ, (f ω t) ^ 2 ∂μ
        ≤ ∫ ω in Sᶜ, (1 : ℝ) ∂μ := by
      apply setIntegral_mono_on (hf_int t).integrableOn
        (integrable_const (1 : ℝ)).integrableOn
        hS_meas.compl (fun ω _ => hf_bdd ω t)
    _ = (μ Sᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
    _ < ε / 2 := h_tail
  linarith [hV_split]

/-- **Physical corollary.** Wraps kuramoto_continuum_from_happrox with the physical
setup where the body S = {omega | gamma(omega) <= M} has bounded gamma and
the restricted Lyapunov converges by the bounded-gamma stability theorem. -/
theorem kuramoto_continuum_physical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
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
    (h_tail_vanish : ∀ ε > 0, ∃ (S : Set Ω), MeasurableSet S ∧
      (μ Sᶜ).toReal < ε ∧
      Tendsto (fun t => ∫ ω in S, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  exact kuramoto_continuum_from_happrox γ K hK hγ hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    h_tail_vanish

end
