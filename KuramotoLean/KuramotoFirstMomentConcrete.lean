/-
  KuramotoFirstMomentConcrete.lean
  =================================
  Concrete convergence theorem WITHOUT γ_min > 0.

  Strengthens KuramotoGammaMinFirstMomentConcrete (exp 295): removes the
  γ_min > 0 restriction, allowing γ(ω) = 0 for some ω (e.g., γ(ω) = |ω|
  at ω = 0 in the standard continuum Kuramoto model on ℝ).

  Uses tail_body_iss_convergence directly — no V antitone needed.
  Body Gronwall (body_gronwall_from_persistence) requires only hγ_nn.

  Covers: all g with ∫γ dμ < ∞ (Gaussian, Student-t ν>1, compact support,
  power-law with exponent > 2) regardless of whether γ has a positive
  lower bound.

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumTailBodyConvergence
import KuramotoLean.BodyGronwallBound
import KuramotoLean.FirstMomentTailVanish

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Equilibrium lower bound: α*(ω) ≥ K·r/(2·M+K·r) when γ(ω) ≤ M.
    Same proof as equil_lb_from_constraint in KuramotoGammaMinFirstMomentConcrete. -/
private lemma equil_lb_no_gmin
    (γ_v α_v K r M : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hM : 0 < M)
    (hα_pos : 0 < α_v) (hα_lt : α_v < 1) (hγ_le : γ_v ≤ M)
    (hequil : γ_v * α_v = (K / 2) * r * (1 - α_v ^ 2)) :
    K * r / (2 * M + K * r) ≤ α_v := by
  have h_denom : 0 < 2 * M + K * r := by positivity
  rw [div_le_iff₀ h_denom]
  have h_expand : 2 * γ_v * α_v = K * r * (1 - α_v ^ 2) := by linarith
  have h_step : K * r ≤ α_v * (2 * γ_v + K * r) := by
    nlinarith [sq_nonneg α_v, mul_pos hα_pos (by linarith : (0 : ℝ) < 1 - α_v),
      mul_pos hK hr]
  calc K * r ≤ α_v * (2 * γ_v + K * r) := h_step
    _ ≤ α_v * (2 * M + K * r) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hα_pos)

/-- **Concrete convergence without γ_min > 0.**

    End-to-end theorem from ODE hypotheses + finite first moment ∫γdμ<∞
    + global persistence α₀_lb > 0 → r(t) → r*.

    Compared to kuramoto_gamma_min_first_moment_concrete (exp 295):
    - REMOVES γ_min > 0 condition (allows γ(ω) = 0)
    - Uses tail_body_iss_convergence directly (no V antitone needed)
    - Covers γ(ω) = |ω| on ℝ with finite-first-moment g

    Body absorbing radius: C(M) = K·τ(M) / (K·α₀_lb·(K·r*/(2M+K·r*))·μ_body)
    Combined vanishing: C(M) + τ(M) → 0 from M·τ(M) → 0 (first moment). -/
theorem kuramoto_first_moment_concrete [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, 0 < t → |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hV_body_cont : ∀ M, 0 < M → ContinuousOn
        (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0))
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  have hds_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → K * r_star / (2 * M + K * r_star) ≤ α_star ω :=
    fun M hM ω hω => equil_lb_no_gmin (γ ω) (α_star ω) K r_star M hK hr_star_pos hM
      (hα_star_pos ω) (hα_star_lt ω) hω (hα_star_equil ω)
  let C : ℝ → ℝ := fun M =>
    K * (μ {ω | M < γ ω}).toReal /
      (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal)
  have hC_nn : ∀ M, 0 ≤ C M := by
    intro M
    show 0 ≤ K * (μ {ω | M < γ ω}).toReal /
        (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal)
    by_cases hM_nn : (0 : ℝ) ≤ M
    · apply div_nonneg (mul_nonneg hK.le ENNReal.toReal_nonneg)
      apply mul_nonneg
      · apply mul_nonneg (mul_nonneg hK.le hα₀_lb_pos.le)
        exact div_nonneg (mul_nonneg hK.le hr_star_pos.le) (by positivity)
      · exact ENNReal.toReal_nonneg
    · push_neg at hM_nn
      have h_empty : (μ {ω : Ω | γ ω ≤ M}).toReal = 0 := by
        have hset : {ω : Ω | γ ω ≤ M} = ∅ := by
          ext ω; simp only [mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_lt_of_le hM_nn (hγ_nn ω)
        simp [hset]
      simp [h_empty]
  have h_body_absorb : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε := by
    intro M hM ε hε
    obtain ⟨hrate_pos, hbound⟩ := body_gronwall_from_persistence γ K hK hγ_nn hγ_meas
      α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
      r α hr_bdd hα_ode hα_int hα_sq_int hα_inv h_sc M hM (hγ_level M)
      α₀_lb hα₀_lb_pos
      (K * r_star / (2 * M + K * r_star)) (by positivity)
      (fun ω _ t ht => hα_lb ω t ht)
      (fun ω hω => hds_lb M hM ω hω)
      (hμ_body_pos M hM) (hV_body_cont M hM)
    -- rate = K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * μ_body (definitional)
    -- K * τ(M) / rate = C M (definitional)
    set V₀ := ∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ
    have hV₀_nn : 0 ≤ V₀ := integral_nonneg (fun _ => sq_nonneg _)
    have h_decay : Tendsto (fun t : ℝ => V₀ * rexp
        (-(K * α₀_lb * (K * r_star / (2 * M + K * r_star)) *
          (μ {ω | γ ω ≤ M}).toReal) * t)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ =>
          K * α₀_lb * (K * r_star / (2 * M + K * r_star)) *
          (μ {ω | γ ω ≤ M}).toReal * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hrate_pos).mpr tendsto_id
      have h2 := (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).const_mul V₀
      simp only [Function.comp_def, mul_zero] at h2
      exact h2.congr (fun _ => by congr 1; congr 1; ring)
    rw [Metric.tendsto_atTop] at h_decay
    obtain ⟨T, hT⟩ := h_decay ε hε
    refine ⟨max T 0, fun t ht => ?_⟩
    have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
    have h_exp_small : V₀ * rexp (-(K * α₀_lb * (K * r_star / (2 * M + K * r_star)) *
        (μ {ω | γ ω ≤ M}).toReal) * t) < ε := by
      have h := hT t (le_trans (le_max_left T 0) ht)
      rw [Real.dist_eq, sub_zero] at h
      rcases le_or_gt V₀ 0 with hV₀ | hV₀
      · have heq : V₀ = 0 := le_antisymm hV₀ hV₀_nn
        simp [heq]; exact hε
      · rw [abs_of_nonneg (mul_nonneg hV₀.le (exp_nonneg _))] at h; linarith
    linarith [hbound t ht_nn]
  have h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    set τ := fun M : ℝ => (μ {ω | M < γ ω}).toReal
    have hτ_nn : ∀ M, 0 ≤ τ M := fun _ => ENNReal.toReal_nonneg
    have hτ_van : Tendsto τ atTop (nhds 0) :=
      tail_measure_tendsto_zero' γ hγ_level
    have hMτ_van : Tendsto (fun M : ℝ => M * τ M) atTop (nhds 0) :=
      first_moment_tail_vanish γ hγ_nn hγ_int hγ_level
    set μ₁ := (μ {ω | γ ω ≤ 1}).toReal
    have hμ₁_pos : 0 < μ₁ := hμ_body_pos 1 one_pos
    have hμ₁_ne : μ₁ ≠ 0 := ne_of_gt hμ₁_pos
    have hK_ne : K ≠ 0 := ne_of_gt hK
    have hr_ne : r_star ≠ 0 := ne_of_gt hr_star_pos
    have hα_ne : α₀_lb ≠ 0 := ne_of_gt hα₀_lb_pos
    set A := 2 / (α₀_lb * K * r_star * μ₁)
    set B := 1 / (α₀_lb * μ₁) + 1
    have h_upper : Tendsto (fun M => A * (M * τ M) + B * τ M) atTop (nhds 0) := by
      have h1 : Tendsto (fun M => A * (M * τ M)) atTop (nhds 0) := by
        have := hMτ_van.const_mul A; simp [mul_zero] at this; exact this
      have h2 : Tendsto (fun M => B * τ M) atTop (nhds 0) := by
        have := hτ_van.const_mul B; simp [mul_zero] at this; exact this
      have := h1.add h2; simp at this; exact this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
      exact add_nonneg (hC_nn M) (hτ_nn M)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
      show C M + τ M ≤ A * (M * τ M) + B * τ M
      have hd : 0 < 2 * M + K * r_star := by positivity
      have hμ_body_ge : μ₁ ≤ (μ {ω | γ ω ≤ M}).toReal := by
        apply ENNReal.toReal_mono (measure_ne_top μ _)
        exact measure_mono (fun ω hω => le_trans hω hM)
      have hμ_body_pos_M : 0 < (μ {ω | γ ω ≤ M}).toReal := lt_of_lt_of_le hμ₁_pos hμ_body_ge
      have h_C_le : C M ≤ K * τ M /
          (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * μ₁) := by
        apply div_le_div_of_nonneg_left (mul_nonneg hK.le (hτ_nn M)) (by positivity)
        exact mul_le_mul_of_nonneg_left hμ_body_ge (by positivity)
      have h_simpl : K * τ M /
          (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * μ₁) =
          τ M * (2 * M + K * r_star) / (α₀_lb * K * r_star * μ₁) := by
        field_simp [hK_ne, hr_ne, hα_ne, hμ₁_ne, ne_of_gt hd]
      have h_arith : τ M * (2 * M + K * r_star) / (α₀_lb * K * r_star * μ₁) + τ M ≤
          A * (M * τ M) + B * τ M := by
        have h_ne : α₀_lb * K * r_star * μ₁ ≠ 0 := by positivity
        have h_eq : τ M * (2 * M + K * r_star) / (α₀_lb * K * r_star * μ₁) + τ M =
            A * (M * τ M) + B * τ M := by
          show τ M * (2 * M + K * r_star) / (α₀_lb * K * r_star * μ₁) + τ M =
            2 / (α₀_lb * K * r_star * μ₁) * (M * τ M) + (1 / (α₀_lb * μ₁) + 1) * τ M
          field_simp [h_ne]; ring
        linarith
      have h_C_simpl : C M ≤ τ M * (2 * M + K * r_star) / (α₀_lb * K * r_star * μ₁) :=
        h_simpl ▸ h_C_le
      linarith [h_C_simpl, h_arith]
  exact tail_body_iss_convergence α_star r_star hα_star_pos hα_star_lt hαs_int
    hr_star_eq r α h_sc hα_int hα_sq_int hα_inv γ hγ_level C hC_nn h_body_absorb h_vanish

end
