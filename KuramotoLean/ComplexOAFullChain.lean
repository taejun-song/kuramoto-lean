/-
  Complex OA Full Chain
  =====================
  Packages the proved body/tail convergence ingredients into the final
  `V → 0` statement for the complex OA.

  The earlier "unconditional" wrapper claimed to derive the body-antitone
  and body-decay inputs directly from the ODE data, but those two complex
  steps are still open elsewhere in the development. This file states the
  valid bridge theorem with those inputs explicit and proves the tail
  estimate from integrability of `g`.
-/

import KuramotoLean.ComplexOAVZero

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- V→0 from explicit body/tail hypotheses, with the tail estimate derived here. -/
theorem complex_oa_V_zero_unconditional [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (K : ℝ) (r_star : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hω_level : ∀ M : ℝ, MeasurableSet {ω | |S.ω_freq ω| ≤ M})
    (h_body_anti : ∀ M : ℝ, 0 < M → Antitone (fun t =>
      ∫ ω in {ω | |S.ω_freq ω| ≤ M}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (h_body_zero : ∀ M : ℝ, 0 < M → Tendsto (fun t =>
      ∫ ω in {ω | |S.ω_freq ω| ≤ M}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0) := by
  apply complex_oa_V_tendsto_zero S z z_star K r_star hK hr_star_pos
    hz_disk hz_star_pos hz_star_lt hg_nn hg_int hg_norm hz_ode
    hr_star_eq hz_star_equil hV_int hω_level h_body_anti h_body_zero
  -- h_tail: tail integral < ε (|z-z*|² ≤ 4 + tail g → 0)
  · intro ε hε
    let tailSet : ℝ → Set Ω := fun M => {ω | M < |S.ω_freq ω|}
    have h_tail_g_nat :
        Tendsto (fun n : ℕ => ∫ ω in tailSet n, S.g ω ∂μ) atTop (nhds 0) := by
      have h_tail_meas : ∀ n : ℕ, MeasurableSet (tailSet n) := by
        intro n
        rw [show tailSet n = {ω | |S.ω_freq ω| ≤ (n : ℝ)}ᶜ by
          ext ω; simp [tailSet, not_le]]
        exact (hω_level n).compl
      have h_tail_anti : Antitone fun n : ℕ => tailSet n := by
        intro m n hmn ω hω
        change (m : ℝ) < |S.ω_freq ω|
        exact lt_of_le_of_lt (Nat.cast_le.mpr hmn) hω
      have h_tail_inter : ⋂ n : ℕ, tailSet n = ∅ := by
        ext ω
        constructor
        · intro hω
          have hω' : ((⌈|S.ω_freq ω|⌉₊ : ℝ) < |S.ω_freq ω|) := by
            exact (mem_iInter.mp hω) ⌈|S.ω_freq ω|⌉₊
          exact (not_lt_of_ge (Nat.le_ceil _)) hω'
        · intro hω
          cases hω
      simpa [h_tail_inter] using
        Antitone.tendsto_setIntegral h_tail_meas h_tail_anti hg_int.integrableOn
    have h_tail_g :
        Tendsto (fun M : ℝ => ∫ ω in tailSet M, S.g ω ∂μ) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      rw [Metric.tendsto_atTop] at h_tail_g_nat
      obtain ⟨N, hN⟩ := h_tail_g_nat δ hδ
      refine ⟨N, fun M hM => ?_⟩
      have h_tail_mono :
          ∫ ω in tailSet M, S.g ω ∂μ ≤ ∫ ω in tailSet N, S.g ω ∂μ := by
        apply setIntegral_mono_set
        · exact hg_int.integrableOn
        · exact Filter.Eventually.of_forall hg_nn
        · exact Filter.Eventually.of_forall fun ω hω =>
            lt_of_le_of_lt hM hω
      have hN' := hN N le_rfl
      have h_tail_nonneg_M : 0 ≤ ∫ ω in tailSet M, S.g ω ∂μ :=
        integral_nonneg hg_nn
      have h_tail_nonneg_N : 0 ≤ ∫ ω in tailSet N, S.g ω ∂μ :=
        integral_nonneg hg_nn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h_tail_nonneg_N] at hN'
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h_tail_nonneg_M]
      exact lt_of_le_of_lt h_tail_mono hN'
    have h_tail4 :
        Tendsto (fun M : ℝ => 4 * ∫ ω in tailSet M, S.g ω ∂μ) atTop (nhds 0) := by
      simpa using h_tail_g.const_mul (4 : ℝ)
    rw [Metric.tendsto_atTop] at h_tail4
    obtain ⟨M, hM⟩ := h_tail4 ε hε
    refine ⟨M, fun t ht => ?_⟩
    have h_tail_dom :
        ∫ ω in tailSet M, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ ≤
          ∫ ω in tailSet M, 4 * S.g ω ∂μ := by
      apply setIntegral_mono_ae
      · exact (hV_int t).integrableOn
      · exact (hg_int.const_mul 4).integrableOn
      · exact Filter.Eventually.of_forall fun ω => by
          apply mul_le_mul_of_nonneg_right ?_ (hg_nn ω)
          have hz_norm_sq_lt : ‖z ω t‖ ^ 2 < 1 := by
            simpa [Complex.normSq_eq_norm_sq] using hz_disk ω t ht
          have hz_norm_le : ‖z ω t‖ ≤ 1 := by
            nlinarith [sq_nonneg ‖z ω t‖, hz_norm_sq_lt]
          have hz_star_norm_sq_lt : ‖z_star ω‖ ^ 2 < 1 := by
            simpa [Complex.normSq_eq_norm_sq] using hz_star_lt ω
          have hz_star_norm_le : ‖z_star ω‖ ≤ 1 := by
            nlinarith [sq_nonneg ‖z_star ω‖, hz_star_norm_sq_lt]
          have hnorm_le : ‖z ω t - z_star ω‖ ≤ 2 := by
            calc
              ‖z ω t - z_star ω‖ ≤ ‖z ω t‖ + ‖z_star ω‖ := norm_sub_le _ _
              _ ≤ 1 + 1 := add_le_add hz_norm_le hz_star_norm_le
              _ = 2 := by norm_num
          have hnorm_sq_le : ‖z ω t - z_star ω‖ ^ 2 ≤ 4 := by
            nlinarith [norm_nonneg (z ω t - z_star ω), hnorm_le]
          simpa [Complex.normSq_eq_norm_sq] using hnorm_sq_le
    have h_tail_nonneg :
        0 ≤ ∫ ω in tailSet M, 4 * S.g ω ∂μ :=
      integral_nonneg fun ω => mul_nonneg (by norm_num) (hg_nn ω)
    have h_small : 4 * ∫ ω in tailSet M, S.g ω ∂μ < ε := by
      have h_small0 := hM M le_rfl
      have h_tail_nonneg' : 0 ≤ 4 * ∫ ω in tailSet M, S.g ω ∂μ := by
        rw [← integral_const_mul]
        exact h_tail_nonneg
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h_tail_nonneg'] at h_small0
      exact h_small0
    have h_tail_dom' :
        ∫ ω in {ω | M < |S.ω_freq ω|}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ ≤
          ∫ ω in {ω | M < |S.ω_freq ω|}, 4 * S.g ω ∂μ := by
      simpa [tailSet] using h_tail_dom
    have h_small' : 4 * ∫ ω in {ω | M < |S.ω_freq ω|}, S.g ω ∂μ < ε := by
      simpa [tailSet] using h_small
    calc
      ∫ ω in {ω | M < |S.ω_freq ω|}, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
          ≤ ∫ ω in {ω | M < |S.ω_freq ω|}, 4 * S.g ω ∂μ := h_tail_dom'
      _ = 4 * ∫ ω in {ω | M < |S.ω_freq ω|}, S.g ω ∂μ := by
          rw [integral_const_mul]
      _ < ε := h_small'

end
