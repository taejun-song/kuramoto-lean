/-
  Frozen OA Convergence (Strong Coupling Regime)
  ================================================
  For the frozen complex OA (constant η = r), starting from incoherence z₀ = 0:
  - Locked equilibria satisfy |z*| = 1, so |z₀-z*|² = 1 < 2 (automatic basin)
  - Strongly locked oscillators: per-oscillator exponential decay
  - Body integral: V_body → 0
  - Tail bound: |z-z*|² < 4 in the disk
  - Combined: V → 0 via body-tail split

  0 sorry.
-/

import KuramotoLean.ComplexOABodyDecay
import KuramotoLean.ComplexOALockedEquil

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem frozen_oa_body_convergence
    (ω_freq : Ω → ℝ) (g : Ω → ℝ) (K r rate : ℝ)
    (z : Ω → ℝ → ℂ)
    (hK : 0 < K) (hr : 0 < r) (hrate : 0 < rate)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (h_locked : ∀ ω, (ω_freq ω) ^ 2 < K ^ 2 * r ^ 2)
    (hz_init : ∀ ω, z ω 0 = 0)
    (hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω)
        (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hz_cont : ∀ ω, Continuous
        (fun t => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r)))
    (h_weight : ∀ ω z', Complex.normSq (z' - lockedEquil (ω_freq ω) K r) < 2 →
        rate ≤ K * r * (z' + lockedEquil (ω_freq ω) K r).re)
    (hfg_int : ∀ t, 0 ≤ t → Integrable
        (fun ω => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω) μ) :
    Tendsto (fun t =>
        ∫ ω, Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω ∂μ)
      atTop (nhds 0) := by
  set z_star := fun ω => lockedEquil (ω_freq ω) K r
  apply complex_oa_body_decay z z_star ω_freq g K r rate hK hr hrate hg_nn hg_int
  · exact fun ω => lockedEquil_is_equil (ω_freq ω) K r hK hr (h_locked ω)
  · exact hz_ode
  · exact hz_cont
  · exact h_weight
  · intro ω; rw [hz_init ω]
    exact near_incoherence_in_basin _ (lockedEquil_normSq (ω_freq ω) K r hK hr (h_locked ω))
  · exact hfg_int

theorem error_sq_bound_in_disk (z z_star : ℂ)
    (hz : Complex.normSq z < 1) (hz_star : Complex.normSq z_star ≤ 1) :
    Complex.normSq (z - z_star) < 4 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith [sq_nonneg (z.re + z_star.re), sq_nonneg (z.im + z_star.im)]

theorem frozen_oa_convergence
    (ω_freq : Ω → ℝ) (g : Ω → ℝ) (K r : ℝ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (hK : 0 < K) (hr : 0 < r)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (_hz_star_eq : ∀ ω, complexOaRHS (ω_freq ω) K (↑r) (z_star ω) = 0)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_ns : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (_hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω)
        (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hV_int : ∀ t, Integrable
        (fun ω => Complex.normSq (z ω t - z_star ω) * g ω) μ)
    (hω_meas : ∀ M : ℝ, MeasurableSet {ω | |ω_freq ω| ≤ M})
    (h_body_zero : ∀ M : ℝ, 0 < M → Tendsto (fun t =>
        ∫ ω in {ω | |ω_freq ω| ≤ M},
        Complex.normSq (z ω t - z_star ω) * g ω ∂μ) atTop (nhds 0))
    (h_tail_mass : ∀ ε > 0, ∃ M : ℝ, 0 < M ∧
        ∫ ω in {ω | M < |ω_freq ω|}, g ω ∂μ < ε) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM_pos, hM_tail⟩ := h_tail_mass (ε / 8) (by linarith)
  have h_body := h_body_zero M hM_pos
  rw [Metric.tendsto_atTop] at h_body
  obtain ⟨T, hT⟩ := h_body (ε / 2) (by linarith)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have ht_ge_T : T ≤ t := le_trans (le_max_left T 0) ht
  have hV_split :
      ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ =
        (∫ ω in {ω | |ω_freq ω| ≤ M},
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ) +
        (∫ ω in {ω | |ω_freq ω| ≤ M}ᶜ,
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ) :=
    (integral_add_compl (hω_meas M) (hV_int t)).symm
  have h_compl : {ω | |ω_freq ω| ≤ M}ᶜ = {ω | M < |ω_freq ω|} := by
    ext ω; simp [not_le]
  have h_full_nn : 0 ≤ ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ :=
    integral_nonneg fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω)
  have h_body_nn : 0 ≤ ∫ ω in {ω | |ω_freq ω| ≤ M},
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ :=
    integral_nonneg fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω)
  have h_body_small : ∫ ω in {ω | |ω_freq ω| ≤ M},
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ < ε / 2 := by
    have h := hT t ht_ge_T
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_body_nn] at h; exact h
  have h_tail_small : ∫ ω in {ω | |ω_freq ω| ≤ M}ᶜ,
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ < ε / 2 := by
    rw [h_compl]
    have h_pw : ∀ ω, Complex.normSq (z ω t - z_star ω) * g ω ≤ 4 * g ω := fun ω => by
      by_cases ht' : 0 ≤ t
      · exact mul_le_mul_of_nonneg_right
          (le_of_lt (error_sq_bound_in_disk _ _ (hz_disk ω t ht') (hz_star_ns ω))) (hg_nn ω)
      · push_neg at ht'; linarith [mul_nonneg (Complex.normSq_nonneg (z ω t - z_star ω)) (hg_nn ω)]
    calc ∫ ω in {ω | M < |ω_freq ω|},
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ
        ≤ ∫ ω in {ω | M < |ω_freq ω|}, 4 * g ω ∂μ := by
          apply setIntegral_mono_ae
          · exact (hV_int t).integrableOn
          · exact (hg_int.const_mul 4).integrableOn
          · exact ae_of_all _ h_pw
      _ = 4 * ∫ ω in {ω | M < |ω_freq ω|}, g ω ∂μ := integral_const_mul _ _
      _ < 4 * (ε / 8) := by linarith [mul_lt_mul_of_pos_left hM_tail (by norm_num : (0:ℝ) < 4)]
      _ = ε / 2 := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_full_nn, hV_split]
  linarith

theorem frozen_oa_V_zero_strong_coupling
    (ω_freq : Ω → ℝ) (g : Ω → ℝ) (K r c : ℝ)
    (z : Ω → ℝ → ℂ)
    (hK : 0 < K) (hr : 0 < r) (hc : 3 / 4 < c)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (h_locked : ∀ ω, (ω_freq ω) ^ 2 < K ^ 2 * r ^ 2)
    (h_re_bound : ∀ ω, c ≤ (lockedEquil (ω_freq ω) K r).re)
    (hz_init : ∀ ω, z ω 0 = 0)
    (hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω)
        (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hz_cont : ∀ ω, Continuous
        (fun t => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r)))
    (hfg_int : ∀ t, 0 ≤ t → Integrable
        (fun ω => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω) μ) :
    Tendsto (fun t =>
        ∫ ω, Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω ∂μ)
      atTop (nhds 0) := by
  apply frozen_oa_body_convergence ω_freq g K r (K * r * (2 * c - 3 / 2)) z
    hK hr (by nlinarith [mul_pos hK hr]) hg_nn hg_int h_locked hz_init hz_ode hz_cont
  · intro ω z' hz'
    have h_re := re_from_normSq_bound z' (lockedEquil (ω_freq ω) K r) hz'
    simp only [Complex.add_re]
    have h1 : 2 * c - 3 / 2 ≤ z'.re + (lockedEquil (ω_freq ω) K r).re := by
      linarith [h_re_bound ω]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hK hr))
  · exact hfg_int

theorem frozen_oa_V_zero_moderate_coupling
    (ω_freq : Ω → ℝ) (g : Ω → ℝ) (K r c : ℝ)
    (z : Ω → ℝ → ℂ)
    (hK : 0 < K) (hr : 0 < r) (hc : 5 / 8 < c)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (h_locked : ∀ ω, (ω_freq ω) ^ 2 < K ^ 2 * r ^ 2)
    (h_re_bound : ∀ ω, c ≤ (lockedEquil (ω_freq ω) K r).re)
    (hz_init : ∀ ω, z ω 0 = 0)
    (hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω)
        (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hz_cont : ∀ ω, Continuous
        (fun t => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r)))
    (hfg_int : ∀ t, 0 ≤ t → Integrable
        (fun ω => Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω) μ) :
    Tendsto (fun t =>
        ∫ ω, Complex.normSq (z ω t - lockedEquil (ω_freq ω) K r) * g ω ∂μ)
      atTop (nhds 0) := by
  have hB : (0 : ℝ) < 3 / 2 := by norm_num
  apply complex_oa_body_decay_B z (fun ω => lockedEquil (ω_freq ω) K r) ω_freq g K r
    (K * r * (2 * c - 5 / 4)) (3 / 2)
    hK hr (by nlinarith [mul_pos hK hr]) hB hg_nn hg_int
  · exact fun ω => lockedEquil_is_equil (ω_freq ω) K r hK hr (h_locked ω)
  · exact hz_ode
  · exact hz_cont
  · intro ω z' hz'
    have h_re := re_from_normSq_bound_3_2 z' (lockedEquil (ω_freq ω) K r) hz'
    simp only [Complex.add_re]
    have h1 : 2 * c - 5 / 4 ≤ z'.re + (lockedEquil (ω_freq ω) K r).re := by
      linarith [h_re_bound ω]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hK hr))
  · intro ω; rw [hz_init ω, zero_sub]
    have h1 : Complex.normSq (-lockedEquil (ω_freq ω) K r) =
        Complex.normSq (lockedEquil (ω_freq ω) K r) := by
      simp only [Complex.normSq_apply, Complex.neg_re, Complex.neg_im]; ring
    rw [h1, lockedEquil_normSq (ω_freq ω) K r hK hr (h_locked ω)]; norm_num
  · exact hfg_int

theorem frozen_oa_V_bounded
    (ω_freq : Ω → ℝ) (g : Ω → ℝ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (M₀ : ℝ)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_ns : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (hV_int : ∀ t, Integrable
        (fun ω => Complex.normSq (z ω t - z_star ω) * g ω) μ)
    (hω_meas : MeasurableSet {ω | |ω_freq ω| ≤ M₀})
    (h_body_zero : Tendsto (fun t =>
        ∫ ω in {ω | |ω_freq ω| ≤ M₀},
        Complex.normSq (z ω t - z_star ω) * g ω ∂μ) atTop (nhds 0)) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ <
          ε + 4 * ∫ ω in {ω | M₀ < |ω_freq ω|}, g ω ∂μ := by
  intro ε hε
  rw [Metric.tendsto_atTop] at h_body_zero
  obtain ⟨T, hT⟩ := h_body_zero ε hε
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have ht_ge_T : T ≤ t := le_trans (le_max_left T 0) ht
  have hV_split :
      ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ =
        (∫ ω in {ω | |ω_freq ω| ≤ M₀},
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ) +
        (∫ ω in {ω | |ω_freq ω| ≤ M₀}ᶜ,
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ) :=
    (integral_add_compl hω_meas (hV_int t)).symm
  have h_compl : {ω | |ω_freq ω| ≤ M₀}ᶜ = {ω | M₀ < |ω_freq ω|} := by
    ext ω; simp [not_le]
  have h_body_nn : 0 ≤ ∫ ω in {ω | |ω_freq ω| ≤ M₀},
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ :=
    integral_nonneg fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω)
  have h_body_small : ∫ ω in {ω | |ω_freq ω| ≤ M₀},
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ < ε := by
    have h := hT t ht_ge_T
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_body_nn] at h; exact h
  have h_tail_bound : ∫ ω in {ω | |ω_freq ω| ≤ M₀}ᶜ,
      Complex.normSq (z ω t - z_star ω) * g ω ∂μ ≤
      4 * ∫ ω in {ω | M₀ < |ω_freq ω|}, g ω ∂μ := by
    rw [h_compl]
    calc ∫ ω in {ω | M₀ < |ω_freq ω|},
          Complex.normSq (z ω t - z_star ω) * g ω ∂μ
        ≤ ∫ ω in {ω | M₀ < |ω_freq ω|}, 4 * g ω ∂μ := by
          apply setIntegral_mono_ae
          · exact (hV_int t).integrableOn
          · exact (hg_int.const_mul 4).integrableOn
          · exact ae_of_all _ fun ω =>
              mul_le_mul_of_nonneg_right
                (le_of_lt (error_sq_bound_in_disk _ _ (hz_disk ω t ht_nn) (hz_star_ns ω)))
                (hg_nn ω)
      _ = 4 * ∫ ω in {ω | M₀ < |ω_freq ω|}, g ω ∂μ := integral_const_mul _ _
  rw [hV_split]; linarith

end
