/-
  Quantitative Refinements for the Self-Consistency Map
  =====================================================
  A. Two-sided critical slowing down: 1 - λ = Θ(K - Kc)
  C. Eventual geometric rate from below: r* - rn ≤ L0^n(r* - r0) when Φ'(r0) < 1
-/

import KuramotoLean.TightLipschitz

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem equil_int [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_meas : Measurable γ) :
    Integrable (fun ω => explicitEquil (γ ω) K r) μ :=
  (integrable_const (1 : ℝ)).mono
    (by exact (((continuous_neg.add (Real.continuous_sqrt.comp
          ((continuous_pow 2).add continuous_const))).div_const _).measurable.comp
        hγ_meas).aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, norm_one]
      exact le_of_lt (abs_lt.mpr
        ⟨by linarith [explicitEquil_pos (γ ω) K r (hγ_pos ω) hK hr],
         explicitEquil_lt_one (γ ω) K r (hγ_pos ω) hK hr⟩))

/-! ## Target A: Two-sided critical slowing down -/

theorem critical_slowing_down_lower [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_inv3_int : Integrable (fun ω => 1 / (γ ω) ^ 3) μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    8 * (K - continuumKc γ μ) /
      ((γ_max + K) * (2 * γ_max + K) ^ 2 * continuumKc γ μ *
       (∫ ω, 1 / (γ ω) ^ 3 ∂μ)) ≤
    1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ := by
  have h_gap_lower := spectral_gap_lower_bound γ K r_star γ_max hγ_pos hK hr_pos
    hγ_max_pos hγ_max hγ_level hfp
  have h_rstar_sq := continuum_rstar_sq_lower γ K r_star hγ_pos hK hr_pos hγ_level
    h_inv_int h_inv_pos h_inv3_int h_super hfp
  set D_max := sqrt (γ_max ^ 2 + K ^ 2 * r_star ^ 2)
  have hD_max_pos : 0 < D_max := sqrt_pos.mpr (by positivity)
  have hD_max_le : D_max ≤ γ_max + K := by
    have h1 : γ_max ^ 2 + K ^ 2 * r_star ^ 2 ≤ (γ_max + K) ^ 2 := by
      nlinarith [mul_pos hr_pos (sub_pos.mpr hr_lt), mul_pos hγ_max_pos hK]
    have h2 : D_max ≤ sqrt ((γ_max + K) ^ 2) := sqrt_le_sqrt h1
    rwa [sqrt_sq (show (0 : ℝ) ≤ γ_max + K from by linarith)] at h2
  have hden_le : γ_max + D_max ≤ 2 * γ_max + K := by linarith
  have hKc_pos : 0 < continuumKc γ μ := div_pos two_pos h_inv_pos
  have hden_max_pos : 0 < D_max * (γ_max + D_max) ^ 2 :=
    mul_pos hD_max_pos (sq_pos_of_pos (by linarith [hD_max_pos]))
  have h_denom_bound : D_max * (γ_max + D_max) ^ 2 ≤ (γ_max + K) * (2 * γ_max + K) ^ 2 :=
    mul_le_mul hD_max_le (sq_le_sq' (by linarith) hden_le)
      (sq_nonneg _) (by linarith)
  have h_big_denom_pos : 0 < (γ_max + K) * (2 * γ_max + K) ^ 2 := by positivity
  suffices h : K ^ 3 * (8 * (K - continuumKc γ μ) /
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ)) /
      ((γ_max + K) * (2 * γ_max + K) ^ 2) ≤
      1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ by
    convert h using 1
    field_simp
  calc K ^ 3 * (8 * (K - continuumKc γ μ) /
        (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ)) /
        ((γ_max + K) * (2 * γ_max + K) ^ 2)
      ≤ K ^ 3 * r_star ^ 2 / ((γ_max + K) * (2 * γ_max + K) ^ 2) := by
        apply div_le_div_of_nonneg_right _ h_big_denom_pos.le
        exact mul_le_mul_of_nonneg_left h_rstar_sq (by positivity)
    _ ≤ K ^ 3 * r_star ^ 2 / (D_max * (γ_max + D_max) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hden_max_pos h_denom_bound
    _ ≤ 1 - ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2) *
          (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ := h_gap_lower

/-! ## Target C: Eventual geometric rate from below -/

theorem tight_slope_antitone (gv K : ℝ) (hgv : 0 < gv) (hK : 0 < K)
    {r1 r2 : ℝ} (hr1 : 0 < r1) (h_le : r1 ≤ r2) :
    K * gv / (sqrt (gv ^ 2 + K ^ 2 * r2 ^ 2) *
      (gv + sqrt (gv ^ 2 + K ^ 2 * r2 ^ 2))) ≤
    K * gv / (sqrt (gv ^ 2 + K ^ 2 * r1 ^ 2) *
      (gv + sqrt (gv ^ 2 + K ^ 2 * r1 ^ 2))) := by
  rcases eq_or_lt_of_le h_le with h_eq | h_lt
  · rw [← h_eq]
  · have hD1 : 0 < sqrt (gv ^ 2 + K ^ 2 * r1 ^ 2) := sqrt_pos.mpr (by positivity)
    have hD2 : 0 < sqrt (gv ^ 2 + K ^ 2 * r2 ^ 2) := sqrt_pos.mpr (by positivity)
    have hden1 : 0 < gv + sqrt (gv ^ 2 + K ^ 2 * r1 ^ 2) := by linarith
    have hden2 : 0 < gv + sqrt (gv ^ 2 + K ^ 2 * r2 ^ 2) := by linarith
    apply div_le_div_of_nonneg_left (mul_pos hK hgv).le (mul_pos hD1 hden1)
    have h_r_sq : r1 ^ 2 ≤ r2 ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt h_lt) hr1.le,
        mul_le_mul_of_nonneg_left (le_of_lt h_lt) (le_trans hr1.le (le_of_lt h_lt))]
    have hD_le : sqrt (gv ^ 2 + K ^ 2 * r1 ^ 2) ≤ sqrt (gv ^ 2 + K ^ 2 * r2 ^ 2) :=
      sqrt_le_sqrt (by nlinarith [sq_nonneg K])
    exact mul_le_mul hD_le (by linarith [hD_le]) (by linarith [hD1]) hD2.le

theorem sc_map_tight_contraction_below [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r) (hr_star : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_below : r < r_star) :
    r_star - ∫ ω, explicitEquil (γ ω) K r ∂μ ≤
    (∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) ∂μ) * (r_star - r) := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hInt_r := equil_int γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have hInt_rs := equil_int γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ)
  have hL_int := tight_slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have h_pw : ∀ ω, explicitEquil (γ ω) K r_star - explicitEquil (γ ω) K r ≤
      K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) * (r_star - r) :=
    fun ω => explicitEquil_tight_lipschitz (γ ω) K r r_star (hγ_pos ω) hK hr h_below
  have h_ineq : ∫ ω, (explicitEquil (γ ω) K r_star - explicitEquil (γ ω) K r) ∂μ ≤
      ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) * (r_star - r) ∂μ :=
    integral_mono (hInt_rs.sub hInt_r) (hL_int.mul_const _) h_pw
  rw [integral_sub hInt_rs hInt_r, integral_mul_const] at h_ineq
  linarith

set_option linter.unusedVariables false in
theorem scMapIter_geometric_below [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r0 r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr0 : 0 < r0) (hr_star : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_below : r0 < r_star)
    (hL0_lt : ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2) *
      (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2))) ∂μ < 1) :
    ∀ n, r_star - scMapIter γ K μ n r0 ≤
      (∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2) *
        (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2))) ∂μ) ^ n * (r_star - r0) := by
  have hfp' : scMap γ K r_star μ = r_star := hfp
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  set L0 := ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2) *
    (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r0 ^ 2))) ∂μ
  have hL0_nn : 0 ≤ L0 := integral_nonneg fun ω =>
    div_nonneg (mul_nonneg hK.le (hγ_pos ω).le)
      (mul_nonneg (sqrt_nonneg _)
        (add_nonneg (hγ_pos ω).le (sqrt_nonneg _)))
  have h_below_n := scMapIter_below_rstar γ K r0 r_star hγ_pos hK hγ_level
    hr0 hr_star hfp' (le_of_lt h_below)
  have h_mono_n := scMapIter_mono_below γ K r0 r_star hγ_pos hK hγ_level
    hr0 hr_star hfp' h_below
  have h_iter_ge_r0 : ∀ n, r0 ≤ scMapIter γ K μ n r0 := by
    intro n; induction n with
    | zero => exact le_refl _
    | succ n ih => exact le_trans ih (h_mono_n n)
  intro n; induction n with
  | zero => simp [scMapIter]
  | succ n ih =>
    have h_pos_n := scMapIter_pos (μ := μ) γ K hγ_pos hK hγ_level r0 hr0 n
    have h_rn_le := h_below_n n
    rcases eq_or_lt_of_le h_rn_le with h_eq | h_lt_rstar
    · simp only [scMapIter] at h_eq ⊢
      have hrn_eq : scMapIter γ K μ n r0 = r_star := h_eq
      rw [show scMap γ K (scMapIter γ K μ n r0) μ = r_star from by rw [hrn_eq]; exact hfp']
      linarith [mul_nonneg (pow_nonneg hL0_nn (n + 1)) (sub_pos.mpr h_below).le]
    · have h_contraction := sc_map_tight_contraction_below γ K
        (scMapIter γ K μ n r0) r_star hγ_pos hK h_pos_n hr_star hγ_level hfp h_lt_rstar
      have h_slope_bound : ∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 *
          (scMapIter γ K μ n r0) ^ 2) * (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 *
          (scMapIter γ K μ n r0) ^ 2))) ∂μ ≤ L0 :=
        integral_mono (tight_slope_integrable γ K _ hγ_pos hK h_pos_n hγ_meas)
          (tight_slope_integrable γ K r0 hγ_pos hK hr0 hγ_meas)
          (fun ω => tight_slope_antitone (γ ω) K (hγ_pos ω) hK hr0 (h_iter_ge_r0 n))
      calc r_star - scMapIter γ K μ (n + 1) r0
          = r_star - ∫ ω, explicitEquil (γ ω) K (scMapIter γ K μ n r0) ∂μ := rfl
        _ ≤ (∫ ω, K * γ ω / (sqrt ((γ ω) ^ 2 + K ^ 2 *
              (scMapIter γ K μ n r0) ^ 2) * (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 *
              (scMapIter γ K μ n r0) ^ 2))) ∂μ) *
            (r_star - scMapIter γ K μ n r0) := h_contraction
        _ ≤ L0 * (r_star - scMapIter γ K μ n r0) :=
            mul_le_mul_of_nonneg_right h_slope_bound (by linarith [h_below_n n])
        _ ≤ L0 * (L0 ^ n * (r_star - r0)) := mul_le_mul_of_nonneg_left ih hL0_nn
        _ = L0 ^ (n + 1) * (r_star - r0) := by ring

end
