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


/-! ## Target B: Critical algebraic decay -/

private theorem slope_gap_lower (gv K r gmax : ℝ)
    (hgv : 0 < gv) (hK : 0 < K) (hr : 0 < r) (hr1 : r ≤ 1)
    (hgmax : 0 < gmax) (hgv_le : gv ≤ gmax) :
    K ^ 3 * r ^ 2 / (2 * gv * (2 * gmax + K) ^ 2) ≤
    K / (2 * gv) - K / (gv + sqrt (gv ^ 2 + K ^ 2 * r ^ 2)) := by
  set S := sqrt (gv ^ 2 + K ^ 2 * r ^ 2)
  have hS_sq : S ^ 2 = gv ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hS_ge : gv ≤ S := by
    calc gv = sqrt (gv ^ 2) := (sqrt_sq (le_of_lt hgv)).symm
      _ ≤ S := sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  have hGS : 0 < gv + S := by linarith
  have h_conj : (gv + S) * (S - gv) = K ^ 2 * r ^ 2 := by nlinarith [hS_sq]
  have hS_sub_nn : 0 ≤ S - gv := by linarith
  have hGS_le : gv + S ≤ 2 * gmax + K := by
    have hS_le : S ≤ gv + K * r := by
      have : gv ^ 2 + K ^ 2 * r ^ 2 ≤ (gv + K * r) ^ 2 := by
        nlinarith [mul_nonneg (le_of_lt hgv) (mul_nonneg (le_of_lt hK) (le_of_lt hr))]
      calc S ≤ sqrt ((gv + K * r) ^ 2) := sqrt_le_sqrt this
        _ = gv + K * r := sqrt_sq (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hr1 (le_of_lt hK)]
  rw [div_sub_div _ _ (ne_of_gt (show (0:ℝ) < 2*gv from by positivity)) (ne_of_gt hGS)]
  have h_lhs_simp : K * (gv + S) - 2 * gv * K = K * (S - gv) := by ring
  rw [h_lhs_simp]
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * gv * (2 * gmax + K) ^ 2)
    (mul_pos (by positivity : 0 < 2 * gv) hGS)]
  have hGS_sq : (gv + S) ^ 2 ≤ (2 * gmax + K) ^ 2 :=
    sq_le_sq' (by linarith) hGS_le
  have h_lhs2 : K ^ 3 * r ^ 2 * (2 * gv * (gv + S)) =
      K * (S - gv) * (2 * gv * (gv + S) ^ 2) := by
    have : K ^ 3 * r ^ 2 = K * ((gv + S) * (S - gv)) := by nlinarith [h_conj]
    nlinarith [this]
  rw [h_lhs2]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)

theorem critical_cubic_drop [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_critical : K = continuumKc γ μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    K ^ 3 * r ^ 3 / (2 * γ_max * (2 * γ_max + K) ^ 2) ≤
    r - ∫ ω, explicitEquil (γ ω) K r ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_Kc_inv : ∫ ω, K / (2 * γ ω) ∂μ = 1 := by
    have hfn : (fun ω => K / (2 * γ ω)) = fun ω => (K / 2) * (1 / γ ω) :=
      funext fun ω => by ring
    rw [hfn, integral_const_mul, h_critical]; unfold continuumKc; field_simp
  have h0_int : Integrable (fun ω => K * r / (2 * γ ω)) μ :=
    ((h_inv_int.const_mul (K * r / 2)).congr (Eventually.of_forall fun ω => by ring))
  have hf_int := equil_int γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have h_r_eq : r = ∫ ω, K * r / (2 * γ ω) ∂μ := by
    have hfn : (fun ω => K * r / (2 * γ ω)) = fun ω => (K / (2 * γ ω)) * r :=
      funext fun ω => by ring
    rw [hfn, integral_mul_const, h_Kc_inv, one_mul]
  have h_pw : ∀ ω, K ^ 3 * r ^ 3 / (2 * γ_max * (2 * γ_max + K) ^ 2) ≤
      K * r / (2 * γ ω) - explicitEquil (γ ω) K r := by
    intro ω
    have h1 := slope_gap_lower (γ ω) K r γ_max (hγ_pos ω) hK hr hr1 hγ_max_pos (hγ_max ω)
    rw [explicitEquil_rationalized (γ ω) K r (hγ_pos ω) hK hr]
    have h_rhs_eq : K * r / (2 * γ ω) - K * r / (γ ω + sqrt ((γ ω)^2 + K^2*r^2)) =
        r * (K / (2 * γ ω) - K / (γ ω + sqrt ((γ ω)^2 + K^2*r^2))) := by ring
    have h_lhs_eq : K^3 * r^3 / (2 * γ_max * (2 * γ_max + K)^2) =
        r * (K^3 * r^2 / (2 * γ_max * (2 * γ_max + K)^2)) := by ring
    rw [h_rhs_eq, h_lhs_eq]
    apply mul_le_mul_of_nonneg_left _ hr.le
    calc K^3 * r^2 / (2 * γ_max * (2 * γ_max + K)^2)
        ≤ K^3 * r^2 / (2 * γ ω * (2 * γ_max + K)^2) :=
          div_le_div_of_nonneg_left (by positivity)
            (mul_pos (mul_pos two_pos (hγ_pos ω)) (sq_pos_of_pos (by linarith [hγ_max_pos])))
            (mul_le_mul_of_nonneg_right (by linarith [hγ_max ω]) (sq_nonneg _))
      _ ≤ K / (2 * γ ω) - K / (γ ω + sqrt ((γ ω)^2 + K^2*r^2)) := h1
  calc K^3 * r^3 / (2 * γ_max * (2 * γ_max + K)^2)
      = ∫ _, K^3 * r^3 / (2 * γ_max * (2 * γ_max + K)^2) ∂μ := by
        simp [integral_const]
    _ ≤ ∫ ω, (K * r / (2 * γ ω) - explicitEquil (γ ω) K r) ∂μ :=
        integral_mono (integrable_const _) (h0_int.sub hf_int) h_pw
    _ = r - ∫ ω, explicitEquil (γ ω) K r ∂μ := by
        rw [integral_sub h0_int hf_int]; linarith

private theorem one_sub_sq_bound (t : ℝ) (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + 2 * t) * (1 - t) ^ 2 ≤ 1 := by nlinarith [sq_nonneg t, sq_nonneg (1 - t)]

theorem critical_algebraic_decay [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r0 γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_critical : K = continuumKc γ μ)
    (hr0 : 0 < r0) (hr0_lt : r0 < 1)
    (h_small : K ^ 3 * r0 ^ 2 < 2 * γ_max * (2 * γ_max + K) ^ 2) :
    ∀ n, scMapIter γ K μ n r0 ≤
      r0 / sqrt (1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2)) := by
  have hD : (0:ℝ) < γ_max * (2 * γ_max + K) ^ 2 := by positivity
  have h_pos : ∀ n, 0 < scMapIter γ K μ n r0 :=
    scMapIter_pos γ K hγ_pos hK hγ_level r0 hr0
  suffices h_sq : ∀ n, (scMapIter γ K μ n r0) ^ 2 *
      (1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2)) ≤ r0 ^ 2 from by
    intro n
    have hrn_pos := h_pos n
    have hBn : (0:ℝ) < 1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2) := by positivity
    have hbn := h_sq n
    have hsBn : (0:ℝ) < sqrt (1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2)) :=
      sqrt_pos.mpr hBn
    suffices h : scMapIter γ K μ n r0 * sqrt (1 + K ^ 3 * r0 ^ 2 * ↑n /
        (γ_max * (2 * γ_max + K) ^ 2)) ≤ r0 from
      (le_div_iff₀ hsBn).mpr h
    have hsq : (scMapIter γ K μ n r0 * sqrt (1 + K ^ 3 * r0 ^ 2 * ↑n /
        (γ_max * (2 * γ_max + K) ^ 2))) ^ 2 ≤ r0 ^ 2 := by
      rw [mul_pow, sq_sqrt (le_of_lt hBn)]; exact hbn
    nlinarith [sq_nonneg (r0 - scMapIter γ K μ n r0 *
      sqrt (1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2))),
      mul_nonneg (le_of_lt hrn_pos) (le_of_lt hsBn)]
  intro n; induction n with
  | zero => simp [scMapIter]
  | succ n ih =>
    set rn := scMapIter γ K μ n r0 with hrn_def
    have hrn_pos := h_pos n
    have hrn1_pos := h_pos (n + 1)
    have hrn_sq_pos : (0:ℝ) < rn ^ 2 := by positivity
    have hrn1_sq_pos : (0:ℝ) < (scMapIter γ K μ (n + 1) r0) ^ 2 := by positivity
    have hrn_le_r0 : rn ≤ r0 := by
      nlinarith [ih, sq_nonneg rn, show (0:ℝ) ≤ K ^ 3 * r0 ^ 2 * ↑n /
        (γ_max * (2 * γ_max + K) ^ 2) from by positivity]
    have hrn_lt_1 : rn < 1 := lt_of_le_of_lt hrn_le_r0 hr0_lt
    have h_drop := critical_cubic_drop γ K rn γ_max hγ_pos hK hγ_max_pos hγ_max
      hγ_level h_inv_int h_inv_pos h_critical hrn_pos (le_of_lt hrn_lt_1)
    have h_step : scMapIter γ K μ (n + 1) r0 ≤
        rn * (1 - K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2)) := by
      have heq : rn - K ^ 3 * rn ^ 3 / (2 * γ_max * (2 * γ_max + K) ^ 2) =
          rn * (1 - K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2)) := by ring
      change ∫ ω, explicitEquil (γ ω) K rn ∂μ ≤ _
      linarith [h_drop, heq]
    have hcrn_nn : (0:ℝ) ≤ K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2) := by positivity
    have hcrn_lt : K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2) < 1 := by
      have h2D : (0:ℝ) < 2 * γ_max * (2 * γ_max + K) ^ 2 := by positivity
      have hrn2 : K ^ 3 * rn ^ 2 ≤ K ^ 3 * r0 ^ 2 := by
        have h_sq : rn ^ 2 ≤ r0 ^ 2 := by nlinarith [sq_nonneg (r0 - rn)]
        exact mul_le_mul_of_nonneg_left h_sq (by positivity : (0:ℝ) ≤ K ^ 3)
      exact (div_lt_one h2D).mpr (by linarith [h_small])
    have h_sq_step : (scMapIter γ K μ (n + 1) r0) ^ 2 ≤
        rn ^ 2 * (1 - K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2)) ^ 2 := by
      nlinarith [sq_nonneg (scMapIter γ K μ (n + 1) r0 -
        rn * (1 - K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2))),
        mul_self_nonneg (rn * (1 - K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2)))]
    have h_alg := one_sub_sq_bound (K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2))
      hcrn_nn (le_of_lt hcrn_lt)
    have h_key : (scMapIter γ K μ (n + 1) r0) ^ 2 *
        (1 + K ^ 3 * rn ^ 2 / (γ_max * (2 * γ_max + K) ^ 2)) ≤ rn ^ 2 := by
      have h2 : K ^ 3 * rn ^ 2 / (γ_max * (2 * γ_max + K) ^ 2) =
          2 * (K ^ 3 * rn ^ 2 / (2 * γ_max * (2 * γ_max + K) ^ 2)) := by
        field_simp
      rw [h2]; nlinarith [h_sq_step, sq_nonneg rn]
    have h_ih_div : 1 + K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2) ≤
        r0 ^ 2 / rn ^ 2 := (le_div_iff₀ hrn_sq_pos).mpr (by nlinarith [ih])
    have h_cancel : rn ^ 2 * (r0 ^ 2 / rn ^ 2) = r0 ^ 2 :=
      mul_div_cancel₀ (r0 ^ 2) (ne_of_gt hrn_sq_pos)
    have h_expand : r0 ^ 2 / rn ^ 2 + K ^ 3 * r0 ^ 2 / (γ_max * (2 * γ_max + K) ^ 2) =
        (1 + K ^ 3 * rn ^ 2 / (γ_max * (2 * γ_max + K) ^ 2)) * (r0 ^ 2 / rn ^ 2) := by
      have hrn_ne : (rn : ℝ) ≠ 0 := ne_of_gt hrn_pos
      field_simp [hrn_ne]
    have h_bound : (scMapIter γ K μ (n + 1) r0) ^ 2 *
        (r0 ^ 2 / rn ^ 2 + K ^ 3 * r0 ^ 2 / (γ_max * (2 * γ_max + K) ^ 2)) ≤ r0 ^ 2 := by
      rw [h_expand, ← mul_assoc]
      calc (scMapIter γ K μ (n + 1) r0) ^ 2 *
            (1 + K ^ 3 * rn ^ 2 / (γ_max * (2 * γ_max + K) ^ 2)) * (r0 ^ 2 / rn ^ 2)
          ≤ rn ^ 2 * (r0 ^ 2 / rn ^ 2) :=
            mul_le_mul_of_nonneg_right h_key
              (div_nonneg (sq_nonneg r0) (le_of_lt hrn_sq_pos))
        _ = r0 ^ 2 := h_cancel
    have h_Bn1_le : 1 + K ^ 3 * r0 ^ 2 * ↑(n + 1) / (γ_max * (2 * γ_max + K) ^ 2) ≤
        r0 ^ 2 / rn ^ 2 + K ^ 3 * r0 ^ 2 / (γ_max * (2 * γ_max + K) ^ 2) := by
      have : K ^ 3 * r0 ^ 2 * (↑(n + 1) : ℝ) / (γ_max * (2 * γ_max + K) ^ 2) =
          K ^ 3 * r0 ^ 2 * ↑n / (γ_max * (2 * γ_max + K) ^ 2) +
          K ^ 3 * r0 ^ 2 / (γ_max * (2 * γ_max + K) ^ 2) := by push_cast; ring
      linarith [h_ih_div]
    calc (scMapIter γ K μ (n + 1) r0) ^ 2 *
          (1 + K ^ 3 * r0 ^ 2 * ↑(n + 1) / (γ_max * (2 * γ_max + K) ^ 2))
        ≤ (scMapIter γ K μ (n + 1) r0) ^ 2 *
          (r0 ^ 2 / rn ^ 2 + K ^ 3 * r0 ^ 2 / (γ_max * (2 * γ_max + K) ^ 2)) :=
          mul_le_mul_of_nonneg_left h_Bn1_le (le_of_lt hrn1_sq_pos)
      _ ≤ r0 ^ 2 := h_bound

end
