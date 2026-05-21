/-
  Continuum Square Root Law
  ==========================
  Near the onset K → Kc+:

    r*² ≥ 8(K - Kc) / (K³ · Kc · ∫(1/γ³) dμ)     (lower bound)
    r*² ≤ (K - Kc) · (2γ_max + K)² / K³            (upper bound)

  Together: r* = Θ(√(K - Kc)) — the universal square-root scaling.

  0 sorry.
-/

import KuramotoLean.ContinuumBifurcationDiagram

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Pointwise slope gap bounds -/

private theorem slope_gap_upper_pw (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) :
    K / (2 * γ_k) - K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) ≤
    K ^ 3 * r ^ 2 / (8 * γ_k ^ 3) := by
  set S := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
  have hS_sq : S ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hS_ge : γ_k ≤ S := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ ≤ S := sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  have hGS : 0 < γ_k + S := by linarith
  have h2γ : (0 : ℝ) < 2 * γ_k := by positivity
  have h8γ3 : (0 : ℝ) < 8 * γ_k ^ 3 := by positivity
  have h_conj : (γ_k + S) * (S - γ_k) = K ^ 2 * r ^ 2 := by nlinarith [hS_sq]
  have hS_sub_nn : 0 ≤ S - γ_k := by linarith
  rw [div_sub_div _ _ (ne_of_gt h2γ) (ne_of_gt hGS)]
  rw [div_le_div_iff₀ (mul_pos h2γ hGS) h8γ3]
  have h_lhs_simp : K * (γ_k + S) - 2 * γ_k * K = K * (S - γ_k) := by ring
  rw [h_lhs_simp]
  have h4 : 4 * γ_k ^ 2 ≤ (γ_k + S) ^ 2 := by nlinarith
  have h_rhs : K ^ 3 * r ^ 2 * (2 * γ_k * (γ_k + S)) =
      K * (S - γ_k) * (2 * γ_k * (γ_k + S) ^ 2) := by
    have : K ^ 3 * r ^ 2 = K * ((γ_k + S) * (S - γ_k)) := by nlinarith [h_conj]
    nlinarith [this]
  rw [h_rhs]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)

private theorem slope_gap_lower_pw (γ_k K r γ_max : ℝ)
    (hγ : 0 < γ_k) (hK : 0 < K) (hr_nn : 0 ≤ r) (hr_le : r ≤ 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : γ_k ≤ γ_max) :
    K ^ 3 * r ^ 2 / (2 * γ_k * (2 * γ_max + K) ^ 2) ≤
    K / (2 * γ_k) - K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) := by
  set S := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
  have hS_sq : S ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hS_ge : γ_k ≤ S := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ ≤ S := sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  have hGS : 0 < γ_k + S := by linarith
  have h2γ : (0 : ℝ) < 2 * γ_k := by positivity
  have h_conj : (γ_k + S) * (S - γ_k) = K ^ 2 * r ^ 2 := by nlinarith [hS_sq]
  have hS_sub_nn : 0 ≤ S - γ_k := by linarith
  have hGS_le : γ_k + S ≤ 2 * γ_max + K := by
    have hS_le : S ≤ γ_k + K * r := by
      have : γ_k ^ 2 + K ^ 2 * r ^ 2 ≤ (γ_k + K * r) ^ 2 := by
        nlinarith [mul_nonneg (le_of_lt hγ) (mul_nonneg (le_of_lt hK) hr_nn)]
      calc S ≤ sqrt ((γ_k + K * r) ^ 2) := sqrt_le_sqrt this
        _ = γ_k + K * r := sqrt_sq (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hr_le (le_of_lt hK)]
  rw [div_sub_div _ _ (ne_of_gt h2γ) (ne_of_gt hGS)]
  have h_lhs_simp : K * (γ_k + S) - 2 * γ_k * K = K * (S - γ_k) := by ring
  rw [h_lhs_simp]
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * γ_k * (2 * γ_max + K) ^ 2)
    (mul_pos h2γ hGS)]
  have hGS_sq : (γ_k + S) ^ 2 ≤ (2 * γ_max + K) ^ 2 :=
    sq_le_sq' (by linarith) hGS_le
  have h_lhs2 : K ^ 3 * r ^ 2 * (2 * γ_k * (γ_k + S)) =
      K * (S - γ_k) * (2 * γ_k * (γ_k + S) ^ 2) := by
    have : K ^ 3 * r ^ 2 = K * ((γ_k + S) * (S - γ_k)) := by nlinarith [h_conj]
    nlinarith [this]
  rw [h_lhs2]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)

/-! ## Main results -/

/-- **SQUARE ROOT LAW (LOWER BOUND).**
    r*² ≥ 8(K - Kc) / (K³ · Kc · ∫(1/γ³) dμ). -/
theorem continuum_rstar_sq_lower [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_inv3_int : Integrable (fun ω => 1 / (γ ω) ^ 3) μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    8 * (K - continuumKc γ μ) /
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ) ≤ r_star ^ 2 := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hKc_pos : 0 < continuumKc γ μ := div_pos two_pos h_inv_pos
  have h_slope_one := slope_integral_eq_one γ K r_star hγ_pos hK hr hγ_meas hfp
  have h0_int : Integrable (fun ω => K / (2 * γ ω)) μ :=
    (h_inv_int.const_mul (K / 2)).congr (Eventually.of_forall fun ω => by ring)
  have hr_int := slope_integrable γ K r_star hγ_pos hK hr hγ_meas (μ := μ)
  have h_slope0 : ∫ ω, K / (2 * γ ω) ∂μ = K / continuumKc γ μ := by
    have : (fun ω => K / (2 * γ ω)) = fun ω => (K / 2) * (1 / γ ω) := by ext ω; ring
    rw [this, integral_const_mul]; unfold continuumKc; field_simp
  have h_int3_pos : 0 < ∫ ω, 1 / (γ ω) ^ 3 ∂μ :=
    (integral_pos_iff_support_of_nonneg
      (fun ω => div_nonneg zero_le_one (pow_nonneg (le_of_lt (hγ_pos ω)) 3)) h_inv3_int).mpr (by
      rw [show Function.support (fun ω => 1 / (γ ω) ^ 3) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (div_pos one_pos (pow_pos (hγ_pos ω) 3))]
      rw [measure_univ]; exact one_pos)
  have h_gap : K / continuumKc γ μ - 1 =
      ∫ ω, (K / (2 * γ ω) - K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ := by
    rw [← h_slope0, ← h_slope_one, ← integral_sub h0_int hr_int]
  have h_gap_le : K / continuumKc γ μ - 1 ≤
      (K ^ 3 * r_star ^ 2 / 8) * ∫ ω, 1 / (γ ω) ^ 3 ∂μ := by
    rw [h_gap]
    calc ∫ ω, (K / (2 * γ ω) -
        K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ
      ≤ ∫ ω, K ^ 3 * r_star ^ 2 / (8 * (γ ω) ^ 3) ∂μ :=
        integral_mono (h0_int.sub hr_int)
          ((h_inv3_int.const_mul (K ^ 3 * r_star ^ 2 / 8)).congr
            (Eventually.of_forall fun ω => by
              have : (γ ω) ^ 3 ≠ 0 := ne_of_gt (pow_pos (hγ_pos ω) 3)
              field_simp))
          (fun ω => slope_gap_upper_pw (γ ω) K r_star (hγ_pos ω) hK)
      _ = (K ^ 3 * r_star ^ 2 / 8) * ∫ ω, 1 / (γ ω) ^ 3 ∂μ := by
          rw [← integral_const_mul]; congr 1; ext ω
          have : (γ ω) ^ 3 ≠ 0 := ne_of_gt (pow_pos (hγ_pos ω) 3)
          field_simp
  have h_KKc_pos : 0 < K / continuumKc γ μ - 1 := by
    rw [sub_pos, lt_div_iff₀ hKc_pos]; linarith
  have hden_pos : 0 < K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ :=
    mul_pos (mul_pos (pow_pos hK 3) hKc_pos) h_int3_pos
  rw [div_le_iff₀ hden_pos]
  have h_from : (K - continuumKc γ μ) / continuumKc γ μ ≤
      (K ^ 3 * r_star ^ 2 / 8) * ∫ ω, 1 / (γ ω) ^ 3 ∂μ := by
    have : K / continuumKc γ μ - 1 = (K - continuumKc γ μ) / continuumKc γ μ := by
      field_simp [ne_of_gt hKc_pos]
    linarith
  have h_scaled := (div_le_iff₀ hKc_pos).mp h_from
  nlinarith

/-- **SQUARE ROOT LAW (UPPER BOUND).**
    r*² ≤ (K - Kc) · (2γ_max + K)² / K³. -/
theorem continuum_rstar_sq_upper [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    r_star ^ 2 ≤ (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3 := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hKc_pos : 0 < continuumKc γ μ := div_pos two_pos h_inv_pos
  have h_slope_one := slope_integral_eq_one γ K r_star hγ_pos hK hr_pos hγ_meas hfp
  have h0_int : Integrable (fun ω => K / (2 * γ ω)) μ :=
    (h_inv_int.const_mul (K / 2)).congr (Eventually.of_forall fun ω => by ring)
  have hr_int := slope_integrable γ K r_star hγ_pos hK hr_pos hγ_meas (μ := μ)
  have h_slope0 : ∫ ω, K / (2 * γ ω) ∂μ = K / continuumKc γ μ := by
    have : (fun ω => K / (2 * γ ω)) = fun ω => (K / 2) * (1 / γ ω) := by ext ω; ring
    rw [this, integral_const_mul]; unfold continuumKc; field_simp
  have h_gap : K / continuumKc γ μ - 1 =
      ∫ ω, (K / (2 * γ ω) - K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2))) ∂μ := by
    rw [← h_slope0, ← h_slope_one, ← integral_sub h0_int hr_int]
  have h_lower_int : Integrable (fun ω =>
      K ^ 3 * r_star ^ 2 / (2 * γ ω * (2 * γ_max + K) ^ 2)) μ :=
    (h_inv_int.const_mul (K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2))).congr
      (Eventually.of_forall fun ω => by
        have hγ_ne : γ ω ≠ 0 := ne_of_gt (hγ_pos ω)
        have h2gK_ne : (2 * γ_max + K) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by linarith : (0:ℝ) < 2 * γ_max + K))
        field_simp)
  have h_gap_ge : (K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2)) *
      ∫ ω, 1 / γ ω ∂μ ≤ K / continuumKc γ μ - 1 := by
    rw [h_gap]
    have h_lhs_eq : (K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2)) * ∫ ω, 1 / γ ω ∂μ =
        ∫ ω, K ^ 3 * r_star ^ 2 / (2 * γ ω * (2 * γ_max + K) ^ 2) ∂μ := by
      rw [← integral_const_mul]; congr 1; ext ω
      have hγ_ne : γ ω ≠ 0 := ne_of_gt (hγ_pos ω)
      have h2gK_ne : (2 * γ_max + K) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by linarith : (0:ℝ) < 2 * γ_max + K))
      field_simp
    rw [h_lhs_eq]
    exact integral_mono h_lower_int (h0_int.sub hr_int)
      (fun ω => slope_gap_lower_pw (γ ω) K r_star γ_max (hγ_pos ω) hK
        (le_of_lt hr_pos) (le_of_lt hr_lt) hγ_max_pos (hγ_max ω))
  have h2gK_pos : (0 : ℝ) < 2 * γ_max + K := by linarith
  have h_Kc_eq : continuumKc γ μ * (∫ ω, 1 / γ ω ∂μ) = 2 := by
    unfold continuumKc; field_simp [ne_of_gt h_inv_pos]
  have h_rearrange : K ^ 3 * r_star ^ 2 ≤
      (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 := by
    have h1 : K / continuumKc γ μ - 1 = (K - continuumKc γ μ) / continuumKc γ μ := by
      field_simp [ne_of_gt hKc_pos]
    rw [h1] at h_gap_ge
    have h2 := (le_div_iff₀ hKc_pos).mp h_gap_ge
    have h3 : K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2) *
        (∫ ω, 1 / γ ω ∂μ) * continuumKc γ μ =
        K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2) *
        (continuumKc γ μ * (∫ ω, 1 / γ ω ∂μ)) := by ring
    rw [h3, h_Kc_eq] at h2
    have h4 : K ^ 3 * r_star ^ 2 / (2 * (2 * γ_max + K) ^ 2) * 2 =
        K ^ 3 * r_star ^ 2 / (2 * γ_max + K) ^ 2 := by
      field_simp [ne_of_gt (sq_pos_of_pos h2gK_pos)]
    rw [h4] at h2
    exact (div_le_iff₀ (sq_pos_of_pos h2gK_pos)).mp h2
  exact (le_div_iff₀ (pow_pos hK 3)).mpr (by nlinarith)

/-- **SQUARE ROOT LAW (COMBINED).**
    c₁(K-Kc) ≤ r*² ≤ c₂(K-Kc) for explicit constants depending on γ distribution. -/
theorem continuum_square_root_law [IsProbabilityMeasure μ]
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
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ) ≤ r_star ^ 2 ∧
    r_star ^ 2 ≤ (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3 :=
  ⟨continuum_rstar_sq_lower γ K r_star hγ_pos hK hr_pos hγ_level h_inv_int h_inv_pos
    h_inv3_int h_super hfp,
   continuum_rstar_sq_upper γ K r_star γ_max hγ_pos hK hr_pos hr_lt hγ_max_pos
    hγ_max hγ_level h_inv_int h_inv_pos h_super hfp⟩

end
