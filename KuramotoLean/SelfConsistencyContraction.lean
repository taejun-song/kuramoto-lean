/-
  Self-Consistency Map Contraction
  =================================
  The self-consistency map Φ(r) = ∫ explicitEquil(γ(ω), K, r) dμ satisfies:
    - For 0 < r < r*:  r < Φ(r)   (map exceeds identity below fixed point)
    - For r* < r < 1:  Φ(r) < r   (map is below identity above fixed point)
    - 0 < Φ(r) < 1 for all r ∈ (0, 1)

  Consequence: r* is the unique attractive fixed point of Φ on (0,1).
  The Picard iteration r_{n+1} = Φ(r_n) converges to r* from any start in (0,1).

  0 sorry.
-/

import KuramotoLean.ContinuumBifurcation

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Slope integral comparison -/

private theorem slope_integral_gt_one [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_lt : r < r_star) :
    1 < ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hs_star := slope_integral_eq_one γ K r_star hγ_pos hK hr_star hγ_meas hfp
  have h_pw : ∀ ω, (0 : ℝ) <
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) -
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) :=
    fun ω => sub_pos.mpr (slope_pointwise_strictAnti (γ ω) K (hγ_pos ω) hK
      (le_of_lt hr) h_lt)
  have hf_r := slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have hf_star := slope_integrable γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ)
  have h_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (h_pw ω)) (hf_r.sub hf_star)).mpr (by
      rw [show Function.support _ = Set.univ from Set.ext fun ω => by
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (h_pw ω)]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hf_r hf_star]

private theorem slope_integral_lt_one [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_gt : r_star < r) :
    ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ < 1 := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hs_star := slope_integral_eq_one γ K r_star hγ_pos hK hr_star hγ_meas hfp
  have h_pw : ∀ ω, (0 : ℝ) <
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r_star ^ 2)) -
      K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) :=
    fun ω => sub_pos.mpr (slope_pointwise_strictAnti (γ ω) K (hγ_pos ω) hK
      (le_of_lt hr_star) h_gt)
  have hf_r := slope_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have hf_star := slope_integrable γ K r_star hγ_pos hK hr_star hγ_meas (μ := μ)
  have h_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (h_pw ω)) (hf_star.sub hf_r)).mpr (by
      rw [show Function.support _ = Set.univ from Set.ext fun ω => by
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (h_pw ω)]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hf_star hf_r]

/-! ## Self-consistency map direction -/

/-- **Φ(r) > r below the fixed point.**
    For 0 < r < r*: the self-consistency map exceeds the identity. -/
theorem sc_map_exceeds_below [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_lt : r < r_star) :
    r < ∫ ω, explicitEquil (γ ω) K r ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_slope_gt := slope_integral_gt_one γ K r r_star hγ_pos hK hγ_level
    hr hr_star hfp h_lt
  have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ =
      (∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ) * r := by
    have : (fun ω => explicitEquil (γ ω) K r) =
        fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) * r := by
      ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
    rw [this, integral_mul_const]
  rw [h_eq]
  exact lt_mul_of_one_lt_left hr h_slope_gt

/-- **Φ(r) < r above the fixed point.**
    For r* < r: the self-consistency map is below the identity. -/
theorem sc_map_below_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_gt : r_star < r) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ < r := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have h_slope_lt := slope_integral_lt_one γ K r r_star hγ_pos hK hγ_level
    hr hr_star hfp h_gt
  have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ =
      (∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ) * r := by
    have : (fun ω => explicitEquil (γ ω) K r) =
        fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) * r := by
      ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
    rw [this, integral_mul_const]
  rw [h_eq]
  exact mul_lt_of_lt_one_left hr h_slope_lt

/-! ## Map range: Φ maps (0,1) into (0,1) -/

private theorem equil_integrable [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r)
    (hγ_meas : Measurable γ) :
    Integrable (fun ω => explicitEquil (γ ω) K r) μ :=
  (integrable_const (1 : ℝ)).mono
    (by have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
          unfold explicitEquil; apply Continuous.div_const
          exact continuous_neg.add (Real.continuous_sqrt.comp
            ((continuous_pow 2).add continuous_const))
        exact (hc.measurable.comp hγ_meas).aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, norm_one]
      exact le_of_lt (abs_lt.mpr
        ⟨by linarith [explicitEquil_pos (γ ω) K r (hγ_pos ω) hK hr],
         explicitEquil_lt_one (γ ω) K r (hγ_pos ω) hK hr⟩))

/-- **Φ(r) > 0 for r > 0.** The self-consistency map is strictly positive. -/
theorem sc_map_pos [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) :
    0 < ∫ ω, explicitEquil (γ ω) K r ∂μ := by
  have h_pw : ∀ ω, (0 : ℝ) < explicitEquil (γ ω) K r :=
    fun ω => explicitEquil_pos (γ ω) K r (hγ_pos ω) hK hr
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hInt := equil_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  exact (integral_pos_iff_support_of_nonneg (fun ω => le_of_lt (h_pw ω)) hInt).mpr (by
    rw [show Function.support _ = Set.univ from Set.ext fun ω => by
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (h_pw ω)]
    rw [measure_univ]; exact one_pos)

/-- **Φ(r) < 1 for r > 0.** The self-consistency map stays below 1. -/
theorem sc_map_lt_one [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ < 1 := by
  have h_lt : ∀ ω, explicitEquil (γ ω) K r < 1 :=
    fun ω => explicitEquil_lt_one (γ ω) K r (hγ_pos ω) hK hr
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hInt := equil_integrable γ K r hγ_pos hK hr hγ_meas (μ := μ)
  have h_gap : ∀ ω, (0 : ℝ) < 1 - explicitEquil (γ ω) K r :=
    fun ω => sub_pos.mpr (h_lt ω)
  have h_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (h_gap ω)) ((integrable_const 1).sub hInt)).mpr (by
      rw [show Function.support _ = Set.univ from Set.ext fun ω => by
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (h_gap ω)]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub (integrable_const (1 : ℝ)) hInt,
    show ∫ _ : Ω, (1 : ℝ) ∂μ = 1 from by simp]

/-! ## Pointwise monotonicity of explicitEquil in r -/

/-- **explicitEquil is strictly increasing in r.**
    Key algebraic identity: (r₁·D₂)² < (r₂·D₁)² when r₁ < r₂,
    hence r₁(γ+D₂) < r₂(γ+D₁), giving the cross-multiplication. -/
theorem explicitEquil_strictMono_r (γ_k K : ℝ) (hγ : 0 < γ_k) (hK : 0 < K)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    explicitEquil γ_k K r₁ < explicitEquil γ_k K r₂ := by
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  rw [explicitEquil_rationalized γ_k K r₁ hγ hK hr₁,
      explicitEquil_rationalized γ_k K r₂ hγ hK hr₂]
  set D₁ := sqrt (γ_k ^ 2 + K ^ 2 * r₁ ^ 2)
  set D₂ := sqrt (γ_k ^ 2 + K ^ 2 * r₂ ^ 2)
  have hD₁_pos : 0 < D₁ := sqrt_pos.mpr (by positivity)
  have hD₂_pos : 0 < D₂ := sqrt_pos.mpr (by positivity)
  have hden₁ : 0 < γ_k + D₁ := by linarith
  have hden₂ : 0 < γ_k + D₂ := by linarith
  rw [div_lt_div_iff₀ hden₁ hden₂]
  have hD₁_sq : D₁ ^ 2 = γ_k ^ 2 + K ^ 2 * r₁ ^ 2 := sq_sqrt (by positivity)
  have hD₂_sq : D₂ ^ 2 = γ_k ^ 2 + K ^ 2 * r₂ ^ 2 := sq_sqrt (by positivity)
  have h_sq : (r₁ * D₂) ^ 2 < (r₂ * D₁) ^ 2 := by
    calc (r₁ * D₂) ^ 2 = r₁ ^ 2 * (γ_k ^ 2 + K ^ 2 * r₂ ^ 2) := by
          rw [mul_pow, hD₂_sq]
      _ < r₂ ^ 2 * (γ_k ^ 2 + K ^ 2 * r₁ ^ 2) := by
          nlinarith [sq_pos_of_pos hγ, sq_lt_sq' (by linarith) hr₁₂]
      _ = (r₂ * D₁) ^ 2 := by rw [mul_pow, hD₁_sq]
  have h_lt_mul : r₁ * D₂ < r₂ * D₁ :=
    lt_of_abs_lt (abs_lt_of_sq_lt_sq h_sq (by positivity))
  have h_γ : r₁ * γ_k < r₂ * γ_k := mul_lt_mul_of_pos_right hr₁₂ hγ
  nlinarith [mul_pos hK (sub_pos.mpr h_lt_mul), mul_pos hK (sub_pos.mpr h_γ)]

/-! ## Self-consistency map monotonicity -/

theorem sc_map_strictMono [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    ∫ ω, explicitEquil (γ ω) K r₁ ∂μ < ∫ ω, explicitEquil (γ ω) K r₂ ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  have h_pw : ∀ ω, (0 : ℝ) < explicitEquil (γ ω) K r₂ - explicitEquil (γ ω) K r₁ :=
    fun ω => sub_pos.mpr (explicitEquil_strictMono_r (γ ω) K (hγ_pos ω) hK hr₁ hr₁₂)
  have hf₁ := equil_integrable γ K r₁ hγ_pos hK hr₁ hγ_meas (μ := μ)
  have hf₂ := equil_integrable γ K r₂ hγ_pos hK hr₂ hγ_meas (μ := μ)
  have h_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (h_pw ω)) (hf₂.sub hf₁)).mpr (by
      rw [show Function.support _ = Set.univ from Set.ext fun ω => by
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (h_pw ω)]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hf₂ hf₁]

/-! ## Combined: fixed point is globally attracting -/

/-- **SELF-CONSISTENCY CONTRACTION.**
    The map Φ has exactly one fixed point r* in (0,1), and Φ maps every
    r ∈ (0,1) \ {r*} strictly closer to r*. -/
theorem sc_map_contraction [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_ne : r ≠ r_star) :
    |∫ ω, explicitEquil (γ ω) K r ∂μ - r_star| < |r - r_star| := by
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · have hΦ_gt := sc_map_exceeds_below γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h_lt
    have hΦ_lt : ∫ ω, explicitEquil (γ ω) K r ∂μ < r_star := by
      calc ∫ ω, explicitEquil (γ ω) K r ∂μ
          < ∫ ω, explicitEquil (γ ω) K r_star ∂μ :=
            sc_map_strictMono γ K hγ_pos hK hγ_level hr h_lt
        _ = r_star := hfp
    rw [abs_of_neg (sub_neg.mpr h_lt), abs_of_neg (sub_neg.mpr hΦ_lt)]
    linarith
  · have hΦ_lt := sc_map_below_above γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h_gt
    have hΦ_gt : r_star < ∫ ω, explicitEquil (γ ω) K r ∂μ := by
      calc r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ := hfp.symm
        _ < ∫ ω, explicitEquil (γ ω) K r ∂μ :=
            sc_map_strictMono γ K hγ_pos hK hγ_level hr_star h_gt
    rw [abs_of_pos (sub_pos.mpr h_gt), abs_of_pos (sub_pos.mpr hΦ_gt)]
    linarith

/-- **SLOPE CHARACTERIZATION of the transition.**
    The slope S(r) = Φ(r)/r equals 1 iff r = r*; S > 1 below r*, S < 1 above. -/
theorem slope_integral_characterization [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    (r < r_star ↔ 1 < ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ) ∧
    (r_star < r ↔ ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ < 1) ∧
    (r = r_star ↔ ∫ ω, K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2)) ∂μ = 1) := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hs_star := slope_integral_eq_one γ K r_star hγ_pos hK hr_star hγ_meas hfp
  refine ⟨⟨fun h => slope_integral_gt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h,
    fun h => ?_⟩, ⟨fun h => slope_integral_lt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h,
    fun h => ?_⟩, ⟨fun h => by rw [h]; exact hs_star, fun h => ?_⟩⟩
  · by_contra h_not; push Not at h_not
    rcases eq_or_lt_of_le h_not with heq | hgt
    · linarith [heq ▸ hs_star]
    · linarith [slope_integral_lt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp hgt]
  · by_contra h_not; push Not at h_not
    rcases eq_or_lt_of_le h_not with heq | hlt
    · linarith [heq ▸ hs_star]
    · linarith [slope_integral_gt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp hlt]
  · by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · linarith [slope_integral_gt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp hlt]
    · linarith [slope_integral_lt_one γ K r r_star hγ_pos hK hγ_level hr hr_star hfp hgt]

end
