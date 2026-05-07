/-
  KuramotoContinuumSCFixedPoint.lean
  ====================================
  Continuum self-consistency fixed point: for K * ∫ (1/γ) dμ > 2,
  Φ(r) = ∫ explicitEquil(γ ω) K r ∂μ has a fixed point r* ∈ (0,1).

  Strategy:
  1. Φ continuous via DCT (bound 1, via explicitEquil_abs_le_one)
  2. Φ(1) < 1 via integral strict inequality
  3. Φ(r₀) > r₀ for small r₀: DCT limit ∫ K/(2γ+Kr) → (K/2)∫1/γ > 1,
     then lower bound explicitEquil_lower
  4. IVT on [r₀, 1]

  0 sorry.
-/

import KuramotoLean.SelfConsistencyFixedPoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Global absolute value bound -/

lemma explicitEquil_abs_le_one (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) :
    |explicitEquil γ_k K r| ≤ 1 := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have hrn : 0 < -r := by linarith
    have hsym : explicitEquil γ_k K r = -(explicitEquil γ_k K (-r)) := by
      unfold explicitEquil
      have h : (-r) ^ 2 = r ^ 2 := by ring
      rw [h]; ring
    rw [hsym, abs_neg, abs_of_pos (explicitEquil_pos γ_k K (-r) hγ hK hrn)]
    exact le_of_lt (explicitEquil_lt_one γ_k K (-r) hγ hK hrn)
  · simp [explicitEquil]
  · rw [abs_of_pos (explicitEquil_pos γ_k K r hγ hK hr)]
    exact le_of_lt (explicitEquil_lt_one γ_k K r hγ hK hr)

/-! ## Rationalized form holds for all r -/

private lemma explicitEquil_eq_rat_all (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) :
    explicitEquil γ_k K r = K * r / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [explicitEquil, sqrt_sq (le_of_lt hγ)]
  · unfold explicitEquil
    set S := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
    have hS_sq : S ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
    have hKr : K * r ≠ 0 := mul_ne_zero (ne_of_gt hK) hr
    have hden : γ_k + S ≠ 0 :=
      ne_of_gt (by have := sqrt_nonneg (γ_k ^ 2 + K ^ 2 * r ^ 2); linarith)
    rw [div_eq_div_iff hKr hden]
    have h1 : (-γ_k + S) * (γ_k + S) = S ^ 2 - γ_k ^ 2 := by ring
    have h2 : K * r * (K * r) = K ^ 2 * r ^ 2 := by ring
    linarith [h1, h2, hS_sq]

/-! ## explicitEquil continuous in r -/

private lemma explicitEquil_cont_in_r (γ_k K : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) :
    Continuous (fun r => explicitEquil γ_k K r) := by
  have heq : ∀ r, explicitEquil γ_k K r = K * r / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) :=
    fun r => explicitEquil_eq_rat_all γ_k K r hγ hK
  simp_rw [heq]
  apply Continuous.div
  · exact continuous_const.mul continuous_id
  · exact continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.add (continuous_const.mul (continuous_pow 2))))
  · intro r; exact ne_of_gt (by have := sqrt_nonneg (γ_k ^ 2 + K ^ 2 * r ^ 2); linarith)

/-! ## Main theorem -/

theorem sc_fixed_point_exists_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (hK_crit : 2 < K * ∫ ω, 1 / γ ω ∂μ) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hKinv_int : Integrable (fun ω => K / (2 * γ ω)) μ :=
    (h_inv_int.const_mul (K / 2)).congr (Eventually.of_forall fun ω => by ring)
  set Φ : ℝ → ℝ := fun r => ∫ ω, explicitEquil (γ ω) K r ∂μ
  -- Measurability: fun ω => explicitEquil (γ ω) K r
  have hF_meas : ∀ r, AEStronglyMeasurable (fun ω => explicitEquil (γ ω) K r) μ := fun r => by
    have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
      unfold explicitEquil; apply Continuous.div_const
      exact continuous_neg.add (Real.continuous_sqrt.comp ((continuous_pow 2).add continuous_const))
    exact (hc.measurable.comp hγ_meas).aestronglyMeasurable
  -- Integrability for each r
  have hInt_r : ∀ r, Integrable (fun ω => explicitEquil (γ ω) K r) μ := fun r =>
    (integrable_const (1 : ℝ)).mono (hF_meas r)
      (Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs, norm_one]
        exact explicitEquil_abs_le_one (γ ω) K r (hγ_pos ω) hK)
  -- Step 1: Φ continuous via DCT
  have hΦ_cont : Continuous Φ := continuous_of_dominated (bound := fun _ => (1 : ℝ))
    hF_meas
    (fun r => Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, norm_one]
      exact explicitEquil_abs_le_one (γ ω) K r (hγ_pos ω) hK)
    (integrable_const 1)
    (Eventually.of_forall fun ω => explicitEquil_cont_in_r (γ ω) K (hγ_pos ω) hK)
  -- Step 2: Φ(1) < 1
  have hΦ_1_lt : Φ 1 < 1 := by
    have h_lt : ∀ ω, explicitEquil (γ ω) K 1 < 1 :=
      fun ω => explicitEquil_lt_one (γ ω) K 1 (hγ_pos ω) hK one_pos
    have h_diff_int : Integrable (fun ω => 1 - explicitEquil (γ ω) K 1) μ :=
      (integrable_const 1).sub (hInt_r 1)
    have h_nn : ∀ ω, (0 : ℝ) ≤ 1 - explicitEquil (γ ω) K 1 :=
      fun ω => le_of_lt (by linarith [h_lt ω])
    have h_supp : 0 < μ (Function.support fun ω => 1 - explicitEquil (γ ω) K 1) := by
      rw [show Function.support (fun ω => 1 - explicitEquil (γ ω) K 1) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (by linarith [h_lt ω])]
      rw [measure_univ]; exact one_pos
    have h_pos : 0 < ∫ ω, (1 - explicitEquil (γ ω) K 1) ∂μ :=
      (integral_pos_iff_support_of_nonneg h_nn h_diff_int).mpr h_supp
    have heq := integral_sub (integrable_const (1 : ℝ)) (hInt_r 1)
    simp only [integral_const, smul_eq_mul, mul_one, probReal_univ] at heq
    linarith
  -- Step 3: DCT limit for lower bound slope
  have hslope_lim : K / 2 * ∫ ω, 1 / γ ω ∂μ > 1 := by linarith
  have hDCT : Tendsto (fun r => ∫ ω, K / (2 * γ ω + K * r) ∂μ)
      (nhdsWithin 0 (Ioi 0)) (nhds (K / 2 * ∫ ω, 1 / γ ω ∂μ)) := by
    have hlim_val : K / 2 * ∫ ω, 1 / γ ω ∂μ = ∫ ω, K / (2 * γ ω) ∂μ := by
      rw [← integral_const_mul]; congr 1; ext ω; ring
    rw [hlim_val]
    apply tendsto_integral_filter_of_dominated_convergence (fun ω => K / (2 * γ ω))
    · apply Eventually.of_forall; intro r
      have hm : Measurable (fun ω => K / (2 * γ ω + K * r)) :=
        measurable_const.div
          ((continuous_const.mul continuous_id |>.add continuous_const).measurable.comp hγ_meas)
      exact hm.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r (hr : r ∈ Ioi 0)
      apply Eventually.of_forall; intro ω
      have hr_pos : (0 : ℝ) < r := hr
      have hd2 : 0 < 2 * γ ω + K * r := by linarith [hγ_pos ω, mul_pos hK hr_pos]
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hK hd2)]
      exact div_le_div_of_nonneg_left (le_of_lt hK) (by linarith [hγ_pos ω])
        (by linarith [mul_pos hK hr_pos])
    · exact hKinv_int
    · apply Eventually.of_forall; intro ω
      have hcont : ContinuousAt (fun r : ℝ => K / (2 * γ ω + K * r)) 0 :=
        ContinuousAt.div continuousAt_const
          (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
          (by simp only [mul_zero, add_zero]; exact ne_of_gt (by linarith [hγ_pos ω]))
      have htend := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simp only [mul_zero, add_zero] at htend
      exact htend
  -- Extract r₀ with ∫ K/(2γ+Kr₀) dμ > 1
  have h_gt : ∀ᶠ r in nhdsWithin 0 (Ioi 0), 1 < ∫ ω, K / (2 * γ ω + K * r) ∂μ :=
    hDCT.eventually (Ioi_mem_nhds hslope_lim)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_gt
  obtain ⟨ε, hε_pos, hε⟩ := h_gt
  set r₀ := min (ε / 2) (1 / 2) with hr₀_def
  have hr₀_pos : 0 < r₀ := lt_min (by linarith) (by norm_num)
  have hr₀_lt : r₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hr₀_slope : 1 < ∫ ω, K / (2 * γ ω + K * r₀) ∂μ :=
    hε
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hr₀_pos];
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
      (Set.mem_Ioi.mpr hr₀_pos)
  -- Integrability of lower bound integrand
  have hlb_int : Integrable (fun ω => K * r₀ / (2 * γ ω + K * r₀)) μ := by
    apply (integrable_const (1 : ℝ)).mono
    · exact (measurable_const.div
        ((continuous_const.mul continuous_id |>.add continuous_const).measurable.comp
          hγ_meas)).aestronglyMeasurable
    · apply Eventually.of_forall; intro ω
      have hd : 0 < 2 * γ ω + K * r₀ := by linarith [hγ_pos ω, mul_pos hK hr₀_pos]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (le_of_lt hd)), norm_one]
      exact (div_le_one hd).mpr (by linarith [hγ_pos ω])
  -- Step 4: Φ(r₀) > r₀
  have hΦ_r₀_gt : r₀ < Φ r₀ :=
    calc r₀ = r₀ * 1 := (mul_one _).symm
      _ < r₀ * ∫ ω, K / (2 * γ ω + K * r₀) ∂μ :=
          mul_lt_mul_of_pos_left hr₀_slope hr₀_pos
      _ = ∫ ω, K * r₀ / (2 * γ ω + K * r₀) ∂μ := by
          rw [← integral_const_mul]; congr 1; ext ω; ring
      _ ≤ Φ r₀ := integral_mono hlb_int (hInt_r r₀)
          (fun ω => explicitEquil_lower (γ ω) K r₀ (hγ_pos ω) hK hr₀_pos)
  -- Step 5: IVT on [r₀, 1]
  set hfn := fun r => Φ r - r
  have hhfn_cont : Continuous hfn := hΦ_cont.sub continuous_id
  obtain ⟨r_star, hr_mem, hr_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr (le_of_lt hr₀_lt))
      (right_mem_Icc.mpr (le_of_lt hr₀_lt))
      continuousOn_const hhfn_cont.continuousOn
      (le_of_lt (sub_pos.mpr hΦ_r₀_gt))
      (le_of_lt (sub_neg.mpr hΦ_1_lt))
  obtain ⟨hr_lo, hr_hi⟩ := mem_Icc.mp hr_mem
  have hr_eq' : Φ r_star = r_star := sub_eq_zero.mp hr_eq.symm
  refine ⟨r_star, lt_of_lt_of_le hr₀_pos hr_lo, ?_, hr_eq'.symm⟩
  rcases lt_or_eq_of_le hr_hi with h_lt | h_eq
  · exact h_lt
  · exfalso; rw [← h_eq] at hΦ_1_lt; linarith [hr_eq']

end
