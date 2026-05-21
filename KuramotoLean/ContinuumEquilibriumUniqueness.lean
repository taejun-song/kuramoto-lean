/-
  Continuum Equilibrium Uniqueness
  =================================
  The self-consistency map Φ(r) = ∫ explicitEquil(γ(ω), K, r) dμ has at most
  one positive fixed point. This eliminates the hΦ_unique hypothesis for
  general frequency distributions.

  Key insight: explicitEquil(γ,K,r) = Kr/(γ+√(γ²+K²r²)) (rationalized).
  If Φ(r₁) = r₁ and Φ(r₂) = r₂ with 0 < r₁ < r₂:
    ∫ K/(γ(ω)+√(γ(ω)²+K²r₁²)) dμ = 1 = ∫ K/(γ(ω)+√(γ(ω)²+K²r₂²)) dμ
  But the LHS integrand is pointwise strictly larger, contradiction.

  0 sorry.
-/

import KuramotoLean.KuramotoContinuumSCFixedPoint
import KuramotoLean.ContinuumInstability

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Helpers -/

theorem slope_den_pos (γ_k : ℝ) (hγ : 0 < γ_k) (K r : ℝ) :
    (0 : ℝ) < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
  have := sqrt_nonneg (γ_k ^ 2 + K ^ 2 * r ^ 2); linarith

theorem explicitEquil_eq_slope_mul_r (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K)
    (hr : 0 < r) :
    explicitEquil γ_k K r = K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) * r := by
  rw [explicitEquil_rationalized γ_k K r hγ hK hr, div_mul_eq_mul_div, mul_comm K r]

theorem slope_pointwise_strictAnti (γ_k K : ℝ) (hγ : 0 < γ_k) (hK : 0 < K)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₁₂ : r₁ < r₂) :
    K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r₂ ^ 2)) <
    K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r₁ ^ 2)) := by
  have h_sq : γ_k ^ 2 + K ^ 2 * r₁ ^ 2 < γ_k ^ 2 + K ^ 2 * r₂ ^ 2 := by
    nlinarith [sq_pos_of_pos hK, sq_lt_sq' (by linarith) hr₁₂]
  exact div_lt_div_of_pos_left hK (slope_den_pos γ_k hγ K r₁)
    (by linarith [sqrt_lt_sqrt (by positivity : 0 ≤ γ_k ^ 2 + K ^ 2 * r₁ ^ 2) h_sq])

theorem slope_measurable (γ : Ω → ℝ) (K r : ℝ)
    (hγ_meas : Measurable γ) :
    Measurable (fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) :=
  measurable_const.div (hγ_meas.add
    (Real.continuous_sqrt.measurable.comp ((hγ_meas.pow_const 2).add measurable_const)))

theorem slope_le_inv_r (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    K / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) ≤ 1 / r := by
  apply (div_le_div_iff₀ (slope_den_pos γ_k hγ K r) hr).mpr
  have : K * r ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
    calc K * r = sqrt ((K * r) ^ 2) := (sqrt_sq (by positivity)).symm
      _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
        sqrt_le_sqrt (by nlinarith [sq_nonneg γ_k])
  linarith [hγ]

theorem slope_integrable [IsProbabilityMeasure μ] (γ : Ω → ℝ) (K r : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r) (hγ_meas : Measurable γ) :
    Integrable (fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))) μ := by
  apply (integrable_const (1 / r)).mono (slope_measurable γ K r hγ_meas).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hK (slope_den_pos (γ ω) (hγ_pos ω) K r)),
        Real.norm_eq_abs, abs_of_pos (div_pos one_pos hr)]
    exact slope_le_inv_r (γ ω) K r (hγ_pos ω) hK hr

/-! ## Main uniqueness theorem -/

theorem continuum_sc_fixed_point_unique [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : ∫ ω, explicitEquil (γ ω) K r₁ ∂μ = r₁)
    (h₂ : ∫ ω, explicitEquil (γ ω) K r₂ ∂μ = r₂) :
    r₁ = r₂ := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  set f := fun (r : ℝ) (ω : Ω) => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))
  have hf_int : ∀ r, 0 < r → Integrable (f r) μ :=
    fun r hr => slope_integrable γ K r hγ_pos hK hr hγ_meas
  have hslope_eq : ∀ r, 0 < r → ∫ ω, explicitEquil (γ ω) K r ∂μ = r →
      ∫ ω, f r ω ∂μ = 1 := by
    intro r hr hfp
    have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ = (∫ ω, f r ω ∂μ) * r := by
      have : (fun ω => explicitEquil (γ ω) K r) =
          fun ω => f r ω * r := by
        ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
      rw [this, integral_mul_const]
    rw [hfp] at h_eq
    exact mul_right_cancel₀ (ne_of_gt hr) (h_eq.symm.trans (one_mul r).symm)
  have hs₁ := hslope_eq r₁ hr₁ h₁
  have hs₂ := hslope_eq r₂ hr₂ h₂
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · exfalso
    have h_diff_pos : ∀ ω, (0 : ℝ) < f r₁ ω - f r₂ ω :=
      fun ω => sub_pos.mpr (slope_pointwise_strictAnti (γ ω) K (hγ_pos ω) hK
        (le_of_lt hr₁) h)
    have h_diff_int := (hf_int r₁ hr₁).sub (hf_int r₂ hr₂)
    have h_supp : 0 < μ (Function.support fun ω => f r₁ ω - f r₂ ω) := by
      rw [show Function.support (fun ω => f r₁ ω - f r₂ ω) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (h_diff_pos ω)]
      rw [measure_univ]; exact one_pos
    have h_pos := (integral_pos_iff_support_of_nonneg
      (fun ω => le_of_lt (h_diff_pos ω)) h_diff_int).mpr h_supp
    linarith [integral_sub (hf_int r₁ hr₁) (hf_int r₂ hr₂)]
  · exact h
  · exfalso
    have h_diff_pos : ∀ ω, (0 : ℝ) < f r₂ ω - f r₁ ω :=
      fun ω => sub_pos.mpr (slope_pointwise_strictAnti (γ ω) K (hγ_pos ω) hK
        (le_of_lt hr₂) h)
    have h_diff_int := (hf_int r₂ hr₂).sub (hf_int r₁ hr₁)
    have h_supp : 0 < μ (Function.support fun ω => f r₂ ω - f r₁ ω) := by
      rw [show Function.support (fun ω => f r₂ ω - f r₁ ω) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (h_diff_pos ω)]
      rw [measure_univ]; exact one_pos
    have h_pos := (integral_pos_iff_support_of_nonneg
      (fun ω => le_of_lt (h_diff_pos ω)) h_diff_int).mpr h_supp
    linarith [integral_sub (hf_int r₂ hr₂) (hf_int r₁ hr₁)]

/-! ## Eliminating hΦ_unique -/

theorem continuum_hPhi_unique [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (r_star : ℝ) (hr_star_pos : 0 < r_star)
    (hr_star_eq : r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ) :
    ∀ x, 0 < x → x ≤ 1 →
      (∫ ω, explicitEquil (γ ω) K x ∂μ) = x → x = r_star :=
  fun x hx _ hfp =>
    continuum_sc_fixed_point_unique γ K hγ_pos hK hγ_level x r_star hx hr_star_pos
      hfp hr_star_eq.symm

/-! ## No positive fixed point in subcritical regime -/

theorem continuum_no_fixed_point_subcritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K ≤ continuumKc γ μ)
    (r : ℝ) (hr : 0 < r) :
    (∫ ω, explicitEquil (γ ω) K r ∂μ) < r := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  set f := fun ω => K / (γ ω + sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2))
  have hf_int : Integrable f μ := slope_integrable γ K r hγ_pos hK hr hγ_meas
  have h_eq : ∫ ω, explicitEquil (γ ω) K r ∂μ = (∫ ω, f ω ∂μ) * r := by
    have : (fun ω => explicitEquil (γ ω) K r) = fun ω => f ω * r := by
      ext ω; exact explicitEquil_eq_slope_mul_r (γ ω) K r (hγ_pos ω) hK hr
    rw [this, integral_mul_const]
  rw [h_eq]
  suffices h : ∫ ω, f ω ∂μ < 1 by
    calc (∫ ω, f ω ∂μ) * r < 1 * r := mul_lt_mul_of_pos_right h hr
      _ = r := one_mul r
  have hf0_int : Integrable (fun ω => K / (2 * γ ω)) μ :=
    (h_inv_int.const_mul (K / 2)).congr (Eventually.of_forall fun ω => by ring)
  have hf_le_f0 : ∀ ω, f ω ≤ K / (2 * γ ω) := by
    intro ω
    exact div_le_div_of_nonneg_left (le_of_lt hK)
      (by linarith [hγ_pos ω])
      (by have : γ ω ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
            calc γ ω = sqrt ((γ ω) ^ 2) := (sqrt_sq (le_of_lt (hγ_pos ω))).symm
              _ ≤ sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
                sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
          linarith)
  have h_rhs : ∫ ω, K / (2 * γ ω) ∂μ = K / 2 * ∫ ω, 1 / γ ω ∂μ := by
    rw [← integral_const_mul]; congr 1; ext ω; ring
  have h_le_one : K / 2 * ∫ ω, 1 / γ ω ∂μ ≤ 1 := by
    unfold continuumKc at h_sub
    rw [le_div_iff₀ h_inv_pos] at h_sub; linarith
  have hf_strict : ∀ ω, f ω < K / (2 * γ ω) := by
    intro ω
    exact div_lt_div_of_pos_left hK (by linarith [hγ_pos ω])
      (by have : γ ω < sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) :=
            calc γ ω = sqrt ((γ ω) ^ 2) := (sqrt_sq (le_of_lt (hγ_pos ω))).symm
              _ < sqrt ((γ ω) ^ 2 + K ^ 2 * r ^ 2) := sqrt_lt_sqrt (sq_nonneg _)
                  (by nlinarith [mul_pos (sq_pos_of_pos hK) (sq_pos_of_pos hr)])
          linarith)
  have h_diff_int := hf0_int.sub hf_int
  have h_strict_pos := (integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (sub_pos.mpr (hf_strict ω))) h_diff_int).mpr (by
      rw [show Function.support (fun ω => K / (2 * γ ω) - f ω) = Set.univ from
        Set.ext fun ω => by
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact ne_of_gt (sub_pos.mpr (hf_strict ω))]
      rw [measure_univ]; exact one_pos)
  linarith [integral_sub hf0_int hf_int, h_rhs]

end
