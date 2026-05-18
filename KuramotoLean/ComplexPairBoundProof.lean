/-
  Complex OA Pair Bound — Fubini Approach
  =========================================
  V' = K(-r*/2·Qc + Dc/2·Sc) with complex pair integrand.
  The Fubini identity RsStar·Qc - Dc·Sc = (1/2)∫∫ I g₁g₂ is proved.
  The pointwise pair bound is FALSE; integral nonnegativity remains open.
  0 sorry.
-/

import KuramotoLean.ComplexOAPairBound
import KuramotoLean.ContinuumIdentity

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The pointwise V' bound is FALSE -/

theorem complex_pair_pointwise_false :
    ¬ ∀ (r_t r_star : ℝ) (z z_star : ℂ),
      (r_t - r_star) / 2 * (starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re -
        r_star / 2 * Complex.normSq (z - z_star) * (z + z_star).re ≤ 0 := by
  push Not
  exact ⟨-1, 1, 0, 1, by norm_num⟩

/-! ## Definitions -/

def complexVDerivIntegrand (K r_t r_star : ℝ) (z z_star : ℂ) : ℝ :=
  K * ((r_t - r_star) / 2 * (starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re -
    r_star / 2 * Complex.normSq (z - z_star) * (z + z_star).re)

def Qc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, Complex.normSq (z ω - z_star ω) * (z ω + z_star ω).re * g ω ∂μ

def Sc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re * g ω ∂μ

def Dc (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (starRingEnd ℂ (z ω - z_star ω)).re * g ω ∂μ

def RsStar (z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (z_star ω).re * g ω ∂μ

def complexPairIntegrand (z z_star : Ω → ℂ) (ω₁ ω₂ : Ω) : ℝ :=
  normSq (z ω₂ - z_star ω₂) * (z_star ω₁).re * (z ω₂ + z_star ω₂).re +
  normSq (z ω₁ - z_star ω₁) * (z_star ω₂).re * (z ω₁ + z_star ω₁).re -
  (z ω₁ - z_star ω₁).re * (starRingEnd ℂ (z ω₂ - z_star ω₂) * (1 - z ω₂ ^ 2)).re -
  (z ω₂ - z_star ω₂).re * (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re

/-! ## V' = K(-r*Qc/2 + DcSc/2) identity -/

private theorem complexVDerivIntegrand_expand (K r_t r_star : ℝ) (z z_star : ℂ)
    (g_val : ℝ) :
    complexVDerivIntegrand K r_t r_star z z_star * g_val =
    K * (r_t - r_star) / 2 *
      ((starRingEnd ℂ (z - z_star) * (1 - z ^ 2)).re * g_val) -
    K * r_star / 2 *
      (Complex.normSq (z - z_star) * (z + z_star).re * g_val) := by
  unfold complexVDerivIntegrand; ring

theorem complex_V_deriv_eq_QDS
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r_t r_star : ℝ)
    (h_op : r_t - r_star = Dc z z_star g μ)
    (h_int_Sc : Integrable
      (fun ω => (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re * g ω) μ)
    (h_int_Qc : Integrable
      (fun ω => Complex.normSq (z ω - z_star ω) * (z ω + z_star ω).re * g ω) μ) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ =
      K * (-r_star / 2 * Qc z z_star g μ +
           Dc z z_star g μ / 2 * Sc z z_star g μ) := by
  simp_rw [complexVDerivIntegrand_expand]
  rw [integral_sub (h_int_Sc.const_mul _) (h_int_Qc.const_mul _)]
  simp_rw [integral_const_mul]
  unfold Qc Sc
  rw [h_op]; ring

/-! ## Fubini identity: RsStar·Qc - Dc·Sc = (1/2)∫∫ pair -/

private theorem Dc_eq_re_integral (z z_star : Ω → ℂ) (g : Ω → ℝ) :
    Dc z z_star g μ = ∫ ω, (z ω - z_star ω).re * g ω ∂μ := by
  unfold Dc; rfl

private theorem inner_term12_complex (z z_star : Ω → ℂ) (g : Ω → ℝ)
    (h_Qc : Integrable
      (fun ω => normSq (z ω - z_star ω) * (z ω + z_star ω).re * g ω) μ)
    (h_Sc : Integrable
      (fun ω => (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re * g ω) μ)
    (ω₁ : Ω) :
    ∫ ω₂, ((z_star ω₁).re * (normSq (z ω₂ - z_star ω₂) * (z ω₂ + z_star ω₂).re * g ω₂) -
      (z ω₁ - z_star ω₁).re *
        ((starRingEnd ℂ (z ω₂ - z_star ω₂) * (1 - z ω₂ ^ 2)).re * g ω₂)) ∂μ =
    (z_star ω₁).re * Qc z z_star g μ -
    (z ω₁ - z_star ω₁).re * Sc z z_star g μ := by
  unfold Qc Sc
  rw [integral_sub (h_Qc.const_mul _) (h_Sc.const_mul _)]
  simp_rw [integral_const_mul]

private theorem inner_term21_complex (z z_star : Ω → ℂ) (g : Ω → ℝ)
    (h_Rs : Integrable (fun ω => (z_star ω).re * g ω) μ)
    (h_Dc : Integrable (fun ω => (z ω - z_star ω).re * g ω) μ)
    (ω₁ : Ω) :
    ∫ ω₂, (normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
        ((z_star ω₂).re * g ω₂) -
      (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
        ((z ω₂ - z_star ω₂).re * g ω₂)) ∂μ =
    normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
      RsStar z_star g μ -
    (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
      Dc z z_star g μ := by
  unfold RsStar; rw [Dc_eq_re_integral (μ := μ)]
  rw [integral_sub (h_Rs.const_mul _) (h_Dc.const_mul _)]
  simp_rw [integral_const_mul]

theorem complex_pair_fubini_identity (z z_star : Ω → ℂ) (g : Ω → ℝ)
    (h_Qc : Integrable
      (fun ω => normSq (z ω - z_star ω) * (z ω + z_star ω).re * g ω) μ)
    (h_Sc : Integrable
      (fun ω => (starRingEnd ℂ (z ω - z_star ω) * (1 - z ω ^ 2)).re * g ω) μ)
    (h_Rs : Integrable (fun ω => (z_star ω).re * g ω) μ)
    (h_Dc : Integrable (fun ω => (z ω - z_star ω).re * g ω) μ) :
    ∫ ω₁, ∫ ω₂,
      complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ =
    2 * (RsStar z_star g μ * Qc z z_star g μ -
         Dc z z_star g μ * Sc z z_star g μ) := by
  have h12 := inner_term12_complex z z_star g h_Qc h_Sc
  have h21 := inner_term21_complex z z_star g h_Rs h_Dc
  have h_decomp : ∀ ω₁ ω₂,
      complexPairIntegrand z z_star ω₁ ω₂ * g ω₂ =
      ((z_star ω₁).re * (normSq (z ω₂ - z_star ω₂) * (z ω₂ + z_star ω₂).re * g ω₂) -
       (z ω₁ - z_star ω₁).re *
         ((starRingEnd ℂ (z ω₂ - z_star ω₂) * (1 - z ω₂ ^ 2)).re * g ω₂)) +
      (normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
         ((z_star ω₂).re * g ω₂) -
       (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
         ((z ω₂ - z_star ω₂).re * g ω₂)) := by
    intro ω₁ ω₂; unfold complexPairIntegrand; ring
  have h_inner : ∀ ω₁,
      ∫ ω₂, complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ =
      g ω₁ * ((z_star ω₁).re * Qc z z_star g μ -
               (z ω₁ - z_star ω₁).re * Sc z z_star g μ +
               normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
                 RsStar z_star g μ -
               (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
                 Dc z z_star g μ) := by
    intro ω₁
    have h_factor : ∀ ω₂,
        complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ =
        g ω₁ * (complexPairIntegrand z z_star ω₁ ω₂ * g ω₂) :=
      fun ω₂ => by ring
    simp_rw [h_factor, h_decomp, integral_const_mul]
    congr 1
    have hi12 : Integrable (fun ω₂ =>
        (z_star ω₁).re * (normSq (z ω₂ - z_star ω₂) * (z ω₂ + z_star ω₂).re * g ω₂) -
        (z ω₁ - z_star ω₁).re *
          ((starRingEnd ℂ (z ω₂ - z_star ω₂) * (1 - z ω₂ ^ 2)).re * g ω₂)) μ :=
      (h_Qc.const_mul _).sub (h_Sc.const_mul _)
    have hi21 : Integrable (fun ω₂ =>
        normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
          ((z_star ω₂).re * g ω₂) -
        (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
          ((z ω₂ - z_star ω₂).re * g ω₂)) μ :=
      (h_Rs.const_mul _).sub (h_Dc.const_mul _)
    rw [integral_add hi12 hi21, h12 ω₁, h21 ω₁]; ring
  simp_rw [h_inner]
  have h_outer_split : ∀ ω₁ : Ω,
      g ω₁ * ((z_star ω₁).re * Qc z z_star g μ -
               (z ω₁ - z_star ω₁).re * Sc z z_star g μ +
               normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re *
                 RsStar z_star g μ -
               (starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re *
                 Dc z z_star g μ) =
      (Qc z z_star g μ * ((z_star ω₁).re * g ω₁) -
       Sc z z_star g μ * ((z ω₁ - z_star ω₁).re * g ω₁)) +
      (RsStar z_star g μ *
         (normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re * g ω₁) -
       Dc z z_star g μ *
         ((starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re * g ω₁))
    := fun ω₁ => by ring
  simp_rw [h_outer_split]
  have hA : Integrable (fun ω₁ =>
      Qc z z_star g μ * ((z_star ω₁).re * g ω₁) -
      Sc z z_star g μ * ((z ω₁ - z_star ω₁).re * g ω₁)) μ :=
    (h_Rs.const_mul _).sub (h_Dc.const_mul _)
  have hB : Integrable (fun ω₁ =>
      RsStar z_star g μ * (normSq (z ω₁ - z_star ω₁) * (z ω₁ + z_star ω₁).re * g ω₁) -
      Dc z z_star g μ *
        ((starRingEnd ℂ (z ω₁ - z_star ω₁) * (1 - z ω₁ ^ 2)).re * g ω₁)) μ :=
    (h_Qc.const_mul _).sub (h_Sc.const_mul _)
  rw [integral_add hA hB,
      integral_sub (h_Rs.const_mul (Qc z z_star g μ))
                   (h_Dc.const_mul (Sc z z_star g μ)),
      integral_sub (h_Qc.const_mul (RsStar z_star g μ))
                   (h_Sc.const_mul (Dc z z_star g μ))]
  simp_rw [integral_const_mul]
  unfold RsStar Qc Sc
  rw [Dc_eq_re_integral (μ := μ)]
  ring

/-! ## Assembly: V' ≤ 0 -/

theorem complex_V_deriv_nonpos_of_pair_bound
    (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r_t r_star : ℝ)
    (hK : 0 < K)
    (hV_eq_QDS :
      ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ =
        K * (-r_star / 2 * Qc z z_star g μ + Dc z z_star g μ / 2 * Sc z z_star g μ))
    (h_pair_fubini :
      r_star * Qc z z_star g μ - Dc z z_star g μ * Sc z z_star g μ =
        (1 / 2) * ∫ ω₁, ∫ ω₂,
          complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ)
    (h_pair_nonneg :
      0 ≤ ∫ ω₁, ∫ ω₂,
        complexPairIntegrand z z_star ω₁ ω₂ * g ω₁ * g ω₂ ∂μ ∂μ) :
    ∫ ω, complexVDerivIntegrand K r_t r_star (z ω) (z_star ω) * g ω ∂μ ≤ 0 := by
  rw [hV_eq_QDS]
  have h_pair_rhs :
      0 ≤ r_star * Qc z z_star g μ - Dc z z_star g μ * Sc z z_star g μ := by
    rw [h_pair_fubini]
    nlinarith
  nlinarith

end
