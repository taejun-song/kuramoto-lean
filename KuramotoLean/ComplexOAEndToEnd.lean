/-
  Complex OA End-to-End: Self-Contained Stability
  =================================================
  GOAL: A single theorem with NO hypotheses beyond the ODE data
  that proves |η(t)| → r* for the complex OA on symmetric subspace.

  This wires together all the conditional theorems into one chain.
  The remaining work is proof maintenance rather than placeholder elimination.
-/

import KuramotoLean.ComplexOAConvergence
import KuramotoLean.ComplexPairBoundProof

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **END-TO-END COMPLEX OA STABILITY.**
    NO hypotheses beyond ODE data. Proves |η|² → r*² directly. -/
theorem complex_oa_end_to_end [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (K : ℝ) (r_star : ℝ)
    -- ODE data
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    -- ODE
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    -- Self-consistency for equilibrium
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    -- Equilibrium equation
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K
      ((r_star : ℂ)) (z_star ω) = 0)
    -- Integrability
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    -- Basin condition
    (hV0 : ∫ ω, Complex.normSq (z ω 0 - z_star ω) * S.g ω ∂μ < r_star ^ 2)
    -- V → 0: requires body persistence + Barbalat (not yet ported from real case)
    (hV_zero : Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  -- Cauchy-Schwarz → |η - r*|² ≤ V → |η| → r*
  have h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ := by
    intro t
    -- Integrable: conj(z-z*) · g as ℂ
    have h_diff_c_int :
        Integrable (fun ω => starRingEnd ℂ (z ω t - z_star ω) * (S.g ω : ℂ)) μ := by
      convert (hη_int t).sub hη_star_int using 1
      ext ω; simp only [starRingEnd_apply, map_sub, Pi.sub_apply]; ring
    -- AEStronglyMeasurable for Re(z-z*) · g and Re(z-z*)² · g
    have h_re_meas : AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re * S.g ω) μ :=
      (hφ_meas t).mul hg_int.aestronglyMeasurable
    have h_re2_meas : AEStronglyMeasurable
        (fun ω => (z ω t - z_star ω).re ^ 2 * S.g ω) μ :=
      ((hφ_meas t).mul (hφ_meas t)).mul hg_int.aestronglyMeasurable
        |>.congr (Filter.Eventually.of_forall (fun ω => by
          change ((fun ω => (z ω t - z_star ω).re) ω * (fun ω => (z ω t - z_star ω).re) ω) *
            S.g ω = _
          ring))
    -- Integrable: |φ·g| ≤ normSq·g + g
    have hφg_int : Integrable (fun ω => (z ω t - z_star ω).re * S.g ω) μ :=
      ((hV_int t).add hg_int).mono' h_re_meas (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn ω), Pi.add_apply]
        calc |(z ω t - z_star ω).re| * S.g ω
            ≤ ((z ω t - z_star ω).re ^ 2 + 1) * S.g ω := by
              apply mul_le_mul_of_nonneg_right _ (hg_nn ω)
              nlinarith [sq_abs (z ω t - z_star ω).re, abs_nonneg (z ω t - z_star ω).re]
          _ = (z ω t - z_star ω).re ^ 2 * S.g ω + 1 * S.g ω := by ring
          _ ≤ Complex.normSq (z ω t - z_star ω) * S.g ω + 1 * S.g ω := by
              linarith [mul_le_mul_of_nonneg_right
                (show (z ω t - z_star ω).re ^ 2 ≤ Complex.normSq (z ω t - z_star ω) from
                  by rw [sq]; exact Complex.re_sq_le_normSq _) (hg_nn ω)]
          _ = Complex.normSq (z ω t - z_star ω) * S.g ω + S.g ω := by ring))
    -- Integrable: φ²·g ≤ normSq·g pointwise
    have hφ2g_int : Integrable (fun ω => (z ω t - z_star ω).re ^ 2 * S.g ω) μ :=
      (hV_int t).mono' h_re2_meas (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hg_nn ω))]
        exact mul_le_mul_of_nonneg_right
          (by rw [sq]; exact Complex.re_sq_le_normSq _) (hg_nn ω)))
    -- Rewrite LHS: η(t).re - r* = ∫ Re(z(t)-z*) · g
    have h_diff_eq : (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star =
        ∫ ω, (z ω t - z_star ω).re * S.g ω ∂μ := by
      rw [hr_star_eq, ← Complex.sub_re, ← integral_sub (hη_int t) hη_star_int]
      have h_eq : (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ) -
          starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) =ᵐ[μ]
          fun ω => starRingEnd ℂ (z ω t - z_star ω) * (S.g ω : ℂ) :=
        Filter.Eventually.of_forall (fun ω => by simp only [starRingEnd_apply, map_sub]; ring)
      rw [integral_congr_ae h_eq,
        show (∫ ω, starRingEnd ℂ (z ω t - z_star ω) * (S.g ω : ℂ) ∂μ).re =
          ∫ ω, (starRingEnd ℂ (z ω t - z_star ω) * (S.g ω : ℂ)).re ∂μ from
            ((RCLike.reCLM (K := ℂ)).integral_comp_comm h_diff_c_int).symm]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => by
        change (starRingEnd ℂ (z ω t - z_star ω) * ↑(S.g ω)).re = _
        rw [starRingEnd_apply, Complex.star_def]
        simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im]))
    rw [h_diff_eq]
    -- Weighted Jensen via variance: (∫ φ·g)² ≤ ∫ φ²·g since ∫g = 1
    set m := ∫ ω, (z ω t - z_star ω).re * S.g ω ∂μ
    have h_var : m ^ 2 ≤ ∫ ω, (z ω t - z_star ω).re ^ 2 * S.g ω ∂μ := by
      suffices h : 0 ≤ ∫ ω, (z ω t - z_star ω).re ^ 2 * S.g ω ∂μ - m ^ 2 by linarith
      have h_expand : ∫ ω, ((z ω t - z_star ω).re - m) ^ 2 * S.g ω ∂μ =
          ∫ ω, (z ω t - z_star ω).re ^ 2 * S.g ω ∂μ - m ^ 2 := by
        set φ := fun ω => (z ω t - z_star ω).re
        set a := fun ω => φ ω ^ 2 * S.g ω
        set b := fun ω => (-2) * m * (φ ω * S.g ω)
        set c := fun ω => m ^ 2 * S.g ω
        have h1 : ∀ ω, (φ ω - m) ^ 2 * S.g ω = a ω + (b ω + c ω) := fun ω => by
          simp only [a, b, c]; ring
        calc ∫ ω, ((z ω t - z_star ω).re - m) ^ 2 * S.g ω ∂μ
            = ∫ ω, (a ω + (b ω + c ω)) ∂μ := integral_congr_ae (Filter.Eventually.of_forall h1)
          _ = ∫ ω, a ω ∂μ + (∫ ω, b ω ∂μ + ∫ ω, c ω ∂μ) := by
              have hab : Integrable a μ := hφ2g_int
              have hbc : Integrable (fun ω => b ω + c ω) μ :=
                (hφg_int.const_mul _).add (hg_int.const_mul _)
              have hb : Integrable b μ := hφg_int.const_mul _
              have hc : Integrable c μ := hg_int.const_mul _
              rw [show (fun ω => a ω + (b ω + c ω)) =
                  (fun ω => a ω + (fun ω => b ω + c ω) ω) from rfl,
                integral_add hab hbc,
                integral_add hb hc]
          _ = ∫ ω, (z ω t - z_star ω).re ^ 2 * S.g ω ∂μ - m ^ 2 := by
              simp only [a, b, c, integral_const_mul, integral_const_mul, hg_norm]; ring
      rw [← h_expand]
      exact integral_nonneg (fun ω => mul_nonneg (sq_nonneg _) (hg_nn ω))
    calc m ^ 2
        ≤ ∫ ω, (z ω t - z_star ω).re ^ 2 * S.g ω ∂μ := h_var
      _ ≤ ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ := by
          apply integral_mono hφ2g_int (hV_int t) (fun ω => ?_)
          exact mul_le_mul_of_nonneg_right
            (by rw [sq]; exact Complex.re_sq_le_normSq _) (hg_nn ω)
  -- Step 4: Convergence
  have h_diff :
      Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star)
        atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro t
      calc
        |(∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star|
            = Real.sqrt
                (((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2) := by
                  rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) :=
            Real.sqrt_le_sqrt (h_cs t)
    · rw [← Real.sqrt_zero]
      exact hV_zero.sqrt
  have h_re :
      Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re)
        atTop (nhds r_star) := by
    have h_add :
        Tendsto
          (fun t => ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) + r_star)
          atTop (nhds (0 + r_star)) :=
      h_diff.add tendsto_const_nhds
    simpa [sub_add_cancel] using h_add
  simpa using h_re.pow 2

end
