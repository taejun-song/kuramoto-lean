/-
  Complex OA Per-Oscillator Error Identity
  ==========================================
  General identity (no equilibrium assumption):

    2·Re(conj(z-z*)·RHS(z)) = -K·Re(η·(z+z*))·|z-z*|²
                                + 2·Re(conj(z-z*)·RHS(z*))

  When z* is equilibrium (RHS(z*) = 0), the forcing vanishes:

    2·Re(conj(z-z*)·RHS(z)) = -K·Re(η·(z+z*))·|z-z*|²

  Consequence: V'(t) = -K·∫Re(η·(z+z*))·|z-z*|²·g + forcing.
-/

import KuramotoLean.ComplexOAEnergy
import KuramotoLean.ComplexLeibniz

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

lemma complexOaRHS_diff (ω K : ℝ) (η z z_star : ℂ) :
    complexOaRHS ω K η z - complexOaRHS ω K η z_star =
      (z - z_star) * (-(↑ω : ℂ) * Complex.I - ↑K / 2 * η * (z + z_star)) := by
  unfold complexOaRHS; ring

theorem complexOa_error_identity (ω K : ℝ) (η z z_star : ℂ)
    (hz_star : complexOaRHS ω K η z_star = 0) :
    2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K η z).re =
      -K * (η * (z + z_star)).re * Complex.normSq (z - z_star) := by
  have h := complexOaRHS_diff ω K η z z_star
  rw [hz_star, sub_zero] at h; rw [h]
  have hK_re : ((K : ℂ) / 2).re = K / 2 := by simp
  have hK_im : ((K : ℂ) / 2).im = 0 := by simp
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    hK_re, hK_im]
  ring

theorem complexOa_error_general (ω K : ℝ) (η z z_star : ℂ) :
    2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K η z).re =
      -K * (η * (z + z_star)).re * Complex.normSq (z - z_star) +
      2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K η z_star).re := by
  have h := complexOaRHS_diff ω K η z z_star
  have : complexOaRHS ω K η z =
      (z - z_star) * (-(↑ω : ℂ) * Complex.I - ↑K / 2 * η * (z + z_star)) +
      complexOaRHS ω K η z_star := sub_eq_iff_eq_add.mp h
  rw [this, mul_add, Complex.add_re, mul_comm 2]
  have hK_re : ((K : ℂ) / 2).re = K / 2 := by simp
  have hK_im : ((K : ℂ) / 2).im = 0 := by simp
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    hK_re, hK_im]
  ring

theorem basin_implies_re_pos (z z_star : ℂ)
    (h_re_star : 0 < z_star.re)
    (h_basin : Complex.normSq (z - z_star) < z_star.re ^ 2) :
    0 < z.re := by
  have h_re_sq : (z.re - z_star.re) ^ 2 ≤ Complex.normSq (z - z_star) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (z.im - z_star.im)]
  have h1 : (z.re - z_star.re) ^ 2 < z_star.re ^ 2 := lt_of_le_of_lt h_re_sq h_basin
  by_contra h_neg
  push_neg at h_neg
  nlinarith [sq_nonneg z.re, mul_nonpos_of_nonpos_of_nonneg h_neg (le_of_lt h_re_star)]

theorem basin_weight_bound (z z_star : ℂ)
    (h_re_star : 0 < z_star.re)
    (h_basin : Complex.normSq (z - z_star) < z_star.re ^ 2) :
    z_star.re < (z + z_star).re := by
  simp only [Complex.add_re]
  linarith [basin_implies_re_pos z z_star h_re_star h_basin]

lemma complexOaRHS_eta_diff (ω K : ℝ) (η₁ η₂ z : ℂ) :
    complexOaRHS ω K η₁ z - complexOaRHS ω K η₂ z =
      ↑K / 2 * (starRingEnd ℂ (η₁ - η₂) - (η₁ - η₂) * z ^ 2) := by
  unfold complexOaRHS
  rw [show starRingEnd ℂ (η₁ - η₂) = starRingEnd ℂ η₁ - starRingEnd ℂ η₂ from map_sub _ _ _]
  ring

theorem hasDerivAt_error_sq (z : ℝ → ℂ) (z_star η : ℂ) (ω_freq K : ℝ) (t : ℝ)
    (hz : HasDerivAt z (complexOaRHS ω_freq K η (z t)) t)
    (hz_star : complexOaRHS ω_freq K η z_star = 0) :
    HasDerivAt (fun s => Complex.normSq (z s - z_star))
      (-K * (η * (z t + z_star)).re * Complex.normSq (z t - z_star)) t :=
  (hasDerivAt_normSq_sub_const z z_star _ t hz).congr_deriv
    (complexOa_error_identity ω_freq K η (z t) z_star hz_star)

theorem hasDerivAt_error_sq_nonautonomous (z : ℝ → ℂ) (z_star η r_star : ℂ)
    (ω_freq K : ℝ) (t : ℝ)
    (hz : HasDerivAt z (complexOaRHS ω_freq K η (z t)) t)
    (hz_star : complexOaRHS ω_freq K r_star z_star = 0) :
    HasDerivAt (fun s => Complex.normSq (z s - z_star))
      (-K * (η * (z t + z_star)).re * Complex.normSq (z t - z_star) +
       2 * (starRingEnd ℂ (z t - z_star) * complexOaRHS ω_freq K η z_star).re) t := by
  have h_deriv := hasDerivAt_normSq_sub_const z z_star _ t hz
  have h_eq := complexOa_error_general ω_freq K η (z t) z_star
  exact h_deriv.congr_deriv h_eq

theorem forcing_eq_eta_diff (ω K : ℝ) (η r_star z_star : ℂ)
    (hz_star : complexOaRHS ω K r_star z_star = 0) :
    complexOaRHS ω K η z_star =
      ↑K / 2 * (starRingEnd ℂ (η - r_star) - (η - r_star) * z_star ^ 2) := by
  have h := complexOaRHS_eta_diff ω K η r_star z_star
  rwa [hz_star, sub_zero] at h

theorem error_deriv_neg_in_basin (ω_freq K r : ℝ) (z z_star : ℂ)
    (hK : 0 < K) (hr : 0 < r)
    (h_re_star : 0 < z_star.re)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (h_basin : Complex.normSq (z - z_star) < z_star.re ^ 2)
    (h_nz : z ≠ z_star) :
    -K * ((↑r : ℂ) * (z + z_star)).re * Complex.normSq (z - z_star) < 0 := by
  have h_weight : z_star.re < (z + z_star).re := basin_weight_bound z z_star h_re_star h_basin
  have h_nsq_pos : 0 < Complex.normSq (z - z_star) := by
    rwa [Complex.normSq_pos, sub_ne_zero]
  have h_re_pos : 0 < ((↑r : ℂ) * (z + z_star)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hr (by linarith)
  have h_prod := mul_pos (mul_pos hK h_re_pos) h_nsq_pos
  have : -K * ((↑r : ℂ) * (z + z_star)).re * Complex.normSq (z - z_star) =
    -(K * ((↑r : ℂ) * (z + z_star)).re * Complex.normSq (z - z_star)) := by ring
  linarith

end
