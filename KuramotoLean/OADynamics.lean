/-
  Kuramoto Stability Project — OA Dynamics
  ==========================================
  0 sorry.
-/

import KuramotoLean.GlobalMonotone

open Complex

noncomputable section

namespace OADyn

def oaVelocity (ω K : ℝ) (r α : ℂ) : ℂ :=
  -I * (ω : ℂ) * α + (↑(K / 2) : ℂ) * (r - starRingEnd ℂ r * α ^ 2)

theorem normSq_deriv_eq (ω K : ℝ) (r α : ℂ) :
    2 * (starRingEnd ℂ α * oaVelocity ω K r α).re =
    K * (starRingEnd ℂ r * α).re * (1 - Complex.normSq α) := by
  simp only [oaVelocity, starRingEnd_self_apply, Complex.normSq_apply, sq,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem barrier_at_boundary (ω K : ℝ) (r α : ℂ) (hα : Complex.normSq α = 1) :
    2 * (starRingEnd ℂ α * oaVelocity ω K r α).re = 0 := by
  have h := normSq_deriv_eq ω K r α
  simp only [hα, sub_self, mul_zero] at h
  exact h

end OADyn

end
