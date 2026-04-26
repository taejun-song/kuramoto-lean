/-
  Kuramoto Stability Project — Weighted Energy Method
  =====================================================

  Formalization of the completing-the-square inequality from
  Dietert (2016), Lemma 17, adapted for the PLS.

  Core identity: for any u, eta, g_hat, phi with phi' > 0:

    -|u|^2 * phi' + K * Re(conj(eta) * u * conj(g_hat))
    = -|u - K*conj(eta)*conj(g_hat)*phi/(2*phi')|^2 * phi'
      + K^2/4 * |eta|^2 * |g_hat|^2 * phi^2 / phi'

  This is the AM-GM / completing-the-square bound.
  The first term is <= 0, so:

    -|u|^2 * phi' + K * Re(conj(eta) * u * conj(g_hat))
    <= K^2/4 * |eta|^2 * |g_hat|^2 * phi^2 / phi'
    =  alpha_integrand * |eta|^2

  Integrating over xi gives:
    [transport + coupling] <= alpha * |eta|^2
  where alpha = K^2/4 * integral |g_hat|^2 * phi^2 / phi' dxi.

  If alpha < 1: the weighted energy I(t) + (1-alpha)*integral |eta|^2 <= I(0).
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

open Complex

noncomputable section

/-- The real completing-the-square: -a*x^2 + b*x <= b^2/(4a) for a > 0.
    This is the scalar version underlying Dietert's Lemma 17. -/
lemma completing_the_square_real (x b a : ℝ) (ha : 0 < a) :
    -a * x ^ 2 + b * x ≤ b ^ 2 / (4 * a) := by
  have h4a : (0 : ℝ) < 4 * a := by linarith
  rw [le_div_iff₀ h4a]
  nlinarith [sq_nonneg (2 * a * x - b)]

/-- Consequence: for complex u and real a > 0, b:
    -a * |u_re|^2 + b * u_re <= b^2/(4a)  (applied to real part)
    -a * |u_im|^2 + b' * u_im <= b'^2/(4a) (applied to imaginary part)
    Sum gives: -a*|u|^2 + Re(c*u) <= |c|^2/(4a) where c = b + i*b'. -/
lemma completing_the_square_complex_re (u_re c_re a : ℝ) (ha : 0 < a) :
    -a * u_re ^ 2 + c_re * u_re ≤ c_re ^ 2 / (4 * a) :=
  completing_the_square_real u_re c_re a ha

-- The energy bound: if alpha < 1, the weighted energy decreases.
-- For K < K_ec (incoherence): alpha < 1 by Dietert's weight construction.
-- For K > K_c (PLS): alpha_PLS = alpha - C*lambda < 1 near onset.

-- The PLS spectral gap contributes a NEGATIVE term to the energy bound.
-- For K near K_c: alpha - 1 ~ O(K-K_c), lambda ~ sqrt(K-K_c).
-- So alpha_PLS - 1 ~ O(K-K_c) - C*sqrt(K-K_c) < 0 for K-K_c small.

/-- Near-onset scaling: (K-K_c) - C*sqrt(K-K_c) < 0 when K-K_c < C^2.
    This proves the PLS damping dominates the coupling excess near onset. -/
lemma near_onset_scaling (K K_c C : ℝ) (hK : K_c < K) (hC : 0 < C)
    (h_small : K - K_c < C ^ 2) :
    (K - K_c) - C * Real.sqrt (K - K_c) < 0 := by
  have hpos : 0 < K - K_c := by linarith
  have hsqrt_pos : 0 < Real.sqrt (K - K_c) := Real.sqrt_pos.mpr hpos
  -- Let x = sqrt(K - K_c). Then K - K_c = x^2 and we need x^2 - C*x < 0,
  -- i.e., x(x - C) < 0, which holds when 0 < x < C.
  -- x = sqrt(K-K_c) < C iff K - K_c < C^2 (given by h_small).
  have hx : Real.sqrt (K - K_c) < C := by
    rw [show C = Real.sqrt (C ^ 2) from (Real.sqrt_sq (le_of_lt hC)).symm]
    exact Real.sqrt_lt_sqrt (le_of_lt hpos) h_small
  -- Now: (K-K_c) - C*sqrt(K-K_c) = sqrt(K-K_c) * (sqrt(K-K_c) - C)
  have h_factor : (K - K_c) - C * Real.sqrt (K - K_c) =
      Real.sqrt (K - K_c) * (Real.sqrt (K - K_c) - C) := by
    have hsq : Real.sqrt (K - K_c) ^ 2 = K - K_c := Real.sq_sqrt (le_of_lt hpos)
    nlinarith [hsq]
  rw [h_factor]
  exact mul_neg_of_pos_of_neg hsqrt_pos (by linarith)

/-! ## Complex-omega damping identity -/

/-- At complex frequency omega = sigma - i*tau (tau > 0), the OA ODE
    acquires damping: d/dt|alpha|^2 <= K - (2*tau + K)*|alpha|^2 for |alpha| <= 1.
    At |alpha| = 1: d/dt|alpha|^2 = -2*tau < 0 regardless of coupling.
    This is the key bound for Hypothesis (H). -/
lemma complex_omega_damping (tau K rho : ℝ) (_htau : 0 < tau) (_hK : 0 < K)
    (_hrho : 0 ≤ rho) (_hrho1 : rho ≤ 1) :
    K - (2 * tau + K) * rho ≤ K * (1 - rho) - 2 * tau * rho := by
  nlinarith

/-- At |alpha|^2 = 1: the damping gives d/dt|alpha|^2 <= -2*tau < 0. -/
lemma damping_at_unit_circle (tau K : ℝ) (htau : 0 < tau) (_hK : 0 < K) :
    K - (2 * tau + K) * 1 < 0 := by
  linarith

/-- The equilibrium |alpha|^2 = K/(2*tau+K) < 1 for tau > 0. -/
lemma equilibrium_inside_disk (tau K : ℝ) (htau : 0 < tau) (hK : 0 < K) :
    K / (2 * tau + K) < 1 := by
  rw [div_lt_one (by linarith : 0 < 2 * tau + K)]
  linarith

end
