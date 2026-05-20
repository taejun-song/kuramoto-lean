/-
  Per-Oscillator Exponential Decay in the Basin
  ===============================================
  For a single oscillator with constant η = r > 0 and equilibrium z*
  with Re(z*) > 0:

  1. Original basin: |z(0)-z*|² < Re(z*)² → |z(t)-z*|² → 0
  2. General basin: any B > 0 with Re(z+z*) ≥ rate/(Kr) on the basin
  3. ω = 0 case: z* = 1, basin B = 2, covers z₀ = 0 (incoherence)

  0 sorry.
-/

import KuramotoLean.ComplexOAErrorIdentity
import KuramotoLean.GronwallBootstrap

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

theorem perOscillator_error_tendsto_zero
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ)
    (hK : 0 < K) (hr : 0 < r)
    (h_re_star : 0 < z_star.re)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (h_basin : Complex.normSq (z 0 - z_star) < z_star.re ^ 2) :
    Tendsto (fun t => Complex.normSq (z t - z_star)) atTop (nhds 0) := by
  apply gronwall_bootstrap_tendsto _ (z_star.re ^ 2) (K * r * z_star.re)
    (mul_pos (mul_pos hK hr) h_re_star) (by positivity) hz_cont
    (fun t _ => Complex.normSq_nonneg _) h_basin
  intro t ht hft
  have h_hd := hasDerivAt_error_sq z z_star (↑r) ω_freq K t
    (hz_ode t (le_of_lt ht)) hz_star
  refine ⟨?_, ?_⟩
  · rw [h_hd.deriv]; exact h_hd
  · rw [h_hd.deriv]
    have h_re : ((↑r : ℂ) * (z t + z_star)).re = r * (z t + z_star).re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [h_re]
    have h_weight := basin_weight_bound (z t) z_star h_re_star hft
    have h_nsq := Complex.normSq_nonneg (z t - z_star)
    nlinarith [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_of_lt h_weight) h_nsq)
      (le_of_lt (mul_pos hK hr))]

theorem perOscillator_error_decay_general
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ) (B rate : ℝ)
    (_hK : 0 < K) (_hr : 0 < r) (hB : 0 < B) (hrate : 0 < rate)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (h_weight : ∀ z', Complex.normSq (z' - z_star) < B →
        rate ≤ K * r * (z' + z_star).re)
    (h_basin : Complex.normSq (z 0 - z_star) < B) :
    Tendsto (fun t => Complex.normSq (z t - z_star)) atTop (nhds 0) := by
  apply gronwall_bootstrap_tendsto _ B rate hrate hB hz_cont
    (fun t _ => Complex.normSq_nonneg _) h_basin
  intro t ht hft
  have h_hd := hasDerivAt_error_sq z z_star (↑r) ω_freq K t
    (hz_ode t (le_of_lt ht)) hz_star
  refine ⟨?_, ?_⟩
  · rw [h_hd.deriv]; exact h_hd
  · rw [h_hd.deriv]
    have h_re : ((↑r : ℂ) * (z t + z_star)).re = r * (z t + z_star).re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [h_re]
    have h_w := h_weight (z t) hft
    have h_nsq := Complex.normSq_nonneg (z t - z_star)
    nlinarith

/-! ## ω = 0 case: global convergence from extended basin -/

theorem complexOaRHS_one_zero (K r : ℝ) :
    complexOaRHS 0 K (↑r) 1 = 0 := by
  unfold complexOaRHS; simp

theorem omega_zero_basin_weight (z : ℂ) (h : Complex.normSq (z - 1) < 2) :
    1 / 2 < (z + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  have h_re_sq : (z.re - 1) ^ 2 ≤ Complex.normSq (z - 1) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero]
    nlinarith [sq_nonneg z.im]
  have h_combined : (z.re - 1) ^ 2 < 2 := lt_of_le_of_lt h_re_sq h
  by_contra h_neg
  push Not at h_neg
  nlinarith [sq_nonneg (z.re + 1 / 2)]

theorem omega_zero_convergence
    (z : ℝ → ℂ) (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - 1)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS 0 K (↑r) (z t)) t)
    (h_basin : Complex.normSq (z 0 - 1) < 2) :
    Tendsto (fun t => Complex.normSq (z t - 1)) atTop (nhds 0) := by
  apply perOscillator_error_decay_general z 0 K r 1 2 (K * r / 2)
    hK hr (by norm_num) (by positivity) (complexOaRHS_one_zero K r)
    hz_cont hz_ode
  · intro z' hz'
    have h_w := omega_zero_basin_weight z' hz'
    simp only [Complex.add_re, Complex.one_re] at h_w ⊢
    nlinarith [mul_pos hK hr]
  · exact h_basin

theorem incoherence_in_omega_zero_basin :
    Complex.normSq ((0 : ℂ) - 1) < 2 := by
  simp [Complex.normSq_apply, Complex.one_re, Complex.one_im]

theorem near_incoherence_in_basin (z_star : ℂ)
    (h_ns : Complex.normSq z_star = 1) :
    Complex.normSq (0 - z_star) < 2 := by
  rw [zero_sub]
  have h : Complex.normSq (-z_star) = Complex.normSq z_star := by
    simp only [Complex.normSq_apply, Complex.neg_re, Complex.neg_im]; ring
  rw [h, h_ns]; norm_num

/-! ## Strongly locked oscillators: convergence from incoherence -/

theorem re_from_normSq_bound (z z_star : ℂ)
    (h : Complex.normSq (z - z_star) < 2) :
    z_star.re - 3 / 2 < z.re := by
  have h_re_sq : (z.re - z_star.re) ^ 2 ≤ Complex.normSq (z - z_star) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (z.im - z_star.im)]
  by_contra h_neg
  push Not at h_neg
  nlinarith [sq_nonneg (z.re - z_star.re + 3 / 2)]

theorem strongly_locked_convergence
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ)
    (hK : 0 < K) (hr : 0 < r)
    (h_re_34 : 3 / 4 < z_star.re)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (h_basin : Complex.normSq (z 0 - z_star) < 2) :
    Tendsto (fun t => Complex.normSq (z t - z_star)) atTop (nhds 0) := by
  apply perOscillator_error_decay_general z ω_freq K r z_star 2
    (K * r * (2 * z_star.re - 3 / 2))
    hK hr (by norm_num) (mul_pos (mul_pos hK hr) (by linarith))
    hz_star hz_cont hz_ode
  · intro z' hz'
    simp only [Complex.add_re]
    have := re_from_normSq_bound z' z_star hz'
    nlinarith [mul_pos hK hr]
  · exact h_basin

/-! ## Per-oscillator exponential bound (quantitative) -/

theorem perOscillator_exp_bound
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ) (B rate : ℝ)
    (_hK : 0 < K) (_hr : 0 < r) (hB : 0 < B) (hrate : 0 < rate)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (h_weight : ∀ z', Complex.normSq (z' - z_star) < B →
        rate ≤ K * r * (z' + z_star).re)
    (h_basin : Complex.normSq (z 0 - z_star) < B)
    (t : ℝ) (ht : 0 ≤ t) :
    Complex.normSq (z t - z_star) ≤
      Complex.normSq (z 0 - z_star) * Real.exp (-rate * t) := by
  let f := fun s => Complex.normSq (z s - z_star)
  have hf_deriv : ∀ s, 0 < s → f s < B →
      HasDerivAt f (deriv f s) s ∧ deriv f s ≤ -rate * f s := by
    intro s hs hfs
    have h_hd := hasDerivAt_error_sq z z_star (↑r) ω_freq K s
      (hz_ode s (le_of_lt hs)) hz_star
    have h_re : ((↑r : ℂ) * (z s + z_star)).re = r * (z s + z_star).re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    constructor
    · have h_eq := h_hd.deriv; rw [h_eq]; exact h_hd
    · have h_eq := h_hd.deriv; rw [h_eq, h_re]
      have h_w := h_weight (z s) hfs
      have h_nsq := Complex.normSq_nonneg (z s - z_star)
      nlinarith
  have hf_basin := basin_invariance f B rate hrate hB hz_cont
    (fun s _ => Complex.normSq_nonneg _) h_basin hf_deriv
  exact exp_decay_bound f B rate hrate hB hz_cont
    (fun s _ => Complex.normSq_nonneg _) h_basin hf_deriv hf_basin t ht

theorem locked_from_incoherence_convergence
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ) (B rate : ℝ)
    (_hK : 0 < K) (_hr : 0 < r) (hB : 1 < B) (hrate : 0 < rate)
    (h_ns : Complex.normSq z_star = 1)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (hz_init : z 0 = 0)
    (h_weight : ∀ z', Complex.normSq (z' - z_star) < B →
        rate ≤ K * r * (z' + z_star).re) :
    Tendsto (fun t => Complex.normSq (z t - z_star)) atTop (nhds 0) := by
  apply perOscillator_error_decay_general z ω_freq K r z_star B rate
    _hK _hr (by linarith) hrate hz_star hz_cont hz_ode h_weight
  rw [hz_init, zero_sub]
  have h1 : Complex.normSq (-z_star) = Complex.normSq z_star := by
    simp only [Complex.normSq_apply, Complex.neg_re, Complex.neg_im]; ring
  rw [h1, h_ns]; linarith

theorem re_from_normSq_bound_3_2 (z z_star : ℂ)
    (h : Complex.normSq (z - z_star) < 3 / 2) :
    z_star.re - 5 / 4 < z.re := by
  have h_re_sq : (z.re - z_star.re) ^ 2 ≤ Complex.normSq (z - z_star) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (z.im - z_star.im)]
  by_contra h_neg
  push_neg at h_neg
  nlinarith [sq_nonneg (z.re - z_star.re + 5 / 4)]

theorem weakly_locked_convergence
    (z : ℝ → ℂ) (ω_freq K r : ℝ) (z_star : ℂ)
    (hK : 0 < K) (hr : 0 < r)
    (h_re : 5 / 8 < z_star.re)
    (h_ns : Complex.normSq z_star = 1)
    (hz_star : complexOaRHS ω_freq K (↑r) z_star = 0)
    (hz_cont : Continuous (fun t => Complex.normSq (z t - z_star)))
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (↑r) (z t)) t)
    (hz_init : z 0 = 0) :
    Tendsto (fun t => Complex.normSq (z t - z_star)) atTop (nhds 0) := by
  apply locked_from_incoherence_convergence z ω_freq K r z_star (3 / 2)
    (K * r * (2 * z_star.re - 5 / 4))
    hK hr (by norm_num) (by nlinarith [mul_pos hK hr])
    h_ns hz_star hz_cont hz_ode hz_init
  intro z' hz'
  have h := re_from_normSq_bound_3_2 z' z_star hz'
  simp only [Complex.add_re]
  have h1 : 2 * z_star.re - 5 / 4 ≤ z'.re + z_star.re := by linarith
  exact mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hK hr))

end
