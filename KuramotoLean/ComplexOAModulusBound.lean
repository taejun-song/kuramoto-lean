/-
  Complex OA Modulus Bound
  =========================
  Given Re(η(t)·z(ω,t)) ≥ c > 0 on [0,T], the modulus |z(ω,t)|²
  converges exponentially to 1:

    1 - |z(ω,T)|² ≤ (1 - |z(ω,0)|²) · exp(-K·c·T)

  Proof: from d|z|²/dt = K·Re(ηz)·(1-|z|²) [ComplexOA.lean],
  the complementary gap u = 1-|z|² satisfies u' = -K·Re(ηz)·u ≤ -Kc·u.
  Gronwall comparison gives u(T) ≤ u(0)·exp(-KcT).

  0 sorry.
-/

import KuramotoLean.ComplexOAEnergy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

theorem hasDerivAt_one_sub_normSq (z : ℝ → ℂ) (z' : ℂ) (t : ℝ)
    (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => 1 - Complex.normSq (z s))
      (-(2 * (starRingEnd ℂ (z t) * z').re)) t := by
  have h1 := hasDerivAt_const t (1 : ℝ)
  have h2 := hasDerivAt_normSq_comp z z' t hz
  have h3 := h1.sub h2
  convert h3 using 1
  simp

theorem hasDerivAt_gap_of_ode (z : ℝ → ℂ) (ω K : ℝ) (η : ℂ) (t : ℝ)
    (hz : HasDerivAt z (complexOaRHS ω K η (z t)) t) :
    HasDerivAt (fun s => 1 - Complex.normSq (z s))
      (-(K * (η * z t).re * (1 - Complex.normSq (z t)))) t := by
  convert hasDerivAt_one_sub_normSq z _ t hz using 1
  have := complexOa_normSq_deriv ω K η (z t)
  linarith

private theorem exp_comparison (f : ℝ → ℝ) (rate : ℝ)
    (_ : 0 < rate)
    (hf_cont : Continuous f) (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hf_diff : ∀ t, 0 < t → HasDerivAt f (deriv f t) t)
    (hf_bound : ∀ t, 0 < t → deriv f t ≤ -rate * f t)
    (t : ℝ) (ht : 0 ≤ t) : f t ≤ f 0 * Real.exp (-rate * t) := by
  suffices h : f t * Real.exp (rate * t) ≤ f 0 by
    have key : Real.exp (rate * t) * Real.exp (-rate * t) = 1 := by
      rw [← Real.exp_add, show rate * t + -rate * t = 0 from by ring, Real.exp_zero]
    calc f t = f t * 1 := (mul_one _).symm
      _ = f t * (Real.exp (rate * t) * Real.exp (-rate * t)) := by rw [key]
      _ = f t * Real.exp (rate * t) * Real.exp (-rate * t) := (mul_assoc _ _ _).symm
      _ ≤ f 0 * Real.exp (-rate * t) :=
          mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos _))
  let g := fun s => f s * Real.exp (rate * s)
  suffices hg : AntitoneOn g (Icc 0 t) by
    exact hg (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht |>.trans_eq (by simp [g])
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
  · exact (hf_cont.mul (continuous_exp.comp (continuous_const.mul continuous_id'))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hf_diff x hx.1).mul
      ((hasDerivAt_const_mul rate (x := x)).exp)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hfd := hf_diff x hx.1
    have hd := hf_bound x hx.1
    have hexp_d : HasDerivAt (fun s => Real.exp (rate * s))
        (Real.exp (rate * x) * rate) x := (hasDerivAt_const_mul rate (x := x)).exp
    have hg_d := hfd.mul hexp_d
    have hg_eq : deriv g x = deriv f x * Real.exp (rate * x) +
        f x * (Real.exp (rate * x) * rate) := by
      have := hg_d.deriv; convert this using 1
    rw [hg_eq]
    nlinarith [hf_nn x (le_of_lt hx.1), Real.exp_pos (rate * x)]

theorem modulus_exp_convergence
    (z : ℝ → ℂ) (K c : ℝ) (ω_freq : ℝ) (η : ℝ → ℂ)
    (hK : 0 < K) (hc : 0 < c)
    (hz_cont : Continuous (fun t => Complex.normSq (z t)))
    (hz_disk : ∀ t, 0 ≤ t → Complex.normSq (z t) < 1)
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K (η t) (z t)) t)
    (h_re_bound : ∀ t, 0 ≤ t → c ≤ (η t * z t).re)
    (t : ℝ) (ht : 0 ≤ t) :
    1 - Complex.normSq (z t) ≤
      (1 - Complex.normSq (z 0)) * Real.exp (-(K * c) * t) := by
  let f := fun s => 1 - Complex.normSq (z s)
  have hf_cont : Continuous f := continuous_const.sub hz_cont
  have hf_nn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s hs =>
    le_of_lt (sub_pos.mpr (hz_disk s hs))
  have hf_diff : ∀ s, 0 < s → HasDerivAt f (deriv f s) s := by
    intro s hs
    have h := hasDerivAt_gap_of_ode z ω_freq K (η s) s (hz_ode s (le_of_lt hs))
    rw [h.deriv]
    exact h
  have hf_bound : ∀ s, 0 < s → deriv f s ≤ -(K * c) * f s := by
    intro s hs
    have h_gap := hasDerivAt_gap_of_ode z ω_freq K (η s) s (hz_ode s (le_of_lt hs))
    have hderiv_eq : deriv f s = -(K * (η s * z s).re * (1 - Complex.normSq (z s))) := by
      have := h_gap.deriv; convert this using 1
    rw [hderiv_eq]
    have h_pos : 0 < 1 - Complex.normSq (z s) := sub_pos.mpr (hz_disk s (le_of_lt hs))
    change -(K * (η s * z s).re * (1 - Complex.normSq (z s))) ≤
      -(K * c) * (1 - Complex.normSq (z s))
    have h_re := h_re_bound s (le_of_lt hs)
    have hKc_le : K * c ≤ K * (η s * z s).re :=
      mul_le_mul_of_nonneg_left h_re (le_of_lt hK)
    nlinarith [mul_le_mul_of_nonneg_right hKc_le (le_of_lt h_pos)]
  exact exp_comparison f (K * c) (mul_pos hK hc) hf_cont hf_nn hf_diff hf_bound t ht

private theorem exp_lower_bound (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 < M)
    (hf_cont : Continuous f) (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hf_diff : ∀ t, 0 < t → HasDerivAt f (deriv f t) t)
    (hf_bound : ∀ t, 0 < t → -M * f t ≤ deriv f t)
    (t : ℝ) (ht : 0 ≤ t) : f 0 * Real.exp (-M * t) ≤ f t := by
  suffices h : f 0 ≤ f t * Real.exp (M * t) by
    have key : Real.exp (M * t) * Real.exp (-M * t) = 1 := by
      rw [← Real.exp_add, show M * t + -M * t = 0 from by ring, Real.exp_zero]
    calc f 0 * Real.exp (-M * t)
        ≤ f t * Real.exp (M * t) * Real.exp (-M * t) :=
          mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos _))
      _ = f t * (Real.exp (M * t) * Real.exp (-M * t)) := by ring
      _ = f t * 1 := by rw [key]
      _ = f t := mul_one _
  let g := fun s => f s * Real.exp (M * s)
  suffices hg : MonotoneOn g (Icc 0 t) by
    have h := hg (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    simp only [g, mul_zero, Real.exp_zero, mul_one] at h
    exact h
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
  · exact (hf_cont.mul (continuous_exp.comp (continuous_const.mul continuous_id'))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hf_diff x hx.1).mul
      ((hasDerivAt_const_mul M (x := x)).exp)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hfd := hf_diff x hx.1
    have hd := hf_bound x hx.1
    have hexp_d : HasDerivAt (fun s => Real.exp (M * s))
        (Real.exp (M * x) * M) x := (hasDerivAt_const_mul M (x := x)).exp
    have hg_d := hfd.mul hexp_d
    have hg_eq : deriv g x = deriv f x * Real.exp (M * x) +
        f x * (Real.exp (M * x) * M) := by
      have := hg_d.deriv; convert this using 1
    rw [hg_eq]
    nlinarith [hf_nn x (le_of_lt hx.1), Real.exp_pos (M * x)]

theorem disk_invariant_frozen
    (z : ℝ → ℂ) (K : ℝ) (ω_freq : ℝ) (η : ℂ) (M : ℝ)
    (hK : 0 < K) (hM : 0 < M)
    (hz_cont : Continuous (fun t => Complex.normSq (z t)))
    (hz_disk : ∀ t, 0 ≤ t → Complex.normSq (z t) < 1)
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K η (z t)) t)
    (h_a_bound : ∀ t, 0 ≤ t → |K * (η * z t).re| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - Complex.normSq (z 0)) * Real.exp (-M * t) ≤ 1 - Complex.normSq (z t) := by
  let f := fun s => 1 - Complex.normSq (z s)
  have hf_cont : Continuous f := continuous_const.sub hz_cont
  have hf_nn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s hs =>
    le_of_lt (sub_pos.mpr (hz_disk s hs))
  have hf_diff : ∀ s, 0 < s → HasDerivAt f (deriv f s) s := by
    intro s hs
    have h := hasDerivAt_gap_of_ode z ω_freq K η s (hz_ode s (le_of_lt hs))
    rw [h.deriv]; exact h
  have hf_bound : ∀ s, 0 < s → -M * f s ≤ deriv f s := by
    intro s hs
    have h_gap := hasDerivAt_gap_of_ode z ω_freq K η s (hz_ode s (le_of_lt hs))
    have hderiv_eq : deriv f s = -(K * (η * z s).re * (1 - Complex.normSq (z s))) := by
      have := h_gap.deriv; convert this using 1
    rw [hderiv_eq]
    have h_pos : 0 ≤ 1 - Complex.normSq (z s) := hf_nn s (le_of_lt hs)
    have h_abs := h_a_bound s (le_of_lt hs)
    rw [abs_le] at h_abs
    nlinarith
  exact exp_lower_bound f M hM hf_cont hf_nn hf_diff hf_bound t ht

theorem disk_invariance_unconditional
    (z : ℝ → ℂ) (K : ℝ) (ω_freq : ℝ) (η : ℂ) (M : ℝ)
    (hK : 0 < K) (hM : 0 < M)
    (hz_cont : Continuous z)
    (hz_init : Complex.normSq (z 0) < 1)
    (hz_ode : ∀ t, 0 ≤ t → HasDerivAt z (complexOaRHS ω_freq K η (z t)) t)
    (h_a_bound : ∀ t, 0 ≤ t → |K * (η * z t).re| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Complex.normSq (z t) < 1 := by
  set u : ℝ → ℝ := fun s => 1 - Complex.normSq (z s)
  have hu_cont : Continuous u :=
    continuous_const.sub (Complex.continuous_normSq.comp hz_cont)
  have hu0 : 0 < u 0 := sub_pos.mpr hz_init
  set h : ℝ → ℝ := fun s => u s ^ 2
  have hh_cont : Continuous h := hu_cont.pow 2
  have hh0_pos : 0 < h 0 := sq_pos_of_pos hu0
  have hh_diff : ∀ s, 0 < s → HasDerivAt h (deriv h s) s := by
    intro s hs
    have hu_at := hasDerivAt_gap_of_ode z ω_freq K η s (hz_ode s (le_of_lt hs))
    have hh_at : HasDerivAt h (2 * u s ^ (2 - 1) * (-(K * (η * z s).re * u s))) s :=
      hu_at.fun_pow 2
    rw [hh_at.deriv]; exact hh_at
  have hh_bound : ∀ s, 0 < s → -(2 * M) * h s ≤ deriv h s := by
    intro s hs
    have hu_at := hasDerivAt_gap_of_ode z ω_freq K η s (hz_ode s (le_of_lt hs))
    have hh_at : HasDerivAt h (2 * u s ^ (2 - 1) * (-(K * (η * z s).re * u s))) s :=
      hu_at.fun_pow 2
    have hderiv_eq : deriv h s = 2 * u s ^ (2 - 1) * (-(K * (η * z s).re * u s)) :=
      hh_at.deriv
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hderiv_eq
    rw [hderiv_eq]
    have h_abs := h_a_bound s (le_of_lt hs)
    rw [abs_le] at h_abs
    nlinarith [sq_nonneg (u s)]
  have hh_lower : h 0 * Real.exp (-(2 * M) * t) ≤ h t :=
    exp_lower_bound h (2 * M) (by linarith) hh_cont (fun _ _ => sq_nonneg _) hh_diff hh_bound t ht
  have hu_ne : u t ≠ 0 := by
    intro heq
    have : h t = 0 := by simp only [h, heq, sq, mul_zero]
    linarith [mul_pos hh0_pos (Real.exp_pos (-(2 * M) * t))]
  suffices 0 < u t by linarith
  by_contra h_not
  push_neg at h_not
  have hut_neg : u t < 0 := lt_of_le_of_ne h_not hu_ne
  obtain ⟨c, hc, huc⟩ := isPreconnected_Icc.intermediate_value₂
    (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
    continuousOn_const hu_cont.continuousOn (le_of_lt hu0) (le_of_lt hut_neg)
  have hc_nn : 0 ≤ c := (mem_Icc.mp hc).1
  have huc_eq : u c = 0 := huc.symm
  have huc_sq : h c = 0 := by simp only [h, huc_eq, sq, mul_zero]
  have hh_lower_c := exp_lower_bound h (2 * M) (by linarith) hh_cont
    (fun _ _ => sq_nonneg _) hh_diff hh_bound c hc_nn
  linarith [mul_pos hh0_pos (Real.exp_pos (-(2 * M) * c))]

end
