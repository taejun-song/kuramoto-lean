/-
  Kuramoto Stability — Explicit Convergence Rate
  ================================================
  Derives explicit convergence time bounds from exponential Lyapunov decay.

  Given V(t) ≤ V₀·exp(-μt) and (r-r*)² ≤ V(t):
    |r(t) - r*| ≤ √V₀ · exp(-μt/2)
    t > log(V₀/ε²)/μ ⟹ |r(t) - r*| < ε

  0 sorry.
-/

import KuramotoLean.GronwallBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Set Filter

noncomputable section

/-! ## Square root of exponential -/

private theorem sqrt_exp (x : ℝ) : √(exp x) = exp (x / 2) := by
  have h1 : exp x = exp (x / 2) * exp (x / 2) := by
    rw [← exp_add]; ring_nf
  rw [h1, ← sq, sqrt_sq (le_of_lt (exp_pos _))]

/-! ## Exponential decay of order parameter distance -/

theorem order_parameter_exp_decay (V r : ℝ → ℝ) (r_star V₀ μ : ℝ)
    (hV₀ : 0 ≤ V₀)
    (hV_decay : ∀ t, 0 ≤ t → V t ≤ V₀ * exp (-μ * t))
    (hr_sq : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    ∀ t, 0 ≤ t → |r t - r_star| ≤ √V₀ * exp (-μ / 2 * t) := by
  intro t ht
  have h1 : (r t - r_star) ^ 2 ≤ V₀ * exp (-μ * t) :=
    le_trans (hr_sq t) (hV_decay t ht)
  have h2 : |r t - r_star| ≤ √(V₀ * exp (-μ * t)) := by
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h1
  calc |r t - r_star|
      ≤ √(V₀ * exp (-μ * t)) := h2
    _ = √V₀ * √(exp (-μ * t)) := sqrt_mul hV₀ _
    _ = √V₀ * exp (-μ * t / 2) := by rw [sqrt_exp]
    _ = √V₀ * exp (-μ / 2 * t) := by ring_nf

/-! ## Absolute value from squared inequality -/

private theorem abs_lt_of_sq_lt (a b : ℝ) (hb : 0 < b) (h : a ^ 2 < b ^ 2) :
    |a| < b := by
  rw [← sqrt_sq_eq_abs, ← sqrt_sq hb.le]
  exact sqrt_lt_sqrt (sq_nonneg _) h

/-! ## Core lemma: exp decay below threshold -/

private theorem exp_decay_lt (V₀ μ t ε : ℝ)
    (hμ : 0 < μ) (hV₀ : 0 < V₀) (hε : 0 < ε)
    (htime : Real.log (V₀ / ε ^ 2) / μ < t) :
    V₀ * exp (-μ * t) < ε ^ 2 := by
  have hε2 := sq_pos_of_pos hε
  have hV₀_div := div_pos hV₀ hε2
  have hμt : Real.log (V₀ / ε ^ 2) < μ * t := by
    have := (div_lt_iff₀ hμ).mp htime; linarith
  have h_exp : V₀ / ε ^ 2 < exp (μ * t) :=
    exp_log hV₀_div ▸ exp_lt_exp.mpr hμt
  have h_bound : V₀ < exp (μ * t) * ε ^ 2 := (div_lt_iff₀ hε2).mp h_exp
  have h1 : V₀ * exp (-μ * t) < exp (μ * t) * ε ^ 2 * exp (-μ * t) :=
    mul_lt_mul_of_pos_right h_bound (exp_pos _)
  have h2 : exp (μ * t) * ε ^ 2 * exp (-μ * t) = ε ^ 2 := by
    rw [neg_mul, exp_neg]; field_simp
  linarith

/-! ## Explicit convergence time -/

theorem explicit_convergence_time (V r : ℝ → ℝ) (r_star V₀ μ ε : ℝ)
    (hμ : 0 < μ) (hV₀ : 0 < V₀) (hε : 0 < ε)
    (hV_decay : ∀ t, 0 ≤ t → V t ≤ V₀ * exp (-μ * t))
    (hr_sq : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    ∀ t, 0 ≤ t → Real.log (V₀ / ε ^ 2) / μ < t →
      |r t - r_star| < ε := by
  intro t ht htime
  exact abs_lt_of_sq_lt _ _ hε
    (lt_of_le_of_lt (le_trans (hr_sq t) (hV_decay t ht))
      (exp_decay_lt V₀ μ t ε hμ hV₀ hε htime))

/-! ## Wrapped with max for guaranteed non-negative time -/

theorem explicit_convergence_wrapped (V r : ℝ → ℝ) (r_star V₀ μ ε : ℝ)
    (hμ : 0 < μ) (hV₀ : 0 < V₀) (hε : 0 < ε)
    (hV_decay : ∀ t, 0 ≤ t → V t ≤ V₀ * exp (-μ * t))
    (hr_sq : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    ∀ t, max 0 (Real.log (V₀ / ε ^ 2) / μ + 1) ≤ t →
      |r t - r_star| < ε := by
  intro t ht
  exact explicit_convergence_time V r r_star V₀ μ ε hμ hV₀ hε hV_decay hr_sq t
    (le_trans (le_max_left _ _) ht)
    (by linarith [le_max_right 0 (Real.log (V₀ / ε ^ 2) / μ + 1)])

/-! ## Half-life of the Lyapunov function -/

theorem lyapunov_halflife (V₀ μ : ℝ) (hμ : 0 < μ) :
    V₀ * exp (-μ * (Real.log 2 / μ)) = V₀ / 2 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hsimp : -μ * (Real.log 2 / μ) = -Real.log 2 := by field_simp
  rw [hsimp, exp_neg, exp_log h2]; field_simp

/-! ## Convergence from exponential V-decay (explicit ∀ε ∃T form) -/

theorem order_parameter_convergence (V r : ℝ → ℝ) (r_star V₀ μ : ℝ)
    (hμ : 0 < μ) (hV₀ : 0 < V₀)
    (hV_decay : ∀ t, 0 ≤ t → V t ≤ V₀ * exp (-μ * t))
    (hr_sq : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |r t - r_star| < ε := by
  intro ε hε
  exact ⟨max 0 (Real.log (V₀ / ε ^ 2) / μ + 1),
    explicit_convergence_wrapped V r r_star V₀ μ ε hμ hV₀ hε hV_decay hr_sq⟩

end
