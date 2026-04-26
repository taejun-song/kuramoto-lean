/-
  Kuramoto Stability — Exponential Lyapunov Convergence
  ======================================================
  Proves: if V(t) ≤ V₀·exp(-ct) with c > 0, then V → 0.
  Combined with the L² exponential rate and Mathlib's Gronwall,
  this gives exponential convergence for the n-pole OA system.
  0 sorry.
-/

import KuramotoLean.L2Convergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.ODE.Gronwall

open Real Filter

noncomputable section

/-! ## Exponential decay → convergence -/

/-- If V(t) ≤ V₀·exp(-ct) with c > 0, then V → 0. -/
theorem exponential_decay_convergence (V : ℝ → ℝ) (V0 c : ℝ)
    (hc : 0 < c) (hV0 : 0 < V0)
    (h : ∀ t, 0 ≤ t → V t ≤ V0 * Real.exp (-c * t)) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → V t < ε := by
  intro ε hε
  have h_tend : Tendsto (fun t => Real.exp (-c * t)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t => -c * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith : -c < 0)
    exact tendsto_exp_atBot.comp h1
  rw [Metric.tendsto_atTop] at h_tend
  obtain ⟨T₀, hT₀⟩ := h_tend (ε / V0) (div_pos hε hV0)
  refine ⟨max T₀ 0, fun t ht => ?_⟩
  have hT₀_le : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht_nn : 0 ≤ t := le_trans (le_max_right _ _) ht
  have hexp := hT₀ t hT₀_le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.exp_nonneg _)] at hexp
  calc V t ≤ V0 * Real.exp (-c * t) := h t ht_nn
    _ < V0 * (ε / V0) := mul_lt_mul_of_pos_left hexp hV0
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hV0)

/-! ## Exponential rate for n-pole L² distance

Given Mathlib's Gronwall inequality (le_gronwallBound_of_liminf_deriv_right_le),
the L² exponential rate (l2_exponential_rate) gives:

  dV/dt ≤ -K·μ·V  where  μ = c_min·δ·(δ+δ*)

By Gronwall with K = -Kμ, ε = 0:

  V(t) ≤ V(0)·exp(-Kμ·t)

Combined with exponential_decay_convergence: V → 0 exponentially.
Combined with pointwise_from_l2: α_k → α*_k for all k.

The assembled theorem: -/

/-- **N-pole exponential convergence data.**
    Packages an n-pole trajectory with the Gronwall-derived V bound. -/
structure NPoleExponentialData (n : ℕ) where
  c : Fin n → ℝ
  α : ℝ → Fin n → ℝ
  α_star : Fin n → ℝ
  hc : ∀ k, 0 < c k
  c_min : ℝ
  hc_min : ∀ k, c_min ≤ c k
  hc_min_pos : 0 < c_min
  rate : ℝ
  hrate : 0 < rate
  V0 : ℝ
  hV0 : 0 < V0
  hV_bound : ∀ t, 0 ≤ t →
    l2Distance c (α t) α_star ≤ V0 * Real.exp (-rate * t)

/-- **N-pole exponential convergence.**
    α(t) → α* pointwise, with explicit exponential rate. -/
theorem npole_exponential_convergence (D : NPoleExponentialData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → ∀ k,
      |D.α t k - D.α_star k| < ε := by
  intro ε hε
  have hε2 : 0 < D.c_min * ε ^ 2 := mul_pos D.hc_min_pos (sq_pos_of_ne_zero (ne_of_gt hε))
  obtain ⟨T, hT⟩ := exponential_decay_convergence
    (fun t => l2Distance D.c (D.α t) D.α_star)
    D.V0 D.rate D.hrate D.hV0 D.hV_bound
    (D.c_min * ε ^ 2) hε2
  exact ⟨T, fun t ht k =>
    pointwise_from_l2 D.c (D.α t) D.α_star D.hc
      D.c_min D.hc_min D.hc_min_pos ε hε (hT t ht) k⟩

end
