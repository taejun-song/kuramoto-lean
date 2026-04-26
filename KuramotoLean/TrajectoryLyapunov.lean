/-
  Kuramoto Stability — Trajectory Lyapunov Bridge
  =================================================
  0 sorry.
-/

import KuramotoLean.ExponentialConvergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Real Finset

noncomputable section

variable {n : ℕ}

/-- Chain rule: d/dt[c_k(α_k(t)-α*_k)²] = c_k · 2(α_k-α*_k) · α'_k(t). -/
theorem hasDerivAt_l2_component (c_k α_star_k : ℝ) (α_k : ℝ → ℝ) (f_k : ℝ) (t : ℝ)
    (hα : HasDerivAt α_k f_k t) :
    HasDerivAt (fun s => c_k * (α_k s - α_star_k) ^ 2)
      (c_k * (2 * (α_k t - α_star_k) * f_k)) t := by
  have h1 : HasDerivAt (fun s => α_k s - α_star_k) f_k t := by
    have := hα.sub (hasDerivAt_const t α_star_k); simp only [sub_zero] at this; exact this
  have h2 : HasDerivAt (fun s => (α_k s - α_star_k) ^ 2)
      (2 * (α_k t - α_star_k) * f_k) t := by
    have := h1.mul h1; simp only [sq] at this ⊢; convert this using 1; ring
  exact h2.const_mul c_k

/-- **Chain rule for V**: d/dt[Σ c_k(α_k(t)-α*_k)²] along a differentiable trajectory. -/
theorem hasDerivAt_l2Distance_along
    (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (f : Fin n → ℝ) (t : ℝ)
    (hα : ∀ k, HasDerivAt (fun s => α s k) (f k) t) :
    HasDerivAt (fun s => l2Distance c (α s) α_star)
      (∑ k, c k * (2 * (α t k - α_star k) * f k)) t := by
  change HasDerivAt (fun s => ∑ k : Fin n, c k * (α s k - α_star k) ^ 2)
    (∑ k, c k * (2 * (α t k - α_star k) * f k)) t
  exact HasDerivAt.fun_sum (fun k _ => hasDerivAt_l2_component (c k) (α_star k)
    (fun s => α s k) (f k) t (hα k))

/-- **Trajectory derivative bound via L² exponential rate.**
    If α(t) solves the n-pole ODE with α_k ≥ δ > 0, then
    dV/dt ≤ -K·c_min·δ·(δ+δ*)·V. -/
theorem trajectory_lyapunov_bound
    (γ c : Fin n → ℝ) (K : ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (δ δ_star c_min : ℝ) (t : ℝ)
    (hK : 0 < K) (_hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα_pos : ∀ k, 0 < α t k) (hα_lt : ∀ k, α t k < 1)
    (hα_star_pos : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (hδ : 0 < δ) (hδ_star : 0 < δ_star) (hc_min : 0 < c_min)
    (hα_lb : ∀ k, δ ≤ α t k)
    (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hc_lb : ∀ k, c_min ≤ c k)
    (hα_deriv : ∀ k, HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t) :
    ∃ V'_t, HasDerivAt (fun s => l2Distance c (α s) α_star) V'_t t ∧
    V'_t ≤ -(K * c_min * δ * (δ + δ_star)) * l2Distance c (α t) α_star := by
  refine ⟨_, hasDerivAt_l2Distance_along c α α_star
    (fun k => nPoleODE γ c K (α t) k) t hα_deriv, ?_⟩
  have h := l2_exponential_rate γ c K (α t) α_star δ δ_star c_min
    hK _hγ hc hα_pos hα_lt
    hα_star_pos hα_star_lt h_equil hδ hδ_star hc_min hα_lb hα_star_lb hc_lb
  convert h using 1
  congr 1; ext k; ring

/-! ## Qualitative Lyapunov bound (no uniform lower bound)

The pair bound holds for ALL α ∈ (0,1)^n, not just α ≥ δ.
Combined with component_positive (ComponentBarrier.lean),
this gives dV/dt ≤ 0 along any trajectory starting in (0,1)^n. -/

/-- **Qualitative trajectory Lyapunov bound.**
    dV/dt ≤ 0 when α(t) ∈ (0,1)^n (no uniform lower bound δ needed). -/
theorem trajectory_lyapunov_qualitative
    (γ c : Fin n → ℝ) (K : ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ) (t : ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα_pos : ∀ k, 0 < α t k) (hα_lt : ∀ k, α t k < 1)
    (hα_star_pos : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (hα_deriv : ∀ k, HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t) :
    ∃ V'_t, HasDerivAt (fun s => l2Distance c (α s) α_star) V'_t t ∧ V'_t ≤ 0 := by
  refine ⟨_, hasDerivAt_l2Distance_along c α α_star
    (fun k => nPoleODE γ c K (α t) k) t hα_deriv, ?_⟩
  have h := l2_lyapunov_theorem γ c K (α t) α_star hK hγ hc hα_pos hα_lt
    hα_star_pos hα_star_lt h_equil
  convert h using 1
  congr 1; ext k; ring

end
