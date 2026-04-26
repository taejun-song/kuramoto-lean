/-
  Kuramoto Stability — Multiplicative V-Drop from Component Lower Bounds
  ========================================================================

  When all components α_k ≥ β > 0 on an interval [a, a+Δ], the uniform
  rate l2_uniform_rate gives dV/dt ≤ -μV, and comparison_decay_interval
  gives V(a+Δ) ≤ exp(-μΔ)·V(a).

  This is the key connection from component persistence (ComponentForwardInvariance)
  to the multiplicative drops needed by SelfContainedData.hdrops.

  0 sorry target.
-/

import KuramotoLean.GronwallBridge
import KuramotoLean.UniformRate

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-- **Multiplicative V-drop from component lower bounds.**
    When all α_k ≥ δ and α*_k ≥ δ* on [a, a+Δ], the L² Lyapunov function
    drops by factor exp(-K·δ·δ*·Δ). -/
theorem l2_drop_from_bounds
    (γ c : Fin n → ℝ) (K : ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (hα_star_lt : ∀ k, α_star k < 1)
    (δ δ_star : ℝ) (hδ : 0 < δ) (hδ_star : 0 < δ_star)
    (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hc_sum : ∑ k, c k = 1)
    (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : 0 ≤ Δ)
    (hα_lb : ∀ t, a ≤ t → t ≤ a + Δ → ∀ k, δ ≤ α t k)
    (hα_lt : ∀ t, a ≤ t → t ≤ a + Δ → ∀ k, α t k < 1)
    (hα_ode : ∀ t, a < t → ∀ k,
      HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t)
    (hV_cont : ContinuousOn (fun t => l2Distance c (α t) α_star) (Icc a (a + Δ))) :
    l2Distance c (α (a + Δ)) α_star ≤
      l2Distance c (α a) α_star * exp (-(K * δ * δ_star) * Δ) := by
  apply comparison_decay_interval
    (fun t => l2Distance c (α t) α_star)
    (fun t => ∑ k, c k * (2 * (α t k - α_star k) * nPoleODE γ c K (α t) k))
    (K * δ * δ_star) a Δ hΔ hV_cont
  · intro t ht_lo ht_hi
    exact hasDerivAt_l2Distance_along c α α_star
      (fun k => nPoleODE γ c K (α t) k) t (hα_ode t ht_lo)
  · intro t ht_lo ht_hi
    have h_rate := l2_uniform_rate γ c K (α t) α_star δ δ_star hK hγ hc
      (fun k => lt_of_lt_of_le hδ (hα_lb t (by linarith) (by linarith) k))
      (hα_lt t (by linarith) (by linarith))
      hα_star_pos hα_star_lt h_equil hδ hδ_star
      (hα_lb t (by linarith) (by linarith)) hα_star_lb hc_sum
    have h_eq : ∑ k, c k * (2 * (α t k - α_star k) *
        nPoleODE γ c K (α t) k) =
      ∑ k, c k * 2 * (α t k - α_star k) *
        nPoleODE γ c K (α t) k := by
      congr 1; ext k; ring
    rw [h_eq]
    linarith

end
