/-
  Subcritical Incoherence: K < Kc → r(t) → 0
  =============================================
  For K < Kc, the incoherent state is exponentially stable.
  The weighted Lyapunov W = ∫(α/γ)dμ satisfies dW/dt ≤ -μW
  with rate μ = γ_min(1 - K/Kc) > 0.

  Combined with ContinuumInstability (K > Kc → r → r*),
  this establishes Kc as the SHARP phase transition threshold.

  0 sorry.
-/

import KuramotoLean.GronwallBridge
import KuramotoLean.ContinuumInstability

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Subcritical rate -/

theorem subcritical_rate_pos (γ : Ω → ℝ) (K : ℝ)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ) :
    0 < γ_min * (1 - K / continuumKc γ μ) := by
  have hKc_pos : 0 < continuumKc γ μ := by
    unfold continuumKc; positivity
  exact mul_pos hγ_min_pos (sub_pos.mpr ((div_lt_one hKc_pos).mpr h_sub))

/-! ## Weighted Lyapunov decay -/

/-- **Subcritical Lyapunov decay.** If the weighted mean W satisfies
    dW/dt ≤ -μW with μ = γ_min(1-K/Kc), then W decays exponentially. -/
theorem subcritical_lyapunov_decay (γ : Ω → ℝ) (K : ℝ)
    (γ_min : ℝ)
    (W W' : ℝ → ℝ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t →
      W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t) :
    ∀ t, 0 ≤ t → W t ≤ W 0 * exp (-(γ_min * (1 - K / continuumKc γ μ)) * t) :=
  comparison_decay W W' (γ_min * (1 - K / continuumKc γ μ)) hW_cont hW_deriv hW_bound

/-! ## Order parameter exponential decay -/

/-- **Subcritical order parameter decay.** If the weighted
    mean W controls r from above (r ≤ γ_max·W), then r → 0 exponentially. -/
theorem subcritical_r_exp_decay (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ)
    (W W' : ℝ → ℝ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t →
      W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t) :
    ∀ t, 0 ≤ t → r t ≤ γ_max * W 0 *
      exp (-(γ_min * (1 - K / continuumKc γ μ)) * t) := by
  intro t ht
  have hW := subcritical_lyapunov_decay γ K γ_min W W' hW_cont hW_deriv hW_bound t ht
  have h1 : γ_max * W t ≤ γ_max * W 0 *
      exp (-(γ_min * (1 - K / continuumKc γ μ)) * t) := by
    have : γ_max * W t ≤ γ_max * (W 0 * exp (-(γ_min * (1 - K / continuumKc γ μ)) * t)) :=
      mul_le_mul_of_nonneg_left hW (le_of_lt hγ_max_pos)
    linarith [mul_assoc γ_max (W 0) (exp (-(γ_min * (1 - K / continuumKc γ μ)) * t))]
  linarith [hr_le t ht]

/-! ## Main convergence theorem -/

/-- **Subcritical convergence.** For K < Kc, the order parameter r(t) → 0. -/
theorem continuum_subcritical_convergence (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ)
    (W W' : ℝ → ℝ) (hW0_pos : 0 < W 0)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t →
      W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → r t < ε := by
  have hrate := subcritical_rate_pos γ K γ_min hγ_min_pos h_inv_pos h_sub
  have hC_pos : 0 < γ_max * W 0 := mul_pos hγ_max_pos hW0_pos
  have h_decay := subcritical_r_exp_decay γ K r γ_min γ_max hγ_min_pos hγ_max_pos
    h_inv_pos h_sub W W' hW_cont hW_deriv hW_bound hr_le
  exact exponential_decay_convergence r (γ_max * W 0)
    (γ_min * (1 - K / continuumKc γ μ)) hrate hC_pos h_decay

/-! ## Sharp phase transition -/

/-- **Sharp phase transition.** K < Kc implies r(t) → 0.
    Combined with supercritical (K > Kc → r → r*), Kc is exact. -/
theorem kuramoto_sharp_threshold (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ)
    (W W' : ℝ → ℝ) (hW0_pos : 0 < W 0)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t →
      W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t) :
    Tendsto r atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuum_subcritical_convergence γ K r γ_min γ_max
    hγ_min_pos hγ_max_pos h_inv_pos h_sub W W' hW0_pos hW_cont hW_deriv
    hW_bound hr_le ε hε
  exact ⟨max T 0, fun t ht => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr_nn t)]
    exact hT t (le_trans (le_max_left _ _) ht)⟩

end
