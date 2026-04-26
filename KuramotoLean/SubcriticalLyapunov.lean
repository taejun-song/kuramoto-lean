/-
  Kuramoto Stability — Subcritical Lyapunov Bound
  =================================================
  Key algebraic inequality for subcritical convergence:
    Σ (c_k/γ_k)·f_k(α) ≤ r·(K/K_c - 1)

  0 sorry.
-/

import KuramotoLean.IncoherenceInstability

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Weighted ODE sum -/

theorem weighted_ode_identity (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) :
    ∑ k, c k / γ k * nPoleODE γ c K α k =
    -(∑ k, c k * α k) +
    (K / 2) * (∑ k, c k * α k) * ∑ k, c k / γ k * (1 - (α k) ^ 2) := by
  unfold nPoleODE
  have : ∀ k, c k / γ k * (-γ k * α k + K / 2 * (∑ j, c j * α j) * (1 - α k ^ 2)) =
    -(c k * α k) + K / 2 * (∑ j, c j * α j) * (c k / γ k * (1 - α k ^ 2)) := by
    intro k
    have hγk : γ k ≠ 0 := ne_of_gt (hγ k)
    field_simp [hγk]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]

theorem weighted_ode_le_r_gap (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hK : 0 ≤ K) (hn : Nonempty (Fin n))
    (hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ 1) :
    ∑ k, c k / γ k * nPoleODE γ c K α k ≤
    (∑ k, c k * α k) * ((K / 2) * (∑ k, c k / γ k) - 1) := by
  rw [weighted_ode_identity γ c K α hγ]
  have h_sq : ∀ k, c k / γ k * (1 - α k ^ 2) ≤ c k / γ k := by
    intro k
    have h1 : 1 - α k ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α k)]
    exact mul_le_of_le_one_right (div_nonneg (le_of_lt (hc k)) (le_of_lt (hγ k))) h1
  have hr_nn : 0 ≤ ∑ k, c k * α k :=
    sum_nonneg fun k _ => mul_nonneg (le_of_lt (hc k)) (hα_nn k)
  have hK2 : 0 ≤ K / 2 := by linarith
  have h_sum_le : ∑ k, c k / γ k * (1 - α k ^ 2) ≤ ∑ k, c k / γ k :=
    sum_le_sum fun k _ => h_sq k
  have h1 : (K / 2) * (∑ k, c k * α k) * ∑ k, c k / γ k * (1 - α k ^ 2) ≤
      (K / 2) * (∑ k, c k * α k) * ∑ k, c k / γ k :=
    mul_le_mul_of_nonneg_left h_sum_le (mul_nonneg hK2 hr_nn)
  linarith

end
