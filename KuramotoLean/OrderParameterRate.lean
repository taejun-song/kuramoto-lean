/-
  Kuramoto Stability — Order Parameter Convergence Rate
  ======================================================

  (r - r*)² ≤ V via weighted Cauchy-Schwarz.

  0 sorry.
-/

import KuramotoLean.UniformRate

noncomputable section

/-- **Weighted Cauchy-Schwarz.** (Σ c_k p_k)² ≤ (Σ c_k)(Σ c_k p_k²). -/
theorem weighted_cauchy_schwarz {n : ℕ} (c p : Fin n → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    (∑ k, c k * p k) ^ 2 ≤ (∑ k, c k) * (∑ k, c k * p k ^ 2) := by
  -- The square difference sum is non-negative
  have h_nn : 0 ≤ ∑ j, ∑ k, c j * c k * (p j - p k) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (hc j) (hc k)) (sq_nonneg _)
  -- Step 1: expand (p_j - p_k)² = p_j² + p_k² - 2p_jp_k
  have h_expand : ∑ j, ∑ k, c j * c k * (p j - p k) ^ 2 =
      (∑ j, ∑ k, c j * c k * (p j ^ 2 + p k ^ 2)) -
      (∑ j, ∑ k, 2 * (c j * p j) * (c k * p k)) := by
    have : ∀ j, (∑ k, c j * c k * (p j - p k) ^ 2) =
        (∑ k, c j * c k * (p j ^ 2 + p k ^ 2)) -
        (∑ k, 2 * (c j * p j) * (c k * p k)) := by
      intro j; rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
    simp_rw [this, Finset.sum_sub_distrib]
  -- Step 2: use full_pair_sum_identity
  have h_pair := full_pair_sum_identity c p
  -- Step 3: factor the cross term
  have h_cross : ∑ j, ∑ k, 2 * (c j * p j) * (c k * p k) =
      2 * (∑ j, c j * p j) * (∑ k, c k * p k) := by
    rw [show (2 : ℝ) * (∑ j, c j * p j) * (∑ k, c k * p k) =
      2 * ((∑ j, c j * p j) * (∑ k, c k * p k)) from by ring]
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]; congr 1; ext j
    rw [Finset.mul_sum]; congr 1; ext k; ring
  -- Combine
  rw [h_expand, h_pair, h_cross] at h_nn
  nlinarith

/-- **Order parameter bound.** (r - r*)² ≤ V for probability weights. -/
theorem order_parameter_sq_le_l2 {n : ℕ} (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hc_sum : ∑ k, c k = 1) :
    (∑ k, c k * (α k - α_star k)) ^ 2 ≤ l2Distance c α α_star := by
  have h := weighted_cauchy_schwarz c (fun k => α k - α_star k) hc
  rw [hc_sum, one_mul] at h; exact h

end
