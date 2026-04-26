/-
  Kuramoto Stability — Bifurcation Monotonicity
  ===============================================
  The PLS order parameter r* is strictly increasing in coupling K.
  For K₁ > K₂ > K_c: r*(K₁) > r*(K₂).

  Key algebraic identity: K₂²D₁² - K₁²D₂² = γ²(K₂² - K₁²)
  where D_i = √(γ² + K_i²r²).

  0 sorry.
-/

import KuramotoLean.SelfConsistencyFixedPoint

open Real Set Finset

noncomputable section

variable {n : ℕ}

private theorem den_pos' (γ_k : ℝ) (hγ : 0 < γ_k) (K r : ℝ) :
    (0 : ℝ) < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
  have := sqrt_nonneg (γ_k ^ 2 + K ^ 2 * r ^ 2); linarith

private theorem summand_mono_K (γ_k K₁ K₂ r : ℝ)
    (hγ : 0 < γ_k) (hK₁ : 0 < K₁) (hr : 0 < r) (hK : K₁ < K₂) :
    K₁ / (γ_k + sqrt (γ_k ^ 2 + K₁ ^ 2 * r ^ 2)) <
    K₂ / (γ_k + sqrt (γ_k ^ 2 + K₂ ^ 2 * r ^ 2)) := by
  have hK₂ : 0 < K₂ := lt_trans hK₁ hK
  have hden₁ := den_pos' γ_k hγ K₁ r
  have hden₂ := den_pos' γ_k hγ K₂ r
  -- Cross-multiply: suffices K₁(γ+D₂) < K₂(γ+D₁)
  rw [div_lt_div_iff₀ hden₁ hden₂]
  have hD₁_sq : sqrt (γ_k ^ 2 + K₁ ^ 2 * r ^ 2) ^ 2 =
      γ_k ^ 2 + K₁ ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hD₂_sq : sqrt (γ_k ^ 2 + K₂ ^ 2 * r ^ 2) ^ 2 =
      γ_k ^ 2 + K₂ ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hD₁_nn := sqrt_nonneg (γ_k ^ 2 + K₁ ^ 2 * r ^ 2)
  have hD₂_nn := sqrt_nonneg (γ_k ^ 2 + K₂ ^ 2 * r ^ 2)
  set D₁ := sqrt (γ_k ^ 2 + K₁ ^ 2 * r ^ 2) with hD₁_def
  set D₂ := sqrt (γ_k ^ 2 + K₂ ^ 2 * r ^ 2) with hD₂_def
  have hK₂D₁_pos : 0 < K₂ * D₁ := by positivity
  have h_sq_diff : (K₁ * D₂) ^ 2 < (K₂ * D₁) ^ 2 := by
    have hK_sq : K₁ ^ 2 < K₂ ^ 2 := by nlinarith [mul_self_lt_mul_self (le_of_lt hK₁) hK]
    have hγ_sq : 0 < γ_k ^ 2 := sq_pos_of_pos hγ
    calc (K₁ * D₂) ^ 2 = K₁ ^ 2 * D₂ ^ 2 := by ring
      _ = K₁ ^ 2 * (γ_k ^ 2 + K₂ ^ 2 * r ^ 2) := by rw [hD₂_sq]
      _ = K₁ ^ 2 * γ_k ^ 2 + K₁ ^ 2 * K₂ ^ 2 * r ^ 2 := by ring
      _ < K₂ ^ 2 * γ_k ^ 2 + K₁ ^ 2 * K₂ ^ 2 * r ^ 2 := by nlinarith
      _ = K₂ ^ 2 * (γ_k ^ 2 + K₁ ^ 2 * r ^ 2) := by ring
      _ = K₂ ^ 2 * D₁ ^ 2 := by rw [hD₁_sq]
      _ = (K₂ * D₁) ^ 2 := by ring
  have hK₁D₂_lt : K₁ * D₂ < K₂ * D₁ :=
    lt_of_abs_lt (abs_lt_of_sq_lt_sq h_sq_diff (le_of_lt hK₂D₁_pos))
  nlinarith

theorem scSlope_mono_K (γ c : Fin n → ℝ) (K₁ K₂ r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hr : 0 < r)
    (hK₁ : 0 < K₁) (hK : K₁ < K₂) :
    scSlope γ c K₁ r < scSlope γ c K₂ r := by
  unfold scSlope
  have step : ∀ k, c k * K₁ / (γ k + sqrt ((γ k) ^ 2 + K₁ ^ 2 * r ^ 2)) <
      c k * K₂ / (γ k + sqrt ((γ k) ^ 2 + K₂ ^ 2 * r ^ 2)) := fun k => by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left
      (summand_mono_K (γ k) K₁ K₂ r (hγ k) hK₁ hr hK) (hc k)
  exact sum_lt_sum (fun k _ => le_of_lt (step k))
    ⟨hn.some, mem_univ _, step hn.some⟩

theorem r_star_mono_K (γ c : Fin n → ℝ) (K₁ K₂ r₁ r₂ : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hn : Nonempty (Fin n))
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hfp₁ : scMapR γ c K₁ r₁ = r₁)
    (hfp₂ : scMapR γ c K₂ r₂ = r₂)
    (hK : K₁ < K₂) :
    r₁ < r₂ := by
  have hs₁ : scSlope γ c K₁ r₁ = 1 :=
    mul_left_cancel₀ (ne_of_gt hr₁) (hfp₁.trans (mul_one r₁).symm)
  have hs₂ : scSlope γ c K₂ r₂ = 1 :=
    mul_left_cancel₀ (ne_of_gt hr₂) (hfp₂.trans (mul_one r₂).symm)
  by_contra h_not
  simp only [not_lt] at h_not
  rcases eq_or_lt_of_le h_not with heq | hlt
  · rw [heq] at hs₂
    linarith [scSlope_mono_K γ c K₁ K₂ r₁ hγ hc hn hr₁ hK₁ hK]
  · have h1 : scSlope γ c K₂ r₁ < 1 := by
      calc scSlope γ c K₂ r₁
          < scSlope γ c K₂ r₂ := scSlope_strictAntiOn γ c K₂ hγ hc hK₂ hn
            (mem_Ici.mpr (le_of_lt hr₂)) (mem_Ici.mpr (le_of_lt hr₁)) hlt
        _ = 1 := hs₂
    linarith [scSlope_mono_K γ c K₁ K₂ r₁ hγ hc hn hr₁ hK₁ hK]

end
