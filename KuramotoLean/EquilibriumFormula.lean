/-
  Kuramoto Stability — Explicit Equilibrium Formula
  ===================================================

  The component equilibrium equation (K/2)r·α² + γ·α - (K/2)r = 0
  has the explicit positive root:
    α*(γ, K, r) = (-γ + √(γ² + K²r²)) / (Kr)

  This gives a closed-form expression for the equilibrium vector,
  enabling continuity and monotonicity proofs.

  0 sorry target.
-/

import KuramotoLean.EquilibriumUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Explicit formula for the positive root -/

def explicitEquil (γ_k K r : ℝ) : ℝ :=
  (-γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) / (K * r)

theorem explicitEquil_solves (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    componentEquil γ_k K r (explicitEquil γ_k K r) = 0 := by
  unfold componentEquil explicitEquil
  set D := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
  have hD_sq : D ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 :=
    sq_sqrt (by positivity)
  have hKr : K * r ≠ 0 := ne_of_gt (mul_pos hK hr)
  field_simp
  nlinarith [hD_sq, sq_nonneg γ_k, sq_nonneg D, sq_nonneg (K * r)]

theorem explicitEquil_pos (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    0 < explicitEquil γ_k K r := by
  unfold explicitEquil
  apply div_pos _ (mul_pos hK hr)
  have h : γ_k < sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ < sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
        sqrt_lt_sqrt (sq_nonneg _) (by linarith [mul_pos (sq_pos_of_pos hK) (sq_pos_of_pos hr)])
  linarith

theorem explicitEquil_lt_one (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    explicitEquil γ_k K r < 1 := by
  unfold explicitEquil
  rw [div_lt_one (mul_pos hK hr)]
  have hD : sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) < γ_k + K * r := by
    calc sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
        < sqrt ((γ_k + K * r) ^ 2) :=
          sqrt_lt_sqrt (by positivity) (by nlinarith [mul_pos hγ (mul_pos hK hr)])
      _ = γ_k + K * r := sqrt_sq (by positivity)
  linarith

end
