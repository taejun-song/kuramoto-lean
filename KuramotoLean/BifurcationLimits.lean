/-
  Kuramoto Stability — Bifurcation Limits
  =========================================
  Near K_c: r*² ≤ (K-K_c)·B  → r* → 0 as K → K_c+.
  Large K:  r*  ≥ 1-2γ_max/K → r* → 1 as K → ∞.

  0 sorry.
-/

import KuramotoLean.SquareRootLaw
import KuramotoLean.SelfConsistencyFixedPoint

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Strong coupling: r* ≥ 1 - 2γ_max/K -/

theorem r_star_lower_strong (γ c : Fin n → ℝ) (K r_star γ_max : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hK : 0 < K) (hr : 0 < r_star) (hγ_max_pos : 0 < γ_max)
    (hγ_max : ∀ k, γ k ≤ γ_max) (hc_sum : ∑ k, c k = 1)
    (hsc : ∑ k, c k * explicitEquil (γ k) K r_star = r_star) :
    1 - 2 * γ_max / K ≤ r_star := by
  have hden : (0 : ℝ) < 2 * γ_max + K * r_star := by positivity
  set q := K * r_star / (2 * γ_max + K * r_star)
  have hq_nn : 0 ≤ q := div_nonneg (by positivity) (le_of_lt hden)
  have h_lb : q ≤ r_star := by
    calc q ≤ ∑ k, c k * explicitEquil (γ k) K r_star := by
          have : ∀ k, q ≤ explicitEquil (γ k) K r_star :=
            fun k => explicitEquil_lower_from_gamma_max (γ k) K r_star γ_max (hγ k) hK hr (hγ_max k)
          calc q = q * ∑ k, c k := by rw [hc_sum, mul_one]
            _ = ∑ k, q * c k := by rw [mul_sum]
            _ = ∑ k, c k * q := by congr 1; ext; ring
            _ ≤ ∑ k, c k * explicitEquil (γ k) K r_star :=
                sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (this k) (le_of_lt (hc k))
      _ = r_star := hsc
  rw [show q = K * r_star / (2 * γ_max + K * r_star) from rfl, div_le_iff₀ hden] at h_lb
  -- K*r ≤ r*(2γ+Kr) = 2γr + Kr²
  -- K*r - Kr² ≤ 2γr
  -- Kr(1-r) ≤ 2γr
  have h_key : K * (1 - r_star) ≤ 2 * γ_max := by
    by_cases h1 : r_star ≤ 1
    · nlinarith
    · push_neg at h1
      nlinarith [mul_neg_of_pos_of_neg hK (by linarith : 1 - r_star < 0)]
  -- K(1-r) ≤ 2γ → (1-r) ≤ 2γ/K → r ≥ 1-2γ/K
  have h_mul : (1 - r_star) * K ≤ 2 * γ_max := by linarith
  have h_div2 : 1 - r_star ≤ 2 * γ_max / K :=
    (le_div_iff₀ hK).mpr h_mul
  linarith

/-! ## Near critical: r*² ≤ (K-K_c)·C, hence r* → 0 as K → K_c+ -/

theorem r_star_vanishes_near_critical (γ c : Fin n → ℝ) (K r_star γ_max : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hK_super : npoleCriticalK γ c < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hfp : scSlope γ c K r_star = 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, γ k ≤ γ_max)
    (ε : ℝ) (hε : 0 < ε)
    (hK_close : K - npoleCriticalK γ c < ε ^ 2 * K ^ 3 / (2 * γ_max + K) ^ 2) :
    r_star < ε := by
  have hub := order_parameter_sq_upper_bound γ c K r_star hγ hc hn hK hK_super
    hr_pos hr_lt hfp γ_max hγ_max_pos hγ_max
  have h2gK : 0 < (2 * γ_max + K) ^ 2 := by positivity
  have hK3 : 0 < K ^ 3 := by positivity
  have h_rsq : r_star ^ 2 < ε ^ 2 := by
    calc r_star ^ 2
        ≤ (K - npoleCriticalK γ c) * (2 * γ_max + K) ^ 2 / K ^ 3 := hub
      _ < ε ^ 2 * K ^ 3 / (2 * γ_max + K) ^ 2 * (2 * γ_max + K) ^ 2 / K ^ 3 := by
          apply div_lt_div_of_pos_right _ hK3
          exact mul_lt_mul_of_pos_right hK_close h2gK
      _ = ε ^ 2 := by field_simp
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hε) h_rsq

end
