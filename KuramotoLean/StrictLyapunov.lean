/-
  Kuramoto Stability — Strict Lyapunov Decrease
  ===============================================

  When V = Σ c_k(α_k - α*_k)² > 0, the Lyapunov derivative is strictly
  negative: dV/dt < 0. This is the LaSalle characterization.

  Proof chain:
    V > 0 → ∃k with α_k ≠ α*_k
    → pair(k,k) > 0 (pair_eq_zero_iff)
    → Σ Σ pair > 0 (all terms ≥ 0, one > 0)
    → r*Q - DS > 0 (pair_expansion_identity)
    → dV/dt = K(DS - r*Q) < 0

  0 sorry.
-/

import KuramotoLean.UniformRate

noncomputable section

/-! ## Strict positivity of the pair double sum when V > 0 -/

/-- If V > 0, some pair diagonal term is strictly positive. -/
theorem pair_double_sum_pos {n : ℕ}
    (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (hV : 0 < l2Distance c α α_star) :
    0 < ∑ j, ∑ k, c j * c k *
      pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
  have hα_ne : α ≠ α_star := by
    intro heq; subst heq
    simp [l2Distance] at hV
  have : ∃ m : Fin n, α m ≠ α_star m := by
    by_contra h
    push Not at h
    exact hα_ne (funext h)
  obtain ⟨m, hm_ne⟩ := this
  have h_pair_pos : 0 < pairIntegrand (α m) (α_star m) (α m) (α_star m) := by
    have h_not_zero : ¬(pairIntegrand (α m) (α_star m) (α m) (α_star m) = 0) := by
      rw [pair_eq_zero_iff (α m) (α m) (α_star m) (α_star m)
        (hα m) (hα m) (hα_lt m) (hα_lt m) (hα_star m) (hα_star m)]
      exact fun ⟨h, _⟩ => hm_ne h
    exact lt_of_le_of_ne
      (pair_bound (α m) (α m) (α_star m) (α_star m)
        (hα m) (hα m) (hα_lt m) (hα_lt m) (hα_star m) (hα_star m))
      (Ne.symm h_not_zero)
  have h_coeff_pos : 0 < c m * c m := mul_pos (hc m) (hc m)
  have h_term_pos : 0 < c m * c m *
      pairIntegrand (α m) (α_star m) (α m) (α_star m) :=
    mul_pos h_coeff_pos h_pair_pos
  have h_nn : ∀ j k : Fin n,
      0 ≤ c j * c k * pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
    intro j k
    exact mul_nonneg (le_of_lt (mul_pos (hc j) (hc k)))
      (pair_bound (α j) (α k) (α_star j) (α_star k)
        (hα j) (hα k) (hα_lt j) (hα_lt k) (hα_star j) (hα_star k))
  calc 0 < c m * c m * pairIntegrand (α m) (α_star m) (α m) (α_star m) :=
        h_term_pos
    _ ≤ ∑ k, c m * c k * pairIntegrand (α m) (α_star m) (α k) (α_star k) :=
        Finset.single_le_sum (fun k _ => h_nn m k) (Finset.mem_univ m)
    _ ≤ ∑ j, ∑ k, c j * c k *
        pairIntegrand (α j) (α_star j) (α k) (α_star k) :=
        Finset.single_le_sum (fun j _ =>
          Finset.sum_nonneg (fun k _ => h_nn j k)) (Finset.mem_univ m)

/-! ## Strict Lyapunov decrease -/

/-- **Strict Lyapunov decrease.** When V > 0, dV/dt < 0.
    This is the LaSalle characterization: dV/dt = 0 only at equilibrium. -/
theorem l2_strict_lyapunov {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (hK : 0 < K) (_hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (hV : 0 < l2Distance c α α_star) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k < 0 := by
  rw [l2_lyapunov_identity γ c K α α_star hα_star h_equil]
  have h_expand := pair_expansion_identity c α α_star
  have h_pos := pair_double_sum_pos c α α_star hc hα hα_lt hα_star hα_star_lt hV
  simp only [pairIntegrand] at h_pos
  nlinarith

/-- **Equivalence**: dV/dt = 0 iff α = α*. -/
theorem l2_lyapunov_zero_iff {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k = 0 ↔
    α = α_star := by
  constructor
  · intro h_zero
    by_contra h_ne
    have hV_pos : 0 < l2Distance c α α_star := by
      have hV_nn := l2Distance_nonneg c α α_star (fun k => le_of_lt (hc k))
      have hV_ne : l2Distance c α α_star ≠ 0 :=
        fun h => h_ne ((l2Distance_eq_zero c α α_star hc).mp h)
      exact lt_of_le_of_ne hV_nn (Ne.symm hV_ne)
    linarith [l2_strict_lyapunov γ c K α α_star hK hγ hc hα hα_lt
      hα_star hα_star_lt h_equil hV_pos]
  · intro h_eq
    subst h_eq
    simp only [sub_self, zero_mul, mul_zero, Finset.sum_const_zero]

end
