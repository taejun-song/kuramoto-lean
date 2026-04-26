/-
  Kuramoto Stability — Boundary Strict Lyapunov
  ===============================================

  Extends pair_double_sum_pos from (0,1)^n to the boundary [0,1)^n:
  whenever V > 0 and at least one α_k > 0, the pair double sum is > 0.

  This means {dV/dt = 0} ∩ {V > 0} ∩ [0,1)^n = {0}.
  The only V-critical point with V > 0 is the incoherent state α = 0.

  Combined with instability of α = 0, this gives V → 0.

  0 sorry target.
-/

import KuramotoLean.ContinuousLaSalle
import KuramotoLean.StrictLyapunov

noncomputable section

open Finset

/-! ## Mixed boundary pair positivity -/

/-- **Pair double sum positive on mixed boundary.**
    When α ∈ [0,1)^n with V(α) > 0 and at least one α_j > 0,
    the pair double sum is > 0 (i.e., dV/dt < 0).

    This extends pair_double_sum_pos from (0,1)^n to the boundary.
    At the fully incoherent state α = 0, the pair sum is 0 — that
    is the ONLY zero of the Lyapunov derivative with V > 0. -/
theorem pair_double_sum_pos_boundary {n : ℕ}
    (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (hV : 0 < l2Distance c α α_star)
    (hα_ne_zero : ∃ j, 0 < α j) :
    0 < ∑ j, ∑ k, c j * c k *
      pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
  -- All terms are ≥ 0 (pair_bound_boundary extends from (0,1) to [0,1))
  have h_nn : ∀ j k : Fin n,
      0 ≤ c j * c k * pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
    intro j k
    apply mul_nonneg (le_of_lt (mul_pos (hc j) (hc k)))
    exact pair_bound_boundary (α j) (α k) (α_star j) (α_star k)
      (hα_nn j) (hα_nn k) (hα_lt j) (hα_lt k) (hα_star j) (hα_star k)
  -- V > 0 means α ≠ α*
  have hα_ne : α ≠ α_star := by
    intro heq; subst heq; simp [l2Distance] at hV
  -- Find a deviating component
  have hdev : ∃ m : Fin n, α m ≠ α_star m := by
    by_contra h; push Not at h; exact hα_ne (funext h)
  obtain ⟨m, hm_ne⟩ := hdev
  obtain ⟨j₀, hj₀_pos⟩ := hα_ne_zero
  -- Case split: either some positive component deviates, or all deviations are at zero components
  by_cases h_pos_dev : ∃ p, 0 < α p ∧ α p ≠ α_star p
  · -- Case 1: some α_p > 0 with α_p ≠ α*_p. Diagonal pair(p,p) > 0.
    obtain ⟨p, hp_pos, hp_ne⟩ := h_pos_dev
    have h_pair_pos : 0 < pairIntegrand (α p) (α_star p) (α p) (α_star p) := by
      have h_not_zero := mt
        ((pair_eq_zero_iff (α p) (α p) (α_star p) (α_star p)
          hp_pos hp_pos (hα_lt p) (hα_lt p) (hα_star p) (hα_star p)).mp)
        (fun ⟨h, _⟩ => hp_ne h)
      exact lt_of_le_of_ne
        (pair_bound (α p) (α p) (α_star p) (α_star p)
          hp_pos hp_pos (hα_lt p) (hα_lt p) (hα_star p) (hα_star p))
        (Ne.symm h_not_zero)
    calc 0 < c p * c p * pairIntegrand (α p) (α_star p) (α p) (α_star p) :=
          mul_pos (mul_pos (hc p) (hc p)) h_pair_pos
      _ ≤ ∑ k, c p * c k * pairIntegrand (α p) (α_star p) (α k) (α_star k) :=
          single_le_sum (fun k _ => h_nn p k) (mem_univ p)
      _ ≤ ∑ j, ∑ k, c j * c k *
          pairIntegrand (α j) (α_star j) (α k) (α_star k) :=
          single_le_sum (fun j _ => sum_nonneg (fun k _ => h_nn j k)) (mem_univ p)
  · -- Case 2: all positive components are at equilibrium.
    -- So all deviations are at zero components: ∃ k, α k = 0, α*_k > 0.
    push Not at h_pos_dev
    -- m deviates: α m ≠ α*m. Since all positive components equal α*, α m ≤ 0.
    have hm_zero : α m = 0 := by
      by_cases h : 0 < α m
      · exact absurd (h_pos_dev m h) hm_ne
      · exact le_antisymm (not_lt.mp h) (hα_nn m)
    -- j₀ is positive and equals α*_{j₀}
    have hj₀_eq : α j₀ = α_star j₀ := h_pos_dev j₀ hj₀_pos
    -- Cross-term pair(j₀, m) > 0 by pair_pos_mixed
    have h_cross : 0 < pairIntegrand (α j₀) (α_star j₀) (α m) (α_star m) := by
      rw [hm_zero, hj₀_eq]
      exact pair_pos_mixed (α_star j₀) (α_star j₀) (α_star m)
        (hα_star j₀) (hα_star_lt j₀) (hα_star j₀) (hα_star m)
    calc 0 < c j₀ * c m * pairIntegrand (α j₀) (α_star j₀) (α m) (α_star m) :=
          mul_pos (mul_pos (hc j₀) (hc m)) h_cross
      _ ≤ ∑ k, c j₀ * c k * pairIntegrand (α j₀) (α_star j₀) (α k) (α_star k) :=
          single_le_sum (fun k _ => h_nn j₀ k) (mem_univ m)
      _ ≤ ∑ j, ∑ k, c j * c k *
          pairIntegrand (α j) (α_star j) (α k) (α_star k) :=
          single_le_sum (fun j _ => sum_nonneg (fun k _ => h_nn j k)) (mem_univ j₀)

/-- **Characterization of {dV/dt = 0} on [0,1)^n.**
    The pair double sum is 0 iff either α = α* or α = 0. -/
theorem pair_sum_zero_characterization {n : ℕ}
    (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_zero_sum : ∑ j, ∑ k, c j * c k *
      pairIntegrand (α j) (α_star j) (α k) (α_star k) = 0) :
    α = α_star ∨ α = 0 := by
  by_cases hV : 0 < l2Distance c α α_star
  · -- V > 0, so pair_sum = 0 forces α to be 0
    by_cases hα_ne_zero : ∃ j, 0 < α j
    · -- Some α_j > 0, but then pair_sum > 0, contradiction
      exact absurd h_zero_sum (ne_of_gt
        (pair_double_sum_pos_boundary c α α_star hc hα_nn hα_lt
          hα_star hα_star_lt hV hα_ne_zero))
    · -- All α_k ≤ 0, so α = 0
      push Not at hα_ne_zero
      right; ext k
      exact le_antisymm (hα_ne_zero k) (hα_nn k)
  · -- V = 0, so α = α*
    push Not at hV
    have hV_nn := l2Distance_nonneg c α α_star (fun k => le_of_lt (hc k))
    have hV_zero : l2Distance c α α_star = 0 := le_antisymm hV hV_nn
    left; exact (l2Distance_eq_zero c α α_star hc).mp hV_zero

end
