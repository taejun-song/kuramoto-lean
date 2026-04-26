/-
  Kuramoto Stability — Energy Exclusion Persistence
  ===================================================

  If V(t) = Σ c_k(α_k(t)-α*_k)² < Σ c_k α*_k² (= V at incoherence),
  then r(t) = Σ c_k α_k(t) > 0 (order parameter positive).

  The contrapositive: r = 0 forces all α_k = 0, giving V = V_incoherent.
  So V < V_incoherent excludes the incoherent state from the sublevel set.

  Combined with V antitone, this gives: once V drops below V_incoherent,
  the order parameter stays positive FOREVER. No persistence hypothesis needed.

  0 sorry target.
-/

import KuramotoLean.L2Lyapunov

open Finset

noncomputable section

variable {n : ℕ}

/-! ## V at the incoherent state -/

/-- V at the incoherent state α = 0: Σ c_k α*_k². -/
def V_incoherent (c α_star : Fin n → ℝ) : ℝ :=
  ∑ k, c k * α_star k ^ 2

/-- V at α = 0 equals V_incoherent. -/
theorem l2Distance_at_zero (c α_star : Fin n → ℝ) :
    l2Distance c (fun _ => 0) α_star = V_incoherent c α_star := by
  unfold l2Distance V_incoherent
  congr 1; ext k; simp

/-- V_incoherent > 0 when c_k > 0 and α*_k > 0. -/
theorem V_incoherent_pos (c α_star : Fin n → ℝ)
    (hn : 0 < n) (hc : ∀ k, 0 < c k) (hα_star : ∀ k, 0 < α_star k) :
    0 < V_incoherent c α_star := by
  unfold V_incoherent
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun k _ => mul_pos (hc k) (sq_pos_of_pos (hα_star k)))
    Finset.univ_nonempty

/-! ## Energy exclusion: V < V_incoherent → r > 0 -/

/-- **Energy exclusion.** If V < V_incoherent, then r > 0.
    Proof: if r = 0 with α_k ≥ 0 and c_k > 0, then all α_k = 0,
    giving V = V_incoherent. Contradiction. -/
theorem energy_exclusion_r_pos (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ k, 0 ≤ α k)
    (hV_lt : l2Distance c α α_star < V_incoherent c α_star) :
    0 < ∑ k, c k * α k := by
  by_contra h
  push Not at h
  have hr_nn : 0 ≤ ∑ k, c k * α k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (le_of_lt (hc k)) (hα_nn k)
  have hr_zero : ∑ k, c k * α k = 0 := le_antisymm h hr_nn
  have hα_zero : ∀ k, α k = 0 := by
    intro k
    have h_nn : ∀ j : Fin n, j ∈ Finset.univ → 0 ≤ c j * α j :=
      fun j _ => mul_nonneg (le_of_lt (hc j)) (hα_nn j)
    have h_term := (Finset.sum_eq_zero_iff_of_nonneg h_nn).mp hr_zero k (Finset.mem_univ k)
    exact (mul_eq_zero.mp h_term).resolve_left (ne_of_gt (hc k))
  have hV_eq : l2Distance c α α_star = V_incoherent c α_star := by
    unfold l2Distance V_incoherent
    congr 1; ext k; rw [hα_zero k]; simp
  linarith

/-- **Energy exclusion along trajectory.** If V is antitone and
    V(T) < V_incoherent, then r(t) > 0 for all t ≥ T. -/
theorem energy_exclusion_persistence
    (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ t, ∀ k, 0 ≤ α t k)
    (hV_anti : Antitone (fun t => l2Distance c (α t) α_star))
    (T : ℝ) (hV_basin : l2Distance c (α T) α_star < V_incoherent c α_star) :
    ∀ t, T ≤ t → 0 < ∑ k, c k * α t k := by
  intro t ht
  have hV_le : l2Distance c (α t) α_star ≤ l2Distance c (α T) α_star :=
    hV_anti ht
  exact energy_exclusion_r_pos c (α t) α_star hc (hα_nn t)
    (lt_of_le_of_lt hV_le hV_basin)

/-! ## Quantitative bound: V < V_incoherent → r ≥ δ -/

/-- **Quantitative energy exclusion.** If all α_k ≤ δ with
    δ ≤ min_k α*_k, then V ≥ V_incoherent - 2δr*. Contrapositive:
    if V ≤ V₀ < V_incoherent, then ∃ k with α_k > δ₀ where
    δ₀ = (V_incoherent - V₀)/(2r*). -/
theorem energy_exclusion_quantitative (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ k, 0 ≤ α k)
    (_hα_star : ∀ k, 0 < α_star k)
    (δ : ℝ) (_hδ : 0 ≤ δ) (hδ_small : ∀ k, δ ≤ α_star k)
    (hα_le : ∀ k, α k ≤ δ) :
    V_incoherent c α_star - 2 * δ * (∑ k, c k * α_star k) ≤
    l2Distance c α α_star := by
  unfold l2Distance V_incoherent
  have h_lhs : (∑ k, c k * α_star k ^ 2) - 2 * δ * (∑ k, c k * α_star k) =
      ∑ k, (c k * α_star k ^ 2 - 2 * δ * (c k * α_star k)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [h_lhs]
  apply Finset.sum_le_sum; intro k _
  calc c k * α_star k ^ 2 - 2 * δ * (c k * α_star k)
      = c k * (α_star k ^ 2 - 2 * δ * α_star k) := by ring
    _ ≤ c k * (α k - α_star k) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (hc k))
        have h1 := hα_nn k
        have h2 := hα_le k
        have h3 := hδ_small k
        nlinarith [sq_nonneg (α k), sq_nonneg (α_star k - δ),
                   mul_nonneg (by linarith : 0 ≤ α_star k) (by linarith : 0 ≤ δ - α k)]
    _ = c k * (α k - α_star k) ^ 2 := rfl

end
