/-
  Kuramoto Stability — Self-Contained N-Pole Convergence
  ========================================================

  Key algebraic results for deriving persistence from V < V_incoherent:
    V_incoherent_sub_l2 — identity for V_incoherent - V
    V_initial_lt_V_incoherent — V(0) < V_incoherent for α ∈ (0, 2α*)
    r_lower_from_V_gap — quantitative r ≥ δ from V < V_incoherent
    quantitative_persistence — r(t) ≥ δ along antitone trajectories

  Combined with energy_exclusion_persistence and RPersistenceComponent,
  these give a self-contained proof path:
    α(0) ∈ (0, 2α*) → V(0) < V_incoherent → r ≥ δ forever
    → component propagation → V drops → iterate → V → 0 → r → r*

  16th independent proof path.

  0 sorry target.
-/

import KuramotoLean.EnergyExclusion
import KuramotoLean.ContinuumBarbalat

noncomputable section

open Finset Filter Topology

variable {n : ℕ}

/-! ## Algebraic identity: V_incoherent - V -/

theorem V_incoherent_sub_l2 (c α α_star : Fin n → ℝ) :
    V_incoherent c α_star - l2Distance c α α_star =
    ∑ k, c k * (2 * α k * α_star k - α k ^ 2) := by
  unfold V_incoherent l2Distance
  have : ∀ k, c k * α_star k ^ 2 - c k * (α k - α_star k) ^ 2 =
      c k * (2 * α k * α_star k - α k ^ 2) := by intro k; ring
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _; exact this k

/-! ## V_incoherent - V ≤ 2·α*_max·r -/

theorem V_gap_le_r_bound (c α α_star : Fin n → ℝ)
    (α_star_max : ℝ) (hα_star_max : ∀ k, α_star k ≤ α_star_max)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ 1)
    (hc : ∀ k, 0 < c k) :
    V_incoherent c α_star - l2Distance c α α_star ≤
    2 * α_star_max * (∑ k, c k * α k) := by
  rw [V_incoherent_sub_l2]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro k _
  have h1 : 0 ≤ c k := le_of_lt (hc k)
  have h2 : 0 ≤ α k := hα_nn k
  have h3 : 2 * α k * α_star k - α k ^ 2 ≤ 2 * α k * α_star_max := by
    have : 0 ≤ α k ^ 2 := sq_nonneg _
    nlinarith [hα_star_max k]
  calc c k * (2 * α k * α_star k - α k ^ 2)
      ≤ c k * (2 * α k * α_star_max) := mul_le_mul_of_nonneg_left h3 h1
    _ = 2 * α_star_max * (c k * α k) := by ring

/-! ## r lower bound from V gap -/

theorem r_lower_from_V_gap (c α α_star : Fin n → ℝ)
    (α_star_max : ℝ) (hα_star_max_pos : 0 < α_star_max)
    (hα_star_max : ∀ k, α_star k ≤ α_star_max)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ 1)
    (hc : ∀ k, 0 < c k)
    (_hV_lt : l2Distance c α α_star < V_incoherent c α_star) :
    (V_incoherent c α_star - l2Distance c α α_star) / (2 * α_star_max) ≤
    ∑ k, c k * α k := by
  have h2pos : (0 : ℝ) < 2 * α_star_max := by linarith
  have h_ub := V_gap_le_r_bound c α α_star α_star_max hα_star_max hα_nn hα_le hc
  rw [div_le_iff₀ h2pos]
  linarith

/-! ## V(0) < V_incoherent for α ∈ (0, 2α*)^n -/

theorem V_initial_lt_V_incoherent (c α α_star : Fin n → ℝ)
    (hn : 0 < n) (hc : ∀ k, 0 < c k)
    (hα_pos : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 2 * α_star k)
    (_hα_star : ∀ k, 0 < α_star k) :
    l2Distance c α α_star < V_incoherent c α_star := by
  suffices h : 0 < V_incoherent c α_star - l2Distance c α α_star by linarith
  rw [V_incoherent_sub_l2]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun k _ => by
  have h1 : 0 < c k := hc k
  have h2 : 0 < α k := hα_pos k
  have h3 : 0 < 2 * α_star k - α k := by linarith [hα_lt k]
  have h4 : c k * (2 * α k * α_star k - α k ^ 2) =
      c k * (α k * (2 * α_star k - α k)) := by ring
  rw [h4]
  exact mul_pos h1 (mul_pos h2 h3)) Finset.univ_nonempty

/-! ## Quantitative persistence along trajectories -/

theorem quantitative_persistence
    (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (α_star_max : ℝ) (hα_star_max_pos : 0 < α_star_max)
    (hα_star_max : ∀ k, α_star k ≤ α_star_max)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ t, ∀ k, 0 ≤ α t k)
    (hα_le : ∀ t, ∀ k, α t k ≤ 1)
    (hV_anti : Antitone (fun t => l2Distance c (α t) α_star))
    (hV_init : l2Distance c (α 0) α_star < V_incoherent c α_star) :
    ∀ t, 0 ≤ t →
    (V_incoherent c α_star - l2Distance c (α 0) α_star) / (2 * α_star_max) ≤
    ∑ k, c k * α t k := by
  intro t _ht
  have hV_t : l2Distance c (α t) α_star ≤ l2Distance c (α 0) α_star :=
    hV_anti (by linarith)
  have hV_lt : l2Distance c (α t) α_star < V_incoherent c α_star :=
    lt_of_le_of_lt hV_t hV_init
  have h_bound := r_lower_from_V_gap c (α t) α_star α_star_max
    hα_star_max_pos hα_star_max (hα_nn t) (hα_le t) hc hV_lt
  have hgap_le : V_incoherent c α_star - l2Distance c (α 0) α_star ≤
      V_incoherent c α_star - l2Distance c (α t) α_star := by linarith
  have h2pos : (0 : ℝ) < 2 * α_star_max := by linarith
  calc (V_incoherent c α_star - l2Distance c (α 0) α_star) / (2 * α_star_max)
      ≤ (V_incoherent c α_star - l2Distance c (α t) α_star) / (2 * α_star_max) :=
        div_le_div_of_nonneg_right hgap_le (by linarith)
    _ ≤ ∑ k, c k * α t k := h_bound

/-! ## Abstract self-contained convergence -/

structure SelfContainedData (n : ℕ) where
  V : ℝ → ℝ
  r : ℝ → ℝ
  r_star : ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hV_controls_r : ∀ t, (r t - r_star) ^ 2 ≤ V t
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  Δ : ℝ
  hΔ : 0 < Δ
  hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + Δ) ≤ q * V t

theorem self_contained_V_zero (D : SelfContainedData n) :
    Tendsto D.V atTop (nhds 0) := by
  have h := continuous_barbalat_general D.V D.q D.Δ D.hV_nn D.hV_anti
    D.hq0 D.hq1 D.hΔ D.hdrops
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := h ε hε
  exact ⟨T, fun s hs => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (D.hV_nn s)]
    exact hT s hs⟩

theorem self_contained_convergence (D : SelfContainedData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - D.r_star| < ε := by
  intro ε hε
  have hV_tend := self_contained_V_zero D
  rw [Metric.tendsto_atTop] at hV_tend
  obtain ⟨T, hT⟩ := hV_tend (ε ^ 2) (by positivity)
  exact ⟨T, fun t ht => by
    have hV_t := hT t ht
    simp only [Real.dist_eq, sub_zero] at hV_t
    rw [abs_of_nonneg (D.hV_nn t)] at hV_t
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt (D.hV_controls_r t) hV_t)
      (le_of_lt hε)⟩

theorem self_contained_tendsto (D : SelfContainedData n) :
    Tendsto (fun t => |D.r t - D.r_star|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := self_contained_convergence D ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_abs]
    exact hT t ht⟩

end
