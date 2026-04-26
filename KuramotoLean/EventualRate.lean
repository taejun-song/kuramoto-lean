/-
  Kuramoto Stability — Eventual Exponential Rate
  ================================================
  After a finite transient, convergence is exponential:
    V(t) ≤ V(T₀) · exp(-μ(t - T₀))
  where μ = K · (δ*/2) · δ* depends only on the equilibrium structure.

  Proof: V → 0 (qualitative, FullChainConvergence) → V enters basin
  → components ≥ δ*/2 (basin_component_lb) → uniform rate
  → l2_drop_from_bounds on [T₀, T₀+(t-T₀)] → exponential decay.

  0 sorry.
-/

import KuramotoLean.FullChainConvergence
import KuramotoLean.L2Convergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Exponential rate constants -/

def FullChainData.exp_rate (D : FullChainData n) : ℝ :=
  D.K * (D.δ_star / 2) * D.δ_star

theorem FullChainData.exp_rate_pos (D : FullChainData n) : 0 < D.exp_rate := by
  unfold FullChainData.exp_rate
  exact mul_pos (mul_pos D.hK (by linarith [D.hδ_star_pos])) D.hδ_star_pos

def FullChainData.basin_thresh (D : FullChainData n) : ℝ :=
  D.c_min * (D.δ_star / 2) ^ 2

theorem FullChainData.basin_thresh_pos (D : FullChainData n) : 0 < D.basin_thresh := by
  unfold FullChainData.basin_thresh
  exact mul_pos D.hc_min_pos (sq_pos_of_pos (by linarith [D.hδ_star_pos]))

/-! ## Basin entry from qualitative V → 0 -/

theorem FullChainData.basin_entry (D : FullChainData n) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      l2_ext D.c D.α D.α_star T₀ < D.basin_thresh := by
  have hV := D.V_tendsto_zero
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T, hT⟩ := hV D.basin_thresh D.basin_thresh_pos
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  have h := hT (max T 0) (le_max_left _ _)
  simp only [Real.dist_eq, sub_zero] at h
  have hnn := l2_ext_nonneg D.c D.α D.α_star D.hc (max T 0)
  rw [abs_of_nonneg hnn] at h; exact h

/-! ## Component bounds from basin + V antitone -/

theorem FullChainData.basin_component_lb_at (D : FullChainData n)
    (T₀ : ℝ) (hT₀ : 0 ≤ T₀)
    (hbasin : l2_ext D.c D.α D.α_star T₀ < D.basin_thresh)
    (t : ℝ) (ht : T₀ ≤ t) (k : Fin n) : D.δ_star / 2 ≤ D.α t k := by
  have ht_nn : 0 ≤ t := le_trans hT₀ ht
  have hVt : l2_ext D.c D.α D.α_star t ≤ l2_ext D.c D.α D.α_star T₀ :=
    D.hV_anti ht
  rw [l2_ext_eq D.c D.α D.α_star t ht_nn,
      l2_ext_eq D.c D.α D.α_star T₀ hT₀] at hVt
  have hVt_basin : l2Distance D.c (D.α t) D.α_star < D.basin_thresh :=
    lt_of_le_of_lt hVt (by rwa [l2_ext_eq D.c D.α D.α_star T₀ hT₀] at hbasin)
  exact basin_component_lb D.c (D.α t) D.α_star
    (fun j => D.hc j) D.c_min D.δ_star D.hc_min_pos D.hc_min
    D.hδ_star_pos D.hα_star_lb hVt_basin k

/-! ## Eventual exponential decay of V -/

theorem FullChainData.eventual_exponential_V (D : FullChainData n) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      l2Distance D.c (D.α t) D.α_star ≤
        l2Distance D.c (D.α T₀) D.α_star *
          exp (-D.exp_rate * (t - T₀)) := by
  obtain ⟨T₀, hT₀, hbasin⟩ := D.basin_entry
  refine ⟨T₀, hT₀, fun t ht => ?_⟩
  set Δ := t - T₀
  have hΔ : 0 ≤ Δ := by linarith
  have ht_eq : t = T₀ + Δ := by ring
  rw [ht_eq]
  exact l2_drop_from_bounds D.γ D.c D.K D.α D.α_star
    D.hK D.hγ D.hc D.h_equil D.hα_star_pos D.hα_star_lt
    (D.δ_star / 2) D.δ_star (by linarith [D.hδ_star_pos]) D.hδ_star_pos
    D.hα_star_lb D.hc_sum T₀ Δ hT₀ hΔ
    (fun s hs_lo hs_hi k => D.basin_component_lb_at T₀ hT₀ hbasin s hs_lo k)
    (fun s hs_lo _ k => D.hα_lt s (le_trans hT₀ hs_lo) k)
    (fun s hs => D.hα_ode s (by linarith [hT₀]))
    (l2_continuousOn D.c D.α D.α_star D.hα_cont |>.mono
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT₀)))

/-! ## Order parameter exponential rate -/

theorem FullChainData.eventual_exponential_r (D : FullChainData n) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      (D.toNPoleBarrierData.r t - ∑ k, D.c k * D.α_star k) ^ 2 ≤
        l2Distance D.c (D.α T₀) D.α_star *
          exp (-D.exp_rate * (t - T₀)) := by
  obtain ⟨T₀, hT₀, hV⟩ := D.eventual_exponential_V
  refine ⟨T₀, hT₀, fun t ht => ?_⟩
  have hcs := order_parameter_sq_le_l2 D.c (D.α t) D.α_star
    (fun k => le_of_lt (D.hc k)) D.hc_sum
  have h_eq : D.toNPoleBarrierData.r t - ∑ k, D.c k * D.α_star k =
      ∑ k, D.c k * (D.α t k - D.α_star k) := by
    unfold NPoleBarrierData.r
    rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
  rw [h_eq]; exact le_trans hcs (hV t ht)

/-! ## Pointwise component exponential convergence -/

theorem FullChainData.eventual_exponential_pointwise (D : FullChainData n) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t → ∀ k,
      (D.α t k - D.α_star k) ^ 2 ≤
        l2Distance D.c (D.α T₀) D.α_star / D.c_min *
          exp (-D.exp_rate * (t - T₀)) := by
  obtain ⟨T₀, hT₀, hV⟩ := D.eventual_exponential_V
  refine ⟨T₀, hT₀, fun t ht k => ?_⟩
  have h_single : D.c_min * (D.α t k - D.α_star k) ^ 2 ≤
      l2Distance D.c (D.α t) D.α_star := by
    have h_le_sum : D.c k * (D.α t k - D.α_star k) ^ 2 ≤
        l2Distance D.c (D.α t) D.α_star := by
      unfold l2Distance
      exact Finset.single_le_sum (f := fun j => D.c j * (D.α t j - D.α_star j) ^ 2)
        (fun j _ => mul_nonneg (le_of_lt (D.hc j)) (sq_nonneg _))
        (Finset.mem_univ k)
    calc D.c_min * (D.α t k - D.α_star k) ^ 2
        ≤ D.c k * (D.α t k - D.α_star k) ^ 2 :=
          mul_le_mul_of_nonneg_right (D.hc_min k) (sq_nonneg _)
      _ ≤ l2Distance D.c (D.α t) D.α_star := h_le_sum
  have hVt := hV t ht
  have h1 : (D.α t k - D.α_star k) ^ 2 ≤
      l2Distance D.c (D.α t) D.α_star / D.c_min := by
    rw [le_div_iff₀ D.hc_min_pos]; linarith [h_single]
  have h2 : l2Distance D.c (D.α t) D.α_star / D.c_min ≤
      l2Distance D.c (D.α T₀) D.α_star / D.c_min *
        exp (-D.exp_rate * (t - T₀)) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hVt (le_of_lt D.hc_min_pos)
  linarith

/-! ## Filter.Tendsto forms -/

theorem FullChainData.tendsto_r (D : FullChainData n) :
    Tendsto D.toNPoleBarrierData.r atTop
      (nhds (∑ k, D.c k * D.α_star k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := full_chain_convergence D ε hε
  exact ⟨T, fun t ht => by rw [Real.dist_eq]; exact hT t ht⟩

theorem FullChainData.tendsto_component (D : FullChainData n) (k : Fin n) :
    Tendsto (fun t => D.α t k) atTop (nhds (D.α_star k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV := D.V_tendsto_zero
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T, hT⟩ := hV (D.c k * ε ^ 2) (mul_pos (D.hc k) (sq_pos_of_pos hε))
  refine ⟨max T 0, fun t ht => ?_⟩
  rw [Real.dist_eq]
  have hT_le : T ≤ t := le_trans (le_max_left _ _) ht
  have ht_nn : 0 ≤ t := le_trans (le_max_right _ _) ht
  have hVt := hT t hT_le
  simp only [Real.dist_eq, sub_zero] at hVt
  rw [abs_of_nonneg (l2_ext_nonneg D.c D.α D.α_star D.hc t),
      l2_ext_eq D.c D.α D.α_star t ht_nn] at hVt
  have h_le : D.c k * (D.α t k - D.α_star k) ^ 2 ≤
      l2Distance D.c (D.α t) D.α_star := by
    unfold l2Distance
    exact Finset.single_le_sum (f := fun j => D.c j * (D.α t j - D.α_star j) ^ 2)
      (fun j _ => mul_nonneg (le_of_lt (D.hc j)) (sq_nonneg _))
      (Finset.mem_univ k)
  have h_sq : (D.α t k - D.α_star k) ^ 2 < ε ^ 2 := by
    have : D.c k * (D.α t k - D.α_star k) ^ 2 < D.c k * ε ^ 2 := lt_of_le_of_lt h_le hVt
    exact lt_of_mul_lt_mul_left this (le_of_lt (D.hc k))
  exact abs_lt_of_sq_lt_sq h_sq (le_of_lt hε)

end
