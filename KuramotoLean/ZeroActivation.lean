/-
  Kuramoto Stability — Zero Component Activation
  ================================================
  0 sorry target.
-/

import KuramotoLean.ShiftedBarrier

open Real Set Finset

noncomputable section

variable {n : ℕ}

theorem r_pos_from_component (D : NPoleBarrierData n)
    (j : Fin n) (hj : 0 < D.α 0 j) (t : ℝ) (ht : 0 ≤ t) :
    0 < D.r t :=
  lt_of_lt_of_le (mul_pos (D.hc j) (component_positive D j hj t ht))
    (Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (D.hc i))
      (D.hα_nn t ht i)) (Finset.mem_univ j))

private theorem alpha_zero_on_interval (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) (ht : 0 ≤ t)
    (h0 : D.α 0 k = 0) (ht_eq : D.α t k = 0) :
    ∀ s, 0 ≤ s → s ≤ t → D.α s k = 0 := by
  intro s hs hst
  have h_barrier := shifted_component_barrier D k s t hs hst
  have : D.α s k * exp (-(D.γ k) * (t - s)) ≤ 0 := by rw [ht_eq] at h_barrier; linarith
  have h_exp : 0 < exp (-(D.γ k) * (t - s)) := exp_pos _
  have h_nn : 0 ≤ D.α s k := D.hα_nn s hs k
  nlinarith [mul_nonneg h_nn (le_of_lt h_exp)]

theorem zero_component_activation (D : NPoleBarrierData n)
    (k : Fin n) (j : Fin n) (hj : 0 < D.α 0 j) :
    ∀ t, 0 < t → 0 < D.α t k := by
  by_cases hα0 : 0 < D.α 0 k
  · exact fun t ht => component_positive D k hα0 t (le_of_lt ht)
  · push_neg at hα0
    have h0 : D.α 0 k = 0 := le_antisymm hα0 (D.hα_nn 0 le_rfl k)
    intro t ht
    by_contra h_neg
    push_neg at h_neg
    have ht_eq : D.α t k = 0 := le_antisymm h_neg (D.hα_nn t (le_of_lt ht) k)
    have h_zero : ∀ s, 0 ≤ s → s ≤ t → D.α s k = 0 :=
      alpha_zero_on_interval D k t (le_of_lt ht) h0 ht_eq
    have hf_cont : ContinuousOn (fun s => D.α s k) (Icc 0 t) :=
      (D.hα_cont k).mono Icc_subset_Ici_self
    have hf_deriv : ∀ s ∈ interior (Icc 0 t), 0 < deriv (fun s => D.α s k) s := by
      rw [interior_Icc]
      intro s ⟨hs_lo, hs_hi⟩
      have hs_zero : D.α s k = 0 := h_zero s (le_of_lt hs_lo) (le_of_lt hs_hi)
      have hrs : 0 < D.r s := r_pos_from_component D j hj s (le_of_lt hs_lo)
      have h_ode : HasDerivAt (fun s => D.α s k) (nPoleODE D.γ D.c D.K (D.α s) k) s :=
        D.hα_ode s hs_lo k
      rw [h_ode.deriv]
      unfold nPoleODE
      rw [hs_zero]
      have : -(D.γ k) * 0 + D.K / 2 * (∑ i, D.c i * D.α s i) * (1 - 0 ^ 2) = D.K / 2 * D.r s := by
        unfold NPoleBarrierData.r; ring
      rw [this]
      exact mul_pos (div_pos D.hK (by norm_num)) hrs
    have hf_strict := strictMonoOn_of_deriv_pos (convex_Icc 0 t) hf_cont hf_deriv
    have := hf_strict (left_mem_Icc.mpr (le_of_lt ht)) (right_mem_Icc.mpr (le_of_lt ht)) ht
    linarith [h0, ht_eq]

end
