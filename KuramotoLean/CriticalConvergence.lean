/-
  Kuramoto Stability — Critical Convergence (K = K_c)
  ====================================================

  At K = K_c: r(t) → 0 by cubic Lyapunov bound.

  dW₀/dt ≤ -(K_c²γ_min/4)·W₀³ (from Cauchy-Schwarz + r ≥ γ_min W₀)
  If W₀ ≥ δ: dW₀/dt ≤ -μW₀ with μ = K_c²γ_minδ²/4
  comparison_decay → W₀(t) ≤ W₀(0)exp(-μt) → 0. Contradiction.

  3 sorry (cubic bound + CS + identity).
-/

import KuramotoLean.SubcriticalConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Weighted Cauchy-Schwarz (Titu's lemma) -/

private theorem titu_weighted (w : Fin n → ℝ) (a : Fin n → ℝ)
    (hw : ∀ k, 0 < w k) (hn : Nonempty (Fin n)) :
    (∑ k, w k) * (∑ k, w k * (a k) ^ 2) ≥ (∑ k, w k * a k) ^ 2 := by
  have h_sq_div : ∀ k ∈ (univ : Finset (Fin n)),
      (w k * a k) ^ 2 / w k = w k * a k ^ 2 := fun k _ => by
    field_simp [ne_of_gt (hw k)]
  have h_sum_pos : 0 < ∑ k, w k := sum_pos (fun k _ => hw k) (univ_nonempty (α := Fin n))
  have hCS := sq_sum_div_le_sum_sq_div univ (fun k => w k * a k) (fun k _ => hw k)
  rw [sum_congr rfl h_sq_div] at hCS
  have := (div_le_iff₀ h_sum_pos).mp hCS
  nlinarith

/-! ## Cubic Lyapunov bound at K = K_c -/

theorem critical_deriv_cubic (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (t : ℝ) (ht : 0 < t) :
    ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤
    -(D.K ^ 2 * γ_min / 4) * (weightedW D.γ D.c D.α t) ^ 3 := by
  have ht_nn := le_of_lt ht
  have hscg_pos : 0 < ∑ k, D.c k / D.γ k :=
    sum_pos (fun k _ => div_pos (D.hc k) (D.hγ k)) (univ_nonempty (α := Fin n))
  have hKc : D.K / 2 * (∑ k, D.c k / D.γ k) = 1 := by
    rw [hK_crit]; unfold npoleCriticalK; field_simp [ne_of_gt hscg_pos]
  have hr_nn : 0 ≤ D.r t := D.r_nonneg t ht_nn
  have hW_nn : 0 ≤ weightedW D.γ D.c D.α t := weightedW_nonneg D t ht_nn
  have hr_ge : γ_min * weightedW D.γ D.c D.α t ≤ D.r t := r_ge_gmin_W D t ht_nn γ_min hγ_min
  have hCS := titu_weighted (fun k => D.c k / D.γ k) (D.α t)
    (fun k => div_pos (D.hc k) (D.hγ k)) hn
  rw [weighted_ode_identity D.γ D.c D.K (D.α t) D.hγ]
  set r := ∑ k, D.c k * D.α t k with hr_def
  set W := ∑ k, D.c k / D.γ k * D.α t k with hW_def
  set S := ∑ k, D.c k / D.γ k * (D.α t k) ^ 2 with hS_def
  set scg := ∑ k, D.c k / D.γ k with hscg_def
  have hS_nn : 0 ≤ S := sum_nonneg fun k _ =>
    mul_nonneg (div_nonneg (le_of_lt (D.hc k)) (le_of_lt (D.hγ k))) (sq_nonneg _)
  have h_simp : ∑ k, D.c k / D.γ k * (1 - D.α t k ^ 2) = scg - S := by
    rw [show (fun k => D.c k / D.γ k * (1 - D.α t k ^ 2)) =
      (fun k => D.c k / D.γ k - D.c k / D.γ k * D.α t k ^ 2) from by ext; ring]
    rw [← Finset.sum_sub_distrib]
  rw [h_simp]
  have hS_ge : D.K / 2 * W ^ 2 ≤ S := by
    have : D.K / 2 * scg * S = S := by
      calc D.K / 2 * scg * S = (D.K / 2 * scg) * S := by ring
        _ = 1 * S := by rw [hKc]
        _ = S := one_mul S
    nlinarith [mul_le_mul_of_nonneg_left hCS
      (div_nonneg (le_of_lt D.hK) (le_of_lt two_pos))]
  have h_rS : γ_min * W * (D.K / 2 * W ^ 2) ≤ r * S :=
    mul_le_mul hr_ge hS_ge (mul_nonneg (div_nonneg (le_of_lt D.hK) (le_of_lt two_pos))
      (sq_nonneg W)) hr_nn
  have h_lhs : -r + D.K / 2 * r * (scg - S) = -(D.K / 2) * r * S := by
    calc -r + D.K / 2 * r * (scg - S)
        = -r + r * (D.K / 2 * scg) - D.K / 2 * r * S := by ring
      _ = -r + r * 1 - D.K / 2 * r * S := by rw [hKc]
      _ = -(D.K / 2) * r * S := by ring
  rw [h_lhs]
  have h_rS2 : D.K / 2 * (r * S) ≥ D.K / 2 * (γ_min * W * (D.K / 2 * W ^ 2)) :=
    mul_le_mul_of_nonneg_left h_rS (div_nonneg (le_of_lt D.hK) (le_of_lt two_pos))
  have h_ring : D.K / 2 * (γ_min * W * (D.K / 2 * W ^ 2)) =
      D.K ^ 2 * γ_min / 4 * W ^ 3 := by ring
  have key : D.K ^ 2 * γ_min / 4 * W ^ 3 ≤ D.K / 2 * r * S := by
    calc D.K ^ 2 * γ_min / 4 * W ^ 3
        = D.K / 2 * (γ_min * W * (D.K / 2 * W ^ 2)) := by ring
      _ ≤ D.K / 2 * (r * S) := h_rS2
      _ = D.K / 2 * r * S := by ring
  show -(D.K / 2) * r * S ≤ -(D.K ^ 2 * γ_min / 4) * W ^ 3
  have h1 : D.K / 2 * r * S = -(-(D.K / 2) * r * S) := by ring
  have h2 : D.K ^ 2 * γ_min / 4 * W ^ 3 = -(-(D.K ^ 2 * γ_min / 4) * W ^ 3) := by ring
  linarith

/-! ## Derivative bound when W₀ ≥ δ -/

theorem critical_deriv_linear (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ) (ht : 0 < t) (hW_ge : δ ≤ weightedW D.γ D.c D.α t) :
    ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤
    -(D.K ^ 2 * γ_min * δ ^ 2 / 4) * weightedW D.γ D.c D.α t := by
  have hcubic := critical_deriv_cubic D hn hK_crit γ_min hγ_min_pos hγ_min t ht
  have hW_nn := weightedW_nonneg D t (le_of_lt ht)
  have hW_sq : δ ^ 2 ≤ (weightedW D.γ D.c D.α t) ^ 2 :=
    sq_le_sq' (by linarith) hW_ge
  set W := weightedW D.γ D.c D.α t
  have hK2 : 0 < D.K ^ 2 := sq_pos_of_pos D.hK
  have hcoeff : 0 < D.K ^ 2 * γ_min / 4 := div_pos (mul_pos hK2 hγ_min_pos) (by norm_num)
  have hW3 : D.K ^ 2 * γ_min / 4 * W ^ 3 ≥
      D.K ^ 2 * γ_min * δ ^ 2 / 4 * W := by
    have : W ^ 2 ≥ δ ^ 2 := hW_sq
    have : W ^ 3 = W ^ 2 * W := by ring
    have : δ ^ 2 * W ≤ W ^ 2 * W := mul_le_mul_of_nonneg_right hW_sq hW_nn
    nlinarith
  linarith

/-! ## Critical convergence by contradiction -/

theorem critical_W_convergence (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → weightedW D.γ D.c D.α t < ε := by
  by_contra h_not
  push_neg at h_not
  obtain ⟨δ, hδ, h_all⟩ := h_not
  have hKc_pos : 0 < npoleCriticalK D.γ D.c := by
    unfold npoleCriticalK
    exact div_pos two_pos
      (sum_pos (fun k _ => div_pos (D.hc k) (D.hγ k)) (univ_nonempty (α := Fin n)))
  have hW_deriv_le : ∀ t, 0 < t →
      ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤ 0 := by
    intro t ht
    have hcubic := critical_deriv_cubic D hn hK_crit γ_min hγ_min_pos hγ_min t ht
    have hW_nn := weightedW_nonneg D t (le_of_lt ht)
    have hcoeff : 0 ≤ D.K ^ 2 * γ_min / 4 := by positivity
    nlinarith [pow_nonneg hW_nn 3]
  have hW_diff : DifferentiableOn ℝ (weightedW D.γ D.c D.α) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_weightedW D t (mem_Ioi.mp ht)).differentiableAt.differentiableWithinAt
  have hW_deriv_nn : ∀ t ∈ Ioi (0 : ℝ), deriv (weightedW D.γ D.c D.α) t ≤ 0 := by
    intro t ht
    rw [(hasDerivAt_weightedW D t (mem_Ioi.mp ht)).deriv]
    exact hW_deriv_le t (mem_Ioi.mp ht)
  have hW_anti : AntitoneOn (weightedW D.γ D.c D.α) (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (𝕜 := ℝ) 0) (weightedW_continuousOn D)
      (by rwa [interior_Ici]) (by rwa [interior_Ici])
  have hW_ge : ∀ t, 0 ≤ t → δ ≤ weightedW D.γ D.c D.α t := by
    intro t ht
    obtain ⟨s, hst, hWs⟩ := h_all t
    exact le_trans hWs (hW_anti (mem_Ici.mpr ht) (mem_Ici.mpr (le_trans ht hst)) hst)
  set μ := D.K ^ 2 * γ_min * δ ^ 2 / 4
  have hμ_pos : 0 < μ := div_pos (mul_pos (mul_pos (sq_pos_of_pos D.hK) hγ_min_pos)
    (sq_pos_of_pos hδ)) (by norm_num)
  have hW_bound : ∀ t, 0 < t →
      ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤
      -μ * weightedW D.γ D.c D.α t :=
    fun t ht => critical_deriv_linear D hn hK_crit γ_min hγ_min_pos hγ_min
      δ hδ t ht (hW_ge t (le_of_lt ht))
  have hW_exp := comparison_decay (weightedW D.γ D.c D.α)
    (fun t => ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k)
    μ (weightedW_continuousOn D)
    (fun t ht => hasDerivAt_weightedW D t ht) hW_bound
  have hW0_pos : 0 < weightedW D.γ D.c D.α 0 + 1 := by linarith [weightedW_nonneg D 0 le_rfl]
  have hW_bound2 : ∀ t, 0 ≤ t → weightedW D.γ D.c D.α t ≤
      (weightedW D.γ D.c D.α 0 + 1) * exp (-μ * t) := by
    intro t ht
    calc weightedW D.γ D.c D.α t
        ≤ weightedW D.γ D.c D.α 0 * exp (-μ * t) := hW_exp t ht
      _ ≤ (weightedW D.γ D.c D.α 0 + 1) * exp (-μ * t) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)
  obtain ⟨T, hT⟩ := exponential_decay_convergence
    (weightedW D.γ D.c D.α) (weightedW D.γ D.c D.α 0 + 1) μ hμ_pos hW0_pos
    hW_bound2 δ hδ
  set T' := max T 0
  have hT'_nn : 0 ≤ T' := le_max_right T 0
  have hW_small := hT T' (le_max_left T 0)
  have hW_big := hW_ge T' hT'_nn
  linarith

theorem critical_r_convergence (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.r t < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := critical_W_convergence D hn hK_crit γ_min hγ_min_pos hγ_min
    (ε / γ_max) (div_pos hε hγ_max_pos)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := le_trans (le_max_right T 0) ht
  calc D.r t
      ≤ γ_max * weightedW D.γ D.c D.α t := by
        unfold NPoleBarrierData.r weightedW; rw [Finset.mul_sum]
        exact sum_le_sum fun k _ => by
          have hγk := D.hγ k
          calc D.c k * D.α t k
              = D.c k / D.γ k * D.α t k * D.γ k := by field_simp [ne_of_gt hγk]
            _ ≤ D.c k / D.γ k * D.α t k * γ_max :=
                mul_le_mul_of_nonneg_left (hγ_max k)
                  (mul_nonneg (div_nonneg (le_of_lt (D.hc k)) (le_of_lt hγk))
                    (D.hα_nn t ht_nn k))
            _ = γ_max * (D.c k / D.γ k * D.α t k) := by ring
    _ < γ_max * (ε / γ_max) :=
        mul_lt_mul_of_pos_left (hT t (le_trans (le_max_left T 0) ht)) hγ_max_pos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hγ_max_pos)

theorem tendsto_r_critical (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max) :
    Tendsto D.r atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := critical_r_convergence D hn hK_crit γ_min γ_max hγ_min_pos hγ_max_pos
    hγ_min hγ_max ε hε
  exact ⟨max T 0, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg
      (D.r_nonneg t (le_trans (le_max_right _ _) ht))]
    exact hT t (le_trans (le_max_left _ _) ht)⟩

theorem parametric_critical_convergence (D : NPoleBarrierData n)
    (hn : 0 < n) (hK_crit : D.K = npoleCriticalK D.γ D.c) :
    Tendsto D.r atTop (nhds 0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k_min, _, hk_min⟩ := Finset.exists_min_image Finset.univ D.γ Finset.univ_nonempty
  obtain ⟨k_max, _, hk_max⟩ := Finset.exists_max_image Finset.univ D.γ Finset.univ_nonempty
  exact tendsto_r_critical D ‹_› hK_crit
    (D.γ k_min) (D.γ k_max) (D.hγ k_min) (D.hγ k_max)
    (fun k => hk_min k (Finset.mem_univ k))
    (fun k => hk_max k (Finset.mem_univ k))

end
