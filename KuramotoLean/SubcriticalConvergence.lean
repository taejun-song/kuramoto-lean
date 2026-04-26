/-
  Kuramoto Stability — Subcritical Convergence
  ==============================================

  For K < K_c: r(t) → 0 exponentially. The weighted Lyapunov
  W₀ = Σ c_k α_k/γ_k satisfies dW₀/dt ≤ -μ W₀ with
  μ = γ_min(1 - K/K_c) > 0.

  Key: r ≥ γ_min · W₀, and dW₀/dt ≤ r(K/K_c - 1) with K/K_c - 1 < 0.
  Multiplying: dW₀/dt ≤ γ_min W₀(K/K_c - 1) = -μ W₀.

  0 sorry.
-/

import KuramotoLean.SubcriticalLyapunov
import KuramotoLean.ComponentBarrier
import KuramotoLean.GronwallBridge
import KuramotoLean.ExponentialConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Weighted Lyapunov function -/

def weightedW {n : ℕ} (γ c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, c k / γ k * α t k

theorem weightedW_nonneg (D : NPoleBarrierData n) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ weightedW D.γ D.c D.α t :=
  sum_nonneg fun k _ => mul_nonneg (div_nonneg (le_of_lt (D.hc k)) (le_of_lt (D.hγ k)))
    (D.hα_nn t ht k)

theorem r_ge_gmin_W (D : NPoleBarrierData n) (t : ℝ) (ht : 0 ≤ t)
    (γ_min : ℝ) (hγ_min : ∀ k, γ_min ≤ D.γ k) :
    γ_min * weightedW D.γ D.c D.α t ≤ D.r t := by
  unfold NPoleBarrierData.r weightedW
  rw [Finset.mul_sum]
  exact sum_le_sum fun k _ => by
    have hγk := D.hγ k
    have hαk := D.hα_nn t ht k
    have hγk_ne := ne_of_gt hγk
    calc γ_min * (D.c k / D.γ k * D.α t k)
        = D.c k * (γ_min / D.γ k) * D.α t k := by field_simp [hγk_ne]
      _ ≤ D.c k * 1 * D.α t k := by
          apply mul_le_mul_of_nonneg_right _ hαk
          exact mul_le_mul_of_nonneg_left
            ((div_le_one hγk).mpr (hγ_min k)) (le_of_lt (D.hc k))
      _ = D.c k * D.α t k := by ring

/-! ## Continuity and derivative -/

theorem weightedW_continuousOn (D : NPoleBarrierData n) :
    ContinuousOn (weightedW D.γ D.c D.α) (Ici 0) := by
  unfold weightedW
  exact continuousOn_finset_sum _ fun k _ =>
    continuousOn_const.mul (D.hα_cont k)

theorem hasDerivAt_weightedW (D : NPoleBarrierData n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (weightedW D.γ D.c D.α)
      (∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k) t := by
  unfold weightedW
  exact HasDerivAt.fun_sum fun k _ => (D.hα_ode t ht k).const_mul _

/-! ## Derivative bound -/

private theorem npoleCriticalK_pos (D : NPoleBarrierData n) (hn : Nonempty (Fin n)) :
    0 < npoleCriticalK D.γ D.c := by
  unfold npoleCriticalK
  exact div_pos two_pos
    (sum_pos (fun k _ => div_pos (D.hc k) (D.hγ k)) (univ_nonempty (α := Fin n)))

theorem weightedW_deriv_le (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (t : ℝ) (ht : 0 < t)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤
    -(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * weightedW D.γ D.c D.α t := by
  have hKc_pos := npoleCriticalK_pos D hn
  have h_gap : (D.K / 2) * ∑ k, D.c k / D.γ k - 1 = D.K / npoleCriticalK D.γ D.c - 1 := by
    unfold npoleCriticalK; field_simp
  have h_neg : D.K / npoleCriticalK D.γ D.c - 1 < 0 := by
    rw [div_sub_one (ne_of_gt hKc_pos)]; exact div_neg_of_neg_of_pos (by linarith) hKc_pos
  have h_le := weighted_ode_le_r_gap D.γ D.c D.K (D.α t) D.hγ D.hc (le_of_lt D.hK) hn
    (D.hα_nn t (le_of_lt ht)) (D.hα_le t (le_of_lt ht))
  have h_r_ge := r_ge_gmin_W D t (le_of_lt ht) γ_min hγ_min
  calc ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k
      ≤ D.r t * ((D.K / 2) * ∑ k, D.c k / D.γ k - 1) := h_le
    _ = D.r t * (D.K / npoleCriticalK D.γ D.c - 1) := by rw [h_gap]
    _ ≤ γ_min * weightedW D.γ D.c D.α t * (D.K / npoleCriticalK D.γ D.c - 1) :=
        mul_le_mul_of_nonpos_right h_r_ge (le_of_lt h_neg)
    _ = -(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * weightedW D.γ D.c D.α t := by
        ring

/-! ## Exponential decay and convergence -/

theorem subcritical_W_decay (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    ∀ t, 0 ≤ t →
    weightedW D.γ D.c D.α t ≤
      weightedW D.γ D.c D.α 0 *
        exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t) :=
  comparison_decay (weightedW D.γ D.c D.α)
    (fun t => ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k)
    (γ_min * (1 - D.K / npoleCriticalK D.γ D.c))
    (weightedW_continuousOn D)
    (fun t ht => hasDerivAt_weightedW D t ht)
    (fun t ht => weightedW_deriv_le D hn t ht γ_min hγ_min_pos hγ_min hK_lt)

theorem subcritical_r_decay (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    ∀ t, 0 ≤ t →
    D.r t ≤ γ_max * weightedW D.γ D.c D.α 0 *
      exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t) := by
  intro t ht
  calc D.r t
      ≤ γ_max * weightedW D.γ D.c D.α t := by
        unfold NPoleBarrierData.r weightedW
        rw [Finset.mul_sum]
        exact sum_le_sum fun k _ => by
          have hγk := D.hγ k
          calc D.c k * D.α t k
              = D.c k / D.γ k * D.α t k * D.γ k := by
                field_simp [ne_of_gt hγk]
            _ ≤ D.c k / D.γ k * D.α t k * γ_max :=
                mul_le_mul_of_nonneg_left (hγ_max k)
                  (mul_nonneg (div_nonneg (le_of_lt (D.hc k)) (le_of_lt hγk))
                    (D.hα_nn t ht k))
            _ = γ_max * (D.c k / D.γ k * D.α t k) := by ring
    _ ≤ γ_max * (weightedW D.γ D.c D.α 0 *
          exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t)) :=
        mul_le_mul_of_nonneg_left
          (subcritical_W_decay D hn γ_min hγ_min_pos hγ_min hK_lt t ht)
          (le_of_lt hγ_max_pos)
    _ = γ_max * weightedW D.γ D.c D.α 0 *
          exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t) := by ring

/-! ## Component exponential decay -/

theorem subcritical_component_decay (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) (k : Fin n) :
    ∀ t, 0 ≤ t →
    D.α t k ≤ D.γ k / D.c k * weightedW D.γ D.c D.α 0 *
      exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t) := by
  intro t ht
  have hW := subcritical_W_decay D hn γ_min hγ_min_pos hγ_min hK_lt t ht
  have hα_le : D.c k / D.γ k * D.α t k ≤ weightedW D.γ D.c D.α t :=
    single_le_sum (fun j _ => mul_nonneg (div_nonneg (le_of_lt (D.hc j)) (le_of_lt (D.hγ j)))
      (D.hα_nn t ht j)) (mem_univ k)
  have hgc : 0 ≤ D.γ k / D.c k := div_nonneg (le_of_lt (D.hγ k)) (le_of_lt (D.hc k))
  calc D.α t k
      = D.γ k / D.c k * (D.c k / D.γ k * D.α t k) := by
        field_simp [ne_of_gt (D.hc k), ne_of_gt (D.hγ k)]
    _ ≤ D.γ k / D.c k * weightedW D.γ D.c D.α t :=
        mul_le_mul_of_nonneg_left hα_le hgc
    _ ≤ D.γ k / D.c k * (weightedW D.γ D.c D.α 0 *
          exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t)) :=
        mul_le_mul_of_nonneg_left hW hgc
    _ = D.γ k / D.c k * weightedW D.γ D.c D.α 0 *
          exp (-(γ_min * (1 - D.K / npoleCriticalK D.γ D.c)) * t) := by ring

/-! ## Convergence -/

private theorem subcritical_rate_pos (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    0 < γ_min * (1 - D.K / npoleCriticalK D.γ D.c) := by
  have hKc_pos := npoleCriticalK_pos D hn
  exact mul_pos hγ_min_pos (sub_pos.mpr ((div_lt_one hKc_pos).mpr hK_lt))

theorem subcritical_r_convergence (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.r t < ε := by
  set μ := γ_min * (1 - D.K / npoleCriticalK D.γ D.c)
  set C := γ_max * weightedW D.γ D.c D.α 0
  have hμ_pos := subcritical_rate_pos D hn γ_min hγ_min_pos hK_lt
  have hbound := subcritical_r_decay D hn γ_min γ_max hγ_min_pos hγ_max_pos hγ_min hγ_max hK_lt
  by_cases hC_le : C ≤ 0
  · intro ε hε; exact ⟨0, fun t ht => by
      calc D.r t ≤ C * exp (-μ * t) := hbound t (by linarith)
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC_le (exp_nonneg _)
        _ < ε := hε⟩
  · push_neg at hC_le
    exact exponential_decay_convergence D.r C μ hμ_pos hC_le hbound

theorem subcritical_component_convergence (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) (k : Fin n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.α t k < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := subcritical_r_convergence D hn γ_min γ_max hγ_min_pos hγ_max_pos
    hγ_min hγ_max hK_lt (D.c k * ε) (mul_pos (D.hc k) hε)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := le_trans (le_max_right _ _) ht
  have hcα_le_r : D.c k * D.α t k ≤ D.r t :=
    single_le_sum (fun j _ => mul_nonneg (le_of_lt (D.hc j)) (D.hα_nn t ht_nn j))
      (mem_univ k)
  have hr_lt := hT t (le_trans (le_max_left _ _) ht)
  nlinarith [D.hc k]

/-! ## Filter.Tendsto forms -/

theorem tendsto_r_subcritical (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) :
    Tendsto D.r atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := subcritical_r_convergence D hn γ_min γ_max hγ_min_pos hγ_max_pos
    hγ_min hγ_max hK_lt ε hε
  exact ⟨max T 0, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg
      (D.r_nonneg t (le_trans (le_max_right _ _) ht))]
    exact hT t (le_trans (le_max_left _ _) ht)⟩

theorem tendsto_component_subcritical (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hK_lt : D.K < npoleCriticalK D.γ D.c) (k : Fin n) :
    Tendsto (fun t => D.α t k) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := subcritical_component_convergence D hn γ_min γ_max hγ_min_pos hγ_max_pos
    hγ_min hγ_max hK_lt k ε hε
  exact ⟨max T 0, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg
      (D.hα_nn t (le_trans (le_max_right _ _) ht) k)]
    exact hT t (le_trans (le_max_left _ _) ht)⟩

end
