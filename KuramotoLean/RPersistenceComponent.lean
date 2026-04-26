/-
  Kuramoto Stability — Component Persistence from Order Parameter Persistence
  =============================================================================

  If the order parameter r(t) ≥ δ > 0 on [a, b], then each component
  α_k(t) grows linearly while below the threshold β_k = min(Kδ/(4γ_k), 1/2).

  Key results:
    component_linear_growth — α_k(b) ≥ α_k(a) + (Kδ/8)·(b-a) when α_k ≤ β_k
    component_must_exceed — α_k can't stay below β_k for time > 8β_k/(Kδ)

  0 sorry target.
-/

import KuramotoLean.ComponentBarrier
import KuramotoLean.ContinuousLaSalle

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Linear growth when α_k is below threshold -/

/-- **Linear growth of component below threshold.**
    If r(t) ≥ δ and α_k(t) ≤ β_k on [a,b], then α_k grows at rate ≥ Kδ/8. -/
theorem component_linear_growth (D : NPoleBarrierData n) (k : Fin n)
    (δ : ℝ) (hδ : 0 < δ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : ∀ t, a ≤ t → t ≤ b → δ ≤ D.r t)
    (hα_small : ∀ t, a ≤ t → t ≤ b → D.α t k ≤ D.K * δ / (4 * D.γ k))
    (hα_half : ∀ t, a ≤ t → t ≤ b → D.α t k ≤ 1 / 2) :
    D.α a k + D.K * δ / 8 * (b - a) ≤ D.α b k := by
  suffices hg : D.α a k - D.K * δ / 8 * a ≤ D.α b k - D.K * δ / 8 * b by linarith
  set μ := D.K * δ / 8 with hμ_def
  change D.α a k - μ * a ≤ D.α b k - μ * b
  set g : ℝ → ℝ := fun t => D.α t k - μ * t
  have hg_cont : ContinuousOn g (Icc a b) :=
    ((D.hα_cont k).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha))).sub
      ((continuous_const.mul continuous_id).continuousOn)
  have hg_deriv : ∀ t, t ∈ Ioo a b →
      HasDerivAt g (nPoleODE D.γ D.c D.K (D.α t) k - μ) t := by
    intro t ⟨ht_lo, ht_hi⟩
    have h1 := D.hα_ode t (by linarith) k
    have h2 : HasDerivAt (fun s => μ * s) μ t := by
      have := (hasDerivAt_id t).const_mul μ
      simpa [mul_one] using this
    exact h1.sub h2
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hg_cont
  · rw [interior_Icc]
    intro t ht
    exact (hg_deriv t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ⟨ht_lo, ht_hi⟩
    rw [(hg_deriv t ⟨ht_lo, ht_hi⟩).deriv]
    have h_vel := npole_velocity_lower_bound D.γ D.c D.K (D.α t) k
      D.hK (D.hγ k) δ hδ
      (by unfold NPoleBarrierData.r at hr; exact hr t (by linarith) (by linarith))
      (D.hα_nn t (by linarith) k)
      (hα_small t (by linarith) (by linarith))
      (hα_half t (by linarith) (by linarith))
    linarith
  · exact left_mem_Icc.mpr hab
  · exact right_mem_Icc.mpr hab
  · exact hab

/-! ## Component must exceed threshold -/

/-- **Component must exceed threshold.** If r ≥ δ on a long enough interval,
    α_k can't stay below β = min(Kδ/(4γ_k), 1/2). -/
theorem component_must_exceed (D : NPoleBarrierData n) (k : Fin n)
    (δ β : ℝ) (hδ : 0 < δ) (_hβ : 0 < β)
    (hβ_small : β ≤ D.K * δ / (4 * D.γ k))
    (hβ_half : β ≤ 1 / 2)
    (a S : ℝ) (ha : 0 ≤ a) (hS : 0 < S)
    (hS_long : 8 * β / (D.K * δ) ≤ S)
    (hr : ∀ t, a ≤ t → t ≤ a + S → δ ≤ D.r t)
    (hα_a : 0 < D.α a k) :
    ∃ t, a ≤ t ∧ t ≤ a + S ∧ β < D.α t k := by
  by_contra h_stay
  simp only [not_exists, not_and, not_lt] at h_stay
  have hα_le : ∀ t, a ≤ t → t ≤ a + S → D.α t k ≤ β :=
    fun t ht1 ht2 => h_stay t ht1 ht2
  have h_growth := component_linear_growth D k δ hδ a (a + S) ha (by linarith)
    hr
    (fun t ht1 ht2 => le_trans (hα_le t ht1 ht2) hβ_small)
    (fun t ht1 ht2 => le_trans (hα_le t ht1 ht2) hβ_half)
  have h_Kd_pos : 0 < D.K * δ := mul_pos D.hK hδ
  have h_calc : β ≤ D.K * δ / 8 * S := by
    have hS_lb : 8 * β ≤ D.K * δ * S := by
      calc 8 * β = 8 * β / (D.K * δ) * (D.K * δ) :=
            (div_mul_cancel₀ (8 * β) (ne_of_gt h_Kd_pos)).symm
        _ ≤ S * (D.K * δ) :=
            mul_le_mul_of_nonneg_right hS_long (le_of_lt h_Kd_pos)
        _ = D.K * δ * S := by ring
    linarith
  linarith [hα_le (a + S) (by linarith) le_rfl]

/-! ## Escape time -/

def escapeTime (K δ β : ℝ) : ℝ := 8 * β / (K * δ)

theorem escapeTime_pos (K δ β : ℝ) (hK : 0 < K) (hδ : 0 < δ) (hβ : 0 < β) :
    0 < escapeTime K δ β := by
  unfold escapeTime; positivity

/-- **Single component threshold guarantee.** -/
theorem single_component_exceeds (D : NPoleBarrierData n) (k : Fin n)
    (δ : ℝ) (hδ : 0 < δ)
    (hα_init : ∀ j, 0 < D.α 0 j)
    (a : ℝ) (ha : 0 ≤ a)
    (β : ℝ) (hβ : 0 < β)
    (hβ_small : β ≤ D.K * δ / (4 * D.γ k))
    (hβ_half : β ≤ 1 / 2)
    (hr : ∀ t, a ≤ t → t ≤ a + escapeTime D.K δ β → δ ≤ D.r t) :
    ∃ t, a ≤ t ∧ t ≤ a + escapeTime D.K δ β ∧ β < D.α t k :=
  component_must_exceed D k δ β hδ hβ hβ_small hβ_half
    a (escapeTime D.K δ β) ha (escapeTime_pos D.K δ β D.hK hδ hβ)
    le_rfl hr (component_positive D k (hα_init k) a ha)

end
