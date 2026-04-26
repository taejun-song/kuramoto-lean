/-
  Kuramoto Stability — Order Parameter Escape
  =============================================

  Connects instability_infinite_escape to the order parameter:
  for any T ≥ 0, r(t) > δ₀ at infinitely many times t ≥ T.

  Combined with V antitone, this gives: V → L where either L = 0
  (done) or L > 0 with r escaping δ₀ infinitely often.

  Corollary: the order parameter does NOT converge to 0
  (weak persistence from instability alone).

  0 sorry target.
-/

import KuramotoLean.InfiniteEscape
import KuramotoLean.EnergyExclusion
import KuramotoLean.BoundaryStrictLyapunov

open Real Set Filter Finset

noncomputable section

variable {n : ℕ}

/-! ## Order parameter escape from component escape -/

/-- **Order parameter escape.** At infinitely many times, r(t) > c_min · ε.
    Direct corollary of instability_infinite_escape + r_pos_at_escape. -/
theorem order_parameter_infinite_escape (D : NPoleBarrierData n)
    (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam)
    (hdisp : npoleDispersion D.γ D.c D.K lam = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (D.K / 2) * (∑ k, D.c k) * ε ^ 2 ≤ lam / 2)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (c_min : ℝ) (hc_min : ∀ j, c_min ≤ D.c j) (hc_min_pos : 0 < c_min) :
    ∀ T : ℝ, 0 ≤ T → ∃ t : ℝ, T ≤ t ∧ c_min * ε < D.r t := by
  intro T hT
  obtain ⟨t, ht_ge, k, hk⟩ := instability_infinite_escape D hn lam hlam
    hdisp ε hε hε_small hα_init_pos T hT
  exact ⟨t, ht_ge, r_pos_at_escape D ε hε c_min hc_min hc_min_pos t (by linarith) k hk⟩

/-! ## Weak persistence: r does not converge to 0 -/

/-- **r does not converge to 0.** The order parameter is eventually above
    c_min · ε infinitely often, so it cannot converge to 0. -/
theorem order_parameter_not_tendsto_zero (D : NPoleBarrierData n)
    (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam)
    (hdisp : npoleDispersion D.γ D.c D.K lam = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (D.K / 2) * (∑ k, D.c k) * ε ^ 2 ≤ lam / 2)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (c_min : ℝ) (hc_min : ∀ j, c_min ≤ D.c j) (hc_min_pos : 0 < c_min) :
    ¬ Tendsto D.r atTop (nhds 0) := by
  intro h_tend
  rw [Metric.tendsto_atTop] at h_tend
  obtain ⟨T₀, hT₀⟩ := h_tend (c_min * ε) (mul_pos hc_min_pos hε)
  obtain ⟨t, ht_ge, hr_pos⟩ := order_parameter_infinite_escape D hn lam hlam
    hdisp ε hε hε_small hα_init_pos c_min hc_min hc_min_pos
    (max 0 T₀) (le_max_left _ _)
  have h_dist := hT₀ t (le_trans (le_max_right 0 T₀) ht_ge)
  simp only [Real.dist_eq, sub_zero] at h_dist
  linarith [lt_of_lt_of_le hr_pos (le_abs_self (D.r t))]

/-! ## V drop at escape: quantitative pair lower bound

When some α_j > ε at time t, the pair double sum (hence -dV/dt)
is bounded below by a term depending on the diagonal pair(j,j).
This connects the escape to an actual V-decrease. -/

/-- **Diagonal pair self-bound.** pair(j,j) ≥ 2·α*_j·α_j·(α_j-α*_j)².
    Direct application of pair_ge_cross with both indices equal. -/
theorem pair_self_ge_cross (αj αsj : ℝ)
    (hαj : 0 < αj) (hαj1 : αj < 1)
    (hαsj : 0 < αsj) (_hαsj1 : αsj < 1) :
    2 * αsj * αj * (αj - αsj) ^ 2 ≤ pairIntegrand αj αsj αj αsj := by
  have h := pair_ge_cross αj αj αsj αsj hαj hαj hαj1 hαj1 hαsj hαsj
  linarith

/-- **Pair double sum lower bound from single component.**
    When α_j ≥ ε and α_j ≠ α*_j, the pair double sum has a
    quantitative positive lower bound. -/
theorem pair_sum_lower_from_component {n : ℕ}
    (c α α_star : Fin n → ℝ) (j : Fin n) (ε : ℝ)
    (hc : ∀ k, 0 < c k)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (hε : 0 < ε) (hα_j : ε ≤ α j) :
    2 * (c j) ^ 2 * (α_star j) * ε * (α j - α_star j) ^ 2 ≤
    ∑ m, ∑ l, c m * c l * pairIntegrand (α m) (α_star m) (α l) (α_star l) := by
  have hαj_pos : 0 < α j := lt_of_lt_of_le hε hα_j
  have h_pair_self := pair_self_ge_cross (α j) (α_star j)
    hαj_pos (hα_lt j) (hα_star j) (hα_star_lt j)
  have h_nn : ∀ m l : Fin n,
      0 ≤ c m * c l * pairIntegrand (α m) (α_star m) (α l) (α_star l) := by
    intro m l
    apply mul_nonneg (le_of_lt (mul_pos (hc m) (hc l)))
    exact pair_bound_boundary (α m) (α l) (α_star m) (α_star l)
      (hα_nn m) (hα_nn l) (hα_lt m) (hα_lt l) (hα_star m) (hα_star l)
  calc 2 * (c j) ^ 2 * (α_star j) * ε * (α j - α_star j) ^ 2
      ≤ (c j) ^ 2 * (2 * (α_star j) * (α j) * (α j - α_star j) ^ 2) := by
        have h1 : (0:ℝ) ≤ (c j) ^ 2 := sq_nonneg _
        have h2 : (0:ℝ) ≤ (α j - α_star j) ^ 2 := sq_nonneg _
        have h3 : (0:ℝ) ≤ α_star j := le_of_lt (hα_star j)
        nlinarith [mul_nonneg h3 h2, mul_nonneg h1 (mul_nonneg h3 h2)]
    _ ≤ (c j) ^ 2 * pairIntegrand (α j) (α_star j) (α j) (α_star j) := by
        apply mul_le_mul_of_nonneg_left h_pair_self (sq_nonneg _)
    _ = c j * c j * pairIntegrand (α j) (α_star j) (α j) (α_star j) := by
        ring_nf
    _ ≤ ∑ l, c j * c l * pairIntegrand (α j) (α_star j) (α l) (α_star l) :=
        Finset.single_le_sum (fun l _ => h_nn j l) (Finset.mem_univ j)
    _ ≤ ∑ m, ∑ l, c m * c l *
        pairIntegrand (α m) (α_star m) (α l) (α_star l) :=
        Finset.single_le_sum (fun m _ =>
          Finset.sum_nonneg (fun l _ => h_nn m l)) (Finset.mem_univ j)

end
