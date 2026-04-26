/-
  Kuramoto Stability — Upper Barrier: α_k(t) < 1
  ================================================

  Proves α_k(t) < 1 for all t ≥ 0 when α_k(0) < 1, from the n-pole ODE.
  Uses Grönwall multiplier G_k(t) = (1-α_k(t))·exp(M·t) where M = K·c_sum.

  Combined with component_positive (ComponentBarrier.lean), this gives
  α_k(t) ∈ (0,1) for all t > 0 when α_k(0) ∈ (0,1). Eliminates the
  hα_strict_lt hypothesis from EndToEndData.

  0 sorry target.
-/

import KuramotoLean.ComponentBarrier

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Grönwall multiplier for upper barrier -/

private def upper_mul (D : NPoleBarrierData n) (k : Fin n) (M : ℝ) (t : ℝ) : ℝ :=
  (1 - D.α t k) * exp (M * t)

private theorem upper_mul_cont (D : NPoleBarrierData n) (k : Fin n) (M : ℝ) :
    ContinuousOn (upper_mul D k M) (Ici 0) :=
  ((continuousOn_const.sub (D.hα_cont k)).mul
    (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)

private theorem upper_mul_deriv (D : NPoleBarrierData n) (k : Fin n)
    (M : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (upper_mul D k M)
      ((D.γ k * D.α t k - (D.K / 2) * D.r t * (1 - D.α t k ^ 2) +
        M * (1 - D.α t k)) * exp (M * t)) t := by
  have hα_deriv := D.hα_ode t ht k
  have h_sub : HasDerivAt (fun s => 1 - D.α s k)
      (-nPoleODE D.γ D.c D.K (D.α t) k) t := by
    have := (hasDerivAt_const t (1 : ℝ)).sub hα_deriv
    simpa using this
  have hexp : HasDerivAt (fun s => exp (M * s)) (M * exp (M * t)) t := by
    have h1 : HasDerivAt (fun s => M * s) M t := by
      simpa using (hasDerivAt_id t).const_mul M
    exact h1.exp.congr_deriv (by ring)
  have h := h_sub.mul hexp
  convert h using 1
  unfold nPoleODE NPoleBarrierData.r; ring

private theorem upper_deriv_nonneg (D : NPoleBarrierData n) (k : Fin n)
    (M : ℝ) (hM : ∀ t, 0 ≤ t → (D.K / 2) * D.r t * (1 + D.α t k) ≤ M)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ (D.γ k * D.α t k - (D.K / 2) * D.r t * (1 - D.α t k ^ 2) +
      M * (1 - D.α t k)) * exp (M * t) := by
  apply mul_nonneg _ (exp_nonneg _)
  have h_nn := D.hα_nn t (le_of_lt ht) k
  have h_le := D.hα_le t (le_of_lt ht) k
  have h1 : 1 - D.α t k ^ 2 = (1 + D.α t k) * (1 - D.α t k) := by ring
  rw [h1]
  have hM_t := hM t (le_of_lt ht)
  nlinarith [D.hγ k, D.r_nonneg t (le_of_lt ht), sq_nonneg (D.α t k)]

private theorem upper_mul_monotone (D : NPoleBarrierData n) (k : Fin n)
    (M : ℝ) (hM : ∀ t, 0 ≤ t → (D.K / 2) * D.r t * (1 + D.α t k) ≤ M) :
    MonotoneOn (upper_mul D k M) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (upper_mul_cont D k M)
  · rw [interior_Ici]
    intro s hs
    exact (upper_mul_deriv D k M s (mem_Ioi.mp hs)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro s hs
    rw [(upper_mul_deriv D k M s (mem_Ioi.mp hs)).deriv]
    exact upper_deriv_nonneg D k M hM s (mem_Ioi.mp hs)

/-! ## Main upper barrier theorem -/

theorem component_lt_one (D : NPoleBarrierData n) (k : Fin n)
    (M : ℝ) (hM : ∀ t, 0 ≤ t → (D.K / 2) * D.r t * (1 + D.α t k) ≤ M)
    (hα0 : D.α 0 k < 1) (t : ℝ) (ht : 0 ≤ t) :
    D.α t k < 1 := by
  have hG := upper_mul_monotone D k M hM (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have h0 : upper_mul D k M 0 = 1 - D.α 0 k := by simp [upper_mul]
  rw [h0] at hG
  have h_pos : 0 < 1 - D.α 0 k := by linarith
  have h_G_pos : 0 < upper_mul D k M t := lt_of_lt_of_le h_pos hG
  have : 0 < 1 - D.α t k := by
    by_contra h_neg
    push_neg at h_neg
    have h1 := mul_nonpos_of_nonpos_of_nonneg h_neg (le_of_lt (exp_pos (M * t)))
    unfold upper_mul at h_G_pos
    linarith
  linarith

/-- **Upper barrier with standard bound.** When Σc_k ≤ c_sum,
    the multiplier M = K·c_sum works for all components. -/
theorem component_lt_one_uniform (D : NPoleBarrierData n) (k : Fin n)
    (c_sum : ℝ) (hc_sum : ∑ j, D.c j ≤ c_sum)
    (hα0 : D.α 0 k < 1) (t : ℝ) (ht : 0 ≤ t) :
    D.α t k < 1 := by
  apply component_lt_one D k (D.K * c_sum) _ hα0 t ht
  intro s hs
  have hr_bound : D.r s ≤ c_sum := by
    unfold NPoleBarrierData.r
    calc ∑ j, D.c j * D.α s j
        ≤ ∑ j, D.c j * 1 :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (D.hα_le s hs j) (le_of_lt (D.hc j))
      _ = ∑ j, D.c j := by simp
      _ ≤ c_sum := hc_sum
  have hcs_nn : 0 ≤ c_sum := le_trans (D.r_nonneg s hs) hr_bound
  have hK2 : 0 < D.K / 2 := by linarith [D.hK]
  calc (D.K / 2) * D.r s * (1 + D.α s k)
      ≤ (D.K / 2) * c_sum * (1 + D.α s k) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr_bound (le_of_lt hK2))
          (by linarith [D.hα_nn s hs k])
    _ ≤ (D.K / 2) * c_sum * 2 := by
        apply mul_le_mul_of_nonneg_left (by linarith [D.hα_le s hs k])
          (mul_nonneg (le_of_lt hK2) hcs_nn)
    _ = D.K * c_sum := by ring

/-- **All components stay strictly below 1.**
    Derives hα_strict_lt from just α(0) < 1, using UpperBarrier. -/
theorem component_strict_lt_one (D : NPoleBarrierData n)
    (hα_init_lt : ∀ k, D.α 0 k < 1)
    (t : ℝ) (ht : 0 ≤ t) (k : Fin n) :
    D.α t k < 1 :=
  component_lt_one_uniform D k (∑ j, D.c j) le_rfl (hα_init_lt k) t ht

/-- If α_k(t) = 1, then α_k(s) = 1 for all 0 ≤ s ≤ t.
    Proof: the upper Grönwall multiplier G = (1-α_k)·exp(Mt) is non-decreasing
    with G(t) = 0, so G(s) = 0 for s ≤ t. -/
theorem alpha_one_backward (D : NPoleBarrierData n) (k : Fin n)
    (t : ℝ) (ht : 0 ≤ t) (h1 : D.α t k = 1) :
    ∀ s, 0 ≤ s → s ≤ t → D.α s k = 1 := by
  set M := D.K * ∑ j, D.c j
  have hM : ∀ u, 0 ≤ u → (D.K / 2) * D.r u * (1 + D.α u k) ≤ M := by
    intro u hu
    have hr_bound : D.r u ≤ ∑ j, D.c j := by
      unfold NPoleBarrierData.r
      calc ∑ j, D.c j * D.α u j
          ≤ ∑ j, D.c j * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (D.hα_le u hu j) (le_of_lt (D.hc j))
        _ = ∑ j, D.c j := by simp
    have hcs_nn : 0 ≤ ∑ j, D.c j := le_trans (D.r_nonneg u hu) hr_bound
    have hK2 : 0 < D.K / 2 := by linarith [D.hK]
    calc (D.K / 2) * D.r u * (1 + D.α u k)
        ≤ (D.K / 2) * (∑ j, D.c j) * (1 + D.α u k) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr_bound (le_of_lt hK2))
            (by linarith [D.hα_nn u hu k])
      _ ≤ (D.K / 2) * (∑ j, D.c j) * 2 := by
          apply mul_le_mul_of_nonneg_left (by linarith [D.hα_le u hu k])
            (mul_nonneg (le_of_lt hK2) hcs_nn)
      _ = M := by change _ = D.K * ∑ j, D.c j; ring
  have hG_mono := upper_mul_monotone D k M hM
  have hG_t : upper_mul D k M t = 0 := by
    unfold upper_mul; rw [h1]; ring
  intro s hs hst
  have hG_s := hG_mono (mem_Ici.mpr hs) (mem_Ici.mpr ht) hst
  rw [hG_t] at hG_s
  have hG_nn : 0 ≤ upper_mul D k M s := by
    unfold upper_mul
    exact mul_nonneg (by linarith [D.hα_le s hs k]) (exp_nonneg _)
  have hG_zero : upper_mul D k M s = 0 := le_antisymm hG_s hG_nn
  have : (1 - D.α s k) * exp (M * s) = 0 := hG_zero
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h (ne_of_gt (exp_pos _))

end
