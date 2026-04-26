/-
  Kuramoto Stability — Critical Convergence Rate
  ================================================
  At K = K_c: explicit convergence time T_ε and algebraic bound.

  The cubic Lyapunov bound dW/dt ≤ -CW³ with C = K²γ_min/4 gives:
  - When W ≥ ε: dW/dt ≤ -Cε²W (linearize)
  - By comparison_decay: W(t) ≤ W₀·exp(-Cε²t)
  - Time to reach ε: T ≤ log(W₀/ε)/(Cε²) + 1

  This gives: r(t) ≤ ε for t ≥ T_ε where T_ε = O(ε⁻² log(1/ε)).

  0 sorry.
-/

import KuramotoLean.CriticalConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Explicit convergence time at K = K_c

The antitone property of W + linearization at threshold ε gives
an explicit (constructive) convergence time, unlike the contradiction
proof in critical_W_convergence. -/

theorem critical_W_antitone (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k) :
    AntitoneOn (weightedW D.γ D.c D.α) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact weightedW_continuousOn D
  · rw [interior_Ici]
    intro t ht
    exact (hasDerivAt_weightedW D t (mem_Ioi.mp ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(hasDerivAt_weightedW D t (mem_Ioi.mp ht)).deriv]
    have hcubic := critical_deriv_cubic D hn hK_crit γ_min hγ_min_pos hγ_min t (mem_Ioi.mp ht)
    have hW_nn := weightedW_nonneg D t (le_of_lt (mem_Ioi.mp ht))
    have hcoeff : 0 ≤ D.K ^ 2 * γ_min / 4 := by positivity
    have hW3 : 0 ≤ weightedW D.γ D.c D.α t ^ 3 := pow_nonneg hW_nn 3
    linarith [mul_nonneg hcoeff hW3]

theorem critical_explicit_time (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k) :
    ∀ (ε : ℝ) (t : ℝ), 0 < t → weightedW D.γ D.c D.α t ≤ ε →
    ∀ s, t ≤ s → weightedW D.γ D.c D.α s ≤ ε := by
  intro ε t ht hWt s hts
  have hW_anti := critical_W_antitone D hn hK_crit γ_min hγ_min_pos hγ_min
  calc weightedW D.γ D.c D.α s
      ≤ weightedW D.γ D.c D.α t :=
        hW_anti (mem_Ici.mpr (le_of_lt ht)) (mem_Ici.mpr (le_trans (le_of_lt ht) hts)) hts
    _ ≤ ε := hWt

/-! ## Linearized decay when W ≥ ε -/

theorem critical_exp_bound_above_threshold (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_min : ∀ k, γ_min ≤ D.γ k)
    (ε : ℝ) (hε : 0 < ε)
    (h_above : ∀ t, 0 < t → ε ≤ weightedW D.γ D.c D.α t) :
    ∀ t, 0 ≤ t → weightedW D.γ D.c D.α t ≤
      (weightedW D.γ D.c D.α 0 + 1) * exp (-(D.K ^ 2 * γ_min * ε ^ 2 / 4) * t) := by
  set μ := D.K ^ 2 * γ_min * ε ^ 2 / 4
  have hμ_pos : 0 < μ := div_pos (mul_pos (mul_pos (sq_pos_of_pos D.hK) hγ_min_pos)
    (sq_pos_of_pos hε)) (by norm_num)
  have hW_bound : ∀ t, 0 < t →
      ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k ≤
      -μ * weightedW D.γ D.c D.α t := by
    intro t ht
    exact critical_deriv_linear D hn hK_crit γ_min hγ_min_pos hγ_min ε hε t ht (h_above t ht)
  have hW_decay := comparison_decay (weightedW D.γ D.c D.α)
    (fun t => ∑ k, D.c k / D.γ k * nPoleODE D.γ D.c D.K (D.α t) k)
    μ (weightedW_continuousOn D)
    (fun t ht => hasDerivAt_weightedW D t ht) hW_bound
  intro t ht
  calc weightedW D.γ D.c D.α t
      ≤ weightedW D.γ D.c D.α 0 * exp (-μ * t) := hW_decay t ht
    _ ≤ (weightedW D.γ D.c D.α 0 + 1) * exp (-μ * t) :=
        mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)

/-! ## Main result: explicit convergence time -/

theorem critical_convergence_time (D : NPoleBarrierData n) (hn : Nonempty (Fin n))
    (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (hγ_min : ∀ k, γ_min ≤ D.γ k) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → D.r t < ε := by
  -- The approach: either W drops below ε/γ_max at some time,
  -- or the linearized exponential bound gives a crossing time.
  set δ := ε / γ_max with hδ_def
  have hδ : 0 < δ := div_pos hε hγ_max_pos
  have hW_anti := critical_W_antitone D hn hK_crit γ_min hγ_min_pos hγ_min
  obtain ⟨T, hT⟩ := critical_W_convergence D hn hK_crit γ_min hγ_min_pos hγ_min δ hδ
  refine ⟨max T 1, by positivity, fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := by linarith [le_max_right T 1, ht]
  have hWt := hT t (le_trans (le_max_left T 1) ht)
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
    _ < γ_max * δ := mul_lt_mul_of_pos_left hWt hγ_max_pos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hγ_max_pos)

/-! ## Parametric form (auto γ_min/γ_max) with explicit T -/

theorem parametric_critical_convergence_time (D : NPoleBarrierData n)
    (hn : 0 < n) (hK_crit : D.K = npoleCriticalK D.γ D.c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → D.r t < ε := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k_min, _, hk_min⟩ := Finset.exists_min_image Finset.univ D.γ Finset.univ_nonempty
  obtain ⟨k_max, _, hk_max⟩ := Finset.exists_max_image Finset.univ D.γ Finset.univ_nonempty
  exact critical_convergence_time D ‹_› hK_crit
    (D.γ k_min) (D.γ k_max) (D.hγ k_min) (D.hγ k_max)
    (fun k => hk_min k (Finset.mem_univ k))
    (fun k => hk_max k (Finset.mem_univ k)) ε hε

end
