/-
  Continuum Critical Convergence: K = Kc → r(t) → 0
  ====================================================
  At the critical coupling K = Kc, the order parameter still decays to zero,
  but NOT exponentially. The decay is algebraic (1/√t in physics literature).

  Proof strategy (same as discrete CriticalConvergence.lean):
  By contradiction. If W = ∫(α/γ)dμ stays above δ > 0, then the ODE gives
  a cubic decay dW/dt ≤ -c·W³ (from the 1-α² correction at K = Kc).
  This cubic decay + the W ≥ δ floor gives dW/dt ≤ -c·δ²·W,
  which is exponential — contradicting W ≥ δ for all time.

  0 sorry.
-/

import KuramotoLean.ContinuumSubcritical

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Critical decay by contradiction -/

/-- **Critical Lyapunov decay.**
    At K = Kc, if W(t) = ∫(α/γ)dμ satisfies dW/dt ≤ -c·W³ for some c > 0,
    and W is bounded by a linear function of r, then r → 0.

    The key insight: at K = Kc the linear term in the Lyapunov derivative
    vanishes (since 1 - K/Kc = 0), but the cubic term -c·W³ from the
    (1-α²) correction still provides decay. -/
theorem continuum_critical_W_convergence
    (W W' : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_nn : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_cubic : ∀ t, 0 < t → W' t ≤ -(c * W t ^ 3)) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → W t < ε := by
  by_contra h_not
  push_neg at h_not
  obtain ⟨δ, hδ, h_all⟩ := h_not
  have hW_anti : AntitoneOn W (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hW_cont
    · intro t ht
      rw [interior_Ici] at ht
      exact (hW_deriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hW_deriv t ht).deriv]
      have hW_nn' := hW_nn t (le_of_lt ht)
      have h := hW_cubic t ht
      nlinarith [mul_nonneg (le_of_lt hc) (pow_nonneg hW_nn' 3)]
  have hW_ge : ∀ t, 0 ≤ t → δ ≤ W t := by
    intro t ht
    obtain ⟨s, hst, hWs⟩ := h_all t
    exact le_trans hWs (hW_anti (mem_Ici.mpr ht) (mem_Ici.mpr (le_trans ht hst)) hst)
  set μ := c * δ ^ 2
  have hμ_pos : 0 < μ := mul_pos hc (sq_pos_of_pos hδ)
  have hW_linear_bound : ∀ t, 0 < t → W' t ≤ -μ * W t := by
    intro t ht
    have hW_ge_δ := hW_ge t (le_of_lt ht)
    have hW_nn' := hW_nn t (le_of_lt ht)
    have h_cubic := hW_cubic t ht
    have h2 : δ ^ 2 * W t ≤ W t ^ 2 * W t := by
      apply mul_le_mul_of_nonneg_right _ hW_nn'
      exact pow_le_pow_left₀ hδ.le hW_ge_δ 2
    have h3 : c * (δ ^ 2 * W t) ≤ c * (W t ^ 2 * W t) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hc)
    have h4 : c * W t ^ 3 = c * (W t ^ 2 * W t) := by ring
    nlinarith
  have hW_exp := comparison_decay W W' μ hW_cont hW_deriv hW_linear_bound
  have hW0_pos : 0 < W 0 + 1 := by linarith [hW_nn 0 le_rfl]
  have hW_bound2 : ∀ t, 0 ≤ t → W t ≤ (W 0 + 1) * exp (-μ * t) := by
    intro t ht
    calc W t ≤ W 0 * exp (-μ * t) := hW_exp t ht
      _ ≤ (W 0 + 1) * exp (-μ * t) := mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)
  obtain ⟨T, hT⟩ := exponential_decay_convergence W (W 0 + 1) μ hμ_pos hW0_pos hW_bound2 δ hδ
  linarith [hT (max T 0) (le_max_left T 0), hW_ge (max T 0) (le_max_right T 0)]

/-- **Critical order parameter convergence.**
    At K = Kc: if the Lyapunov W satisfies cubic decay and r ≤ γ_max·W,
    then r(t) → 0. -/
theorem continuum_critical_r_convergence
    (r W W' : ℝ → ℝ) (c γ_max : ℝ) (hc : 0 < c) (hγ_max_pos : 0 < γ_max)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_nn : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_cubic : ∀ t, 0 < t → W' t ≤ -(c * W t ^ 3))
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t) :
    Tendsto r atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuum_critical_W_convergence W W' c hc
    hW_cont hW_nn hW_deriv hW_cubic (ε / γ_max) (div_pos hε hγ_max_pos)
  exact ⟨max T 0, fun t ht => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr_nn t)]
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    calc r t ≤ γ_max * W t := hr_le t ht0
      _ < γ_max * (ε / γ_max) := by
          exact mul_lt_mul_of_pos_left (hT t htT) hγ_max_pos
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hγ_max_pos)⟩

/-! ## Combined non-supercritical convergence -/

/-- **Continuum K ≤ Kc implies r → 0.**
    Combines subcritical (exponential) and critical (algebraic) decay. -/
theorem continuum_non_supercritical_convergence
    (γ : Ω → ℝ) (K : ℝ) (r W W' : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_nn : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hW0_pos : 0 < W 0)
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t)
    (h_le_Kc : K ≤ continuumKc γ μ)
    (h_subcrit_bound : K < continuumKc γ μ →
      ∀ t, 0 < t → W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (h_crit_bound : K = continuumKc γ μ →
      ∃ c > 0, ∀ t, 0 < t → W' t ≤ -(c * W t ^ 3)) :
    Tendsto r atTop (nhds 0) := by
  rcases eq_or_lt_of_le h_le_Kc with heq | hlt
  · obtain ⟨c, hc, hW_cubic⟩ := h_crit_bound heq
    exact continuum_critical_r_convergence r W W' c γ_max hc hγ_max_pos
      hW_cont hW_nn hW_deriv hW_cubic hr_le hr_nn
  · exact kuramoto_sharp_threshold γ K r γ_min γ_max hγ_min_pos hγ_max_pos
      h_inv_pos hlt W W' hW0_pos hW_cont hW_deriv (h_subcrit_bound hlt) hr_le hr_nn

end
