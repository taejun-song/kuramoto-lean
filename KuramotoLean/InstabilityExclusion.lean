/-
  Kuramoto Stability — Instability Exclusion
  ============================================

  Combines strict Lyapunov decrease on [0,1)^n with instability at α = 0
  to prove V → 0 from V antitone alone.

  The key insight: {dV/dt = 0} ∩ {V > 0} ∩ [0,1)^n = {0} (boundary strict
  Lyapunov), and α = 0 is unstable (instability Lyapunov). Together these
  exclude all possibilities for V → L > 0.

  This is formalized as: V antitone + strict decrease except at {0, α*}
  + instability repulsion at 0 → V → 0.

  0 sorry target.
-/

import KuramotoLean.BoundaryStrictLyapunov
import KuramotoLean.InstabilityLyapunov
import KuramotoLean.ContinuumBarbalat

open Filter Topology

noncomputable section

/-! ## Abstract convergence from instability exclusion

The core combinatorial argument: if V is antitone with two possible
accumulation points (0 and V₀) and the V₀ accumulation point is
repelled (W grows), then V → 0.

We formalize this as: V antitone + drops whenever W is large enough
+ W can't stay small forever → V → 0. -/

/-- **Instability-excluded convergence data.**
    V: Lyapunov function (antitone, ≥ 0)
    W: instability function
    When W ≥ η, V drops (pair coercivity from bounded-below components).
    W can't stay below η forever (instability growth). -/
structure InstabilityExclusionData where
  V : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  W : ℝ → ℝ
  hW_nn : ∀ t, 0 ≤ W t
  η : ℝ
  hη : 0 < η
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  Δ : ℝ
  hΔ : 0 < Δ
  -- When W ≥ η (components bounded below), V drops
  hdrops : ∀ t, η ≤ W t → V (t + Δ) ≤ q * V t
  -- W can't stay below η forever (instability repulsion)
  hW_escapes : ∀ T : ℝ, ∃ t, T ≤ t ∧ η ≤ W t

/-- **V → 0 from instability exclusion.**
    The drops occur infinitely often (from hW_escapes + hdrops),
    and each drop multiplies V by q < 1. By Barbalat, V → 0. -/
theorem instability_exclusion_convergence (D : InstabilityExclusionData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.V t < ε := by
  have hdrops_io : ∀ T : ℝ, ∃ t, T ≤ t ∧ D.V (t + D.Δ) ≤ D.q * D.V t := by
    intro T
    obtain ⟨t, ht, hW⟩ := D.hW_escapes T
    exact ⟨t, ht, D.hdrops t hW⟩
  exact continuous_barbalat_general D.V D.q D.Δ D.hV_nn D.hV_anti
    D.hq0 D.hq1 D.hΔ hdrops_io

theorem instability_exclusion_tendsto (D : InstabilityExclusionData) :
    Tendsto D.V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := instability_exclusion_convergence D ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (D.hV_nn t)]
    exact hT t ht⟩

/-- **V → 0 implies r → r* when (r-r*)² ≤ V.** -/
theorem instability_exclusion_global_stability (D : InstabilityExclusionData)
    (r : ℝ → ℝ) (r_star : ℝ)
    (hV_controls_r : ∀ t, (r t - r_star) ^ 2 ≤ D.V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |r t - r_star| < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := instability_exclusion_convergence D (ε ^ 2) (by positivity)
  exact ⟨T, fun t ht =>
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt (hV_controls_r t) (hT t ht)) (le_of_lt hε)⟩

end
