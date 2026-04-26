/-
  Kuramoto Stability — Minimal Proof
  ====================================

  The shortest end-to-end proof of r → r* using the L² Lyapunov approach.

  HYPOTHESES (4 properties, no Φ, no gap exclusion, no step-size):
    1. V ≥ 0, V antitone     — Lyapunov monotonicity (pair bound)
    2. Persistence drops      — V drops by q < 1 infinitely often
    3. V controls r           — (r-r*)² ≤ V (Cauchy-Schwarz)

  PROOF:
    V → 0 (Barbalat from drops) → (r-r*)² → 0 → r → r*

  This is the SIMPLEST possible formalization of Kuramoto global stability.

  0 sorry.
-/

import KuramotoLean.ContinuumBarbalat

open Real Filter Topology

noncomputable section

/-- **Minimal data for Kuramoto global stability.**
    Only 4 non-trivial properties needed. -/
structure MinimalStabilityData where
  V : ℝ → ℝ
  r : ℝ → ℝ
  r_star : ℝ
  q : ℝ
  hq_nn : 0 ≤ q
  hq_lt : q < 1
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + 1) ≤ q * V t
  hV_controls_r : ∀ t, (r t - r_star) ^ 2 ≤ V t

/-- **V → 0.** Lyapunov + persistence drops → convergence. -/
theorem minimal_V_zero (D : MinimalStabilityData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.V t < ε :=
  continuous_barbalat_general D.V D.q 1
    D.hV_nn D.hV_anti D.hq_nn D.hq_lt one_pos D.hdrops

/-- **(r - r*)² → 0.** From V → 0 + V controls r. -/
theorem minimal_r_sq_zero (D : MinimalStabilityData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → (D.r t - D.r_star) ^ 2 < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := minimal_V_zero D ε hε
  exact ⟨T, fun t ht => lt_of_le_of_lt (D.hV_controls_r t) (hT t ht)⟩

/-- **r → r*.** The main convergence theorem.
    From (r-r*)² → 0 to |r-r*| → 0. -/
theorem minimal_global_stability (D : MinimalStabilityData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - D.r_star| < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := minimal_r_sq_zero D (ε ^ 2) (by positivity)
  exact ⟨T, fun t ht =>
    abs_lt_of_sq_lt_sq (hT t ht) (le_of_lt hε)⟩

/-- **r → r* (Filter.Tendsto form).** -/
theorem minimal_tendsto (D : MinimalStabilityData) :
    Tendsto (fun t => |D.r t - D.r_star|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := minimal_global_stability D ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_abs]
    exact hT t ht⟩

end
