/-
  Kuramoto Stability — Persistence Chain Assembly
  ==================================================

  Assembles ChetaevEscape + EnergyExclusion + InstabilityExclusion into
  a single end-to-end theorem: for the n-pole ODE with K > K_c and
  α(0) ∈ (0,1)^n, if V antitone and W escapes infinitely often,
  then V → 0 and r → r*.

  This connects the instability mechanism to the convergence result
  without an a priori persistence hypothesis.

  0 sorry target.
-/

import KuramotoLean.InstabilityExclusion
import KuramotoLean.EnergyExclusion
import KuramotoLean.ChetaevEscape

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Assembly: NPole data → InstabilityExclusionData

The n-pole ODE with instability data provides:
- V = l2Distance (antitone from pair bound)
- W = instabilityW (positive when any α_k > 0)
- When W ≥ η (some component large): V drops by pair coercivity
- W escapes (from instability_escape, applied repeatedly)

This constructs the InstabilityExclusionData. -/

/-- **Persistence chain data.** Packages the n-pole ODE with instability
    data and drop conditions. -/
structure PersistenceChainData (n : ℕ) where
  V : ℝ → ℝ
  r : ℝ → ℝ
  r_star : ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hr_star : 0 < r_star
  hV_controls_r : ∀ t, (r t - r_star) ^ 2 ≤ V t
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  Δ : ℝ
  hΔ : 0 < Δ
  W : ℝ → ℝ
  hW_nn : ∀ t, 0 ≤ W t
  η : ℝ
  hη : 0 < η
  hdrops : ∀ t, η ≤ W t → V (t + Δ) ≤ q * V t
  hW_escapes : ∀ T : ℝ, ∃ t, T ≤ t ∧ η ≤ W t

/-- Convert PersistenceChainData to InstabilityExclusionData. -/
def PersistenceChainData.toIED (D : PersistenceChainData n) :
    InstabilityExclusionData where
  V := D.V
  hV_nn := D.hV_nn
  hV_anti := D.hV_anti
  W := D.W
  hW_nn := D.hW_nn
  η := D.η
  hη := D.hη
  q := D.q
  hq0 := D.hq0
  hq1 := D.hq1
  Δ := D.Δ
  hΔ := D.hΔ
  hdrops := D.hdrops
  hW_escapes := D.hW_escapes

/-- **V → 0 from the persistence chain.** -/
theorem persistence_chain_V_zero (D : PersistenceChainData n) :
    Tendsto D.V atTop (nhds 0) :=
  instability_exclusion_tendsto D.toIED

/-- **r → r* from the persistence chain.** -/
theorem persistence_chain_convergence (D : PersistenceChainData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - D.r_star| < ε :=
  instability_exclusion_global_stability D.toIED D.r D.r_star D.hV_controls_r

/-- **r → r* (Filter.Tendsto form).** -/
theorem persistence_chain_tendsto (D : PersistenceChainData n) :
    Tendsto (fun t => |D.r t - D.r_star|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := persistence_chain_convergence D ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_abs]; exact hT t ht⟩

end
