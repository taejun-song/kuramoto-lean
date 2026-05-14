/-
  ApproximationBridge.lean
  ========================
  Bridge between the continuum and discrete (n-pole) frameworks
  for the Kuramoto global stability proof.

  Contains:
  - npole_V_eventually_small: PROVED (0 sorry)
    V_n → 0 for any FullChainData, from full_chain_convergence.

  0 sorry.
-/

import KuramotoLean.FullChainConvergence
import KuramotoLean.ContinuumSolvedFinal
import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.MeasureApproximation
import KuramotoLean.NPoleFromDiscrete
import KuramotoLean.ODEContinuousDependence

open MeasureTheory Real Set Filter Topology Finset

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem npole_V_eventually_small
    {n : ℕ} (D : FullChainData n) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t, T ≤ t →
      ∑ k, D.c k * (D.toNPoleBarrierData.α t k - D.α_star k) ^ 2 < ε := by
  have hV := D.V_tendsto_zero
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T, hT⟩ := hV ε hε
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := le_trans (le_max_right T 0) ht
  have hT_le : T ≤ t := le_trans (le_max_left T 0) ht
  have hVt := hT t hT_le
  simp only [Real.dist_eq, sub_zero] at hVt
  rw [abs_of_nonneg (l2_ext_nonneg D.c D.α D.α_star D.hc t),
      l2_ext_eq D.c D.α D.α_star t ht_nn] at hVt
  exact hVt

end
