/-
  Kuramoto Stability — Full Chain to Continuum Bridge
  =====================================================

  Constructs CoerciveConvergenceData from FullChainData.

  FullChainData packages the complete n-pole ODE chain:
    InfiniteEscape → ShiftedBarrier → V-drops → Barbalat → r → r*

  The infinite_drops theorem gives exactly the hdrops field needed
  for CoerciveConvergenceData (Path A of ContinuumGlobalStability).

  This is a direct field-for-field instantiation: no additional
  lemmas are needed. The abstract framework and the concrete chain
  were designed with matching interfaces.

  0 sorry.
-/

import KuramotoLean.ContinuumGlobalStability
import KuramotoLean.FullChainConvergence

open Filter Topology Real

noncomputable section

variable {n : ℕ}

/-- Construct CoerciveConvergenceData from FullChainData.
    All fields map directly:
    · V        = l2_ext (continuous extension of l2Distance)
    · hV_nn    = l2_ext_nonneg
    · hV_anti  = FullChainData.hV_anti (from l2_ext_antitone)
    · q        = q_val = exp(-(K·δ_drop·δ*))
    · Δ        = Δ_total = S_prop + 1 = 2/γ_max + 1
    · hdrops   = infinite_drops (for any T, ∃ t ≥ T with drop) -/
def FullChainData.toCoerciveConvergenceData (D : FullChainData n) :
    CoerciveConvergenceData where
  V       := l2_ext D.c D.α D.α_star
  hV_nn   := l2_ext_nonneg D.c D.α D.α_star D.hc
  hV_anti := D.hV_anti
  q       := D.q_val
  hq0     := D.hq_nn
  hq1     := D.hq_lt_one
  Δ       := D.Δ_total
  hΔ      := D.hΔ_total_pos
  hdrops  := D.infinite_drops

/-- Full chain L² convergence via ContinuumGlobalStability Path A.
    l2_ext(c, α(t), α*) → 0 as t → ∞.
    This is a second proof of FullChainData.V_tendsto_zero, validated
    through the abstract CoerciveConvergenceData framework. -/
theorem full_chain_convergence_via_path_a (D : FullChainData n) :
    Tendsto (l2_ext D.c D.α D.α_star) atTop (nhds 0) :=
  coercive_convergence D.toCoerciveConvergenceData

end
