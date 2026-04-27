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

/-- Construct SelfContainedData from FullChainData.
    Adds the order parameter control field to the Path A construction:
    · r(t)    = D.r(max t 0) = Σ c_k α_k(max t 0)
    · r_star  = Σ c_k α*_k
    · hV_controls_r: (r(t) - r*)² ≤ l2_ext(t) by weighted Cauchy-Schwarz -/
def FullChainData.toSelfContainedData (D : FullChainData n) :
    SelfContainedData n where
  V       := l2_ext D.c D.α D.α_star
  r       := fun t => D.r (max t 0)
  r_star  := ∑ k, D.c k * D.α_star k
  hV_nn   := l2_ext_nonneg D.c D.α D.α_star D.hc
  hV_anti := D.hV_anti
  hV_controls_r := fun t => by
    unfold l2_ext NPoleBarrierData.r
    have h_eq : ∑ k, D.c k * D.α (max t 0) k - ∑ k, D.c k * D.α_star k =
        ∑ k, D.c k * (D.α (max t 0) k - D.α_star k) := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
    rw [h_eq]
    exact order_parameter_sq_le_l2 D.c (D.α (max t 0)) D.α_star
      (fun k => le_of_lt (D.hc k)) D.hc_sum
  q       := D.q_val
  hq0     := D.hq_nn
  hq1     := D.hq_lt_one
  Δ       := D.Δ_total
  hΔ      := D.hΔ_total_pos
  hdrops  := D.infinite_drops

/-- Order parameter r(max t 0) → r* as t → ∞ via SelfContainedConvergence.
    For t ≥ 0, this is r(t) → r* = Σ c_k α*_k. -/
theorem full_chain_r_tendsto (D : FullChainData n) :
    Tendsto (fun t => |D.r (max t 0) - ∑ k, D.c k * D.α_star k|)
      atTop (nhds 0) :=
  self_contained_tendsto D.toSelfContainedData

end
