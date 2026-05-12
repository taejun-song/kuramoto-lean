/-
  N-Pole FullChainData from Discrete Approximation
  ==================================================
  Constructs FullChainData from a discrete n-pole system:
    - n points with weights c₁,...,cₙ > 0 summing to 1
    - γₖ > 0 (damping rates)
    - K > K_c (supercritical coupling)
    - Initial data α₀ₖ ∈ (0,1)

  For a discrete measure μ = Σ cₖ δ_{ωₖ}, the OA ODE reduces to the
  n-pole system and all FullChainData fields are explicit.

  0 sorry.
-/

import KuramotoLean.FullChainConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-- Input data for constructing FullChainData from a discrete n-pole system.
    All auxiliary constants (c_min, γ_max, δ_star, ε_inst) are provided
    explicitly; the caller verifies the bounds. -/
structure DiscreteNPoleInput (n : ℕ) extends NPoleBarrierData n where
  hn : 0 < n
  α_star : Fin n → ℝ
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hc_sum : ∑ k, c k = 1
  hα_init_pos : ∀ k, 0 < α 0 k
  hα_init_lt_one : ∀ k, α 0 k < 1
  lam : ℝ
  hlam : 0 < lam
  hdisp : npoleDispersion γ c K lam = 1
  γ_max : ℝ
  hγ_max_pos : 0 < γ_max
  hγ_max : ∀ k, γ k ≤ γ_max
  δ_star : ℝ
  hδ_star_pos : 0 < δ_star
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  c_min : ℝ
  hc_min_pos : 0 < c_min
  hc_min : ∀ k, c_min ≤ c k
  ε_inst : ℝ
  hε_pos : 0 < ε_inst
  hε_small : (K / 2) * (∑ k, c k) * ε_inst ^ 2 ≤ lam / 2
  hε_beta : K * (c_min * ε_inst * exp (-2)) ≤ 2 * γ_max

/-- **Main construction**: FullChainData from discrete n-pole input. -/
def DiscreteNPoleInput.toFullChainData (D : DiscreteNPoleInput n) :
    FullChainData n where
  toNPoleBarrierData := D.toNPoleBarrierData
  hn := D.hn
  α_star := D.α_star
  hα_star_pos := D.hα_star_pos
  hα_star_lt := D.hα_star_lt
  h_equil := D.h_equil
  hc_sum := D.hc_sum
  hα_init_pos := D.hα_init_pos
  hα_init_lt_one := D.hα_init_lt_one
  lam := D.lam
  hlam := D.hlam
  hdisp := D.hdisp
  γ_max := D.γ_max
  hγ_max_pos := D.hγ_max_pos
  hγ_max := D.hγ_max
  δ_star := D.δ_star
  hδ_star_pos := D.hδ_star_pos
  hα_star_lb := D.hα_star_lb
  c_min := D.c_min
  hc_min_pos := D.hc_min_pos
  hc_min := D.hc_min
  ε_inst := D.ε_inst
  hε_pos := D.hε_pos
  hε_small := D.hε_small
  hε_beta := D.hε_beta

/-- **Convergence**: For a discrete n-pole system with K > K_c,
    the order parameter r(t) = Σ cₖ αₖ(t) converges to r* = Σ cₖ α*ₖ. -/
theorem discrete_npole_convergence (D : DiscreteNPoleInput n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.toNPoleBarrierData.r t - ∑ k, D.c k * D.α_star k| < ε :=
  full_chain_convergence D.toFullChainData

end
