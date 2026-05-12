/-
  ApproximationBridge.lean
  ========================
  Bridge lemmas for V_pointwise_small. Connects:
    1. MeasureApproximation (exists_discrete_approx)
    2. NPoleFromDiscrete (discrete_npole_convergence / FullChainData)
    3. ODEContinuousDependence (Gronwall)

  Sorry inventory:
    - npole_V_eventually_small: CLOSED (from V_tendsto_zero)
    - npole_approx_combined: 1 sorry (the full approximation argument)

  The single remaining sorry encapsulates the standard ODE approximation
  theory: given a continuum OA system, approximate by n-pole, bound the
  error by Gronwall, combine with discrete convergence.
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

/-! ## Closed: V_n → 0 from full_chain_convergence -/

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

/-! ## The combined approximation argument

This single lemma encapsulates the entire n-pole approximation strategy.
It is the ONLY remaining sorry in the global stability proof.

Mathematical content (all standard):
  1. Use exists_discrete_approx to approximate ∫ f dμ by ∑ cₖ f(ωₖ).
  2. At the sample points ωₖ, solve the n-pole ODE with γₖ = γ(ωₖ),
     weights cₖ, coupling K. By supercriticality + Perron-Frobenius,
     the n-pole system has a unique equilibrium α*ₖ in (0,1)ⁿ.
  3. By full_chain_convergence (0 sorry), V_n(T) < ε/3 for large T.
  4. By Gronwall continuous dependence (0 sorry in ODEContinuousDependence),
     |α(ωₖ,t) - αₖ(t)| is controlled by |r - r_n| on [0,T].
  5. The self-consistent r-difference is controlled by the measure
     approximation error via the contraction mapping (also 0 sorry).
  6. For n large enough, all errors are < ε/3, giving V(T) < ε.

Each sub-step uses a theorem that is already proved (0 sorry).
The sorry here is the TYPE-LEVEL WIRING: translating between the
continuum (Ω, μ) framework and the discrete (Fin n) framework,
and managing the quantifier order (n first, then T). -/

theorem npole_approximation_gives_small_V [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (_hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (_hr_cont : Continuous r) (_hr_bdd : ∀ t, |r t| ≤ 1)
    (_hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (_hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (_h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (_hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (_hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (_α_star : Ω → ℝ) (_r_star : ℝ)
    (_hr_star_pos : 0 < _r_star)
    (_hα_star_pos : ∀ ω, 0 < _α_star ω) (_hα_star_lt : ∀ ω, _α_star ω < 1)
    (_hαs_int : Integrable _α_star μ)
    (_hr_star_eq : _r_star = ∫ ω, _α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * _α_star ω = (K / 2) * _r_star * (1 - (_α_star ω) ^ 2))
    (_hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - _α_star ω) ^ 2) μ) :
    ∀ ε > 0, ∃ T : ℝ, ∫ ω, (α ω T - _α_star ω) ^ 2 ∂μ < ε := by
  sorry

end
