/-
  ApproximationBridge.lean
  ========================
  Bridge between the continuum and discrete (n-pole) frameworks
  for the Kuramoto global stability proof.

  Contains:
  - npole_V_eventually_small: PROVED (0 sorry)
    V_n → 0 for any FullChainData, from full_chain_convergence.
  - npole_approximation_gives_small_V: 1 sorry
    The complete n-pole approximation argument.

  The single sorry encapsulates the standard approximation theory:
    1. Approximate μ by n-pole measure (exists_discrete_approx)
    2. Solve n-pole ODE at sample points (ODE existence + FullChainData)
    3. V_n → 0 by full_chain_convergence (proved)
    4. Gronwall controls |α(ωₖ,t) - αₖ(t)| (oa_continuous_dependence_on_g)
    5. Combine: V(T) ≈ V_n(T) < ε
  Each sub-step uses a 0-sorry theorem. The sorry is the wiring.
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

/-- **N-pole approximation gives V(T) < ε.**

The proof combines three 0-sorry ingredients:
  1. `exists_discrete_approx` (MeasureApproximation): approximate ∫fdμ by ∑cₖf(ωₖ)
  2. `full_chain_convergence` (FullChainConvergence): V_n(t) → 0 for n-pole systems
  3. `oa_continuous_dependence_on_g` (ODEContinuousDependence): Gronwall proximity

Proof outline:
  Given ε > 0, pick sample points ωₖ with weights cₖ approximating μ.
  At those points, solve the n-pole ODE (γₖ = γ(ωₖ), coupling K).
  By full_chain_convergence, ∃ T with V_n(T) = ∑cₖ(αₖ(T)-α*ₖ)² < ε/3.
  By Gronwall continuous dependence on [0,T]:
    |α(ωₖ,t) - αₖ(t)| ≤ C·δ where δ is the r-approximation error.
  This gives |∑cₖ(α(ωₖ,T)-α*(ωₖ))² - V_n(T)| < ε/3.
  By exists_discrete_approx at time T:
    |∫(α(·,T)-α*)²dμ - ∑cₖ(α(ωₖ,T)-α*(ωₖ))²| < ε/3.
  Triangle inequality: V(T) < ε. -/
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
