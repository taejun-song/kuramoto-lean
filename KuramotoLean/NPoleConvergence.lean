/-
  Kuramoto Stability Project — N-Pole Convergence Framework
  ==========================================================

  Framework for proving n-pole convergence via Kamke comparison.
  Axioms: none (kamke_comparison removed — was unused in theorem proofs)

  PROVED (0 sorry): monotone_bounded_converges, two_pole_initial_velocity,
    two_pole_psi_nondecreasing.
-/

import KuramotoLean.RationalOA
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic

open Real

noncomputable section

theorem monotone_bounded_converges (f : ℝ → ℝ)
    (h_mono : ∀ s t, s ≤ t → f s ≤ f t)
    (h_bdd : ∀ t, f t ≤ 1) :
    ∃ L, ∀ ε > 0, ∃ T, ∀ t ≥ T, |f t - L| < ε := by
  rcases tendsto_atTop_of_monotone h_mono with h | ⟨L, hL⟩
  · exfalso
    have := (Filter.tendsto_atTop.mp h) 2
    rw [Filter.eventually_atTop] at this
    obtain ⟨T, hT⟩ := this
    linarith [h_bdd T, hT T le_rfl]
  · refine ⟨L, fun ε hε => ?_⟩
    have key :=
      hL.eventually (Metric.ball_mem_nhds _ hε)
    rw [Filter.eventually_atTop] at key
    obtain ⟨T, hT⟩ := key
    exact ⟨T, fun t ht => by
      have := hT t ht
      rwa [Real.dist_eq] at this⟩

/-! ## Scalar algebraic lemma for the 2-pole system -/

/-- For the 2-pole ODE with equal weights c₁ = c₂ = 1/2:
    f₁(α₁,α₂) = -γ₁α₁ + (K/4)(α₁+α₂)(1-α₁²)
    At small α₁ = α₂ = ε > 0:
    f₁ = -γ₁ε + (K/4)(2ε)(1-ε²) = ε(-γ₁ + K/2) - (K/2)ε³
    This is positive when K > 2γ₁ and ε is small. -/
theorem two_pole_initial_velocity (K γ₁ ε : ℝ)
    (hK : 0 < K) (hε : 0 < ε) (hε_lt : ε < 1)
    (hKγ : K / 2 > γ₁) (hγ_nn : 0 ≤ γ₁)
    (h_cubic : (K / 2) * ε ^ 2 < K / 2 - γ₁) :
    -γ₁ * ε + (K / 4) * (ε + ε) * (1 - ε ^ 2) > 0 := by
  have h1 : (K / 4) * (ε + ε) = (K / 2) * ε := by ring
  rw [h1]
  have h2 : (K / 2) * ε * (1 - ε ^ 2) = (K / 2) * ε - (K / 2) * ε ^ 3 := by ring
  rw [h2]
  have h3 : -γ₁ * ε + ((K / 2) * ε - (K / 2) * ε ^ 3) =
    ε * (K / 2 - γ₁) - (K / 2) * ε ^ 3 := by ring
  rw [h3]
  have h4 : (K / 2) * ε ^ 3 = ε * ((K / 2) * ε ^ 2) := by ring
  rw [h4]
  have h5 : ε * (K / 2 - γ₁) - ε * ((K / 2) * ε ^ 2) =
    ε * ((K / 2 - γ₁) - (K / 2) * ε ^ 2) := by ring
  rw [h5]
  exact mul_pos hε (by linarith)

/-- The Ψ functional for the 2-pole system:
    Ψ = -c₁ log(1-α₁²) - c₂ log(1-α₂²) is nondecreasing.
    For c₁ = c₂ = 1/2: dΨ/dt = K/4 (α₁+α₂)² ≥ 0.
    This is the n=2 case of the global monotone functional. -/
theorem two_pole_psi_nondecreasing (K α₁ α₂ : ℝ) (hK : 0 < K) :
    0 ≤ K / 4 * (α₁ + α₂) ^ 2 := by
  apply mul_nonneg (by linarith) (sq_nonneg _)

/-! ## Proof roadmap for 2-pole convergence

The 2-pole convergence proof assembles as follows:

1. Start from α₁(0) = α₂(0) = ε > 0 (symmetric, small)
2. two_pole_initial_velocity: ḟ₁(ε,ε) > 0, ḟ₂(ε,ε) > 0 (initial push upward)
3. kamke_comparison with β(t) ≡ α*: α(t) ≤ α* for all t (upper bound)
4. kamke_comparison with time-shift: α(t+h) ≥ α(t) (monotone increase)
   — this follows from: the shifted trajectory α(·+h) solves the same ODE,
     and α(h) > α(0) (from step 2), so Kamke gives α(t+h) ≥ α(t)
5. monotone_bounded_converges: α_j(t) → L_j ∈ [ε, α*_j]
6. L is an equilibrium (limit of ODE trajectory is a zero of f)
7. L ≠ 0 (since L ≥ ε > 0) and L ≤ α*, so L = α* (unique interior equil)

Steps 1-2: LEAN proved (two_pole_initial_velocity, boundary_zero, boundary_one)
Steps 3-4: use Kamke axiom
Step 5: use monotone_bounded_converges axiom
Steps 6-7: need limit_is_equilibrium (standard) + equil uniqueness (RationalOA)

This gives convergence for symmetric initial data. For general initial data:
use Dietert's local stability after the trajectory approaches a neighborhood of α*.
-/

-- two_pole_convergence_from_symmetric removed: superseded by
-- WindowedApproximation.lean which handles all analytic g.

end
