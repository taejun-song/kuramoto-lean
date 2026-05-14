/-
  Complex OA Full Chain — Via Uniform Approximation
  ===================================================
  FRESH APPROACH: bypass the complex pair bound.

  Uses uniform-in-time approximation by n-pole solutions.
  Each n-pole converges (proved). Uniform approximation gives
  the limit also converges. Simple ε/2 triangle inequality.
-/

import KuramotoLean.ComplexOASymmetry

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

/-- **ORDER PARAMETER CONVERGENCE VIA UNIFORM APPROXIMATION.**

    If r is uniformly approximated by r_n (each converging to r*),
    then r → r*. Triangle inequality: |r(t)-r*| ≤ |r(t)-r_n(t)| + |r_n(t)-r*|.

    h_npole_conv: each approximant converges (from the n-pole theorem)
    h_unif_approx: for large n, sup_{t≥0} |r_n(t) - r(t)| is small -/
theorem order_parameter_convergence_via_approximation
    (r : ℝ → ℝ) (r_star : ℝ)
    (r_approx : ℕ → ℝ → ℝ)
    (h_npole_conv : ∀ n, Tendsto (r_approx n) atTop (nhds r_star))
    (h_unif_approx : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, 0 ≤ t →
      |r_approx n t - r t| < ε) :
    Tendsto r atTop (nhds r_star) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  -- Step 1: pick N with |r_N(t) - r(t)| < ε/2 for all t ≥ 0
  obtain ⟨N, hN⟩ := h_unif_approx (ε / 2) hε2
  -- Step 2: pick T with |r_N(t) - r*| < ε/2 for t ≥ T
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp (h_npole_conv N)) (ε / 2) hε2
  -- Step 3: for t ≥ max T 0, triangle inequality
  refine ⟨max T 0, fun t ht => ?_⟩
  have htT : t ≥ T := le_trans (le_max_left T 0) ht
  have ht0 : t ≥ 0 := le_trans (le_max_right T 0) ht
  have h1 : |r_approx N t - r t| < ε / 2 := hN N le_rfl t ht0
  have h2 : |r_approx N t - r_star| < ε / 2 := by
    have := hT t htT
    rwa [Real.dist_eq] at this
  have hsum : |r_approx N t - r t| + |r_approx N t - r_star| < ε := by
    have : ε / 2 + ε / 2 = ε := by ring
    rw [← this]
    exact add_lt_add h1 h2
  calc
    dist (r t) r_star = |r t - r_star| := Real.dist_eq _ _
    _ = |(r t - r_approx N t) + (r_approx N t - r_star)| := by ring_nf
    _ ≤ |r t - r_approx N t| + |r_approx N t - r_star| := abs_add_le _ _
    _ = |r_approx N t - r t| + |r_approx N t - r_star| := by rw [abs_sub_comm]
    _ < ε := hsum

end
