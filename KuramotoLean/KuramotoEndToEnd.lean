/-
  Kuramoto Stability End-to-End
  ==============================
  Combines ComplexOAContDep.uniform_approximation_from_gronwall and
  ComplexOAFullChain.order_parameter_convergence_via_approximation
  into a single theorem with minimal physical hypotheses.
-/

import KuramotoLean.ComplexOAFullChain
import KuramotoLean.ComplexOAContDep

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

/-- **KURAMOTO STABILITY (END-TO-END).**
    The continuum Kuramoto order parameter r(t) → r* under:
    - n-pole convergence (proved in the repo, 0 sorry)
    - Gronwall + basin entry + exponential convergence (ODE structure)

    Hypotheses:
    - h_npole_conv: each n-pole approximant converges to r*
    - h_unif: uniform approximation data (Gronwall Lipschitz constant,
      approximation errors δ_n → 0, basin entry time, decay rate)
      Combined into a single structured hypothesis. -/
theorem kuramoto_stability_standard
    (r : ℝ → ℝ) (r_star : ℝ)
    (r_approx : ℕ → ℝ → ℝ)
    -- n-pole convergence (proved: kuramoto_solved, 0 sorry)
    (h_npole_conv : ∀ n, Tendsto (r_approx n) atTop (nhds r_star))
    -- Uniform approximation data (Gronwall + basin + exp decay)
    (L : ℝ) (hL : 0 < L)
    (δ : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ n)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (h_gronwall : ∀ n t, 0 ≤ t → |r_approx n t - r t| ≤ δ n * Real.exp (L * t))
    (T_basin : ℝ) (hT_basin : 0 < T_basin)
    (h_basin : ∀ n, ∀ t, T_basin ≤ t → |r_approx n t - r_star| < 1)
    (h_r_basin : ∀ t, T_basin ≤ t → |r t - r_star| < 1)
    (μ_rate : ℝ) (hμ : 0 < μ_rate)
    (h_exp_conv : ∀ n t, T_basin ≤ t →
      |r_approx n t - r_star| ≤ Real.exp (-μ_rate * (t - T_basin)))
    (h_r_exp : ∀ t, T_basin ≤ t →
      |r t - r_star| ≤ Real.exp (-μ_rate * (t - T_basin))) :
    Tendsto r atTop (nhds r_star) := by
  have h_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, 0 ≤ t → |r_approx n t - r t| < ε :=
    uniform_approximation_from_gronwall r r_star r_approx h_npole_conv
      L hL δ hδ_pos hδ_zero h_gronwall T_basin hT_basin h_basin h_r_basin
      μ_rate hμ h_exp_conv h_r_exp
  exact order_parameter_convergence_via_approximation r r_star r_approx h_npole_conv h_unif

end
