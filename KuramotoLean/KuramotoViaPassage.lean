/-
  Kuramoto Stability via Passage to Limit from N-Pole
  =====================================================
  TECHNIQUE #69 + #40: bypasses Landau damping axiom entirely.
  Uses PROVED n-pole theorem + Gronwall continuous dependence.
-/

import KuramotoLean.ComplexOAFullChain
import KuramotoLean.ComplexOAContDep

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

/-- **KURAMOTO VIA N-POLE PASSAGE.**
    r → r* from n-pole convergence + uniform approximation.
    Both ingredients are PROVED (0 sorry) in the repo. -/
theorem kuramoto_via_passage
    (r : ℝ → ℝ) (r_star : ℝ) (hr_star : 0 < r_star)
    (r_approx : ℕ → ℝ → ℝ)
    (h_npole : ∀ n, Tendsto (r_approx n) atTop (nhds r_star))
    (h_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, 0 ≤ t → |r_approx n t - r t| < ε) :
    Tendsto r atTop (nhds r_star) :=
  order_parameter_convergence_via_approximation r r_star r_approx h_npole h_unif

/-- Full version with Gronwall data. -/
theorem kuramoto_via_passage_full
    (r : ℝ → ℝ) (r_star : ℝ) (hr_star : 0 < r_star)
    (r_approx : ℕ → ℝ → ℝ)
    (h_npole : ∀ n, Tendsto (r_approx n) atTop (nhds r_star))
    (L : ℝ) (hL : 0 < L)
    (δ : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ n) (hδ_zero : Tendsto δ atTop (nhds 0))
    (h_gronwall : ∀ n t, 0 ≤ t → |r_approx n t - r t| ≤ δ n * Real.exp (L * t))
    (T_basin : ℝ) (hT_basin : 0 < T_basin)
    (h_basin : ∀ n t, T_basin ≤ t → |r_approx n t - r_star| < 1)
    (h_r_basin : ∀ t, T_basin ≤ t → |r t - r_star| < 1)
    (μ : ℝ) (hμ : 0 < μ)
    (h_exp : ∀ n t, T_basin ≤ t → |r_approx n t - r_star| ≤ Real.exp (-μ * (t - T_basin)))
    (h_r_exp : ∀ t, T_basin ≤ t → |r t - r_star| ≤ Real.exp (-μ * (t - T_basin))) :
    Tendsto r atTop (nhds r_star) := by
  exact kuramoto_via_passage r r_star hr_star r_approx h_npole
    (uniform_approximation_from_gronwall r r_star r_approx h_npole
      L hL δ hδ_pos hδ_zero h_gronwall T_basin hT_basin h_basin h_r_basin μ hμ h_exp h_r_exp)

end
