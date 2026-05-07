/-
  ContinuumSolvedWired3.lean
  ==========================
  Eliminates `hα_lb`, `hδ_lb_pos`, and `δ_lb` from `kuramoto_continuum_wired2`
  by deriving body persistence internally via `body_persistence_lower_bound`.

  ELIMINATED (now proved internally):
    • δ_lb function (derived as min(δ₀_body M, bodyEquilibrium M K r_min))
    • hδ_lb_pos (positivity of derived δ_lb)
    • hα_lb (α(ω,t) ≥ δ_lb M on body {γ ≤ M}, all t ≥ 0)
    • hr_min_le (r_min ≤ 1, derived from hr_bound + hr_bdd + hr_nn)

  ADDED (to derive body persistence):
    • r_min, hr_min_pos : r(t) ≥ r_min > 0 for all t ≥ 0
    • hr_bound : r(t) ≥ r_min for all t ≥ 0
    • δ₀_body : ℝ → ℝ (explicit initial body lower bound function)
    • hδ₀_body_pos : ∀ M, 0 < M → 0 < δ₀_body M
    • hα_0_body : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → δ₀_body M ≤ α ω 0

  The derived bound is:
    δ_lb M := min (δ₀_body M) (bodyEquilibrium M K r_min)
  where bodyEquilibrium M K r_min = (-M + √(M² + K²·r_min²)) / (K·r_min).

  REMAINING OPEN (3 genuine analytic inputs):
    • hr_star_pos — r_star > 0 (supercritical K > K_c)
    • hμ_body_pos — each body {γ ≤ M} has positive measure
    • h_combined_vanish — C(M) + μ(tail) → 0 (depends on g's tail decay)

  C(M) is explicit:
    K · μ(tail M) / (K · min(δ₀_body M, βeq(M)) · (K·r*/(2M+K·r*)) · μ(body M))

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired2
import KuramotoLean.BodyPersistenceFromODE

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fully wired continuum theorem with body persistence from ODE.**

  Compared to `kuramoto_continuum_wired2`, this derives body persistence
  (α(ω,t) ≥ δ_lb M on {γ ≤ M}) internally from:
    - r(t) ≥ r_min > 0 (lower bound on the order parameter)
    - Initial body lower bound δ₀_body(M) at t = 0

  The derived δ_lb M := min (δ₀_body M) (bodyEquilibrium M K r_min)
  where bodyEquilibrium is the comparison-ODE equilibrium with γ=M, r=r_min. -/
theorem kuramoto_continuum_wired3 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- r is bounded below: r(t) ≥ r_min > 0 for all t ≥ 0
    (r_min : ℝ) (hr_min_pos : 0 < r_min)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    -- Explicit initial body lower bound (per-M function)
    (δ₀_body : ℝ → ℝ)
    (hδ₀_body_pos : ∀ M, 0 < M → 0 < δ₀_body M)
    (hα_0_body : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → δ₀_body M ≤ α ω 0)
    -- Positivity of body measure
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal)
    -- Combined vanishing with δ_lb = min(δ₀_body M, bodyEquilibrium M K r_min)
    (h_combined_vanish : Tendsto
        (fun M => K * (μ {ω | M < γ ω}).toReal /
              (K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
               (K * r_star / (2 * M + K * r_star)) *
               (μ {ω | γ ω ≤ M}).toReal) +
              (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  -- Derive r_min ≤ 1 from hr_bound, hr_bdd, hr_nn
  have hr_min_le : r_min ≤ 1 := by
    have h1 := hr_bound 0 le_rfl
    have h2 := (abs_le.mp (hr_bdd 0)).2
    linarith
  -- Derive body persistence: α(ω,t) ≥ min(δ₀_body M, bodyEquilibrium M K r_min) on {γ ≤ M}
  have hα_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t →
      min (δ₀_body M) (bodyEquilibrium M K r_min) ≤ α ω t := by
    intro M hM ω hγω t ht
    have h_lower := body_persistence_lower_bound (γ ω) M K r (α ω) r_min
      (hγ ω) hγω hK hr_min_pos hr_min_le hr_bound hr_bdd
      (fun t ht => hα_ode ω t (le_of_lt ht))
      (hα_inv ω) (hα_cont ω) t ht
    exact le_trans (min_le_min (hα_0_body M hM ω hγω) le_rfl) h_lower
  -- Positivity of min(δ₀_body M, bodyEquilibrium M K r_min)
  have hδ_lb_pos : ∀ M, 0 < M → 0 < min (δ₀_body M) (bodyEquilibrium M K r_min) := fun M hM =>
    lt_min (hδ₀_body_pos M hM)
      (bodyEquilibrium_pos M K r_min (le_of_lt hM) hK hr_min_pos)
  -- Apply kuramoto_continuum_wired2
  exact kuramoto_continuum_wired2 γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    (fun M => min (δ₀_body M) (bodyEquilibrium M K r_min))
    hδ_lb_pos hα_lb hμ_body_pos h_combined_vanish

end
