/-
  KuramotoGammaMinConvergence.lean
  =================================
  Proves r(t) → r* for the continuum OA model when γ(ω) ≥ γ_min > 0.

  MOTIVATION: kuramoto_continuum_wired6 requires the opaque hypothesis
    hδ₀_body_lb : ∃ c > 0, ∀ M > 0, c/M ≤ δ₀_body M
  which is not physically obvious. This file derives it automatically from
  two physically natural conditions:
    (1) hγ_lb : ∀ ω, γ_min ≤ γ ω    (minimum damping)
    (2) hα_0_lb : ∀ ω, α₀_lb ≤ α ω 0  (initial activity lower bound)

  KEY ARGUMENT for hδ₀_body_lb:
    Set δ₀_body M := α₀_lb * γ_min / (2 * M).
    For M < γ_min: body {γ ≤ M} = ∅ (since γ ≥ γ_min), so hα_0_body is vacuous.
    For M ≥ γ_min: α₀_lb * γ_min / (2*M) ≤ α₀_lb * γ_min / (2*γ_min)
                             = α₀_lb / 2 ≤ α₀_lb ≤ α(ω,0).
    With c = α₀_lb * γ_min / 4: c/M ≤ α₀_lb * γ_min / (4*M) ≤ δ₀_body M. ✓

  RESULT: removes hδ₀_body_lb from the caller's obligation when γ is
  bounded below. Covers all physical models with positive minimum damping,
  including constant-γ (Lorentzian-OA) and smooth positive-damping models.

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired6

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Continuum convergence under γ lower bound.**

    Replaces the structural hypothesis `hδ₀_body_lb` of `kuramoto_continuum_wired6`
    with two physically natural conditions:
    - `hγ_lb`: all oscillators have damping ≥ γ_min > 0
    - `hα_0_lb`: all oscillators start with activity ≥ α₀_lb > 0

    The choice δ₀_body M := α₀_lb * γ_min / (2 * M) satisfies all wired6
    structural hypotheses automatically. -/
theorem kuramoto_gamma_min_convergence [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
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
    (r_min : ℝ) (hr_min_pos : 0 < r_min)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ)
    -- Physical lower bounds replacing the structural hδ₀_body_lb
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_lb : ∀ ω, γ_min ≤ γ ω)
    (α₀_lb : ℝ) (hα₀_lb : 0 < α₀_lb) (hα_0_lb : ∀ ω, α₀_lb ≤ α ω 0) :
    Tendsto r atTop (nhds r_star) := by
  -- δ₀_body M := α₀_lb * γ_min / (2 * M) decays as 1/M
  let δ₀_body : ℝ → ℝ := fun M => α₀_lb * γ_min / (2 * M)
  apply kuramoto_continuum_wired6 γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hr_cont hr_bdd hr_nn
    hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv r_min hr_min_pos hr_bound
    δ₀_body
    -- hδ₀_body_pos: α₀_lb * γ_min / (2 * M) > 0 for M > 0
    (fun M hM => by positivity)
    -- hα_0_body: δ₀_body M ≤ α(ω,0) when γ(ω) ≤ M
    (fun M hM ω hγω => by
      -- γ(ω) ≤ M and γ(ω) ≥ γ_min, so M ≥ γ_min
      have hM_ge : γ_min ≤ M := le_trans (hγ_lb ω) hγω
      -- α₀_lb * γ_min / (2 * M) ≤ α₀_lb (since γ_min ≤ 2 * M)
      have h1 : α₀_lb * γ_min / (2 * M) ≤ α₀_lb := by
        have h2M : (0 : ℝ) < 2 * M := by linarith
        rw [div_le_iff₀ h2M]
        nlinarith
      exact le_trans h1 (hα_0_lb ω))
    hγ_sq_int
    -- hδ₀_body_lb: c = α₀_lb * γ_min / 4 satisfies c/M ≤ δ₀_body M
    ⟨α₀_lb * γ_min / 4, by positivity, fun M hM => by
      -- c/M = (α₀_lb * γ_min / 4) / M = α₀_lb * γ_min / (4 * M)
      -- δ₀_body M = α₀_lb * γ_min / (2 * M)
      -- Need: α₀_lb * γ_min / (4 * M) ≤ α₀_lb * γ_min / (2 * M)
      -- This holds since 2 * M ≤ 4 * M (M > 0)
      have ha : (0 : ℝ) ≤ α₀_lb * γ_min := by positivity
      have h2M : (0 : ℝ) < 2 * M := by linarith
      have h4M : (0 : ℝ) < 4 * M := by linarith
      have h1 : α₀_lb * γ_min / 4 / M = α₀_lb * γ_min / (4 * M) := by ring
      rw [h1]
      exact div_le_div_of_nonneg_left ha h2M (by linarith)⟩
end
