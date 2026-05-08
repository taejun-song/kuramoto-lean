import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.ContinuumFiniteMoment
import KuramotoLean.ContinuumSolvedStandard
import KuramotoLean.KuramotoFirstMomentConcrete

/-
  GeneralGBodyAbsorbBypass.lean
  =============================

  This file records the finite-first-moment bypass for the remaining
  `h_body_absorb` hypothesis in `GeneralGMainTheorem`.

  The body-restricted LaSalle route is blocked in general because `V_body`
  need not be antitone. For finite first moment, however, the project
  already proves an alternative end-to-end theorem:

  * `kuramoto_first_moment_concrete` handles the standard continuum model
    from full OA data, a global persistence lower bound, and `∫ γ dμ < ∞`.

  The theorem below repackages that result under a name that makes the
  intended use explicit: in the finite-first-moment regime, one can bypass
  a separate proof of `h_body_absorb`.
-/

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Global Lyapunov convergence implies zero-radius body absorption.**

If the full Lyapunov functional
`t ↦ ∫ ω, (α ω t - α_star ω)^2 ∂μ`
converges to `0`, then every truncated body Lyapunov
`t ↦ ∫_{γ ≤ M} (α-α*)^2 dμ`
also converges to `0`, hence satisfies the `h_body_absorb` interface with
absorbing radius `C(M) = 0`.

This is the direct finite-moment bypass for the remaining body hypothesis:
once full `V → 0` is available, no separate body-only asymptotic argument is
needed. -/
theorem h_body_absorb_zero_of_full_lyapunov [IsProbabilityMeasure μ]
    (γ : Ω → ℝ)
    (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hV_zero : Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0)) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < (0 : ℝ) + ε := by
  intro M hM ε hε
  have h_body_zero : Tendsto
      (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ)
      atTop (nhds 0) :=
    body_conv_of_full_conv α α_star hα_sq_int _ (hγ_level M) hV_zero
  rw [Metric.tendsto_atTop] at h_body_zero
  obtain ⟨T, hT⟩ := h_body_zero ε hε
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
  simpa [zero_add] using h

/-- **Finite-first-moment data imply zero-radius body absorption.**

Under the global Leibniz-Barbalat hypotheses for the finite-first-moment
continuum theorem, the full Lyapunov functional tends to zero. Therefore each
body truncation satisfies the `h_body_absorb` condition with absorbing radius
`C(M) = 0`.

This theorem isolates the exact replacement for the missing `h_body_absorb`
input in the finite-first-moment regime. -/
theorem h_body_absorb_zero_of_finite_first_moment [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (α_star : Ω → ℝ)
    (_hα_star_pos : ∀ ω, 0 < α_star ω) (_hα_star_lt : ∀ ω, α_star ω < 1)
    (_hαs_int : Integrable α_star μ)
    (_r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (_hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (_hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hV_anti : Antitone (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ))
    (coercivity : ℝ → ℝ) (h_coer_pos : ∀ M, 0 < M → 0 < coercivity M)
    (h_leibniz_drop : ∀ M, 0 < M → ∃ T : ℝ, ∀ t, T ≤ t →
      (∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) -
          (∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ) ≥
        K * coercivity M *
          ((∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ) -
            (μ {ω | M < γ ω}).toReal)) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < (0 : ℝ) + ε := by
  have hV_nn : ∀ t, 0 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    intro t
    exact integral_nonneg (fun _ => sq_nonneg _)
  set tail_mass : ℝ → ℝ := fun M => (μ {ω | M < γ ω}).toReal
  have h_tail_nn : ∀ M, 0 ≤ tail_mass M := fun _ => ENNReal.toReal_nonneg
  have h_tail_vanish : Tendsto tail_mass atTop (nhds 0) :=
    tail_measure_from_integrable γ hγ hγ_int hγ_level
  have hV_zero : Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) := by
    simpa [tail_mass] using
      (TailBodyBarbalat.LeibnizReductionData.mk
        (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ)
        K hK hV_nn hV_anti tail_mass h_tail_nn h_tail_vanish
        coercivity h_coer_pos h_leibniz_drop).convergence
  exact h_body_absorb_zero_of_full_lyapunov
    (γ := γ) (α := α) (α_star := α_star)
    hγ_level hα_sq_int hV_zero

/-- **Finite-first-moment bypass for `h_body_absorb`.**

For the standard continuum OA system, if `γ` has finite first moment and the
trajectory has a uniform positive lower bound `α₀_lb ≤ α(ω,t)`, then the
order parameter converges to `r_star` without separately supplying the
eventual body absorbing-ball hypothesis from `kuramoto_continuum_standard`.

This theorem is a small interface bridge: it reuses the already-proved
`kuramoto_first_moment_concrete` result in the spot where the general theorem
would otherwise ask for `h_body_absorb`. -/
theorem kuramoto_continuum_standard_of_first_moment [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, 0 < t → |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hV_body_cont : ∀ M, 0 < M → ContinuousOn
        (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0))
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  exact kuramoto_first_moment_concrete γ K hK hγ_nn hγ_meas hγ_level hγ_int
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode h_sc hα_int hα_sq_int hα_inv
    α₀_lb hα₀_lb_pos hα_lb hV_body_cont hμ_body_pos
