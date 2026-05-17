import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.ContinuumFiniteMoment
import KuramotoLean.ContinuumSolvedStandard
import KuramotoLean.KuramotoFirstMomentConcrete
import KuramotoLean.BodyPersistenceFromODE
import KuramotoLean.ContinuumSolvedFinal
import KuramotoLean.ContinuumBodyAbsorbBridge

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

/-- **Positive order-parameter floor bypasses `h_body_absorb`.**

Once the dynamics supplies a uniform lower bound `r(t) ≥ r_min > 0`,
the ODE comparison theorem `continuum_body_persistence` upgrades the initial
body lower bounds to persistent body coherence. At that point the project can
call `kuramoto_standard_tendsto` directly, so no separate eventual
absorbing-ball hypothesis `h_body_absorb` needs to be constructed.

This isolates the exact remaining interface in `KuramotoGlobal`: prove
`r_stays_positive`, then apply this theorem. -/
theorem body_persistence_of_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (r_min : ℝ) (hr_min_pos : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (hr_floor : ∀ t, 0 ≤ t → r_min ≤ r t) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
  intro M hM
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hα_ode' : ∀ ω, ∀ t, 0 < t →
      HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t :=
    fun ω t ht => hα_ode ω t (le_of_lt ht)
  exact @continuum_body_persistence Ω _ μ ‹_› γ K r α r_min M hK hγ
    hr_min_pos hr_min_le hM hr_floor hr_bdd hα_ode' hα_inv hα_cont
    (fun ω _ => (hα_inv ω 0 le_rfl).1)
    (h_init_body M hM)

/-- **Positive order-parameter floor yields an explicit body absorbing profile.**

Assume the order parameter stays uniformly positive, so the comparison theorem
produces a persistent lower bound for `α` on each body `{γ ≤ M}`. If those body
sets also have positive measure, then the existing body-Gronwall bridge turns
that persistence profile into an explicit absorbing radius `C(M)` together with
the eventual body estimate required by the tail-body convergence theorems.

This theorem packages the exact `h_body_absorb`-side progress available from an
`r`-floor, independently of the remaining task of proving such a floor from the
initial condition `r(0) > 0`. -/
theorem exists_absorbing_profile_of_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (r_min : ℝ) (hr_min_pos : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (hr_floor : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  have hγ_nn : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have h_body_persist :
      ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
        ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t :=
    body_persistence_of_r_floor (μ := μ) (γ := γ) (K := K)
      hK hγ_pos r α hr_bdd hα_ode hα_cont hα_inv h_init_body
      r_min hr_min_pos hr_min_le hr_floor
  choose δ_lb hδ_lb_pos hα_lb using h_body_persist
  let δ_profile : ℝ → ℝ := fun M =>
    if hM : 0 < M then δ_lb M hM else 1
  have hδ_profile_pos : ∀ M, 0 < M → 0 < δ_profile M := by
    intro M hM
    simp [δ_profile, hM, hδ_lb_pos M hM]
  have hα_profile_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ_profile M ≤ α ω t := by
    intro M hM ω hω t ht
    simp [δ_profile, hM]
    exact hα_lb M hM ω hω t ht
  exact exists_absorbing_profile_from_persistence
    (μ := μ) γ K hK hγ_nn hγ_meas hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    δ_profile hδ_profile_pos hα_profile_lb hμ_body_pos

/-- **Existential positive floor yields an absorbing profile.**

This is the interface-matching version of
`exists_absorbing_profile_of_r_floor`: if a separate argument such as
`r_stays_positive` only produces an existential floor
`∃ r_min > 0, ∀ t ≥ 0, r_min ≤ r t`, then the body-absorption bypass can be
invoked directly without manually extracting the auxiliary bound `r_min ≤ 1`.

The upper bound is recovered from the global a priori estimate `|r(t)| ≤ 1`,
so this theorem isolates the remaining global-stability gap to proving the
existence of the positive floor itself. -/
theorem exists_absorbing_profile_of_pos_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hr_pos_floor : ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  rcases hr_pos_floor with ⟨r_min, hr_min_pos, hr_floor⟩
  have hr_min_le : r_min ≤ 1 := by
    have h0_floor : r_min ≤ r 0 := hr_floor 0 le_rfl
    have h0_upper : r 0 ≤ 1 := (abs_le.mp (hr_bdd 0)).2
    linarith
  exact exists_absorbing_profile_of_r_floor
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    h_init_body r_min hr_min_pos hr_min_le hr_floor hμ_body_pos

/-- **Positive order-parameter floor yields the exact `h_body_absorb` interface.**

This is the hypothesis needed by the tail-body convergence theorems in
`GeneralGMainTheorem`. The theorem packages the existing persistence-to-profile
machinery into the final quantified form:

for each body cutoff `M > 0`, there is an absorbing radius `C M ≥ 0` such that
the body Lyapunov eventually stays below `C M + ε`.

The only dynamic input is an existential positive floor
`∃ r_min > 0, ∀ t ≥ 0, r_min ≤ r t`. -/
theorem h_body_absorb_of_pos_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hr_pos_floor : ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  exact exists_absorbing_profile_of_pos_floor
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    h_init_body hr_pos_floor hμ_body_pos

private theorem shift_continuousOn_right (f : ℝ → ℝ) (T₀ : ℝ)
    (hf : ContinuousOn f (Ici T₀)) :
    ContinuousOn (fun t => f (t + T₀)) (Ici 0) :=
  hf.comp (continuous_add_const T₀).continuousOn
    (fun _ ht => mem_Ici.mpr (by linarith [mem_Ici.mp ht]))

private theorem shift_hasDerivAt_right
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (T₀ t : ℝ)
    (hf : HasDerivAt f (f' (t + T₀)) (t + T₀)) :
    HasDerivAt (fun s => f (s + T₀)) (f' (t + T₀)) t := by
  have hcomp := hf.comp t ((hasDerivAt_id t).add_const T₀)
  simpa only [mul_one] using hcomp

/-- **Eventual positive order-parameter floor yields the body-absorption interface.**

This is the time-shifted version of `h_body_absorb_of_pos_floor`.  It is the
exact bridge needed by the Chetaev-style restart strategy in
`KuramotoGlobal.lean`: once one has an activation time `T₀`, a lower floor
`r(t) ≥ r_min > 0` for all `t ≥ T₀`, and a positive body seed at that same
time, the body-persistence / body-Gronwall machinery should produce the same
eventual absorbing profile as in the time-zero theorem.

The remaining proof obligation is the analytic time-shift argument that
restarts the comparison principle from `T₀` instead of `0`.  We isolate that
gap here so downstream global-stability statements can depend on a single
precise lemma rather than duplicating the restart interface. -/
theorem h_body_absorb_of_eventual_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (T₀ r_min : ℝ)
    (hT₀ : 0 ≤ T₀) (hr_min_pos : 0 < r_min)
    (hr_floor : ∀ t, T₀ ≤ t → r_min ≤ r t)
    (h_body_seed :
      ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  let rShift : ℝ → ℝ := fun t => r (t + T₀)
  let αShift : Ω → ℝ → ℝ := fun ω t => α ω (t + T₀)
  have hrShift_bdd : ∀ t, |rShift t| ≤ 1 := by
    intro t
    simp [rShift, hr_bdd]
  have hαShift_ode : ∀ ω, ∀ t ≥ 0,
      HasDerivAt (αShift ω) (oaScalarRHS (γ ω) K rShift t (αShift ω t)) t := by
    intro ω t ht
    have hbase : HasDerivAt (α ω)
        (oaScalarRHS (γ ω) K r (t + T₀) (α ω (t + T₀))) (t + T₀) :=
      hα_ode ω (t + T₀) (by linarith)
    simpa [αShift, rShift] using shift_hasDerivAt_right (α ω)
      (fun s => oaScalarRHS (γ ω) K r s (α ω s)) T₀ t hbase
  have hαShift_cont : ∀ ω, ContinuousOn (αShift ω) (Ici 0) := by
    intro ω
    simpa [αShift] using shift_continuousOn_right (α ω) T₀
      ((hα_cont ω).mono (Ici_subset_Ici.mpr hT₀))
  have hShift_sc : ∀ t ≥ 0, rShift t = ∫ ω, αShift ω t ∂μ := by
    intro t ht
    simpa [rShift, αShift] using h_sc (t + T₀) (by linarith)
  have hαShift_int : ∀ t, Integrable (fun ω => αShift ω t) μ := by
    intro t
    simpa [αShift] using hα_int (t + T₀)
  have hαShift_sq_int : ∀ t, Integrable (fun ω => (αShift ω t - α_star ω) ^ 2) μ := by
    intro t
    simpa [αShift] using hα_sq_int (t + T₀)
  have hαShift_inv : ∀ ω t, 0 ≤ t → 0 < αShift ω t ∧ αShift ω t < 1 := by
    intro ω t ht
    simpa [αShift] using hα_inv ω (t + T₀) (by linarith)
  have hrShift_floor : ∃ r0 : ℝ, 0 < r0 ∧ ∀ t, 0 ≤ t → r0 ≤ rShift t := by
    refine ⟨r_min, hr_min_pos, ?_⟩
    intro t ht
    simpa [rShift] using hr_floor (t + T₀) (by linarith)
  obtain ⟨C, hC_nn, hC_absorb⟩ := h_body_absorb_of_pos_floor
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil rShift αShift hrShift_bdd hαShift_ode hαShift_cont
    hShift_sc hαShift_int hαShift_sq_int hαShift_inv
    (by intro M hM; obtain ⟨δ₀, hδ₀, hδ₀_lb⟩ := h_body_seed M hM
        exact ⟨δ₀, hδ₀, fun ω hω => by simpa [αShift] using hδ₀_lb ω hω⟩)
    hrShift_floor hμ_body_pos
  refine ⟨C, hC_nn, ?_⟩
  intro M hM ε hε
  obtain ⟨T, hT⟩ := hC_absorb M hM ε hε
  refine ⟨T + T₀, ?_⟩
  intro t ht
  have hshift : T ≤ t - T₀ := by linarith
  have hbound := hT (t - T₀) hshift
  simpa [αShift, sub_add_cancel] using hbound

/-- **Positive order-parameter floor bypasses `h_body_absorb`.**

Once the dynamics supplies a uniform lower bound `r(t) ≥ r_min > 0`,
the ODE comparison theorem `continuum_body_persistence` upgrades the initial
body lower bounds to persistent body coherence. At that point the project can
call `kuramoto_standard_tendsto` directly, so no separate eventual
absorbing-ball hypothesis `h_body_absorb` needs to be constructed.

This isolates the exact remaining interface in `KuramotoGlobal`: prove
`r_stays_positive`, then apply this theorem. -/
theorem kuramoto_standard_tendsto_of_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (_hr_star_pos : 0 < r_star) (_hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (r_min : ℝ) (hr_min_pos : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (hr_floor : ∀ t, 0 ≤ t → r_min ≤ r t) :
    Tendsto r atTop (nhds r_star) := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := by
    intro t ht
    rw [h_sc t ht]
    exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  have h_body_persist :=
    body_persistence_of_r_floor (μ := μ) (γ := γ) (K := K) hK hγ_pos
      r α hr_bdd hα_ode hα_cont hα_inv h_init_body
      r_min hr_min_pos hr_min_le hr_floor
  have hγ_int_pos : 0 < ∫ ω, γ ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg hγ hγ_int).mpr
    rw [show Function.support γ = Set.univ from
      Set.ext (fun ω => ⟨fun _ => Set.mem_univ _, fun _ => ne_of_gt (hγ_pos ω)⟩)]
    simp [measure_univ]
  exact kuramoto_standard_tendsto γ K hK hγ hγ_int hγ_meas hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int
    hα_neg hα_inv h_body_persist hγ_level

theorem kuramoto_V_zero_of_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (_hr_star_pos : 0 < r_star) (_hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (r_min : ℝ) (hr_min_pos : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (hr_floor : ∀ t, 0 ≤ t → r_min ≤ r t) :
    Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := by
    intro t ht
    rw [h_sc t ht]
    exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  have h_body_persist :=
    body_persistence_of_r_floor (μ := μ) (γ := γ) (K := K) hK hγ_pos
      r α hr_bdd hα_ode hα_cont hα_inv h_init_body
      r_min hr_min_pos hr_min_le hr_floor
  have hγ_int_pos : 0 < ∫ ω, γ ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg hγ hγ_int).mpr
    rw [show Function.support γ = Set.univ from
      Set.ext (fun ω => ⟨fun _ => Set.mem_univ _, fun _ => ne_of_gt (hγ_pos ω)⟩)]
    simp [measure_univ]
  exact kuramoto_V_tendsto_zero γ K hK hγ hγ_int hγ_meas hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int
    hα_neg hα_inv h_body_persist hγ_level
