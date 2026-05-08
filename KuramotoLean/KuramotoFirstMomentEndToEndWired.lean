/-
  KuramotoFirstMomentEndToEndWired.lean
  ======================================
  End-to-end convergence for finite second moment distributions WITHOUT hα_lb.

  Combines:
  - sc_fixed_point_exists_continuum (exp 304): K·∫(1/γ)dμ > 2 → ∃ r* ∈ (0,1)
  - kuramoto_explicit_init_convergence (exp 291): wired chain with explicitEquil initial data
  - α_star derivation from explicitEquil formula (as in V7, exp 303)
  - hα_sq_int derivation from hα_bdd (as in V9, exp 308)

  Vs EndToEndV3 (exp 308): replaces the vacuous
    hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t     (inconsistent with convergence for unbounded γ)
    hα₀_lb_pos : 0 < α₀_lb
    hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal
  with the physically correct wired-chain hypotheses:
    hγ_sq_int : Integrable (fun ω => (γ ω)^2) μ  (second moment — for C(M)→0)
    hγ_pos : ∀ ω, 0 < γ ω                          (strict positivity for explicitEquil_mono)
    hα_bdd : ∀ ω t, 0 ≤ α ω t ∧ α ω t ≤ 1         (trajectory invariance, for hα_sq_int)
    r₀ : ℝ, hr₀ : 0 < r₀, hα_0_explicitEquil      (above-equilibrium initialization)
    r_min, hr_min_pos, hr_bound                     (r persistence)
    hr_cont, hr_bdd, hr_nn, hα_cont                 (regularity for wired chain)

  NET: non-vacuous for Gaussian (second moment), Student-t ν>2, compact support.
  hα_lb NEVER required. Conclusion existential: ∃ r_star ∈ (0,1), r(t)→r_star.

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoExplicitInitWired7
import KuramotoLean.KuramotoContinuumSCFixedPoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **End-to-end convergence for second-moment distributions without global persistence.**

    For K·∫(1/γ)dμ > 2 and oscillators starting above explicitEquil(γ(ω),K,r₀),
    there exists r_star ∈ (0,1) with r(t) → r_star.

    Key difference from `kuramoto_first_moment_end_to_end_v3` (EndToEndV3):
    - REMOVES `hα_lb` (uniform lower bound — vacuous for Gaussian at equilibrium)
    - REMOVES `hα₀_lb_pos`, `hμ_body_pos`
    - ADDS `hγ_sq_int` (second moment — required for C(M)~M²τ(M)→0)
    - ADDS `hα_bdd` (trajectory invariance — used to derive hα_sq_int, like V9)
    - ADDS `hα_0_explicitEquil`, `r₀`, `r_min` (physical initialization + persistence)

    These conditions ARE consistent with convergence: α(ω,t) → α*(ω) → 0 as γ(ω) → ∞,
    so the per-body initial bound δ₀(M) ~ Kr₀/(4M) → 0, matching the equilibrium. -/
theorem kuramoto_first_moment_end_to_end_wired [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (hK_crit : 2 < K * ∫ ω, 1 / γ ω ∂μ)
    (hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_bdd : ∀ ω t, 0 ≤ α ω t ∧ α ω t ≤ 1)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (r_min : ℝ) (hr_min_pos : 0 < r_min)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hα_0_explicitEquil : ∀ ω, explicitEquil (γ ω) K r₀ ≤ α ω 0) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧ Tendsto r atTop (nhds r_star) := by
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  -- Step 1: Obtain r_star from self-consistency fixed point
  obtain ⟨r_star, hr_pos, hr_lt, hr_sc⟩ :=
    sc_fixed_point_exists_continuum γ K hK hγ_pos hγ_level h_inv_int hK_crit
  -- Step 2: Derive α_star = explicitEquil (γ ω) K r_star (same derivation as V7)
  let α_star : Ω → ℝ := fun ω => explicitEquil (γ ω) K r_star
  have hα_star_pos : ∀ ω, 0 < α_star ω :=
    fun ω => explicitEquil_pos (γ ω) K r_star (hγ_pos ω) hK hr_pos
  have hα_star_lt : ∀ ω, α_star ω < 1 :=
    fun ω => explicitEquil_lt_one (γ ω) K r_star (hγ_pos ω) hK hr_pos
  have hαs_meas : Measurable α_star := by
    have hc : Continuous (fun x : ℝ => explicitEquil x K r_star) := by
      unfold explicitEquil; apply Continuous.div_const
      exact continuous_neg.add (Real.continuous_sqrt.comp
        ((continuous_pow 2).add continuous_const))
    exact hc.measurable.comp hγ_meas
  have hαs_int : Integrable α_star μ :=
    (integrable_const (1 : ℝ)).mono hαs_meas.aestronglyMeasurable
      (Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, norm_one, abs_of_pos (hα_star_pos ω)]
        exact le_of_lt (hα_star_lt ω)))
  have hr_star_eq : r_star = ∫ ω, α_star ω ∂μ := hr_sc
  have hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2) := by
    intro ω
    have h := explicitEquil_solves (γ ω) K r_star (hγ_pos ω) hK hr_pos
    unfold componentEquil at h
    linarith
  -- Step 3: Derive hα_sq_int from hα_bdd + hαs_int (same technique as V9)
  have hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ := fun t => by
    have ha_int : Integrable (fun ω => α ω t - α_star ω) μ := (hα_int t).sub hαs_int
    apply (integrable_const (1 : ℝ)).mono
    · simp_rw [sq]; exact ha_int.1.mul ha_int.1
    · apply Eventually.of_forall; intro ω
      rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (sq_nonneg _)]
      have ha := hα_bdd ω t
      nlinarith [ha.1, ha.2, hα_star_pos ω, hα_star_lt ω]
  -- Step 4: Apply kuramoto_explicit_init_convergence
  exact ⟨r_star, hr_pos, hr_lt,
    kuramoto_explicit_init_convergence γ K hK hγ hγ_meas.aestronglyMeasurable hγ_level
      α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
      r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
      r_min hr_min_pos hr_bound hγ_sq_int hγ_pos r₀ hr₀ hα_0_explicitEquil⟩

end
