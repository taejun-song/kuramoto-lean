/-
  LorentzianContinuumInstantiation.lean
  ======================================
  Self-contained Lorentzian continuum convergence with canonical flow.

  Instantiates lorentzian_continuum_V_inf_tendsto with:
    α(ω,t) = lorentzian_oa_flow K γ₀ r₀ α₀ ... (γ(ω)) (hγ(ω)) t
    α*(ω)  = explicitEquil (γ(ω)) K r*

  All hypotheses are derived from measurability of γ : Ω → ℝ and
  γ(ω) > 0 everywhere. No additional sorries.

  MAIN RESULT: lorentzian_continuum_V_inf_tendsto_canonical
    Given measurable γ : Ω → ℝ with γ(ω) > 0 everywhere and α₀ ∈ (0,1),
    the continuum Lyapunov V∞(t) = ∫(α(ω,t) - α*(ω))² dμ → 0.

  0 sorry.
-/

import KuramotoLean.LorentzianContinuumConvergence
import KuramotoLean.OAScalarMeasurableFlow
import KuramotoLean.EquilibriumFormula

open MeasureTheory Real Set Filter Topology

noncomputable section

private lemma explicitEquil_equil_eq (γ K r_star : ℝ) (hγ : 0 < γ) (hK : 0 < K)
    (hr : 0 < r_star) :
    γ * explicitEquil γ K r_star = K / 2 * r_star * (1 - (explicitEquil γ K r_star) ^ 2) := by
  have h := explicitEquil_solves γ K r_star hγ hK hr
  unfold componentEquil at h
  linarith

private lemma explicitEquil_continuous_in_gamma (K r_star : ℝ) (hK : 0 < K) (hr : 0 < r_star) :
    Continuous (fun γ => explicitEquil γ K r_star) := by
  unfold explicitEquil
  have hKr : K * r_star ≠ 0 := ne_of_gt (mul_pos hK hr)
  apply Continuous.div_const
  apply Continuous.add
  · exact continuous_neg.comp continuous_id
  · apply Real.continuous_sqrt.comp
    apply Continuous.add
    · exact (continuous_pow 2).comp continuous_id
    · exact continuous_const

/-- **Canonical Lorentzian continuum convergence.**
    When γ : Ω → ℝ is measurable with γ(ω) > 0 everywhere, α₀ ∈ (0,1), and
    K > 2γ₀, the continuum Lyapunov
      V∞(t) = ∫ (lorentzian_oa_flow(γ(ω),t) - α*(γ(ω)))² dμ → 0
    where α*(γ) = explicitEquil(γ,K,r*) and r* = √(1-2γ₀/K). -/
theorem lorentzian_continuum_V_inf_tendsto_canonical
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ_fun : Ω → ℝ)
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    (hγ_meas : Measurable γ_fun)
    (hγ_pos : ∀ ω, 0 < γ_fun ω) :
    let r_star := Real.sqrt (1 - 2 * γ₀ / K)
    let α_star := fun ω => explicitEquil (γ_fun ω) K r_star
    let α := fun ω t =>
      lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt
        (γ_fun ω) (hγ_pos ω) t
    Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) := by
  set r_star := Real.sqrt (1 - 2 * γ₀ / K)
  set α_star := fun ω => explicitEquil (γ_fun ω) K r_star
  set α := fun ω t =>
    lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt
      (γ_fun ω) (hγ_pos ω) t
  have hr_star_pos : 0 < r_star :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ₀ hK hKγ₀)
  have hα_star_equil : ∀ ω, γ_fun ω * α_star ω =
      K / 2 * r_star * (1 - (α_star ω) ^ 2) :=
    fun ω => explicitEquil_equil_eq (γ_fun ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hα_star_pos : ∀ ω, 0 < α_star ω :=
    fun ω => explicitEquil_pos (γ_fun ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hα_star_lt : ∀ ω, α_star ω < 1 :=
    fun ω => explicitEquil_lt_one (γ_fun ω) K r_star (hγ_pos ω) hK hr_star_pos
  have hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0) :=
    fun ω => (lorentzian_oa_flow_spec_raw K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt
      hα₀_pos hα₀_lt (γ_fun ω) (hγ_pos ω)).2.1
  have hα_ode : ∀ ω t, 0 < t →
      HasDerivAt (α ω) (oaScalarRHS (γ_fun ω) K (lorentzian_explicit K γ₀ r₀) t (α ω t)) t :=
    fun ω t ht => (lorentzian_oa_flow_spec_raw K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt
      hα₀_pos hα₀_lt (γ_fun ω) (hγ_pos ω)).2.2.1 t (le_of_lt ht)
  have hα_bdd : ∀ ω t, 0 ≤ t → 0 ≤ α ω t ∧ α ω t ≤ 1 :=
    fun ω t ht =>
      let h := (lorentzian_oa_flow_spec_raw K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt
        hα₀_pos hα₀_lt (γ_fun ω) (hγ_pos ω)).2.2.2 t ht
      ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hα_sq_meas : ∀ᶠ t in atTop, AEStronglyMeasurable (fun ω => (α ω t - α_star ω) ^ 2) μ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hmeas_α : AEStronglyMeasurable (fun ω => α ω t) μ :=
      lorentzian_oa_flow_aestronglyMeasurable K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt
        hα₀_pos hα₀_lt γ_fun hγ_meas hγ_pos t ht
    have hmeas_αstar : Measurable (fun ω => α_star ω) :=
      ((explicitEquil_continuous_in_gamma K r_star hK hr_star_pos).measurable.comp hγ_meas)
    exact (continuous_pow 2).comp_aestronglyMeasurable
      (hmeas_α.sub hmeas_αstar.aestronglyMeasurable)
  exact lorentzian_continuum_V_inf_tendsto γ_fun K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt
    (Eventually.of_forall (fun ω => hγ_pos ω))
    α_star
    (fun ω => by rw [hα_star_equil ω])
    hα_star_pos hα_star_lt
    α hα_cont hα_ode hα_bdd hα_sq_meas

end
