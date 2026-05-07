/-
  KuramotoFirstMomentBarbalat.lean
  =================================
  End-to-end convergence for FIRST moment distributions WITHOUT γ_min or second moment.

  Covers: Student-t 1 < ν ≤ 2, power-law tails (α ∈ (1,2]), γ = |ω| on any distribution
  with ∫γ < ∞ but possibly ∫γ² = ∞ and possibly inf γ = 0.

  Combines:
  - sc_fixed_point_exists_continuum (exp 304): K·∫(1/γ)dμ > 2 → ∃ r* ∈ (0,1)
  - kuramoto_standard_continuum (ContinuumSolvedFinal): contradiction route via
    body_pair_coercive, requires hγ_int (first moment) + h_body_persist (body persistence)

  vs KuramotoFirstMomentEndToEndWired (exp 309):
    OLD: requires hγ_sq_int (second moment) — excludes Student-t 1 < ν ≤ 2
    OLD: requires hα_bdd + r₀ + hα_0_explicitEquil (wired initialization)
    NEW: requires only hγ_int (first moment) + h_body_persist (body persistence)
    NEW: no initialization hypothesis, no wired structure

  vs ContinuumGammaMinFirstMoment (ISS route, requires γ_min > 0):
    OLD: requires γ_min ≤ γ ω for all ω — excludes γ = |ω|
    NEW: hγ_pos (strict pointwise) is used only for sc_fixed_point IVT

  Coverage: ALL distributions with ∫(1/γ) < ∞, ∫γ < ∞, γ > 0 pointwise,
  and body persistence. Closes the Student-t 1 < ν ≤ 2 gap.

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoContinuumSCFixedPoint
import KuramotoLean.ContinuumSolvedFinal

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **End-to-end convergence for first-moment distributions without γ_min or second moment.**

    For K·∫(1/γ)dμ > 2, ∫γ < ∞, body persistence, and strict γ > 0, there exists
    r_star ∈ (0,1) with r(t) → r_star.

    Key differences from prior end-to-end theorems:
    - REMOVES hγ_sq_int (second moment) — the barrier to Student-t 1 < ν ≤ 2
    - REMOVES γ_min uniform lower bound — allows γ = |ω|
    - KEEPS only hγ_int (first moment) + h_body_persist (body persistence)
    - No initialization hypothesis (no explicitEquil condition, no wired structure)

    Physical meaning of h_body_persist: for each truncated body {γ ≤ M}, the trajectory
    α(ω,t) maintains a uniform positive lower bound δ(M) > 0 for all t ≥ 0. This holds
    whenever r(t) ≥ r_min > 0 for all t (persistence of order). -/
theorem kuramoto_first_moment_barbalat [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (hK_crit : 2 < K * ∫ ω, 1 / γ ω ∂μ)
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_body_persist : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
        ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧ Tendsto r atTop (nhds r_star) := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : Measurable γ := measurable_of_Iic hγ_level
  -- Step 1: Obtain r_star from self-consistency fixed point
  obtain ⟨r_star, hr_pos, hr_lt, hr_sc⟩ :=
    sc_fixed_point_exists_continuum γ K hK hγ_pos hγ_level h_inv_int hK_crit
  -- Step 2: Define α_star = explicitEquil (γ ω) K r_star
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
  -- Step 3: Derive hα_sq_int from hα_inv + hα_neg + hα_int
  have hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ := fun t => by
    have ha_int : Integrable (fun ω => α ω t - α_star ω) μ := (hα_int t).sub hαs_int
    apply (integrable_const (1 : ℝ)).mono
    · simp_rw [sq]; exact ha_int.1.mul ha_int.1
    · apply Eventually.of_forall; intro ω
      rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (sq_nonneg _)]
      by_cases ht : 0 ≤ t
      · nlinarith [(hα_inv ω t ht).1, (hα_inv ω t ht).2, hα_star_pos ω, hα_star_lt ω]
      · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]
        nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2, hα_star_pos ω, hα_star_lt ω]
  -- Step 4: Derive hγ_int_pos: ∫γ > 0 from γ > 0 everywhere and IsProbabilityMeasure
  have hγ_int_pos : 0 < ∫ ω, γ ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun ω => hγ ω) hγ_int).mpr
    rw [show Function.support γ = Set.univ from
      Set.ext (fun ω => ⟨fun _ => Set.mem_univ _, fun _ => ne_of_gt (hγ_pos ω)⟩)]
    simp [measure_univ]
  -- Step 5: Apply kuramoto_standard_tendsto (explicit r/α version returning Tendsto r directly)
  exact ⟨r_star, hr_pos, hr_lt,
    kuramoto_standard_tendsto γ K hK hγ hγ_int hγ_meas.aestronglyMeasurable hγ_int_pos
      α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
      r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int
      hα_neg hα_inv h_body_persist hγ_level⟩

end
