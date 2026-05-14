/-
  Kuramoto Global Stability via Approximation Bridge
  ====================================================

  Proves global continuum stability using kuramoto_standard_tendsto
  from ContinuumSolvedFinal (0 sorry, body/tail contradiction).

  The original n-pole approximation route (npole_approximation_gives_small_V)
  is replaced by a direct call to the body/tail coercivity argument.

  0 sorry.
-/

import KuramotoLean.FullChainConvergence
import KuramotoLean.ContinuumSolvedFinal
import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.ApproximationBridge

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Main theorem -/

/-- **GLOBAL CONTINUUM STABILITY VIA BODY/TAIL COERCIVITY.**

For any OA solution on a probability space (Ω, μ) with body persistence:
  - conclusion: r(t) → r*

Proof: delegates to `kuramoto_standard_tendsto` (ContinuumSolvedFinal, 0 sorry)
which proves V → 0 via the body/tail Markov + pair coercivity contradiction,
then derives r → r* from V → 0 + Cauchy-Schwarz.

0 sorry. -/
theorem global_stability_via_npole [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
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
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt' : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_body_persist : ∀ M, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) :
    Tendsto r atTop (nhds r_star) := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  have hγ_int_pos : 0 < ∫ ω, γ ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg hγ hγ_int).mpr
    rw [show Function.support γ = Set.univ from
      Set.ext (fun ω => ⟨fun _ => Set.mem_univ _, fun _ => ne_of_gt (hγ_pos ω)⟩)]
    simp [measure_univ]
  exact kuramoto_standard_tendsto γ K hK hγ hγ_int hγ_meas hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt' hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int
    hα_neg hα_inv h_body_persist hγ_level

end
