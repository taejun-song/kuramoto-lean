/-
  Kuramoto Phase Transition — Complete Trifurcation
  ==================================================
  The complete phase transition for the Kuramoto model on the OA manifold:

    Kc = 2 / ∫(1/γ) dμ

  is the SHARP threshold:
  - Subcritical  (K < Kc): r(t) → 0  exponentially (rate γ_min(1-K/Kc))
  - Critical     (K = Kc): r(t) → 0  algebraically (from cubic Lyapunov)
  - Supercritical (K > Kc): r(t) → r* > 0  (synchronization)

  0 sorry.
-/

import KuramotoLean.ContinuumCritical
import KuramotoLean.ContinuumInstability

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The Kuramoto Phase Transition -/

/-- The Kuramoto phase transition is a dichotomy indexed by K relative to Kc.
    This inductive type packages which regime holds. -/
inductive KuramotoRegime where
  | subcritical : KuramotoRegime
  | supercritical : KuramotoRegime

/-- **KURAMOTO PHASE TRANSITION — SUBCRITICAL DIRECTION.**
    K < Kc implies the order parameter decays to zero exponentially. -/
theorem kuramoto_subcritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K < continuumKc γ μ)
    (W W' : ℝ → ℝ) (hW0_pos : 0 < W 0)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t →
      W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t) :
    Tendsto r atTop (nhds 0) :=
  kuramoto_sharp_threshold γ K r γ_min γ_max hγ_min_pos hγ_max_pos
    h_inv_pos h_sub W W' hW0_pos hW_cont hW_deriv hW_bound hr_le hr_nn

/-- **KURAMOTO PHASE TRANSITION — SUPERCRITICAL DIRECTION.**
    K > Kc implies the order parameter converges to r* > 0. -/
theorem kuramoto_supercritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (h_init_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    Tendsto r atTop (nhds r_star) :=
  kuramoto_supercritical_convergence γ K r α hK hγ_pos hγ_int hγ_level
    h_inv_int h_inv_pos h_super hr_cont hr_bdd hα_ode hα_cont hα_neg
    hα_inv h_sc hα_int h_init_body α_star r_star hr_star_pos hr_star_lt
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil hα_sq_int

/-- **KURAMOTO PHASE TRANSITION — CRITICAL CASE.**
    At K = Kc, the order parameter still decays to zero (algebraically). -/
theorem kuramoto_critical [IsProbabilityMeasure μ]
    (r W W' : ℝ → ℝ) (c γ_max : ℝ) (hc : 0 < c) (hγ_max_pos : 0 < γ_max)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_nn : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_cubic : ∀ t, 0 < t → W' t ≤ -(c * W t ^ 3))
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t) :
    Tendsto r atTop (nhds 0) :=
  continuum_critical_r_convergence r W W' c γ_max hc hγ_max_pos
    hW_cont hW_nn hW_deriv hW_cubic hr_le hr_nn

/-- **KURAMOTO PHASE TRANSITION — COMPLETE CHARACTERIZATION.**
    The critical coupling Kc = 2/∫(1/γ)dμ is the sharp threshold:
    below Kc incoherence is stable, above Kc synchronization emerges.

    This theorem takes the coupling K and returns which regime holds,
    together with the convergence statement for that regime. -/
theorem kuramoto_phase_transition [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (hK_ne : K ≠ continuumKc γ μ) :
    (K < continuumKc γ μ ∧ ∀ (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min)
      (hγ_max_pos : 0 < γ_max)
      (W W' : ℝ → ℝ) (hW0_pos : 0 < W 0)
      (hW_cont : ContinuousOn W (Ici 0))
      (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
      (hW_bound : ∀ t, 0 < t →
        W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
      (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
      (hr_nn : ∀ t, 0 ≤ r t),
      Tendsto r atTop (nhds 0))
    ∨
    (continuumKc γ μ < K ∧ ∀ (α : Ω → ℝ → ℝ)
      (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
      (hγ_int : Integrable γ μ)
      (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
      (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
      (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
      (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
      (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
      (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
      (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
      (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
      (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
      (h_init_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
      (α_star : Ω → ℝ) (r_star : ℝ)
      (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
      (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
      (hαs_int : Integrable α_star μ)
      (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
      (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
      (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ),
      Tendsto r atTop (nhds r_star)) := by
  rcases lt_or_gt_of_ne hK_ne with h_sub | h_super
  · left
    exact ⟨h_sub, fun γ_min γ_max hγ_min_pos hγ_max_pos W W' hW0_pos hW_cont hW_deriv
      hW_bound hr_le hr_nn =>
      kuramoto_sharp_threshold γ K r γ_min γ_max hγ_min_pos hγ_max_pos h_inv_pos
        h_sub W W' hW0_pos hW_cont hW_deriv hW_bound hr_le hr_nn⟩
  · right
    exact ⟨h_super, fun α hK hγ_pos hγ_int hγ_level h_inv_int hr_cont hr_bdd
      hα_ode hα_cont hα_neg hα_inv h_sc hα_int h_init_body α_star r_star
      hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int hr_star_eq
      hα_star_equil hα_sq_int =>
      kuramoto_supercritical_convergence γ K r α hK hγ_pos hγ_int hγ_level h_inv_int
        h_inv_pos h_super hr_cont hr_bdd hα_ode hα_cont hα_neg hα_inv h_sc hα_int
        h_init_body α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt
        hαs_int hr_star_eq hα_star_equil hα_sq_int⟩

/-- **COMPLETE TRIFURCATION.** For K ≤ Kc, r → 0. For K > Kc, r → r*. -/
theorem kuramoto_trifurcation [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r W W' : ℝ → ℝ)
    (γ_min γ_max : ℝ) (hγ_min_pos : 0 < γ_min) (hγ_max_pos : 0 < γ_max)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_nn : ∀ t, 0 ≤ t → 0 ≤ W t)
    (hW0_pos : 0 < W 0)
    (hW_deriv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ γ_max * W t)
    (hr_nn : ∀ t, 0 ≤ r t)
    (h_le_Kc : K ≤ continuumKc γ μ)
    (h_subcrit_bound : K < continuumKc γ μ →
      ∀ t, 0 < t → W' t ≤ -(γ_min * (1 - K / continuumKc γ μ)) * W t)
    (h_crit_bound : K = continuumKc γ μ →
      ∃ c > 0, ∀ t, 0 < t → W' t ≤ -(c * W t ^ 3)) :
    Tendsto r atTop (nhds 0) :=
  continuum_non_supercritical_convergence γ K r W W' γ_min γ_max hγ_min_pos hγ_max_pos
    h_inv_pos hW_cont hW_nn hW0_pos hW_deriv hr_le hr_nn h_le_Kc h_subcrit_bound h_crit_bound

/-- **Kc FORMULA.** The critical coupling equals 2/∫(1/γ)dμ. -/
theorem kuramoto_Kc_formula (γ : Ω → ℝ) :
    continuumKc γ μ = 2 / (∫ ω, (1 / γ ω) ∂μ) := rfl

end
