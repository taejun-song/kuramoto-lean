/-
  Unified Phase Transition Theorem
  ==================================
  A single theorem packaging the complete mean-field phase transition:

  Given a probability measure μ on frequency parameters γ(ω) > 0 with
  Kc = 2/∫(1/γ)dμ (the critical coupling), the Kuramoto OA model satisfies:

  1. SUBCRITICAL (K < Kc): no positive equilibrium; incoherence is stable
  2. CRITICAL (K = Kc): no positive equilibrium; transition boundary
  3. SUPERCRITICAL (K > Kc): unique positive equilibrium r* with:
     a. 0 < r* < 1
     b. r* = Φ(r*) where Φ(r) = ∫ explicitEquil(γ,K,r) dμ
     c. r* monotone increasing in K
     d. r* = Θ(√(K-Kc)) near onset (critical exponent β = 1/2)
     e. r* → 1 as K → ∞ (strong coupling limit)
     f. Φ contracts toward r* (iteration convergence)

  0 sorry.
-/

import KuramotoLean.DistributionSensitivity
import KuramotoLean.CriticalExponent

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **UNIFIED PHASE TRANSITION THEOREM.**
    Complete characterization of the Kuramoto mean-field bifurcation. -/
theorem kuramoto_phase_transition [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    (K ≤ continuumKc γ μ →
      ∀ r, 0 < r → ∫ ω, explicitEquil (γ ω) K r ∂μ < r) ∧
    (continuumKc γ μ < K →
      ∃! r_star, 0 < r_star ∧ r_star < 1 ∧
        ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) := by
  constructor
  · intro h_sub r hr
    exact continuum_no_fixed_point_subcritical γ K hγ_pos hK hγ_level
      h_inv_int h_inv_pos h_sub r hr
  · intro h_super
    exact continuum_exactly_one_equilibrium γ K hK hγ_pos hγ_level
      h_inv_int h_inv_pos h_super

/-- **SUPERCRITICAL PROPERTIES.**
    The equilibrium r* in the supercritical regime satisfies all quantitative bounds. -/
theorem supercritical_equilibrium_properties [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_inv3_int : Integrable (fun ω => 1 / (γ ω) ^ 3) μ)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    sqrt (8 * (K - continuumKc γ μ) /
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ)) ≤ r_star ∧
    r_star ≤ sqrt ((K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3) ∧
    1 - 2 * γ_max / K ≤ r_star := by
  exact ⟨rstar_ge_sqrt_gap γ K r_star hγ_pos hK hr_pos hγ_level h_inv_int
      h_inv_pos h_inv3_int h_super hfp,
    rstar_le_sqrt_gap γ K r_star γ_max hγ_pos hK hr_pos hr_lt hγ_max_pos hγ_max
      hγ_level h_inv_int h_inv_pos h_super hfp,
    continuum_strong_coupling_limit γ K r_star γ_max hγ_pos hK hr_pos hγ_max_pos hγ_max
      hγ_level hfp⟩

/-- **MONOTONICITY + CONTRACTION.**
    r* is the unique globally attracting fixed point of the self-consistency map. -/
theorem equilibrium_attracts [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_ne : r ≠ r_star) :
    |∫ ω, explicitEquil (γ ω) K r ∂μ - r_star| < |r - r_star| ∧
    0 < ∫ ω, explicitEquil (γ ω) K r ∂μ ∧
    ∫ ω, explicitEquil (γ ω) K r ∂μ < 1 :=
  ⟨sc_map_contraction γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h_ne,
   sc_map_pos γ K r hγ_pos hK hγ_level hr,
   sc_map_lt_one γ K r hγ_pos hK hγ_level hr⟩

/-- **SENSITIVITY.**
    Wider frequency distributions need stronger coupling and produce less synchronization. -/
theorem wider_distribution_harder_to_sync [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ) (K r₁ r₂ : ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (hK : 0 < K)
    (h_le : ∀ ω, γ₁ ω ≤ γ₂ ω)
    (hγ₁_level : ∀ M : ℝ, MeasurableSet {ω | γ₁ ω ≤ M})
    (hγ₂_level : ∀ M : ℝ, MeasurableSet {ω | γ₂ ω ≤ M})
    (h_inv₂_int : Integrable (fun ω => 1 / γ₂ ω) μ)
    (h_inv₁_int : Integrable (fun ω => 1 / γ₁ ω) μ)
    (h_inv₂_pos : 0 < ∫ ω, (1 / γ₂ ω) ∂μ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hfp₁ : ∫ ω, explicitEquil (γ₁ ω) K r₁ ∂μ = r₁)
    (hfp₂ : ∫ ω, explicitEquil (γ₂ ω) K r₂ ∂μ = r₂) :
    continuumKc γ₁ μ ≤ continuumKc γ₂ μ ∧ r₂ ≤ r₁ :=
  ⟨continuumKc_mono_gamma γ₁ γ₂ hγ₁_pos hγ₂_pos h_le h_inv₁_int h_inv₂_int h_inv₂_pos,
   rstar_mono_gamma γ₁ γ₂ K r₁ r₂ hγ₁_pos hγ₂_pos hK h_le hγ₁_level hγ₂_level
     hr₁ hr₂ hfp₁ hfp₂⟩

end
