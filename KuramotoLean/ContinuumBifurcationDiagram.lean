/-
  Complete Continuum Bifurcation Diagram
  =======================================
  Unified characterization of the Kuramoto bifurcation:

    Kc = 2 / ∫(1/γ) dμ

  • K ≤ Kc: no positive equilibrium (Φ(r) < r for all r > 0)
  • K > Kc: unique positive equilibrium r*(K) with 0 < r* < 1
  • r* is strictly increasing in K
  • r* ≥ 1 - 2γ_max/K → 1 as K → ∞

  0 sorry.
-/

import KuramotoLean.ContinuumBifurcation

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Existence reformulated with continuumKc -/

theorem sc_fixed_point_exists_supercritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      r_star = ∫ ω, explicitEquil (γ ω) K r_star ∂μ := by
  apply sc_fixed_point_exists_continuum γ K hK hγ_pos hγ_level h_inv_int
  unfold continuumKc at h_super
  rw [div_lt_iff₀ h_inv_pos] at h_super
  linarith

/-! ## No equilibrium in subcritical -/

theorem no_equilibrium_subcritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_sub : K ≤ continuumKc γ μ)
    (r : ℝ) (hr : 0 < r) :
    ∫ ω, explicitEquil (γ ω) K r ∂μ ≠ r :=
  ne_of_lt (continuum_no_fixed_point_subcritical γ K hγ_pos hK hγ_level
    h_inv_int h_inv_pos h_sub r hr)

/-! ## Complete Bifurcation Diagram -/

/-- **COMPLETE BIFURCATION DIAGRAM.**
    The supercritical equilibrium exists, is unique, strictly increasing in K,
    and satisfies the strong coupling bound. -/
theorem continuum_bifurcation_diagram [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K₁ K₂ : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super₁ : continuumKc γ μ < K₁)
    (hK₁₂ : K₁ < K₂) :
    ∃ r₁ r₂ : ℝ,
      (0 < r₁ ∧ r₁ < 1 ∧ r₁ = ∫ ω, explicitEquil (γ ω) K₁ r₁ ∂μ) ∧
      (0 < r₂ ∧ r₂ < 1 ∧ r₂ = ∫ ω, explicitEquil (γ ω) K₂ r₂ ∂μ) ∧
      r₁ < r₂ := by
  have h_super₂ : continuumKc γ μ < K₂ := lt_trans h_super₁ hK₁₂
  obtain ⟨r₁, hr₁_pos, hr₁_lt, hr₁_eq⟩ :=
    sc_fixed_point_exists_supercritical γ K₁ hK₁ hγ_pos hγ_level h_inv_int h_inv_pos h_super₁
  obtain ⟨r₂, hr₂_pos, hr₂_lt, hr₂_eq⟩ :=
    sc_fixed_point_exists_supercritical γ K₂ hK₂ hγ_pos hγ_level h_inv_int h_inv_pos h_super₂
  refine ⟨r₁, r₂, ⟨hr₁_pos, hr₁_lt, hr₁_eq⟩, ⟨hr₂_pos, hr₂_lt, hr₂_eq⟩, ?_⟩
  exact continuum_r_star_mono_K γ K₁ K₂ r₁ r₂ hγ_pos hK₁ hK₂ hγ_level
    hr₁_pos hr₂_pos hr₁_eq.symm hr₂_eq.symm hK₁₂

/-- **EQUILIBRIUM UNIQUENESS + EXISTENCE = EXACTLY ONE.**
    For K > Kc there is exactly one r ∈ (0,1) with Φ(r) = r. -/
theorem continuum_exactly_one_equilibrium [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K) :
    ∃! r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star := by
  obtain ⟨r_star, hr_pos, hr_lt, hr_eq⟩ :=
    sc_fixed_point_exists_supercritical γ K hK hγ_pos hγ_level h_inv_int h_inv_pos h_super
  refine ⟨r_star, ⟨hr_pos, hr_lt, hr_eq.symm⟩, ?_⟩
  intro y ⟨hy_pos, _, hy_eq⟩
  exact continuum_sc_fixed_point_unique γ K hγ_pos hK hγ_level y r_star
    hy_pos hr_pos hy_eq hr_eq.symm

/-- **STRONG COUPLING LIMIT.**
    For any bounded frequency distribution, r*(K) → 1 as K → ∞.
    Quantitative: r*(K) ≥ 1 - 2γ_max/K for all supercritical K. -/
theorem continuum_strong_coupling_limit [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    1 - 2 * γ_max / K ≤ r_star :=
  continuum_r_star_lower_strong γ K r_star γ_max hγ_pos hK hr hγ_max_pos hγ_max hγ_level hfp

/-- **DICHOTOMY.**
    K ≤ Kc ↔ no positive equilibrium. K > Kc ↔ unique positive equilibrium. -/
theorem continuum_bifurcation_dichotomy [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    (K ≤ continuumKc γ μ ∧
      ∀ r, 0 < r → ∫ ω, explicitEquil (γ ω) K r ∂μ < r) ∨
    (continuumKc γ μ < K ∧
      ∃! r_star, 0 < r_star ∧ r_star < 1 ∧
        ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) := by
  rcases Classical.em (K ≤ continuumKc γ μ) with h_sub | h_not
  · left
    exact ⟨h_sub, fun r hr => continuum_no_fixed_point_subcritical γ K hγ_pos hK
      hγ_level h_inv_int h_inv_pos h_sub r hr⟩
  · right
    have h_super : continuumKc γ μ < K := by linarith [not_le.mp h_not]
    exact ⟨h_super, continuum_exactly_one_equilibrium γ K hK hγ_pos hγ_level
      h_inv_int h_inv_pos h_super⟩

end
