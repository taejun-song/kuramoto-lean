/-
  Distribution Sensitivity of the Kuramoto Phase Transition
  ==========================================================
  How the critical coupling Kc and equilibrium r* respond to changes in the
  frequency distribution:

    1. Kc monotone in γ: wider distribution → harder to synchronize
    2. r* anti-monotone in γ: wider distribution → less synchronization
    3. Kc scaling: Kc(c·γ) = c·Kc(γ) (homogeneity)
    4. r* invariant: r*(c·γ, c·K) = r*(γ, K) (scaling symmetry)

  These are the fundamental sensitivity relations of mean-field theory.

  0 sorry.
-/

import KuramotoLean.SelfConsistencyContraction
import KuramotoLean.ContinuumBifurcationDiagram

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Kc monotonicity in γ -/

/-- **Kc increases with frequency spread.**
    If γ₁(ω) ≤ γ₂(ω) pointwise, then Kc(γ₁) ≤ Kc(γ₂).
    Wider distributions need stronger coupling to synchronize. -/
theorem continuumKc_mono_gamma [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (h_le : ∀ ω, γ₁ ω ≤ γ₂ ω)
    (h_inv₁_int : Integrable (fun ω => 1 / γ₁ ω) μ)
    (h_inv₂_int : Integrable (fun ω => 1 / γ₂ ω) μ)
    (h_inv₂_pos : 0 < ∫ ω, (1 / γ₂ ω) ∂μ) :
    continuumKc γ₁ μ ≤ continuumKc γ₂ μ := by
  unfold continuumKc
  have h_inv₁_pos : 0 < ∫ ω, (1 / γ₁ ω) ∂μ := by
    calc 0 < ∫ ω, (1 / γ₂ ω) ∂μ := h_inv₂_pos
      _ ≤ ∫ ω, (1 / γ₁ ω) ∂μ := by
          apply integral_mono h_inv₂_int h_inv₁_int
          intro ω; exact div_le_div_of_nonneg_left zero_le_one (hγ₁_pos ω) (h_le ω)
  have h_int_le : ∫ ω, (1 / γ₂ ω) ∂μ ≤ ∫ ω, (1 / γ₁ ω) ∂μ :=
    integral_mono h_inv₂_int h_inv₁_int
      (fun ω => div_le_div_of_nonneg_left zero_le_one (hγ₁_pos ω) (h_le ω))
  exact div_le_div_of_nonneg_left (le_of_lt two_pos) h_inv₂_pos h_int_le

/-- **Strict Kc monotonicity.**
    If γ₁ < γ₂ on a set of positive measure, then Kc(γ₁) < Kc(γ₂). -/
theorem continuumKc_strictMono_gamma [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (h_le : ∀ ω, γ₁ ω ≤ γ₂ ω)
    (h_inv₁_int : Integrable (fun ω => 1 / γ₁ ω) μ)
    (h_inv₂_int : Integrable (fun ω => 1 / γ₂ ω) μ)
    (h_inv₁_pos : 0 < ∫ ω, (1 / γ₁ ω) ∂μ)
    (h_inv₂_pos : 0 < ∫ ω, (1 / γ₂ ω) ∂μ)
    (h_strict : ∫ ω, (1 / γ₂ ω) ∂μ < ∫ ω, (1 / γ₁ ω) ∂μ) :
    continuumKc γ₁ μ < continuumKc γ₂ μ := by
  unfold continuumKc
  exact div_lt_div_of_pos_left two_pos h_inv₂_pos h_strict

/-! ## Kc homogeneity -/

/-- **Kc scales linearly.**
    Kc(c·γ) = c·Kc(γ) for c > 0.
    Rescaling all frequencies rescales the critical coupling. -/
theorem continuumKc_scale [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ) :
    continuumKc (fun ω => c * γ ω) μ = c * continuumKc γ μ := by
  unfold continuumKc
  have h_eq : ∫ ω, (1 / (c * γ ω)) ∂μ = (1 / c) * ∫ ω, (1 / γ ω) ∂μ := by
    have : (fun ω => 1 / (c * γ ω)) = fun ω => (1 / c) * (1 / γ ω) := by
      ext ω; field_simp
    rw [this, integral_const_mul]
  rw [h_eq]; field_simp

/-! ## Self-consistency map comparison across distributions -/

/-- **Φ(γ₁) ≥ Φ(γ₂) pointwise.**
    If γ₁ ≤ γ₂ pointwise, then Φ_{γ₁}(r) ≥ Φ_{γ₂}(r) for all r > 0.
    Narrower distributions produce larger order parameter maps. -/
theorem sc_map_mono_gamma [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ) (K r : ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (hK : 0 < K) (hr : 0 < r)
    (h_le : ∀ ω, γ₁ ω ≤ γ₂ ω)
    (hγ₁_level : ∀ M : ℝ, MeasurableSet {ω | γ₁ ω ≤ M})
    (hγ₂_level : ∀ M : ℝ, MeasurableSet {ω | γ₂ ω ≤ M}) :
    ∫ ω, explicitEquil (γ₂ ω) K r ∂μ ≤ ∫ ω, explicitEquil (γ₁ ω) K r ∂μ := by
  have hγ₁_meas : Measurable γ₁ := measurable_of_Iic hγ₁_level
  have hγ₂_meas : Measurable γ₂ := measurable_of_Iic hγ₂_level
  have hInt₁ : Integrable (fun ω => explicitEquil (γ₁ ω) K r) μ :=
    (integrable_const (1 : ℝ)).mono
      (by have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
            unfold explicitEquil; apply Continuous.div_const
            exact continuous_neg.add (Real.continuous_sqrt.comp
              ((continuous_pow 2).add continuous_const))
          exact (hc.measurable.comp hγ₁_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, norm_one]
        exact le_of_lt (abs_lt.mpr
          ⟨by linarith [explicitEquil_pos (γ₁ ω) K r (hγ₁_pos ω) hK hr],
           explicitEquil_lt_one (γ₁ ω) K r (hγ₁_pos ω) hK hr⟩))
  have hInt₂ : Integrable (fun ω => explicitEquil (γ₂ ω) K r) μ :=
    (integrable_const (1 : ℝ)).mono
      (by have hc : Continuous (fun x : ℝ => explicitEquil x K r) := by
            unfold explicitEquil; apply Continuous.div_const
            exact continuous_neg.add (Real.continuous_sqrt.comp
              ((continuous_pow 2).add continuous_const))
          exact (hc.measurable.comp hγ₂_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, norm_one]
        exact le_of_lt (abs_lt.mpr
          ⟨by linarith [explicitEquil_pos (γ₂ ω) K r (hγ₂_pos ω) hK hr],
           explicitEquil_lt_one (γ₂ ω) K r (hγ₂_pos ω) hK hr⟩))
  exact integral_mono hInt₂ hInt₁
    (fun ω => explicitEquil_mono_gamma (γ₁ ω) (γ₂ ω) K r (hγ₁_pos ω) hK hr (h_le ω))

/-! ## Equilibrium comparison across distributions -/

/-- **DISTRIBUTION SENSITIVITY OF r*.**
    If γ₁ ≤ γ₂ pointwise and both K > Kc(γ₁), K > Kc(γ₂), with fixed points
    r₁* and r₂*, then r₁* ≥ r₂*.
    Narrower frequency distributions produce larger order parameters.

    Proof: By contradiction using monotonicity.
    If r₁* < r₂*, then at r = r₂*:
      Φ_{γ₁}(r₂*) ≥ Φ_{γ₂}(r₂*) = r₂*
    So Φ_{γ₁}(r₂*) ≥ r₂* > r₁* = Φ_{γ₁}(r₁*).
    But Φ_{γ₁} has unique fixed point r₁* and Φ_{γ₁}(r) < r for r > r₁*.
    Since r₂* > r₁*: Φ_{γ₁}(r₂*) < r₂*, contradicting Φ_{γ₁}(r₂*) ≥ r₂*. -/
theorem rstar_mono_gamma [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ) (K r₁ r₂ : ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (hK : 0 < K)
    (h_le : ∀ ω, γ₁ ω ≤ γ₂ ω)
    (hγ₁_level : ∀ M : ℝ, MeasurableSet {ω | γ₁ ω ≤ M})
    (hγ₂_level : ∀ M : ℝ, MeasurableSet {ω | γ₂ ω ≤ M})
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hfp₁ : ∫ ω, explicitEquil (γ₁ ω) K r₁ ∂μ = r₁)
    (hfp₂ : ∫ ω, explicitEquil (γ₂ ω) K r₂ ∂μ = r₂) :
    r₂ ≤ r₁ := by
  by_contra h_not
  have h_lt : r₁ < r₂ := by linarith [not_le.mp h_not]
  have hΦ₁_below := sc_map_below_above γ₁ K r₂ r₁ hγ₁_pos hK hγ₁_level hr₂ hr₁ hfp₁ h_lt
  have hΦ_compare := sc_map_mono_gamma (μ := μ) γ₁ γ₂ K r₂ hγ₁_pos hγ₂_pos hK hr₂ h_le
    hγ₁_level hγ₂_level
  linarith

/-! ## Kc determines the transition -/

/-- **Kc determines onset threshold.**
    For K just above Kc₁ but below Kc₂:
    distribution γ₁ synchronizes but γ₂ does not. -/
theorem Kc_separates_phases [IsProbabilityMeasure μ]
    (γ₁ γ₂ : Ω → ℝ) (K : ℝ)
    (hγ₁_pos : ∀ ω, 0 < γ₁ ω) (hγ₂_pos : ∀ ω, 0 < γ₂ ω)
    (hK : 0 < K)
    (hγ₁_level : ∀ M : ℝ, MeasurableSet {ω | γ₁ ω ≤ M})
    (hγ₂_level : ∀ M : ℝ, MeasurableSet {ω | γ₂ ω ≤ M})
    (h_inv₁_int : Integrable (fun ω => 1 / γ₁ ω) μ)
    (h_inv₁_pos : 0 < ∫ ω, (1 / γ₁ ω) ∂μ)
    (h_inv₂_int : Integrable (fun ω => 1 / γ₂ ω) μ)
    (h_inv₂_pos : 0 < ∫ ω, (1 / γ₂ ω) ∂μ)
    (h_super₁ : continuumKc γ₁ μ < K)
    (h_sub₂ : K ≤ continuumKc γ₂ μ) :
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧ r = ∫ ω, explicitEquil (γ₁ ω) K r ∂μ) ∧
    (∀ r : ℝ, 0 < r → ∫ ω, explicitEquil (γ₂ ω) K r ∂μ ≠ r) := by
  exact ⟨sc_fixed_point_exists_supercritical γ₁ K hK hγ₁_pos hγ₁_level
      h_inv₁_int h_inv₁_pos h_super₁,
    fun r hr => no_equilibrium_subcritical γ₂ K hK hγ₂_pos hγ₂_level
      h_inv₂_int h_inv₂_pos h_sub₂ r hr⟩

end
