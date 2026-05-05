/-
  Body Leibniz Proof: HasDerivAt for body-restricted Lyapunov integral
  ====================================================================
  Proves d/dt ∫_{γ≤M} (α-α*)² g = ∫_{γ≤M} 2(α-α*)·α' g using
  hasDerivAt_integral_of_dominated_loc_of_deriv_le with constant
  dominator 2M+K on restricted measure μ.restrict {γ≤M}.

  No γ integrability needed — works for Lorentzian g.

  0 sorry.
-/

import KuramotoLean.ContinuumSolvedDerived

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Body Leibniz rule.** HasDerivAt for the body-restricted integral
    ∫_{γ≤M} (α(ω,t) - α*(ω))² dμ. Uses constant dominator 2M+K
    (from γ ≤ M on body). No γ integrability needed. -/
theorem body_leibniz_hasDerivAt [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (hK : 0 < K) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hαs_int : Integrable α_star μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (M : ℝ) (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    HasDerivAt (fun s => ∫ ω in {ω | γ ω ≤ M}, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω in {ω | γ ω ≤ M}, 2 * (α ω t₀ - α_star ω) *
        oaScalarRHS (γ ω) K r t₀ (α ω t₀) ∂μ) t₀ := by
  set body := {ω | γ ω ≤ M}
  haveI : IsFiniteMeasure (μ.restrict body) := isFiniteMeasureRestrict μ body
  have hα_inv_all : ∀ ω t, 0 < α ω t ∧ α ω t < 1 := by
    intro ω t; by_cases ht : 0 ≤ t
    · exact hα_inv ω t ht
    · have ht' := not_le.mp ht
      rw [hα_neg ω t (le_of_lt ht')]; exact hα_inv ω 0 le_rfl
  have h_pw_deriv : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
      HasDerivAt (fun u => (α ω u - α_star ω) ^ 2)
        (2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)) s := by
    intro ω s hs
    have h := (hα_ode ω s (le_of_lt (mem_Ioi.mp hs))).sub_const (α_star ω)
    convert h.pow 2 using 1; push_cast; ring
  have h_norm_bound : ∀ ω, ω ∈ body → ∀ s ∈ Ioi (0:ℝ),
      ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖ ≤ 2 * M + K := by
    intro ω hω s hs
    have hs_pos := mem_Ioi.mp hs
    have hp := (hα_inv ω s (le_of_lt hs_pos)).1
    have hl := (hα_inv ω s (le_of_lt hs_pos)).2
    have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
    have hγ_le : γ ω ≤ M := hω
    have h_diff_le : |α ω s - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h_rhs_le : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ M + K / 2 := by
      unfold oaScalarRHS
      have hα1 : 0 ≤ α ω s := le_of_lt hp
      have hα2 : α ω s ≤ 1 := le_of_lt hl
      have hγ_nn : 0 ≤ γ ω := le_of_lt (hγ_pos ω)
      have hr1 : |r s| ≤ 1 := hr_bdd s
      have h1mα2 : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
      have h1mα2' : 1 - (α ω s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω s)]
      have hrs_lo : -1 ≤ r s := by linarith [(abs_le.mp hr1).1]
      have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
      have h_prod_bdd : |r s * (1 - (α ω s) ^ 2)| ≤ 1 := by
        rw [abs_mul]; exact mul_le_one₀ (abs_le.mpr ⟨hrs_lo, hrs_hi⟩)
          (abs_nonneg _) (abs_le.mpr ⟨by linarith, h1mα2'⟩)
      rw [abs_le]; constructor <;> nlinarith [(abs_le.mp h_prod_bdd).1, (abs_le.mp h_prod_bdd).2]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
    nlinarith [abs_nonneg (α ω s - α_star ω), abs_nonneg (oaScalarRHS (γ ω) K r s (α ω s))]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => (α ω s - α_star ω) ^ 2)
    (F' := fun s ω => 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s))
    (bound := fun _ => 2 * M + K)
    (x₀ := t₀)
    (μ := μ.restrict body)
    (hs := Ioi_mem_nhds ht₀)
    (hF_meas := Eventually.of_forall fun s =>
      ((hα_sq_int s).aestronglyMeasurable).mono_measure Measure.restrict_le_self)
    (hF_int := (hα_sq_int t₀).mono_measure Measure.restrict_le_self)
    (hF'_meas := by
      change AEStronglyMeasurable
        (fun ω => 2 * (α ω t₀ - α_star ω) *
          (-(γ ω) * α ω t₀ + K / 2 * r t₀ * (1 - (α ω t₀) ^ 2))) (μ.restrict body)
      exact ((aestronglyMeasurable_const.mul
        ((hα_int t₀).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable)).mul
        ((hγ_meas.neg.mul (hα_int t₀).aestronglyMeasurable).add
          (aestronglyMeasurable_const.mul
            (aestronglyMeasurable_const.sub
              ((hα_int t₀).aestronglyMeasurable.pow 2))))).mono_measure
                Measure.restrict_le_self)
    (h_bound := by
      apply (ae_restrict_mem hγ_level).mono
      intro ω hω s hs; exact h_norm_bound ω hω s hs)
    (bound_integrable := integrable_const _)
    (h_diff := Eventually.of_forall fun ω s hs => h_pw_deriv ω s hs)).2

end
