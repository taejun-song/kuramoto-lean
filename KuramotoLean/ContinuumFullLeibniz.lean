/-
  ContinuumFullLeibniz.lean
  =========================
  Proves: HasDerivAt for the FULL Lyapunov V(t) = ∫ (α(ω,t) - α*(ω))² dμ
  using the first moment condition hγ_int : Integrable γ μ.

  Key difference from body_leibniz_hasDerivAt (BodyLeibnizProof.lean):
    - No body restriction: integrates over all of Ω.
    - Dominator: fun ω => 2*γ(ω)+K (not constant 2M+K).
    - Dominator integrability: from hγ_int (not from finite body measure).

  Method: hasDerivAt_integral_of_dominated_loc_of_deriv_le with
    F(s,ω) = (α(ω,s)-α*(ω))², F'(s,ω) = 2(α-α*)·RHS,
    bound(ω) = 2γ(ω)+K.

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedDerived

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Full Leibniz rule.** HasDerivAt for the full-domain Lyapunov integral
    V(t) = ∫ (α(ω,t) - α*(ω))² dμ. Uses dominator 2γ(ω)+K, integrable from
    first moment hγ_int. Generalises body_leibniz_hasDerivAt to all of Ω. -/
theorem full_v_leibniz_hasDerivAt [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hK : 0 < K) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hαs_int : Integrable α_star μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    HasDerivAt (fun s => ∫ ω, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω, 2 * (α ω t₀ - α_star ω) *
        oaScalarRHS (γ ω) K r t₀ (α ω t₀) ∂μ) t₀ := by
  have hγ_nn : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have h_pw_deriv : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
      HasDerivAt (fun u => (α ω u - α_star ω) ^ 2)
        (2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)) s := by
    intro ω s hs
    have h := (hα_ode ω s (le_of_lt (mem_Ioi.mp hs))).sub_const (α_star ω)
    convert h.pow 2 using 1; push_cast; ring
  have h_norm_bound : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
      ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖ ≤ 2 * γ ω + K := by
    intro ω s hs
    have hs_pos := mem_Ioi.mp hs
    have hp := (hα_inv ω s (le_of_lt hs_pos)).1
    have hl := (hα_inv ω s (le_of_lt hs_pos)).2
    have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
    have h_diff_le : |α ω s - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h_rhs_le : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ γ ω + K / 2 := by
      unfold oaScalarRHS
      have hα1 : 0 ≤ α ω s := le_of_lt hp
      have hα2 : α ω s ≤ 1 := le_of_lt hl
      have hr1 : |r s| ≤ 1 := hr_bdd s
      have h1mα2 : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
      have h1mα2' : 1 - (α ω s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω s)]
      have hrs_lo : -1 ≤ r s := by linarith [(abs_le.mp hr1).1]
      have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
      have h_prod_bdd : |r s * (1 - (α ω s) ^ 2)| ≤ 1 := by
        rw [abs_mul]; exact mul_le_one₀ (abs_le.mpr ⟨hrs_lo, hrs_hi⟩)
          (abs_nonneg _) (abs_le.mpr ⟨by linarith, h1mα2'⟩)
      rw [abs_le]; constructor <;>
        nlinarith [(abs_le.mp h_prod_bdd).1, (abs_le.mp h_prod_bdd).2, hγ_nn ω]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
    nlinarith [abs_nonneg (α ω s - α_star ω), abs_nonneg (oaScalarRHS (γ ω) K r s (α ω s)),
              hγ_nn ω, hK.le]
  have h_bound_int : Integrable (fun ω => 2 * γ ω + K) μ := by
    have h1 : Integrable (fun ω => 2 * γ ω) μ := hγ_int.const_mul 2
    exact h1.add (integrable_const K)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => (α ω s - α_star ω) ^ 2)
    (F' := fun s ω => 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s))
    (bound := fun ω => 2 * γ ω + K)
    (x₀ := t₀)
    (μ := μ)
    (hs := Ioi_mem_nhds ht₀)
    (hF_meas := Eventually.of_forall fun s => (hα_sq_int s).aestronglyMeasurable)
    (hF_int := hα_sq_int t₀)
    (hF'_meas := by
      change AEStronglyMeasurable
        (fun ω => 2 * (α ω t₀ - α_star ω) *
          (-(γ ω) * α ω t₀ + K / 2 * r t₀ * (1 - (α ω t₀) ^ 2))) μ
      exact (aestronglyMeasurable_const.mul
        ((hα_int t₀).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable)).mul
        ((hγ_meas.neg.mul (hα_int t₀).aestronglyMeasurable).add
          (aestronglyMeasurable_const.mul
            (aestronglyMeasurable_const.sub
              ((hα_int t₀).aestronglyMeasurable.pow 2)))))
    (h_bound := Eventually.of_forall fun ω s hs => h_norm_bound ω s hs)
    (bound_integrable := h_bound_int)
    (h_diff := Eventually.of_forall fun ω s hs => h_pw_deriv ω s hs)).2

end
