/-
  ContinuumSolvedWired5.lean
  ==========================
  Eliminates `h_combined_vanish` from `kuramoto_continuum_wired4` by
  deriving it from a finite-second-moment condition + initial body bound.

  ELIMINATED (now proved internally):
    • h_combined_vanish — C(M) + μ(tail) → 0. Proved from:
        (a) hγ_sq_int : Integrable (γ·)² → M²·τ(M) → 0 (second_moment_tail_vanish)
        (b) hδ₀_body_lb : ∃ c > 0, ∀ M > 0, c/M ≤ δ₀_body M
        Key estimate: C(M) ≤ 6·M²·τ(M) / (K·r*·C₁) → 0
        where C₁ = min(c, K·r_min/3) > 0.

  REMAINING OPEN (1 genuine analytic input):
    • hμ_body_pos — each body {γ ≤ M} has positive measure (support condition on g)

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired4
import KuramotoLean.TailSecondMoment
import KuramotoLean.ContinuumSolvedStandardModel

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Algebraic lower bound: bodyEquilibrium M K r_min ≥ K·r_min / (2M + K·r_min). -/
private theorem bodyEquil_ge_frac (M K r : ℝ) (hM : 0 < M) (hK : 0 < K) (hr : 0 < r) :
    K * r / (2 * M + K * r) ≤ bodyEquilibrium M K r := by
  have h_equil := bodyEquilibrium_equil M K r hK hr
  have h_pos := bodyEquilibrium_pos M K r hM.le hK hr
  exact body_equil_lower_bound M K r (bodyEquilibrium M K r) M hK hr h_pos le_rfl hM h_equil

/-- **Fully wired continuum theorem** — eliminates h_combined_vanish.

  Replaces h_combined_vanish with two physically natural conditions:
  - hγ_sq_int : Integrable (γ·)² — finite second moment of frequency distribution
  - hδ₀_body_lb : ∃ c > 0, ∀ M > 0, c/M ≤ δ₀_body M — initial body lower bound ≥ c/M

  Remaining open: hμ_body_pos (body measure positive = support condition). -/
theorem kuramoto_continuum_wired5 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (r_min : ℝ) (hr_min_pos : 0 < r_min)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (δ₀_body : ℝ → ℝ)
    (hδ₀_body_pos : ∀ M, 0 < M → 0 < δ₀_body M)
    (hα_0_body : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → δ₀_body M ≤ α ω 0)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal)
    (hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ)
    (hδ₀_body_lb : ∃ c : ℝ, 0 < c ∧ ∀ M, 0 < M → c / M ≤ δ₀_body M) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := hδ₀_body_lb
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq]
    have h_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ :=
      integral_nonneg (fun ω => (hα_star_pos ω).le)
    rcases h_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hae : α_star =ᵐ[μ] (fun _ => (0 : ℝ)) :=
        (integral_eq_zero_iff_of_nonneg (f := α_star)
          (fun ω => (hα_star_pos ω).le) hαs_int).mp h.symm
      exact absurd hae.exists.choose_spec (ne_of_gt (hα_star_pos _))
  have h_τ_vanish : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero' γ hγ_level
  have h_sq_tail := second_moment_tail_vanish γ hγ_sq_int hγ_level
  let C₁ := min c (K * r_min / 3)
  have hC₁_pos : 0 < C₁ := lt_min hc_pos (by positivity)
  let C₂ := K ^ 2 * r_star * C₁ / 6
  have hC₂_pos : 0 < C₂ := by positivity
  have h_combined_vanish : Tendsto
      (fun M => K * (μ {ω | M < γ ω}).toReal /
            (K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
             (K * r_star / (2 * M + K * r_star)) *
             (μ {ω | γ ω ≤ M}).toReal) +
            (μ {ω | M < γ ω}).toReal)
      atTop (nhds 0) := by
    let τ := fun M => (μ {ω | M < γ ω}).toReal
    let b := fun M => (μ {ω | γ ω ≤ M}).toReal
    let δ := fun M => min (δ₀_body M) (bodyEquilibrium M K r_min)
    let ds := fun M => K * r_star / (2 * M + K * r_star)
    let CM := fun M => K * τ M / (K * δ M * ds M * b M)
    have hCM_vanish : Tendsto CM atTop (nhds 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [eventually_ge_atTop (max (K * r_min) (K * r_star)),
                        h_τ_vanish.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
                        eventually_gt_atTop (0:ℝ)] with M hM hτ hM_pos
        have hM_Kr : K * r_min ≤ M := le_of_max_le_left hM
        have hM_Ks : K * r_star ≤ M := le_of_max_le_right hM
        have hb_lb : (1:ℝ)/2 ≤ b M := by
          have h_disj : Disjoint {ω | M < γ ω} {ω | γ ω ≤ M} := by
            simp only [Set.disjoint_left, Set.mem_setOf_eq]
            intro ω h1 h2; linarith
          have h_union : {ω | M < γ ω} ∪ {ω | γ ω ≤ M} = Set.univ :=
            Set.eq_univ_iff_forall.mpr (fun ω => by
              simp only [Set.mem_union, Set.mem_setOf_eq]; exact lt_or_ge M (γ ω))
          have h_mu : μ {ω | M < γ ω} + μ {ω | γ ω ≤ M} = 1 := by
            rw [← measure_union h_disj (hγ_level M), h_union, measure_univ]
          have h_toReal := ENNReal.toReal_add
            (measure_ne_top μ {ω | M < γ ω}) (measure_ne_top μ {ω | γ ω ≤ M})
          rw [h_mu, ENNReal.toReal_one] at h_toReal
          simp only [b, τ]; linarith [hτ.le, h_toReal]
        have hδ_lb : C₁ / M ≤ δ M := by
          simp only [δ]
          apply le_min
          · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hM_pos.le)
                (hc_bound M hM_pos)
          · calc C₁ / M ≤ (K * r_min / 3) / M := by
                      exact div_le_div_of_nonneg_right (min_le_right _ _) hM_pos.le
                  _ = K * r_min / (3 * M) := by ring
                  _ ≤ K * r_min / (2 * M + K * r_min) := by
                      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
                  _ ≤ bodyEquilibrium M K r_min :=
                      bodyEquil_ge_frac M K r_min hM_pos hK hr_min_pos
        have hds_lb : K * r_star / (3 * M) ≤ ds M := by
          simp only [ds]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        have hτ_nn : 0 ≤ τ M := ENNReal.toReal_nonneg
        have hK_τ_nn : 0 ≤ K * τ M := mul_nonneg hK.le hτ_nn
        have h_denom_lb : C₂ / M ^ 2 ≤ K * δ M * ds M * b M := by
          have heq : C₂ / M ^ 2 = K * (C₁ / M) * (K * r_star / (3 * M)) * (1 / 2) := by
            show K ^ 2 * r_star * C₁ / 6 / M ^ 2 =
                 K * (C₁ / M) * (K * r_star / (3 * M)) * (1 / 2)
            field_simp [hM_pos.ne']; ring
          rw [heq]
          have hKδ_nn : 0 ≤ K * δ M :=
            mul_nonneg hK.le (le_trans (div_nonneg hC₁_pos.le hM_pos.le) hδ_lb)
          have hds_nn : 0 ≤ K * r_star / (3 * M) := by positivity
          apply mul_le_mul _ hb_lb (by norm_num) (mul_nonneg hKδ_nn (le_trans hds_nn hds_lb))
          apply mul_le_mul _ hds_lb hds_nn hKδ_nn
          exact mul_le_mul_of_nonneg_left hδ_lb hK.le
        have h_denom_pos : 0 < K * δ M * ds M * b M :=
          lt_of_lt_of_le (by positivity) h_denom_lb
        show ‖CM M‖ ≤ K / C₂ * (M ^ 2 * τ M)
        rw [Real.norm_of_nonneg (div_nonneg hK_τ_nn h_denom_pos.le)]
        have h1 : K * τ M / (K * δ M * ds M * b M) ≤ K * τ M / (C₂ / M ^ 2) :=
          div_le_div_of_nonneg_left hK_τ_nn (by positivity) h_denom_lb
        have h2 : K * τ M / (C₂ / M ^ 2) = K / C₂ * (M ^ 2 * τ M) := by
          field_simp [hC₂_pos.ne', hM_pos.ne']
        exact h1.trans h2.le
      · simpa using h_sq_tail.const_mul (K / C₂)
    have h_add : Tendsto (fun M => CM M + τ M) atTop (nhds 0) := by
      simpa using hCM_vanish.add h_τ_vanish
    exact h_add.congr' (Eventually.of_forall (fun M => by simp [CM, τ, b, δ, ds]))
  exact kuramoto_continuum_wired4 γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    r_min hr_min_pos hr_bound δ₀_body hδ₀_body_pos hα_0_body hμ_body_pos h_combined_vanish

end
