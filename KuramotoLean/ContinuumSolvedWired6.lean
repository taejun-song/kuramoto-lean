/-
  ContinuumSolvedWired6.lean
  ==========================
  Eliminates `hμ_body_pos` — the last remaining assumption in the wired chain.

  KEY IDEA: case-split on μ{γ ≤ M} = 0.
    ∙ Null body: V_body(M,t) = 0 (integral over null set), Gronwall trivial.
    ∙ Positive body: use body_gronwall_wired.
  For h_combined_vanish, μ(body M) > 0 holds for large M automatically
  (τ M → 0 forces b M → 1 > 0 from b M + τ M = 1).

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired5

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- K·r/(2M+K·r) ≤ bodyEquilibrium M K r. -/
private theorem bodyEquil_ge_frac'' (M K r : ℝ) (hM : 0 < M) (hK : 0 < K) (hr : 0 < r) :
    K * r / (2 * M + K * r) ≤ bodyEquilibrium M K r :=
  body_equil_lower_bound M K r (bodyEquilibrium M K r) M hK hr
    (bodyEquilibrium_pos M K r hM.le hK hr) le_rfl hM
    (bodyEquilibrium_equil M K r hK hr)

theorem kuramoto_continuum_wired6 [IsProbabilityMeasure μ]
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
    (hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ)
    (hδ₀_body_lb : ∃ c : ℝ, 0 < c ∧ ∀ M, 0 < M → c / M ≤ δ₀_body M) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := hδ₀_body_lb
  have hr_min_le : r_min ≤ 1 := by linarith [(abs_le.mp (hr_bdd 0)).2, hr_bound 0 le_rfl]
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq]
    have h_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ :=
      integral_nonneg (fun ω => (hα_star_pos ω).le)
    rcases h_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨ω, hω⟩ := ((integral_eq_zero_iff_of_nonneg
        (fun ω => (hα_star_pos ω).le) hαs_int).mp h.symm).exists
      simp at hω; linarith [hα_star_pos ω]
  have h_τ_vanish : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero' γ hγ_level
  have h_sq_tail := second_moment_tail_vanish γ hγ_sq_int hγ_level
  let C₁ := min c (K * r_min / 3)
  have hC₁_pos : 0 < C₁ := lt_min hc_pos (by positivity)
  let C₂ := K ^ 2 * r_star * C₁ / 6
  have hC₂_pos : 0 < C₂ := by positivity
  have hα_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t →
      min (δ₀_body M) (bodyEquilibrium M K r_min) ≤ α ω t := fun M hM ω hγω t ht =>
    le_trans (min_le_min (hα_0_body M hM ω hγω) le_rfl)
      (body_persistence_lower_bound (γ ω) M K r (α ω) r_min (hγ ω) hγω hK hr_min_pos
        hr_min_le hr_bound hr_bdd (fun t ht => hα_ode ω t (le_of_lt ht))
        (hα_inv ω) (hα_cont ω) t ht)
  have hδ_lb_pos : ∀ M, 0 < M → 0 < min (δ₀_body M) (bodyEquilibrium M K r_min) :=
    fun M hM => lt_min (hδ₀_body_pos M hM)
      (bodyEquilibrium_pos M K r_min (le_of_lt hM) hK hr_min_pos)
  -- b M + τ M = 1 (partition into body and tail)
  have h_partition : ∀ M : ℝ,
      (μ {ω | M < γ ω}).toReal + (μ {ω | γ ω ≤ M}).toReal = 1 := fun M => by
    have h_disj : Disjoint {ω | M < γ ω} {ω | γ ω ≤ M} := by
      simp only [Set.disjoint_left, Set.mem_setOf_eq]; intro ω h1 h2; linarith
    have h_union : {ω | M < γ ω} ∪ {ω | γ ω ≤ M} = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun ω => by
        simp only [Set.mem_union, Set.mem_setOf_eq]; exact lt_or_ge M (γ ω)
    have h_mu : μ {ω | M < γ ω} + μ {ω | γ ω ≤ M} = 1 := by
      rw [← measure_union h_disj (hγ_level M), h_union, measure_univ]
    have h_toReal := ENNReal.toReal_add
      (measure_ne_top μ {ω | M < γ ω}) (measure_ne_top μ {ω | γ ω ≤ M})
    rw [h_mu, ENNReal.toReal_one] at h_toReal
    linarith
  -- Absorbing radius C M = max 0 (K·τ/(K·δ·ds·b))
  let CM := fun M => K * (μ {ω | M < γ ω}).toReal /
      (K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
       (K * r_star / (2 * M + K * r_star)) *
       (μ {ω | γ ω ≤ M}).toReal)
  set C := fun M => max 0 (CM M) with hC_def
  have hC_nn : ∀ M, 0 ≤ C M := fun M => le_max_left 0 _
  -- For M > 0 with b M > 0, CM M ≥ 0 so C M = CM M
  have hCM_nn_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal → 0 ≤ CM M := fun M hM hb => by
    apply div_nonneg (mul_nonneg hK.le ENNReal.toReal_nonneg)
    exact le_of_lt (mul_pos (mul_pos (mul_pos hK (hδ_lb_pos M hM))
      (div_pos (mul_pos hK hr_star_pos) (by positivity))) hb)
  -- CM M → 0 as M → ∞
  have hCM_vanish : Tendsto CM atTop (nhds 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_ge_atTop (max (K * r_min) (K * r_star)),
                      h_τ_vanish.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
                      eventually_gt_atTop (0:ℝ)] with M hM hτ hM_pos
      have hM_Kr : K * r_min ≤ M := le_of_max_le_left hM
      have hM_Ks : K * r_star ≤ M := le_of_max_le_right hM
      have hb_lb : (1:ℝ)/2 ≤ (μ {ω | γ ω ≤ M}).toReal := by
        linarith [hτ.le, h_partition M]
      have hb_pos : 0 < (μ {ω | γ ω ≤ M}).toReal :=
        lt_of_lt_of_le (by norm_num) hb_lb
      -- δ_lb ≥ C₁/M
      have hδ_lb : C₁ / M ≤ min (δ₀_body M) (bodyEquilibrium M K r_min) := by
        apply le_min
        · exact le_trans (div_le_div_of_nonneg_right (min_le_left c (K * r_min / 3)) hM_pos.le)
              (hc_bound M hM_pos)
        · have hstep1 : C₁ / M ≤ K * r_min / (3 * M) := by
            have hle : C₁ ≤ K * r_min / 3 := min_le_right c (K * r_min / 3)
            have heq : K * r_min / 3 / M = K * r_min / (3 * M) := by ring
            rw [← heq]; exact div_le_div_of_nonneg_right hle hM_pos.le
          have hstep2 : K * r_min / (3 * M) ≤ K * r_min / (2 * M + K * r_min) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
          exact le_trans (le_trans hstep1 hstep2) (bodyEquil_ge_frac'' M K r_min hM_pos hK hr_min_pos)
      -- ds M ≥ K*r*/(3M)
      have hds_lb : K * r_star / (3 * M) ≤ K * r_star / (2 * M + K * r_star) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      -- Denominator lower bound: C₂/M² ≤ K·δ·ds·b
      have h_denom_lb : C₂ / M ^ 2 ≤
          K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
          (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal := by
        have heq : C₂ / M ^ 2 = K * (C₁ / M) * (K * r_star / (3 * M)) * (1 / 2) := by
          show K ^ 2 * r_star * C₁ / 6 / M ^ 2 =
               K * (C₁ / M) * (K * r_star / (3 * M)) * (1 / 2)
          field_simp [hM_pos.ne']; ring
        rw [heq]
        have hKδ_nn : 0 ≤ K * min (δ₀_body M) (bodyEquilibrium M K r_min) :=
          mul_nonneg hK.le (le_trans (div_nonneg hC₁_pos.le hM_pos.le) hδ_lb)
        have hds_nn : 0 ≤ K * r_star / (3 * M) := by positivity
        apply mul_le_mul _ hb_lb (by norm_num) (mul_nonneg hKδ_nn (le_trans hds_nn hds_lb))
        apply mul_le_mul _ hds_lb hds_nn hKδ_nn
        exact mul_le_mul_of_nonneg_left hδ_lb hK.le
      have h_denom_pos : 0 < K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
          (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal :=
        lt_of_lt_of_le (by positivity) h_denom_lb
      show ‖CM M‖ ≤ K / C₂ * (M ^ 2 * (μ {ω | M < γ ω}).toReal)
      rw [Real.norm_of_nonneg
        (div_nonneg (mul_nonneg hK.le ENNReal.toReal_nonneg) h_denom_pos.le)]
      have h1 : CM M ≤ K * (μ {ω | M < γ ω}).toReal / (C₂ / M ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hK.le ENNReal.toReal_nonneg)
          (by positivity) h_denom_lb
      have h2 : K * (μ {ω | M < γ ω}).toReal / (C₂ / M ^ 2) =
          K / C₂ * (M ^ 2 * (μ {ω | M < γ ω}).toReal) := by
        field_simp [hC₂_pos.ne', hM_pos.ne']
      exact h1.trans h2.le
    · simpa using h_sq_tail.const_mul (K / C₂)
  -- C M + τ M → 0: for large M, C M = CM M, so this follows from hCM_vanish + h_τ_vanish
  have h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have hkey : Tendsto (fun M => CM M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
      have h := hCM_vanish.add h_τ_vanish; simp only [add_zero] at h; exact h
    apply hkey.congr'
    filter_upwards [h_τ_vanish.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
                    eventually_gt_atTop (0:ℝ)] with M hτ hM_pos
    have hb_pos : 0 < (μ {ω | γ ω ≤ M}).toReal := by linarith [hτ.le, h_partition M]
    simp [hC_def, max_eq_right (hCM_nn_pos M hM_pos hb_pos)]
  -- Body Gronwall: case split on μ{γ ≤ M} = 0
  have h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧ ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M := fun M hM => by
    by_cases hμ_null : μ {ω | γ ω ≤ M} = 0
    · -- Null body: V_body = 0
      have hC_zero : C M = 0 := by
        simp only [hC_def, CM]
        rw [show (μ {ω | γ ω ≤ M}).toReal = 0 from by simp [hμ_null]]
        simp
      have hV_zero : ∀ t : ℝ,
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ = 0 := fun t => by
        show ∫ ω, (α ω t - α_star ω) ^ 2 ∂(μ.restrict {ω | γ ω ≤ M}) = 0
        rw [Measure.restrict_eq_zero.mpr hμ_null]; exact integral_zero_measure _
      exact ⟨1, one_pos, fun t ht => by rw [hV_zero t, hV_zero 0, hC_zero]; simp⟩
    · -- Positive body: use body_gronwall_wired
      have hb_pos : 0 < (μ {ω | γ ω ≤ M}).toReal :=
        ENNReal.toReal_pos hμ_null (measure_ne_top μ _)
      obtain ⟨hrate, h_bound⟩ := body_gronwall_wired γ K hK hγ hγ_meas α_star r_star
        hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
        r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
        M hM (hγ_level M)
        (min (δ₀_body M) (bodyEquilibrium M K r_min))
        (hδ_lb_pos M hM) (hα_lb M hM) hb_pos
      exact ⟨_, hrate, fun t ht => by
        have hC_eq : C M = CM M := max_eq_right (hCM_nn_pos M hM hb_pos)
        rw [hC_eq]; exact h_bound t ht⟩
  -- Conclude
  exact kuramoto_continuum_stability_gronwall γ K hK hγ hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level C hC_nn h_body_gronwall h_combined_vanish

end
