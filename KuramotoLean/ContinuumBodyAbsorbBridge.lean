/-
  ContinuumBodyAbsorbBridge.lean
  ==============================

  Bridges the remaining `h_body_absorb` hypothesis in the tail-body
  convergence theorems to the already-proved body Gronwall machinery.

  Input data:
  * body persistence profile `δ_lb(M)` on `{γ ≤ M}`
  * positive equilibrium order parameter `r_star > 0`
  * positive body mass on each truncation

  Existing ingredients:
  * `body_gronwall_wired` produces the explicit body Gronwall bound
  * `body_absorb_from_gronwall` converts that Gronwall bound into the
    eventual absorbing-ball statement needed by the ISS bridge

  Output:
  * an explicit absorbing radius
      C(M) = K μ({γ > M}) / (K δ(M) ds(M) μ({γ ≤ M}))
    with `ds(M) = K r* / (2M + K r*)`
  * the corresponding `h_body_absorb` hypothesis

  This isolates the remaining analytic gap to the persistence/tail profile,
  rather than the conversion from persistence to absorbing ball.
-/

import KuramotoLean.BodyGronwallWired
import KuramotoLean.ContinuumTailBodyConvergence
import Mathlib

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The persistence profile and body-mass positivity hypotheses imply an explicit
body absorbing radius together with the `h_body_absorb` statement required by
the tail-body ISS convergence theorem. -/
theorem h_body_absorb_from_persistence_profile [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (δ_lb : ℝ → ℝ)
    (hδ_lb_pos : ∀ M, 0 < M → 0 < δ_lb M)
    (hα_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ_lb M ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    let C := fun M =>
      max 0 (K * (μ {ω | M < γ ω}).toReal /
        (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
          (μ {ω | γ ω ≤ M}).toReal))
    (∀ M, 0 ≤ C M) ∧
    (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  intro C
  constructor
  · intro M
    exact le_max_left 0 _
  · intro M hM ε hε
    have hds_pos : 0 < K * r_star / (2 * M + K * r_star) := by
      have hden : 0 < 2 * M + K * r_star := by positivity
      exact div_pos (mul_pos hK hr_star_pos) hden
    have hC_eq :
        C M = K * (μ {ω | M < γ ω}).toReal /
          (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
            (μ {ω | γ ω ≤ M}).toReal) := by
      dsimp [C]
      apply max_eq_right
      apply div_nonneg
      · exact mul_nonneg (le_of_lt hK) ENNReal.toReal_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (le_of_lt hK) (le_of_lt (hδ_lb_pos M hM))
          · exact le_of_lt hds_pos
        · exact ENNReal.toReal_nonneg
    have h_body_gronwall : ∀ M' : ℝ, 0 < M' →
        ∃ (rate : ℝ), 0 < rate ∧
          ∀ t ≥ (0 : ℝ),
            ∫ ω in {ω | γ ω ≤ M'}, (α ω t - α_star ω) ^ 2 ∂μ ≤
              (∫ ω in {ω | γ ω ≤ M'}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
                rexp (-rate * t) + C M' := by
      intro M' hM'
      obtain ⟨hrate, hbound⟩ := body_gronwall_wired γ K hK hγ_nn hγ_meas α_star r_star
        hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
        r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
        M' hM' (hγ_level M') (δ_lb M') (hδ_lb_pos M' hM') (hα_lb M' hM')
        (hμ_body_pos M' hM')
      have hC_eq' :
          C M' = K * (μ {ω | M' < γ ω}).toReal /
            (K * δ_lb M' * (K * r_star / (2 * M' + K * r_star)) *
              (μ {ω | γ ω ≤ M'}).toReal) := by
        dsimp [C]
        apply max_eq_right
        apply div_nonneg
        · exact mul_nonneg (le_of_lt hK) ENNReal.toReal_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · exact mul_nonneg (le_of_lt hK) (le_of_lt (hδ_lb_pos M' hM'))
            · have hds_pos' : 0 < K * r_star / (2 * M' + K * r_star) := by
                have hden' : 0 < 2 * M' + K * r_star := by positivity
                exact div_pos (mul_pos hK hr_star_pos) hden'
              exact le_of_lt hds_pos'
          · exact ENNReal.toReal_nonneg
      refine ⟨_, hrate, ?_⟩
      intro t ht
      rw [hC_eq']
      exact hbound t ht
    simpa [hC_eq] using
      body_absorb_from_gronwall α α_star hα_sq_int hγ_level C
        (fun M' => le_max_left 0 _) h_body_gronwall M hM ε hε

/-- The previous bridge packages the body absorbing radius into an existential
form that can be fed directly into the definitive continuum theorems. -/
theorem exists_absorbing_profile_from_persistence [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (δ_lb : ℝ → ℝ)
    (hδ_lb_pos : ∀ M, 0 < M → 0 < δ_lb M)
    (hα_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ_lb M ≤ α ω t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  refine ⟨fun M => max 0 (K * (μ {ω | M < γ ω}).toReal /
    (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
      (μ {ω | γ ω ≤ M}).toReal)), ?_, ?_⟩
  · intro M
    exact le_max_left 0 _
  · exact (h_body_absorb_from_persistence_profile γ K hK hγ_nn hγ_meas hγ_level
      α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
      hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
      δ_lb hδ_lb_pos hα_lb hμ_body_pos).2

end
