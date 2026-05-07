/-
  ContinuumSolvedWired2.lean
  ==========================
  Eliminates `h_gronwall_from_persist` from `kuramoto_continuum_wired` by
  internally using `body_gronwall_wired`. Reduces open assumptions from 4 to 3.

  ELIMINATED (now proved internally):
    • h_gronwall_from_persist (body Gronwall from persistence)
    • hV_body_cont (V_body continuity — subsumed by body_gronwall_wired)

  REMAINING OPEN (genuine analytic inputs):
    • hα_lb — body persistence (derivable from h_r_persist + hα_0_body
      via continuum_body_persistence, left to user for flexibility)
    • hr_star_pos — r_star > 0 (supercritical condition K > K_c)
    • hμ_body_pos — each body {γ ≤ M} has positive measure
    • h_combined_vanish — C(M) + μ(tail) → 0 (depends on g's tail decay)

  C(M) is explicit: K · μ(tail M) / (K · δ_lb(M) · ds(M) · μ(body M))
  where ds(M) = K · r* / (2M + K · r*)

  0 sorry. 0 axioms.
-/

import KuramotoLean.BodyGronwallWired
import KuramotoLean.ContinuumSolvedComplete

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fully wired Kuramoto continuum theorem** — eliminates h_gronwall_from_persist.

  Compared to `kuramoto_continuum_wired`, this removes h_gronwall_from_persist
  and derives the body Gronwall bound internally via `body_gronwall_wired`. -/
theorem kuramoto_continuum_wired2 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
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
    -- Body persistence: α(ω,t) ≥ δ_lb(M) for all ω ∈ {γ ≤ M}, t ≥ 0.
    -- Derivable from h_r_persist + hα_0_body via continuum_body_persistence.
    (δ_lb : ℝ → ℝ) (hδ_lb_pos : ∀ M, 0 < M → 0 < δ_lb M)
    (hα_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ_lb M ≤ α ω t)
    -- Positivity of each body's measure
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal)
    -- Combined vanishing: C(M) + μ(tail) → 0
    -- C(M) = K · μ(tail M) / (K · δ_lb(M) · ds(M) · μ(body M))
    --       where ds(M) = K · r* / (2M + K · r*)
    (h_combined_vanish : Tendsto
        (fun M => K * (μ {ω | M < γ ω}).toReal /
              (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
                (μ {ω | γ ω ≤ M}).toReal) +
            (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  -- Use max 0 to ensure C M ≥ 0 for all M
  set C := fun M => max 0 (K * (μ {ω | M < γ ω}).toReal /
      (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
        (μ {ω | γ ω ≤ M}).toReal))
  have hC_nn : ∀ M, 0 ≤ C M := fun M => le_max_left 0 _
  -- For M > 0, C M equals the explicit formula (denominator > 0)
  have hC_eq : ∀ M, 0 < M → C M = K * (μ {ω | M < γ ω}).toReal /
        (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
          (μ {ω | γ ω ≤ M}).toReal) := fun M hM => by
    simp only [C]
    apply max_eq_right
    apply div_nonneg (mul_nonneg (le_of_lt hK) ENNReal.toReal_nonneg)
    apply mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt (hδ_lb_pos M hM)))
      (div_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt hr_star_pos)) (by positivity)))
    exact ENNReal.toReal_nonneg
  -- Derive h_body_gronwall using body_gronwall_wired (explicit rate)
  have h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧ ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M := fun M hM => by
    obtain ⟨hrate, h_bound⟩ := body_gronwall_wired γ K hK hγ hγ_meas α_star r_star
      hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
      r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
      M hM (hγ_level M) (δ_lb M) (hδ_lb_pos M hM) (hα_lb M hM) (hμ_body_pos M hM)
    rw [hC_eq M hM]
    exact ⟨_, hrate, h_bound⟩
  -- Combined vanishing for max-adjusted C M
  have h_cv : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have : (fun M => C M + (μ {ω | M < γ ω}).toReal) =ᶠ[atTop]
        (fun M => K * (μ {ω | M < γ ω}).toReal /
          (K * δ_lb M * (K * r_star / (2 * M + K * r_star)) *
            (μ {ω | γ ω ≤ M}).toReal) + (μ {ω | M < γ ω}).toReal) := by
      apply Filter.eventually_atTop.mpr ⟨1, fun M hM => ?_⟩
      simp only [hC_eq M (by linarith)]
    exact h_combined_vanish.congr' this.symm
  -- Apply kuramoto_continuum_stability_gronwall
  exact kuramoto_continuum_stability_gronwall γ K hK hγ hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    hγ_level C hC_nn h_body_gronwall h_cv

end
