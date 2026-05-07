/-
  KuramotoExplicitInitWired7.lean
  ================================
  Applies kuramoto_continuum_wired7 to the case where oscillators start at
  their equilibrium activities for an initial order parameter r₀.

  KEY LEMMA (explicitEquil_eventually_lb):
    explicitEquil M K r₀ ≥ (K * r₀ / 4) / M  when  M ≥ K * r₀ / 2.

  Proof:
    explicitEquil M K r₀ = K*r₀/(M + √(M²+K²r₀²))  (rationalized form)
    √(M²+K²r₀²) ≤ M + K*r₀  (since (M+K*r₀)² ≥ M²+K²r₀²)
    → denominator ≤ 2M + K*r₀
    → explicitEquil M K r₀ ≥ K*r₀/(2M+K*r₀)
    For M ≥ K*r₀/2: (K*r₀/4)/M ≤ K*r₀/(2M+K*r₀) iff K²r₀²/4 ≤ K*r₀*M/2 iff M ≥ K*r₀/2  ✓

  RESULT: kuramoto_explicit_init_convergence replaces hδ₀_body_lb and
  hδ₀_body_pos in kuramoto_continuum_wired7 with:
    hr₀ : 0 < r₀  (initial order parameter)
    hα_0_explicitEquil : ∀ ω, explicitEquil (γ ω) K r₀ ≤ α ω 0  (initial activity ≥ equilibrium)

  Covers all finite-second-moment distributions with explicitEquil initial data.

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired7
import KuramotoLean.SelfConsistencyFixedPoint

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For M ≥ K*r₀/2: (K*r₀/4)/M ≤ K*r₀/(2M+K*r₀) ≤ explicitEquil M K r₀. -/
private lemma explicitEquil_eventually_lb (M K r₀ : ℝ)
    (hM_pos : 0 < M) (hK : 0 < K) (hr₀ : 0 < r₀)
    (hM₀ : K * r₀ / 2 ≤ M) :
    K * r₀ / 4 / M ≤ explicitEquil M K r₀ := by
  rw [explicitEquil_rationalized M K r₀ hM_pos hK hr₀]
  have h_sqrt_le : sqrt (M ^ 2 + K ^ 2 * r₀ ^ 2) ≤ M + K * r₀ := by
    rw [← sqrt_sq (by positivity : 0 ≤ M + K * r₀)]
    exact sqrt_le_sqrt (by nlinarith [mul_pos hM_pos (mul_pos hK hr₀)])
  have h_denom_le : M + sqrt (M ^ 2 + K ^ 2 * r₀ ^ 2) ≤ 2 * M + K * r₀ := by linarith
  have h_denom_pos : 0 < M + sqrt (M ^ 2 + K ^ 2 * r₀ ^ 2) := by positivity
  have h_frac_le : K * r₀ / 4 / M ≤ K * r₀ / (2 * M + K * r₀) := by
    rw [show K * r₀ / 4 / M = K * r₀ / (4 * M) from by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc K * r₀ / 4 / M
      ≤ K * r₀ / (2 * M + K * r₀) := h_frac_le
    _ ≤ K * r₀ / (M + sqrt (M ^ 2 + K ^ 2 * r₀ ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) h_denom_pos h_denom_le

/-- **Continuum convergence with explicitEquil initial data.**

    Applies kuramoto_continuum_wired7 when each oscillator starts at or above
    its equilibrium activity for initial order parameter r₀.

    The structural hypothesis `hδ₀_body_lb` is auto-derived: since
      explicitEquil M K r₀ ≥ (K*r₀/4)/M  for M ≥ K*r₀/2,
    the eventual c/M lower bound (wired7's weakened form) is satisfied with
    c = K*r₀/4 and M₀ = K*r₀/2.

    The positivity `hδ₀_body_pos` is also auto-derived from `explicitEquil_pos`.

    The caller supplies `hα_0_explicitEquil`: each oscillator starts with
    activity ≥ explicitEquil(γ(ω), K, r₀) — physically, the initial state
    is at (or above) the equilibrium configuration for order parameter r₀. -/
theorem kuramoto_explicit_init_convergence [IsProbabilityMeasure μ]
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
    (hγ_sq_int : Integrable (fun ω => (γ ω) ^ 2) μ)
    -- Positive damping (required for explicitEquil monotonicity)
    (hγ_pos : ∀ ω, 0 < γ ω)
    -- Initial order parameter: replaces hδ₀_body_pos + hδ₀_body_lb
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    -- Each oscillator starts at or above equilibrium for r₀
    (hα_0_explicitEquil : ∀ ω, explicitEquil (γ ω) K r₀ ≤ α ω 0) :
    Tendsto r atTop (nhds r_star) := by
  let δ₀_body : ℝ → ℝ := fun M => explicitEquil M K r₀
  apply kuramoto_continuum_wired7 γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hr_cont hr_bdd hr_nn
    hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv r_min hr_min_pos hr_bound
    δ₀_body
    -- hδ₀_body_pos: explicitEquil M K r₀ > 0 for M > 0
    (fun M hM => explicitEquil_pos M K r₀ hM hK hr₀)
    -- hα_0_body: explicitEquil M K r₀ ≤ α(ω,0) when γ(ω) ≤ M
    (fun M _ ω hγω => by
      calc explicitEquil M K r₀
          ≤ explicitEquil (γ ω) K r₀ :=
            explicitEquil_mono_gamma (γ ω) M K r₀ (hγ_pos ω) hK hr₀ hγω
        _ ≤ α ω 0 := hα_0_explicitEquil ω)
    hγ_sq_int
    -- hδ₀_body_lb: c = K*r₀/4, M₀ = K*r₀/2 satisfy c/M ≤ explicitEquil M K r₀ for M ≥ M₀
    ⟨K * r₀ / 4, by positivity, K * r₀ / 2, by positivity,
      fun M hM₀ => by
        have hM_pos : 0 < M := lt_of_lt_of_le (by positivity) hM₀
        exact explicitEquil_eventually_lb M K r₀ hM_pos hK hr₀ hM₀⟩

end
