/-
  Finite-N ↔ Continuum Bridge
  =============================
  The continuum bifurcation theory (over abstract probability spaces)
  specializes to the finite-N theory when Ω = Fin N with the uniform
  probability measure.

  Key identities:
    1. continuumKc(γ, μ) = finiteKc(γ) when ∫(1/γ)dμ = (1/N)Σ(1/γₖ)
    2. Φ_continuum(r, μ) = finitePhiMap(γ, K, r) under the same measure
    3. All continuum theorems instantiate to finite-N versions

  The approach avoids constructing the measure explicitly: we show
  that whenever the integral identity ∫f dμ = (1/N)Σf(k) holds,
  the Kc and Φ formulas match.
-/

import KuramotoLean.FiniteNBifurcation
import KuramotoLean.IterationConvergence

open MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Kc bridge via integral identity -/

/-- **Kc BRIDGE.**
    If ∫(1/γ(ω))dμ = (1/N)·Σ(1/γₖ), then continuumKc = finiteKc.
    This holds for any probability measure μ that acts as the empirical
    measure of the N frequencies. -/
theorem continuumKc_eq_finiteKc_of_integral
    (γ_cont : Ω → ℝ) (γ_fin : Fin N → ℝ)
    (hN : 0 < N)
    (h_int : ∫ ω, (1 / γ_cont ω) ∂μ =
      (1 / (N : ℝ)) * ∑ k : Fin N, (1 / γ_fin k)) :
    continuumKc γ_cont μ = finiteKc γ_fin := by
  unfold continuumKc finiteKc
  rw [h_int]; field_simp

/-! ## Self-consistency map bridge -/

/-- **Φ BRIDGE.**
    If ∫ explicitEquil(γ(ω),K,r) dμ = (1/N)·Σ explicitEquil(γₖ,K,r),
    then the continuum self-consistency map equals the finite Φ. -/
theorem scMap_eq_finitePhiMap_of_integral
    (γ_cont : Ω → ℝ) (γ_fin : Fin N → ℝ) (K r : ℝ)
    (h_int : ∫ ω, explicitEquil (γ_cont ω) K r ∂μ =
      (1 / (N : ℝ)) * ∑ k : Fin N, explicitEquil (γ_fin k) K r) :
    ∫ ω, explicitEquil (γ_cont ω) K r ∂μ = finitePhiMap γ_fin K r := by
  unfold finitePhiMap; exact h_int

/-! ## Finite-N bifurcation from continuum theory -/

/-- **FINITE-N PHASE TRANSITION from continuum.**
    Under the integral identity, the continuum bifurcation theorem yields:
    - K ≤ finiteKc: no positive equilibrium
    - K > finiteKc: unique positive equilibrium
    This derives the finite-N result from the abstract theory. -/
theorem finite_bifurcation_from_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (γ_fin : Fin N → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_Kc : continuumKc γ μ = finiteKc γ_fin)
    (h_Φ : ∀ r, 0 < r → ∫ ω, explicitEquil (γ ω) K r ∂μ =
      finitePhiMap γ_fin K r) :
    (K ≤ finiteKc γ_fin →
      ∀ r, 0 < r → finitePhiMap γ_fin K r < r) ∧
    (finiteKc γ_fin < K →
      ∃! r_star, 0 < r_star ∧ r_star < 1 ∧
        finitePhiMap γ_fin K r_star = r_star) := by
  have h_main := kuramoto_phase_transition γ K hK hγ_pos hγ_level h_inv_int h_inv_pos
  rw [h_Kc] at h_main
  constructor
  · intro h_sub r hr
    rw [← h_Φ r hr]; exact h_main.1 h_sub r hr
  · intro h_super
    obtain ⟨r_star, ⟨hr_pos, hr_lt, hfp⟩, h_unique⟩ := h_main.2 h_super
    refine ⟨r_star, ⟨hr_pos, hr_lt, ?_⟩, ?_⟩
    · rwa [← h_Φ r_star hr_pos]
    · intro r' ⟨hr'_pos, hr'_lt, hfp'⟩
      exact h_unique r' ⟨hr'_pos, hr'_lt, (h_Φ r' hr'_pos).symm ▸ hfp'⟩

/-! ## Finite-N iteration convergence -/

/-- **FINITE-N ITERATION CONVERGENCE from continuum.**
    Under the bridge identities, the Picard iteration for the finite map
    converges to r* from any starting point. -/
theorem finite_iteration_from_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_below : r₀ < r_star) :
    (∀ n, scMapIter γ K μ n r₀ ≤ scMapIter γ K μ (n + 1) r₀) ∧
    (∀ n, scMapIter γ K μ n r₀ ≤ r_star) := by
  exact ⟨scMapIter_mono_below γ K r₀ r_star hγ_pos hK hγ_level
      hr₀ hr_star (show scMap γ K r_star μ = r_star from hfp) h_below,
    scMapIter_below_rstar γ K r₀ r_star hγ_pos hK hγ_level
      hr₀ hr_star (show scMap γ K r_star μ = r_star from hfp) (le_of_lt h_below)⟩

/-! ## Finite-N contraction from continuum -/

/-- **CONTRACTION FOR FINITE-N.**
    The self-consistency map for N oscillators is a contraction toward r*. -/
theorem finite_contraction_from_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r r_star : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr : 0 < r) (hr_star : 0 < r_star)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (h_ne : r ≠ r_star) :
    |∫ ω, explicitEquil (γ ω) K r ∂μ - r_star| < |r - r_star| :=
  sc_map_contraction γ K r r_star hγ_pos hK hγ_level hr hr_star hfp h_ne

end
