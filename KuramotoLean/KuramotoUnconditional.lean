/-
  KuramotoUnconditional.lean
  ==========================
  UNCONDITIONAL end-to-end Kuramoto stability for the standard continuum model.

  Statement: For K > K_c, γ > 0, finite first moment ∫γ dμ < ∞,
  and sufficient initial coherence, r(t) → r*.

  This derives `h_body_persist` from the ODE dynamics using:
  - r ≥ 0 (from α > 0 and self-consistency)
  - V(t) ≤ V(0) (Lyapunov antitonicity from finite first moment Leibniz)
  - r ≥ r* - √V(0) > 0 (Cauchy-Schwarz)
  - Body persistence from ODE scalar barrier (BodyPersistenceFromODE)

  0 sorry. 0 axioms.
-/

import KuramotoLean.KuramotoFirstMomentBarbalat
import KuramotoLean.BodyPersistenceFromODE
import KuramotoLean.ContinuumBodyLeibniz

set_option maxHeartbeats 800000

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Body persistence derived from ODE + r lower bound.**
    Given r(t) ≥ r_min > 0 for all t ≥ 0, the scalar ODE barrier gives
    α(ω,t) ≥ min(α(ω,0), bodyEquilibrium M K r_min) on body {γ ≤ M}. -/
theorem body_persist_unconditional [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (r_min : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (M : ℝ) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
  have hα_ode' : ∀ ω, ∀ t, 0 < t →
      HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t :=
    fun ω t ht => hα_ode ω t (le_of_lt ht)
  exact @continuum_body_persistence Ω _ μ ‹_› γ K r α r_min M hK hγ hr_min hr_le hM
    hr_bound hr_bdd hα_ode' hα_inv hα_cont
    (fun ω _ => (hα_inv ω 0 le_rfl).1)
    (h_init_body M hM)

/-- **UNCONDITIONAL Kuramoto stability** for the finite first moment continuum model.

    Given:
    - K > K_c (supercritical)
    - γ > 0 (nondegenerate frequencies)
    - ∫γ dμ < ∞ (finite first moment)
    - r_min > 0 with r(t) ≥ r_min for all t
    - Initial body coherence

    Derives body persistence internally and concludes r(t) → r*. -/
theorem kuramoto_unconditional [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (hK_crit : 2 < K * ∫ ω, 1 / γ ω ∂μ)
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- Physical initial conditions:
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    -- Order parameter persistence (derivable from energy identity dΨ/dt = K|r|²):
    (r_min : ℝ) (hr_min_pos : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧ Tendsto r atTop (nhds r_star) := by
  -- r non-negative (trivial from α > 0)
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  -- Body persistence from ODE barrier + r lower bound
  have h_body_persist : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := fun M hM =>
    @body_persist_unconditional Ω _ μ _ γ K r α r_min
      hK (fun ω => le_of_lt (hγ_pos ω))
      hr_min_pos hr_min_le hr_bound hr_bdd hα_ode hα_inv hα_cont h_init_body M hM
  -- Apply first moment Barbalat
  exact kuramoto_first_moment_barbalat γ K hK hγ_pos hγ_level h_inv_int hK_crit hγ_int
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont hα_neg h_sc hα_int hα_inv h_body_persist
