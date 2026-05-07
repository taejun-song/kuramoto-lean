/-
  VBodyContinuous.lean
  ====================
  Proves that the body Lyapunov functional
    V_body(M, t) = ∫_{γ ≤ M} (α(ω,t) - α*(ω))² dμ(ω)
  is ContinuousOn on Ici 0, via dominated convergence.

  Proof: `continuousOn_of_dominated` with:
  - F(t, ω) = (α(ω,t) - α*(ω))²
  - bound = 4 (since α,α* ∈ (0,1) → |α-α*| < 2)
  - pointwise continuity from hα_cont

  0 sorry. 0 axioms.
-/

import KuramotoLean.BodyGronwallBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## V_body is ContinuousOn on [0,∞) -/

/-- The body Lyapunov functional V_body(M,t) = ∫_{γ ≤ M} (α-α*)² dμ is
    ContinuousOn on Ici 0.

    Proof via `continuousOn_of_dominated` applied to μ.restrict body:
    - Pointwise: t ↦ (α(ω,t) - α*(ω))² is ContinuousOn Ici 0 for each ω
      (from hα_cont and continuity of squaring).
    - Bound: |(α-α*)²| ≤ 4 since α,α* ∈ (0,1) gives |α-α*| < 2.
    - Bound 4 is integrable on the finite restricted measure. -/
theorem V_body_continuousOn [IsFiniteMeasure μ]
    (γ : Ω → ℝ) (M : ℝ)
    (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    ContinuousOn (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0) := by
  set body := {ω | γ ω ≤ M}
  haveI : IsFiniteMeasure (μ.restrict body) := isFiniteMeasureRestrict μ body
  -- ∫ ω in body, f ∂μ = ∫ ω, f ∂(μ.restrict body) by definition of set integral
  show ContinuousOn (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ.restrict body) (Ici 0)
  apply continuousOn_of_dominated (μ := μ.restrict body) (bound := fun _ => 4)
  · intro t _
    exact ((hα_sq_int t).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  · intro t ht
    apply (ae_restrict_mem hγ_level).mono
    intro ω _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := (hα_inv ω t (mem_Ici.mp ht)).1
    have hl := (hα_inv ω t (mem_Ici.mp ht)).2
    have hps := hα_star_pos ω; have hls := hα_star_lt ω
    nlinarith [sq_nonneg (α ω t - α_star ω)]
  · exact integrable_const 4
  · apply (ae_restrict_mem hγ_level).mono
    intro ω _
    exact ((hα_cont ω).sub continuousOn_const).pow 2

/-- V_body is ContinuousOn on Ici 0 when μ is a probability measure. -/
theorem V_body_continuousOn_prob [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (M : ℝ)
    (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    ContinuousOn (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0) :=
  V_body_continuousOn γ M hγ_level α α_star hα_cont hα_inv hα_star_pos hα_star_lt hα_sq_int

end
