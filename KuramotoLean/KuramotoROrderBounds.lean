/-
  KuramotoROrderBounds.lean
  ==========================
  Standalone lemmas proving that the Kuramoto order parameter r(t) stays in
  (0, 1) for t > 0, derivable from self-consistency + OA trajectory bounds.

  These lemmas allow callers to drop `hr_bdd : ∀ t, |r t| ≤ 1` from theorem
  statements when only t > 0 behavior is needed (e.g. body Leibniz at t₀ > 0).

  Main results:
  - `r_nonneg_from_sc`:   ∀ t ≥ 0, 0 ≤ r t
  - `r_le_one_from_sc`:   ∀ t ≥ 0, r t ≤ 1
  - `r_abs_le_one_from_sc`: ∀ t ≥ 0, |r t| ≤ 1

  0 sorry. 0 axioms.
-/

import KuramotoLean.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The order parameter is nonneg for t ≥ 0: r t = ∫ α ω t ∂μ ≥ 0
    since α ω t > 0 for all ω. -/
lemma r_nonneg_from_sc [IsProbabilityMeasure μ]
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) :
    ∀ t ≥ 0, 0 ≤ r t := by
  intro t ht
  rw [h_sc t ht]
  exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)

/-- The order parameter is at most 1 for t ≥ 0: r t = ∫ α ω t ∂μ ≤ 1
    since α ω t < 1 for all ω and μ is a probability measure. -/
lemma r_le_one_from_sc [IsProbabilityMeasure μ]
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) :
    ∀ t ≥ 0, r t ≤ 1 := by
  intro t ht
  rw [h_sc t ht]
  have h : ∫ ω, α ω t ∂μ ≤ ∫ (ω : Ω), (1 : ℝ) ∂μ :=
    integral_mono (hα_int t) (integrable_const 1) (fun ω => le_of_lt (hα_inv ω t ht).2)
  simp at h
  linarith

/-- The absolute value of the order parameter is at most 1 for t ≥ 0:
    |r t| ≤ 1, derived from r t ∈ [0, 1]. -/
lemma r_abs_le_one_from_sc [IsProbabilityMeasure μ]
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) :
    ∀ t ≥ 0, |r t| ≤ 1 :=
  fun t ht => abs_le.mpr ⟨by linarith [r_nonneg_from_sc r α h_sc hα_inv t ht],
                           r_le_one_from_sc r α h_sc hα_int hα_inv t ht⟩

end
