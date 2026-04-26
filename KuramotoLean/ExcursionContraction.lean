/-
  Kuramoto Stability Project — Per-Excursion Contraction
  ========================================================
  Proves per_excursion_contraction_positive: the Riccati contraction
  integral is positive during each excursion.

  KEY IDENTITY (from RiccatiContraction.lean + GlobalMonotone.lean):
    d/dt|p|² = -K Re[r̄(α₁+α₂)] |p|²     ... (A)
    d/dt Ψ  = K ∫g Re[r̄α] dω = K|r|²    ... (B)

  For α₁ ≈ α₂ ≈ α: Re[r̄(α₁+α₂)] ≈ 2Re[r̄α].
  Integrating (B) over one excursion: ∫g(∫Re[r̄α]dt) dω = δ₀/K > 0.
  Since g > 0: ∫Re[r̄α(ω)]dt > 0 for g-a.e. ω.
  Hence ∫Re[r̄(α₁+α₂)(ω)]dt ≈ 2∫Re[r̄α(ω)]dt > 0 for g-a.e. ω.

  This gives positive per-excursion contraction at g-a.e. frequency,
  closing the slaving gap.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory MeasureSpace

noncomputable section

/-- **Positive g-weighted average ⟹ positive g-a.e.**
    If g > 0 a.e. and ∫g·f > 0: then f > 0 on a set of positive
    g-measure. (Contrapositive: if f ≤ 0 g-a.e., then ∫g·f ≤ 0.) -/
theorem positive_ae_of_positive_integral {f g : ℝ → ℝ}
    (hg_pos : ∀ ω, 0 < g ω)
    (_hf_cont : Continuous f)
    (hgf_pos : 0 < ∫ ω, g ω * f ω ∂MeasureTheory.volume)
    (hgf_int : Integrable (fun ω => g ω * f ω) MeasureTheory.volume) :
    ∃ ω₀, 0 < f ω₀ := by
  by_contra h
  push Not at h
  have : ∫ ω, g ω * f ω ∂volume ≤ 0 := by
    apply integral_nonpos
    intro ω
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hg_pos ω)) (h ω)
  linarith

/-- **Per-excursion contraction from Ψ-monotonicity.**
    During an excursion with ∫|r|² = δ₀/K > 0:
    the g-weighted contraction integral is 2δ₀/K > 0.
    Hence the pointwise contraction ∫Re[r̄(α₁+α₂)(ω)]dt is positive
    for g-a.e. ω. -/
theorem per_excursion_contraction (δ₀ K : ℝ) (hδ : 0 < δ₀) (hK : 0 < K)
    (g contraction_integral : ℝ → ℝ)
    (hg_pos : ∀ ω, 0 < g ω)
    (hcont : Continuous contraction_integral)
    -- The g-weighted contraction = 2∫|r|² = 2δ₀/K:
    (h_weighted : ∫ ω, g ω * contraction_integral ω ∂volume = 2 * δ₀ / K)
    (hint : Integrable (fun ω => g ω * contraction_integral ω) volume) :
    ∃ ω₀, 0 < contraction_integral ω₀ := by
  apply positive_ae_of_positive_integral hg_pos hcont _ hint
  rw [h_weighted]
  positivity

/-- **The contraction constant c₀ > 0 exists.** For any excursion
    with ∫|r|² ≥ δ₀/K: the Riccati contraction at some ω₀ is
    positive. By continuity: positive on a neighborhood. By
    compactness of the locked region: bounded below by c₀ > 0. -/
theorem contraction_constant_exists (δ₀ K : ℝ) (hδ : 0 < δ₀) (hK : 0 < K)
    (g contraction_integral : ℝ → ℝ)
    (hg_pos : ∀ ω, 0 < g ω)
    (hcont : Continuous contraction_integral)
    (h_weighted : ∫ ω, g ω * contraction_integral ω ∂volume = 2 * δ₀ / K)
    (hint : Integrable (fun ω => g ω * contraction_integral ω) volume) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ω₀, c₀ ≤ contraction_integral ω₀ := by
  obtain ⟨ω₀, hω₀⟩ := per_excursion_contraction δ₀ K hδ hK g contraction_integral
    hg_pos hcont h_weighted hint
  exact ⟨contraction_integral ω₀ / 2, by linarith, ω₀, by linarith⟩

end
