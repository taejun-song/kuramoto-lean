/-
  Kuramoto Stability — Continuum Pair Rigidity
  =============================================

  If ∫∫ pairIntegrand = 0 with pair ≥ 0 pointwise, then α = α* μ-a.e.
  This is the LaSalle characterization for the continuum OA flow:
  dV∞/dt = 0 implies α is at equilibrium.

  Uses Mathlib's integral_eq_zero_iff_of_nonneg to transfer pointwise
  non-negativity + vanishing integral to a.e. equality.

  0 sorry.
-/

import KuramotoLean.ContinuumLyapunov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Double integral rigidity.** If ∫∫ f = 0 with f ≥ 0 pointwise,
    and the inner/outer integrals are integrable, then for a.e. ω₁,
    f(ω₁,·) = 0 a.e. -/
theorem double_integral_rigidity
    (f : Ω → Ω → ℝ)
    (hf_nn : ∀ ω₁ ω₂, 0 ≤ f ω₁ ω₂)
    (h_inner_int : ∀ ω₁, Integrable (f ω₁) μ)
    (h_outer_int : Integrable (fun ω₁ => ∫ ω₂, f ω₁ ω₂ ∂μ) μ)
    (h_zero : ∫ ω₁, ∫ ω₂, f ω₁ ω₂ ∂μ ∂μ = 0) :
    ∀ᵐ ω₁ ∂μ, f ω₁ =ᵐ[μ] 0 := by
  have h_outer_nn : ∀ ω₁, 0 ≤ ∫ ω₂, f ω₁ ω₂ ∂μ :=
    fun ω₁ => integral_nonneg (fun ω₂ => hf_nn ω₁ ω₂)
  have h_outer_zero : (fun ω₁ => ∫ ω₂, f ω₁ ω₂ ∂μ) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg h_outer_nn h_outer_int).mp h_zero
  filter_upwards [h_outer_zero] with ω₁ h1
  exact (integral_eq_zero_iff_of_nonneg (hf_nn ω₁) (h_inner_int ω₁)).mp h1

/-- **Continuum pair rigidity.** If ∫∫ pairIntegrand = 0 with
    α, α* ∈ (0,1), then α = α* μ-a.e.

    This is the LaSalle characterization: dV∞/dt = 0 iff α = α*.
    Uses pair_eq_zero_iff: pair(ω₁,ω₂) = 0 → α(ω₁) = α*(ω₁). -/
theorem continuum_pair_rigidity [IsProbabilityMeasure μ]
    (α α_star : Ω → ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω) (_hα_star1 : ∀ ω, α_star ω < 1)
    (h_inner_int : ∀ ω₁, Integrable
      (fun ω₂ => pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂)) μ)
    (h_outer_int : Integrable
      (fun ω₁ => ∫ ω₂, pairIntegrand (α ω₁) (α_star ω₁)
        (α ω₂) (α_star ω₂) ∂μ) μ)
    (h_zero : ∫ ω₁, ∫ ω₂,
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ = 0) :
    ∀ᵐ ω ∂μ, α ω = α_star ω := by
  have h_nn : ∀ ω₁ ω₂, 0 ≤
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) :=
    fun ω₁ ω₂ => pairIntegrand_nonneg _ _ _ _
      (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)
  have h_ae := double_integral_rigidity
    (fun ω₁ ω₂ => pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂))
    h_nn h_inner_int h_outer_int h_zero
  filter_upwards [h_ae] with ω₁ h1
  -- h1 : pair(ω₁, ·) = 0 a.e.
  -- Extract: for a.e. ω₂, pair(ω₁,ω₂) = 0 → α(ω₁) = α*(ω₁)
  have h_const : ∀ᵐ ω₂ ∂μ, α ω₁ = α_star ω₁ := by
    filter_upwards [h1] with ω₂ hω₂
    have := (pair_eq_zero_iff (α ω₁) (α ω₂) (α_star ω₁) (α_star ω₂)
      (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)).mp
    exact (this hω₂).1
  -- ae constant → constant (μ is a probability measure, hence ae.NeBot)
  exact h_const.exists.elim (fun _ h => h)

/-! ## Continuum strict Lyapunov: V∞ > 0 → ∫∫ pair > 0 -/

/-- **Continuum strict Lyapunov.** If V∞ = ∫(α-α*)² > 0, then ∫∫ pair > 0.
    Proof: ∫∫ pair ≥ 0 (nonneg). If = 0, rigidity gives α = α* a.e.,
    so ∫(α-α*)² = 0, contradicting V∞ > 0. -/
theorem continuum_strict_lyapunov [IsProbabilityMeasure μ]
    (α α_star : Ω → ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω) (hα_star1 : ∀ ω, α_star ω < 1)
    (h_inner_int : ∀ ω₁, Integrable
      (fun ω₂ => pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂)) μ)
    (h_outer_int : Integrable
      (fun ω₁ => ∫ ω₂, pairIntegrand (α ω₁) (α_star ω₁)
        (α ω₂) (α_star ω₂) ∂μ) μ)
    (hp2_int : Integrable (fun ω => (α ω - α_star ω) ^ 2) μ)
    (hV_pos : 0 < ∫ ω, (α ω - α_star ω) ^ 2 ∂μ) :
    0 < ∫ ω₁, ∫ ω₂,
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ := by
  by_contra h_not
  push_neg at h_not
  have h_nn : 0 ≤ ∫ ω₁, ∫ ω₂,
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ :=
    integral_nonneg fun ω₁ => integral_nonneg fun ω₂ =>
      pairIntegrand_nonneg _ _ _ _ (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)
  have h_zero : ∫ ω₁, ∫ ω₂,
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ = 0 :=
    le_antisymm h_not h_nn
  have h_ae := continuum_pair_rigidity α α_star hα hα1 hα_star hα_star1
    h_inner_int h_outer_int h_zero
  have h_sq_ae : (fun ω => (α ω - α_star ω) ^ 2) =ᵐ[μ] 0 := by
    filter_upwards [h_ae] with ω hω; simp [hω]
  have h_sq_zero := (integral_eq_zero_iff_of_nonneg
    (fun ω => sq_nonneg _) hp2_int).mpr h_sq_ae
  linarith

end
