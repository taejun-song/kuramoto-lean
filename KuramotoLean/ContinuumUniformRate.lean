/-
  Kuramoto Stability — Continuum Uniform Rate
  =============================================

  Extends the n-pole uniform rate (UniformRate.lean) to the continuum.

  Part 1: For a probability measure μ:
    ∫∫(p(ω₁)² + p(ω₂)²) dμ dμ = 2·∫p² dμ

  Part 2: Pointwise coercivity + integral_mono gives:
    ∫∫ pairIntegrand dμ dμ ≥ 2δδ* · V∞

  Part 3: Convergence from uniform rate via geometric decay.

  0 sorry.
-/

import KuramotoLean.PairCoercivity
import KuramotoLean.ContinuumBarbalat
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Real Set

noncomputable section

/-! ## Part 1: Double integral identity for probability measures -/

private theorem prob_real_univ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : μ.real univ = 1 := by
  simp [Measure.real, measure_univ]

private theorem prob_integral_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ _ : Ω, c ∂μ = c := by
  rw [integral_const, prob_real_univ μ, one_smul]

/-- **Double integral identity.** For a probability measure μ:
    ∫∫(p(ω₁)² + p(ω₂)²) dμ dμ = 2·∫p² dμ. -/
theorem double_integral_sq_prob {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ω → ℝ) (hp2 : Integrable (fun ω => p ω ^ 2) μ) :
    ∫ ω₁, ∫ ω₂, (p ω₁ ^ 2 + p ω₂ ^ 2) ∂μ ∂μ =
    2 * ∫ ω, p ω ^ 2 ∂μ := by
  have h_inner : ∀ ω₁, ∫ ω₂, (p ω₁ ^ 2 + p ω₂ ^ 2) ∂μ =
      p ω₁ ^ 2 + ∫ ω, p ω ^ 2 ∂μ := by
    intro ω₁
    rw [integral_add (integrable_const _) hp2,
        prob_integral_const μ]
  simp_rw [h_inner]
  rw [integral_add hp2 (integrable_const _),
      prob_integral_const μ]
  ring

/-! ## Part 2: Continuum coercive integral bound -/

/-- Pointwise: pair ≥ δδ*(p₁²+p₂²) under locked-amplitude conditions. -/
theorem pair_ge_delta_sq {α₁ α₂ αs₁ αs₂ δ ds : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα₁_lt : α₁ < 1) (hα₂_lt : α₂ < 1)
    (hαs₁ : 0 < αs₁) (hαs₂ : 0 < αs₂)
    (hδ : 0 < δ) (hα₁_lb : δ ≤ α₁) (hα₂_lb : δ ≤ α₂)
    (hds₁ : ds ≤ αs₁) (hds₂ : ds ≤ αs₂) :
    δ * ds * ((α₁ - αs₁) ^ 2 + (α₂ - αs₂) ^ 2) ≤
    pairIntegrand α₁ αs₁ α₂ αs₂ := by
  have h_pc := pair_coercive α₁ α₂ αs₁ αs₂ δ
    hα₁ hα₂ hα₁_lt hα₂_lt hαs₁ hαs₂ hδ hα₁_lb hα₂_lb
  have hmin : ds ≤ min αs₁ αs₂ := le_min hds₁ hds₂
  have hsum_nn : 0 ≤ (α₁ - αs₁) ^ 2 + (α₂ - αs₂) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (le_of_lt hδ)) hsum_nn]

/-- **Continuum coercive integral bound.** For a probability measure μ
    with locked amplitudes:
      ∫∫ pairIntegrand dμ dμ ≥ 2δδ* · ∫(α-α*)² dμ.

    Requires integrability hypotheses for integral_mono. -/
theorem continuum_coercive_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α αs : Ω → ℝ) (δ ds : ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hαs : ∀ ω, 0 < αs ω)
    (hδ : 0 < δ) (_hds : 0 < ds)
    (hα_lb : ∀ ω, δ ≤ α ω) (hαs_lb : ∀ ω, ds ≤ αs ω)
    (hp2 : Integrable (fun ω => (α ω - αs ω) ^ 2) μ)
    (h_pair_int : ∀ ω₁, Integrable
      (fun ω₂ => pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂)) μ)
    (h_bound_int : ∀ ω₁, Integrable
      (fun ω₂ => δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
        (α ω₂ - αs ω₂) ^ 2)) μ)
    (h_outer_pair : Integrable
      (fun ω₁ => ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁)
        (α ω₂) (αs ω₂) ∂μ) μ)
    (h_outer_bound : Integrable
      (fun ω₁ => δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
        ∫ ω, (α ω - αs ω) ^ 2 ∂μ)) μ) :
    2 * (δ * ds) * ∫ ω, (α ω - αs ω) ^ 2 ∂μ ≤
    ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁)
      (α ω₂) (αs ω₂) ∂μ ∂μ := by
  have h_inner_mono : ∀ ω₁,
      δ * ds * ((α ω₁ - αs ω₁) ^ 2 + ∫ ω, (α ω - αs ω) ^ 2 ∂μ) ≤
      ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ := by
    intro ω₁
    have h_pw : ∀ ω₂,
        δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ≤
        pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) :=
      fun ω₂ => pair_ge_delta_sq (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂)
        (hαs ω₁) (hαs ω₂) hδ (hα_lb ω₁) (hα_lb ω₂) (hαs_lb ω₁) (hαs_lb ω₂)
    calc δ * ds * ((α ω₁ - αs ω₁) ^ 2 + ∫ ω, (α ω - αs ω) ^ 2 ∂μ)
        = ∫ ω₂, δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
            (α ω₂ - αs ω₂) ^ 2) ∂μ := by
          conv_lhs =>
            rw [show δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
                ∫ ω, (α ω - αs ω) ^ 2 ∂μ) =
                δ * ds * (α ω₁ - αs ω₁) ^ 2 +
                δ * ds * ∫ ω, (α ω - αs ω) ^ 2 ∂μ from by ring]
          conv_rhs =>
            arg 2; ext ω₂
            rw [show δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) =
                δ * ds * (α ω₁ - αs ω₁) ^ 2 +
                δ * ds * (α ω₂ - αs ω₂) ^ 2 from by ring]
          rw [integral_add (integrable_const _) (hp2.const_mul _)]
          rw [prob_integral_const μ, integral_const_mul]
      _ ≤ ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ :=
          integral_mono (h_bound_int ω₁) (h_pair_int ω₁) h_pw
  have h_lhs : 2 * (δ * ds) * ∫ ω, (α ω - αs ω) ^ 2 ∂μ =
      ∫ ω₁, δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
        ∫ ω, (α ω - αs ω) ^ 2 ∂μ) ∂μ := by
    conv_rhs =>
      arg 2; ext ω₁
      rw [show δ * ds * ((α ω₁ - αs ω₁) ^ 2 +
          ∫ ω, (α ω - αs ω) ^ 2 ∂μ) =
          δ * ds * (α ω₁ - αs ω₁) ^ 2 +
          δ * ds * ∫ ω, (α ω - αs ω) ^ 2 ∂μ from by ring]
    rw [integral_add (hp2.const_mul _) (integrable_const _)]
    rw [integral_const_mul, prob_integral_const μ]
    ring
  rw [h_lhs]
  exact integral_mono h_outer_bound h_outer_pair h_inner_mono

/-! ## Part 3: Convergence from uniform rate -/

/-- **Continuum uniform rate convergence.**
    V antitone + V ≥ 0 + geometric drops → V → 0.
    Rate parameter = K·δ·δ* (same as n-pole, independent of n). -/
theorem continuum_rate_convergence
    (V : ℝ → ℝ) (rate : ℝ) (hrate : 0 < rate)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧
      V (t + 1) ≤ exp (-rate) * V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → V t < ε :=
  continuous_barbalat_general V (exp (-rate)) 1
    hV_nn hV_anti (le_of_lt (exp_pos _))
    (exp_lt_one_iff.mpr (by linarith)) one_pos hdrops

/-- **Continuum Lyapunov → 0 at uniform rate.**
    Corollary: Filter.Tendsto form. -/
theorem continuum_V_tendsto_zero
    (V : ℝ → ℝ) (rate : ℝ) (hrate : 0 < rate)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧
      V (t + 1) ≤ exp (-rate) * V t) :
    Filter.Tendsto V Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuum_rate_convergence V rate hrate
    hV_nn hV_anti hdrops ε hε
  exact ⟨T, fun s hs => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (hV_nn s)]
    exact hT s hs⟩

/-! ## Part 4: Continuum Jensen inequality (variance bound)

For a probability measure: (∫f dμ)² ≤ ∫f² dμ.
Proof: 0 ≤ Var(f) = E[f²] - E[f]² gives E[f]² ≤ E[f²].
The variance is computed by expanding ∫(f - E[f])² ≥ 0. -/

/-- **Continuum Jensen/Cauchy-Schwarz.**
    (∫f dμ)² ≤ ∫f² dμ for probability measures.
    This is the continuum version of order_parameter_sq_le_l2. -/
theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  set m := ∫ ω, f ω ∂μ
  suffices h : 0 ≤ ∫ ω, f ω ^ 2 ∂μ - m ^ 2 by linarith
  have h_var : ∫ ω, (f ω - m) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - m ^ 2 := by
    have h_int_sub : ∫ ω, (f ω - m) ^ 2 ∂μ =
        ∫ ω, (f ω ^ 2 - 2 * m * f ω + m ^ 2) ∂μ := by
      congr 1; ext ω; ring
    rw [h_int_sub]
    have h1 : ∫ ω, (f ω ^ 2 - 2 * m * f ω + m ^ 2) ∂μ =
        ∫ ω, (f ω ^ 2 - 2 * m * f ω) ∂μ + ∫ ω, (m ^ 2 : ℝ) ∂μ := by
      have : (fun ω => f ω ^ 2 - 2 * m * f ω + m ^ 2) =
          fun ω => (f ω ^ 2 - 2 * m * f ω) + m ^ 2 := by ext; ring
      rw [this]; exact integral_add (hf2.sub (hf.const_mul _)) (integrable_const _)
    have h2 : ∫ ω, (f ω ^ 2 - 2 * m * f ω) ∂μ =
        ∫ ω, f ω ^ 2 ∂μ - 2 * m * ∫ ω, f ω ∂μ := by
      rw [integral_sub hf2 (hf.const_mul _), integral_const_mul]
    rw [h1, h2, prob_integral_const μ]; ring
  rw [← h_var]
  exact integral_nonneg (fun ω => sq_nonneg _)

/-- **Continuum order parameter bound.**
    (r - r*)² ≤ V∞ where r = ∫α dμ, r* = ∫α* dμ, V∞ = ∫(α-α*)² dμ. -/
theorem continuum_order_parameter_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ω → ℝ)
    (hf : Integrable p μ) (hf2 : Integrable (fun ω => p ω ^ 2) μ) :
    (∫ ω, p ω ∂μ) ^ 2 ≤ ∫ ω, p ω ^ 2 ∂μ :=
  sq_integral_le_integral_sq μ p hf hf2

end
