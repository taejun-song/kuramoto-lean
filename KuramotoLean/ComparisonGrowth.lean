/-
  Kuramoto Stability — Comparison Growth Principle
  ==================================================

  Dual of comparison_decay (GronwallBridge.lean):
  dW/dt ≥ μW ⟹ W(t) ≥ W₀·exp(μt).

  Used with instability_growth_rate to show W = Σ c_k v_k α_k
  grows exponentially near the incoherent state.

  0 sorry target.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Real Set Filter

noncomputable section

/-- **Comparison growth principle.**
    If W'(t) ≥ μ·W(t) on (0,∞), then W(t) ≥ W(0)·exp(μt) for t ≥ 0.

    Proof: U(t) = W(t)·exp(-μt) has U'(t) = (W'-μW)·exp(-μt) ≥ 0,
    so U is monotone by monotoneOn_of_deriv_nonneg. -/
theorem comparison_growth (W : ℝ → ℝ) (W' : ℝ → ℝ) (μ : ℝ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_hasderiv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t → μ * W t ≤ W' t) :
    ∀ t, 0 ≤ t → W 0 * exp (μ * t) ≤ W t := by
  intro t ht
  suffices h : W 0 * exp (-μ * 0) ≤ W t * exp (-μ * t) by
    simp only [mul_zero, exp_zero, mul_one] at h
    have : W t = W t * exp (-μ * t) * exp (μ * t) := by
      rw [mul_assoc, ← exp_add]; simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h (exp_nonneg _)
  set U : ℝ → ℝ := fun s => W s * exp (-μ * s)
  have hexp_deriv : ∀ s, HasDerivAt (fun u => exp (-μ * u)) (-μ * exp (-μ * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u => -μ * u) (-μ * 1) s :=
      (hasDerivAt_id s).const_mul (-μ)
    rw [mul_one] at h1
    convert h1.exp using 1; ring
  have hexp_cont : Continuous (fun s => exp (-μ * s)) :=
    continuous_exp.comp (continuous_const.mul continuous_id)
  have hU_cont : ContinuousOn U (Ici 0) :=
    hW_cont.mul hexp_cont.continuousOn
  have hU_nonneg : ∀ s ∈ Ioi (0:ℝ), 0 ≤ deriv U s := by
    intro s hs
    have hs_pos := mem_Ioi.mp hs
    have hd : HasDerivAt U (W' s * exp (-μ * s) + W s * (-μ * exp (-μ * s))) s :=
      (hW_hasderiv s hs_pos).mul (hexp_deriv s)
    rw [hd.deriv]
    have : W' s * exp (-μ * s) + W s * (-μ * exp (-μ * s)) =
        (W' s - μ * W s) * exp (-μ * s) := by ring
    rw [this]
    exact mul_nonneg (by linarith [hW_bound s hs_pos]) (le_of_lt (exp_pos _))
  have hU_diff : DifferentiableOn ℝ U (Ioi 0) := by
    intro s hs
    exact ((hW_hasderiv s (mem_Ioi.mp hs)).mul
      (hexp_deriv s)).differentiableAt.differentiableWithinAt
  have hU_diff_int : DifferentiableOn ℝ U (interior (Ici 0)) := by
    rw [interior_Ici]; exact hU_diff
  have hU_nonneg_int : ∀ s ∈ interior (Ici (0:ℝ)), 0 ≤ deriv U s := by
    rw [interior_Ici]; exact hU_nonneg
  exact monotoneOn_of_deriv_nonneg (convex_Ici 0) hU_cont hU_diff_int
    hU_nonneg_int (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr ht) ht

/-- **Exponential growth escape.**
    W(0) > 0 + comparison growth → W eventually exceeds any level.
    Uses Tendsto exp atTop atTop. -/
theorem comparison_growth_escape (W : ℝ → ℝ) (W' : ℝ → ℝ) (μ : ℝ)
    (hμ : 0 < μ)
    (hW_cont : ContinuousOn W (Ici 0))
    (hW_hasderiv : ∀ t, 0 < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, 0 < t → μ * W t ≤ W' t)
    (hW0 : 0 < W 0) (η : ℝ) :
    ∃ T, 0 ≤ T ∧ η ≤ W T := by
  by_cases hη : η ≤ 0
  · exact ⟨0, le_refl 0, le_trans hη (le_of_lt hW0)⟩
  · push_neg at hη
    -- exp(μ·t) → ∞ as t → ∞, so W(0)·exp(μ·t) exceeds η/W(0) eventually
    have hexp_tend : Tendsto (fun t => exp (μ * t)) atTop atTop := by
      exact tendsto_exp_atTop.comp
        (tendsto_atTop_atTop_of_monotone (fun a b h => by nlinarith)
          (fun b => ⟨b / μ, by field_simp; linarith⟩))
    have hprod_tend : Tendsto (fun t => W 0 * exp (μ * t)) atTop atTop := by
      have := Tendsto.atTop_mul_const hW0 hexp_tend
      simp only [mul_comm] at this
      exact this
    obtain ⟨T, hT⟩ := (hprod_tend.eventually (eventually_ge_atTop η)).exists
    refine ⟨max 0 T, le_max_left _ _, ?_⟩
    have hgrowth := comparison_growth W W' μ hW_cont hW_hasderiv hW_bound
      (max 0 T) (le_max_left _ _)
    calc η ≤ W 0 * exp (μ * T) := hT
      _ ≤ W 0 * exp (μ * max 0 T) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hW0)
        exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hμ))
      _ ≤ W (max 0 T) := hgrowth

end
