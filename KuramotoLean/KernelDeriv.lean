/-
  Kuramoto Stability Project — Kernel Derivative
  =================================================
  Algebraic identities for the OA velocity field.
-/

import KuramotoLean.Defs

open Complex MeasureTheory Real

noncomputable section

/-- Key algebraic fact: Re(ᾱ · (-iωα)) = 0. Rotation preserves |α|². -/
lemma rotation_drops_out (α : ℂ) (ω : ℝ) :
    (starRingEnd ℂ α * (-Complex.I * (ω : ℂ) * α)).re = 0 := by
  simp [Complex.I]
  ring

-- deriv_normSq_eq and deriv_normSq_diff removed:
-- they used HasDerivAt (ODE solutions) which requires Complex.conjCLE chain rule.
-- The stability proof uses OADynamics.lean (normSq_deriv_eq) instead.

end
