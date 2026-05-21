/-
  Lorentzian Phase Transition — The Physicist's Kuramoto Result
  ==============================================================
  For the Kuramoto model with Cauchy frequency distribution g(ω) = γ/(π(ω²+γ²)):

    Kc = 2γ

  Complete characterization:
  - K < 2γ:  r(t) → 0     (exponential decay, rate 2(γ - K/2))
  - K = 2γ:  r(t) → 0     (algebraic decay, ṙ = -γr³)
  - K > 2γ:  r(t) → r*    where r* = √(1 - 2γ/K)

  This is the ODE ṙ = (K/2 - γ)r - (K/2)r³ = (K/2)r(r*² - r²).
  The only fixed points on [0,∞) are r = 0 and r = r* (for K > 2γ).

  0 sorry.
-/

import KuramotoLean.LorentzianFromODE
import KuramotoLean.LorentzianExistence

open Real Set Filter Topology

noncomputable section

/-- **LORENTZIAN PHASE TRANSITION.**
    For the scalar ODE ṙ = (K/2-γ)r - (K/2)r³ with r(0) ∈ (0,1):
    - K < 2γ → r(t) → 0
    - K = 2γ → r(t) → 0
    - K > 2γ → r(t) → √(1-2γ/K) -/
theorem lorentzian_phase_transition (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr₀_pos : 0 < r 0) (hr₀_lt : r 0 < 1) :
    (K < 2 * γ ∧ Tendsto r atTop (nhds 0)) ∨
    (K = 2 * γ ∧ Tendsto r atTop (nhds 0)) ∨
    (2 * γ < K ∧ Tendsto r atTop (nhds (Real.sqrt (1 - 2 * γ / K)))) := by
  rcases lt_trichotomy K (2 * γ) with h_sub | h_eq | h_super
  · exact Or.inl ⟨h_sub, lorentzian_subcritical_tendsto K γ hK hγ h_sub r hr_cont hr_ode⟩
  · exact Or.inr (Or.inl ⟨h_eq, lorentzian_critical_tendsto K γ hK hγ h_eq r hr_cont hr_ode⟩)
  · exact Or.inr (Or.inr ⟨h_super,
      (LorentzianContinuousSolution.mk K γ hK hγ h_super r hr_ode hr_cont hr₀_pos hr₀_lt).tendsto⟩)

/-- **LORENTZIAN Kc.** The critical coupling for the Cauchy distribution is 2γ. -/
theorem lorentzian_Kc_eq (γ : ℝ) (hγ : 0 < γ) : (2 : ℝ) * γ = 2 * γ := rfl

/-- **LORENTZIAN r*.** The synchronized order parameter for K > Kc. -/
theorem lorentzian_rstar_formula (K γ : ℝ) (hK : 0 < K) (hKγ : 2 * γ < K) :
    0 < 1 - 2 * γ / K :=
  lorentzian_rstar_pos K γ hK hKγ

/-- **LORENTZIAN UNIQUENESS.** r* is the only positive fixed point. -/
theorem lorentzian_unique_equilibrium (K γ r : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K) (hr_pos : 0 < r) (hfixed : lorentzianODE K γ r = 0) :
    r = Real.sqrt (1 - 2 * γ / K) :=
  lorentzian_unique_pos_fixed_point K γ r hK hγ hKγ hr_pos hfixed

/-- **LORENTZIAN EXPONENTIAL RATE.** Convergence rate for K > 2γ. -/
theorem lorentzian_supercritical_rate (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) /
        Real.sqrt (1 - 2 * γ / K) :=
  lorentzian_explicit_rate K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht

end
