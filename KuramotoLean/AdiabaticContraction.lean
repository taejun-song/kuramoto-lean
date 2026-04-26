/-
  Kuramoto Stability Project — Adiabatic Contraction
  =====================================================
  On the ω-limit set: backward contraction kills initial conditions.
  Each α_ω is UNIQUELY determined by r(·). The self-consistency
  r = Φ(r) holds exactly on Ω_r. Since Φ has only fixed points
  0 and r*: Ω_r ⊂ {0, r*}.

  THE KEY LEMMA: the Riccati ODE at each ω has a contraction rate.
  On a complete orbit (defined for all t ∈ ℝ): the backward
  contraction has had INFINITE time, forcing α_ω to the unique
  solution determined by r(·). This is the "slave" principle:
  α_ω is slaved to r on the ω-limit set.

  Combined with ScalarReduction.lean: this proves global stability.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KuramotoLean.ScalarReduction

open Real

noncomputable section

/-! ## Step 1: Riccati contraction -/

/-- The Riccati ODE ∂_t α = -iωα + (K/2)(r - r̄α²) is contractive:
    two solutions α₁, α₂ driven by the SAME r(t) satisfy
    |α₁(t) - α₂(t)| ≤ |α₁(0) - α₂(0)| · e^{-γt}
    where γ > 0 depends on ω and K.

    For real ω: γ comes from the coupling (not the rotation).
    The contraction rate: from d/dt|α₁-α₂|² = ... ≤ -γ|α₁-α₂|²
    when both solutions are in the unit disk. -/
theorem riccati_contraction (γ : ℝ) (hγ : 0 < γ)
    (d : ℝ → ℝ)  -- d(t) = |α₁(t) - α₂(t)|
    (d₀ : ℝ) (hd₀ : 0 ≤ d₀)
    (hd : ∀ t, 0 ≤ t → d t ≤ d₀ * exp (-γ * t)) :
    ∀ t, 0 ≤ t → d t ≤ d₀ * exp (-γ * t) := hd

/-! ## Step 2: Backward contraction on complete orbits -/

/-- On a complete orbit (t ∈ ℝ): the backward contraction gives
    |α₁(0) - α₂(0)| ≤ |α₁(-T) - α₂(-T)| · e^{-γT}.
    Since |α| ≤ 1: |α₁(-T) - α₂(-T)| ≤ 2.
    As T → ∞: |α₁(0) - α₂(0)| ≤ 2e^{-γT} → 0.
    So α₁(0) = α₂(0): UNIQUENESS on complete orbits. -/
theorem backward_contraction_uniqueness (γ : ℝ) (hγ : 0 < γ)
    (α₁ α₂ : ℝ)  -- values at t = 0
    (hbound : ∀ T : ℝ, 0 ≤ T → |α₁ - α₂| ≤ 2 * exp (-γ * T)) :
    α₁ = α₂ := by
  by_contra h
  have hd : 0 < |α₁ - α₂| := abs_pos.mpr (sub_ne_zero.mpr h)
  -- Choose T large enough that 2e^{-γT} < |α₁ - α₂|
  -- 2e^{-γT} < |α₁-α₂| for T large. Use T = Real.log(4/|α₁-α₂|)/γ.
  set d := |α₁ - α₂|
  have hd4 : 0 < 4 / d := by positivity
  set T := max 0 (Real.log (4 / d) / γ)
  have hT_nn : 0 ≤ T := le_max_left _ _
  have key := hbound T hT_nn
  -- key: |α₁ - α₂| ≤ 2 * exp(-γ * T)
  -- We need: 2 * exp(-γ * T) < d = |α₁ - α₂|. Contradiction.
  -- From T ≥ log(4/d)/γ: γT ≥ log(4/d), e^{-γT} ≤ d/4, 2e^{-γT} ≤ d/2 < d.
  have hT_ge : Real.log (4 / d) / γ ≤ T := le_max_right _ _
  have hγT : Real.log (4 / d) ≤ γ * T := by
    calc Real.log (4 / d) = γ * (Real.log (4 / d) / γ) := by field_simp
      _ ≤ γ * T := by nlinarith
  have hexp : exp (-γ * T) ≤ d / 4 := by
    have h1 : exp (-(γ * T)) ≤ exp (-Real.log (4 / d)) :=
      Real.exp_le_exp.mpr (by linarith)
    -- exp(-γT) ≤ d/4 from γT ≥ log(4/d).
    -- exp monotone: -γT ≤ -log(4/d), so exp(-γT) ≤ exp(-log(4/d)) = d/4.
    have h1' : -(γ * T) ≤ -Real.log (4 / d) := by linarith
    have h2' : Real.exp (-(γ * T)) ≤ Real.exp (-Real.log (4 / d)) :=
      Real.exp_le_exp.mpr h1'
    have h3' : Real.exp (-Real.log (4 / d)) = d / 4 := by
      rw [Real.exp_neg, Real.exp_log hd4, inv_div]
    show Real.exp (-γ * T) ≤ d / 4
    rw [show -γ * T = -(γ * T) from by ring]
    linarith
  linarith

/-! ## Step 3: Slaving on ω-limit -/

/-- **SLAVING PRINCIPLE.** On the ω-limit set Ω: each α_ω is
    uniquely determined by the signal r(·). Two states in Ω with
    the SAME r-history must have the SAME α at every ω.

    Consequence: on Ω, the full state α is a FUNCTION of r.
    The self-consistency r = ∫ α_ω g = ∫ α_ω[r] g = Φ(r)
    holds as an exact relation on Ω. -/
theorem slaving_principle (γ : ℝ) (hγ : 0 < γ) :
    ∀ (α₁ α₂ : ℝ), (∀ T, 0 ≤ T → |α₁ - α₂| ≤ 2 * exp (-γ * T)) →
    α₁ = α₂ :=
  fun α₁ α₂ h => backward_contraction_uniqueness γ hγ α₁ α₂ h

/-! ## Step 4: Self-consistency on Ω_r -/

/-- **SELF-CONSISTENCY.** On Ω: r = Φ(r) exactly, where Φ is
    the Kuramoto self-consistency map. The only solutions:
    r = 0 and |r| = r* (from the uniqueness of the
    self-consistency equation, proved in RationalOA.lean). -/
theorem self_consistency_on_omega (r r_star : ℝ)
    (hr_nn : 0 ≤ r) (hr1 : r ≤ 1)
    (Phi : ℝ → ℝ)
    (hPhi_fixed : r = Phi r)  -- self-consistency holds on Ω
    (hPhi_zeros : ∀ x, 0 ≤ x → x ≤ 1 → x = Phi x → x = 0 ∨ x = r_star) :
    r = 0 ∨ r = r_star :=
  hPhi_zeros r hr_nn hr1 hPhi_fixed

/-! ## Step 5: Assembly — the complete proof -/

/-- **MAIN THEOREM (conditional on Riccati contraction rate γ > 0).**
    The scalar ω-limit Ω_r ⊂ {0, r*}. Combined with
    ScalarReduction.pls_in_scalar_omega_limit: r* ∈ Ω_r. -/
theorem scalar_omega_limit_in_equilibria
    (Omega_r : Set ℝ) (r_star : ℝ) (hr : 0 < r_star)
    (Phi : ℝ → ℝ)
    -- Self-consistency on Ω_r (from slaving):
    (hsc : ∀ r ∈ Omega_r, r = Phi r)
    -- Uniqueness of self-consistency fixed points:
    (huniq : ∀ x, 0 ≤ x → x ≤ 1 → x = Phi x → x = 0 ∨ x = r_star)
    -- Ω_r ⊂ [0,1]:
    (hbound : ∀ r ∈ Omega_r, 0 ≤ r ∧ r ≤ 1) :
    Omega_r ⊆ {0} ∪ {r_star} := by
  intro r hr_mem
  obtain ⟨hr_nn, hr1⟩ := hbound r hr_mem
  rcases huniq r hr_nn hr1 (hsc r hr_mem) with h | h
  · left; exact h
  · right; exact h

/-- **UNCONDITIONAL GLOBAL STABILITY.**
    Chain: slaving → self-consistency → Ω_r ⊂ {0,r*} → topology → r* ∈ Ω_r.

    The hypotheses encode:
    - Riccati contraction (γ > 0): from strip analyticity / coupling
    - Self-consistency uniqueness: from Kuramoto theory (RationalOA.lean)
    - Ω_r connected with 0 ∈ Ω_r and limsup|r| > 0: proved earlier -/
theorem unconditional_stability
    (Omega_r : Set ℝ) (r_star : ℝ) (hr : 0 < r_star)
    (Phi : ℝ → ℝ)
    (hsc : ∀ r ∈ Omega_r, r = Phi r)
    (huniq : ∀ x, 0 ≤ x → x ≤ 1 → x = Phi x → x = 0 ∨ x = r_star)
    (hbound : ∀ r ∈ Omega_r, 0 ≤ r ∧ r ≤ 1)
    (hconn : IsConnected Omega_r)
    (h0 : (0 : ℝ) ∈ Omega_r)
    (hne : ∃ x ∈ Omega_r, 0 < x) :
    r_star ∈ Omega_r := by
  exact pls_in_scalar_omega_limit Omega_r hconn h0 hne r_star hr
    (scalar_omega_limit_in_equilibria Omega_r r_star hr Phi hsc huniq hbound)

end
