/-
  Kuramoto Stability — Grounded Convergence from Parameters
  ==========================================================

  Given NPoleBarrierData + the self-consistency fixed point r*,
  assembles InitialConditionData and proves r(t) → r*.

  The fixed point r* comes from sc_fixed_point_exists (K > K_c → ∃ r*).
  This file connects it to the convergence chain.

  0 sorry target.
-/

import KuramotoLean.SelfConsistencyFixedPoint
import KuramotoLean.EndToEndConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Connecting componentEquil to nPoleODE -/

theorem fixed_point_nPoleODE (γ c : Fin n → ℝ) (K r_star : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr_star : 0 < r_star)
    (h_sc : ∑ k, c k * explicitEquil (γ k) K r_star = r_star) (k : Fin n) :
    nPoleODE γ c K (fun j => explicitEquil (γ j) K r_star) k = 0 := by
  rw [← componentEquil_eq_nPoleODE γ c K
    (fun j => explicitEquil (γ j) K r_star) k r_star h_sc.symm]
  exact explicitEquil_solves (γ k) K r_star (hγ k) hK hr_star

/-! ## Grounded convergence: given the fixed point, build convergence -/

theorem grounded_convergence (D : NPoleBarrierData n) (hn : 0 < n)
    (hc_sum : ∑ k, D.c k = 1)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (hα_init_lt_one : ∀ k, D.α 0 k < 1)
    (γ_max : ℝ) (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (r_star : ℝ) (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (h_sc : ∑ k, D.c k * explicitEquil (D.γ k) D.K r_star = r_star)
    (δ_star : ℝ) (hδ_star_pos : 0 < δ_star)
    (hδ_star : ∀ k, δ_star ≤ explicitEquil (D.γ k) D.K r_star)
    (hα_init_small : ∀ k, D.α 0 k < 2 * explicitEquil (D.γ k) D.K r_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, D.c k * D.α t k - r_star| < ε := by
  set α_star := fun k => explicitEquil (D.γ k) D.K r_star
  have h_nPoleODE : ∀ k, nPoleODE D.γ D.c D.K α_star k = 0 :=
    fixed_point_nPoleODE D.γ D.c D.K r_star D.hγ D.hK hr_pos h_sc
  exact initial_condition_r_convergence
    { D with
      hn := hn
      α_star := α_star
      γ_max := γ_max
      δ_star := δ_star
      hα_star_pos := fun k => explicitEquil_pos (D.γ k) D.K r_star (D.hγ k) D.hK hr_pos
      hα_star_lt := fun k => explicitEquil_lt_one (D.γ k) D.K r_star (D.hγ k) D.hK hr_pos
      hγ_max_pos := hγ_max_pos
      hγ_max := hγ_max
      hδ_star_pos := hδ_star_pos
      hα_star_lb := hδ_star
      h_equil := h_nPoleODE
      hc_sum := hc_sum
      hα_init_pos := hα_init_pos
      hα_init_lt := hα_init_small
      hα_init_lt_one := hα_init_lt_one }
    r_star h_sc.symm

/-! ## Automatic δ_star from γ_max via monotonicity -/

theorem grounded_convergence_auto (D : NPoleBarrierData n) (hn : 0 < n)
    (hc_sum : ∑ k, D.c k = 1)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (hα_init_lt_one : ∀ k, D.α 0 k < 1)
    (γ_max : ℝ) (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (r_star : ℝ) (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (h_sc : ∑ k, D.c k * explicitEquil (D.γ k) D.K r_star = r_star)
    (hα_init_small : ∀ k, D.α 0 k < 2 * explicitEquil (D.γ k) D.K r_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, D.c k * D.α t k - r_star| < ε :=
  grounded_convergence D hn hc_sum hα_init_pos hα_init_lt_one
    γ_max hγ_max_pos hγ_max r_star hr_pos hr_lt h_sc
    (explicitEquil γ_max D.K r_star)
    (explicitEquil_pos γ_max D.K r_star hγ_max_pos D.hK hr_pos)
    (fun k => explicitEquil_mono_gamma (D.γ k) γ_max D.K r_star (D.hγ k)
      D.hK hr_pos (hγ_max k))
    hα_init_small

end
