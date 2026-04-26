/-
  Kuramoto Stability — Shifted Component Barrier
  =================================================

  α_k(t) ≥ α_k(t₀)·exp(-γ_k·(t-t₀)) for 0 ≤ t₀ ≤ t.

  0 sorry target.
-/

import KuramotoLean.ComponentBarrier
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Real Set

noncomputable section

variable {n : ℕ}

private def gm (D : NPoleBarrierData n) (k : Fin n) (t : ℝ) : ℝ :=
  D.α t k * exp (D.γ k * t)

private theorem gm_cont (D : NPoleBarrierData n) (k : Fin n) :
    ContinuousOn (gm D k) (Ici 0) :=
  (D.hα_cont k).mul (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

private theorem gm_hasderiv (D : NPoleBarrierData n) (k : Fin n) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (gm D k) ((D.K / 2) * D.r s * (1 - D.α s k ^ 2) * exp (D.γ k * s)) s := by
  have hα := D.hα_ode s hs k
  have hexp : HasDerivAt (fun u => exp (D.γ k * u)) (D.γ k * exp (D.γ k * s)) s := by
    have h1 : HasDerivAt (fun u => D.γ k * u) (D.γ k) s :=
      (hasDerivAt_id s).const_mul (D.γ k) |>.congr_deriv (mul_one _)
    exact h1.exp.congr_deriv (by ring)
  have h := hα.mul hexp
  convert h using 1
  unfold nPoleODE NPoleBarrierData.r; ring

private theorem gm_deriv_nn (D : NPoleBarrierData n) (k : Fin n) (s : ℝ) (hs : 0 < s) :
    0 ≤ (D.K / 2) * D.r s * (1 - D.α s k ^ 2) * exp (D.γ k * s) := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg (by linarith [D.hK]) (D.r_nonneg s (le_of_lt hs))
    · have hle := D.hα_le s (le_of_lt hs) k
      have hnn := D.hα_nn s (le_of_lt hs) k
      have hsq : D.α s k * D.α s k ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hle hnn) (by linarith)
      have : (D.α s k) ^ 2 ≤ 1 := by rw [sq]; exact hsq
      linarith
  · exact exp_nonneg _

private theorem gm_mono (D : NPoleBarrierData n) (k : Fin n) :
    MonotoneOn (gm D k) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (gm_cont D k)
  · rw [interior_Ici]; intro s hs
    exact (gm_hasderiv D k s (mem_Ioi.mp hs)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro s hs
    rw [(gm_hasderiv D k s (mem_Ioi.mp hs)).deriv]
    exact gm_deriv_nn D k s (mem_Ioi.mp hs)

theorem shifted_component_barrier (D : NPoleBarrierData n)
    (k : Fin n) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    D.α t₀ k * exp (-(D.γ k) * (t - t₀)) ≤ D.α t k := by
  have hF := gm_mono D k (mem_Ici.mpr ht₀) (mem_Ici.mpr (le_trans ht₀ ht)) ht
  change gm D k t₀ ≤ gm D k t at hF
  unfold gm at hF
  calc D.α t₀ k * exp (-(D.γ k) * (t - t₀))
      = D.α t₀ k * exp (D.γ k * t₀) * exp (-(D.γ k) * t) := by
        rw [mul_assoc, ← exp_add]; ring_nf
    _ ≤ D.α t k * exp (D.γ k * t) * exp (-(D.γ k) * t) :=
        mul_le_mul_of_nonneg_right hF (exp_nonneg _)
    _ = D.α t k := by rw [mul_assoc, ← exp_add]; simp

/-- **Uniform lower bound on shifted interval.** -/
theorem component_lower_shifted (D : NPoleBarrierData n)
    (k : Fin n) (t₀ Δ : ℝ) (ht₀ : 0 ≤ t₀) (_hΔ : 0 ≤ Δ)
    (t : ℝ) (ht_lo : t₀ ≤ t) (ht_hi : t ≤ t₀ + Δ) :
    D.α t₀ k * exp (-(D.γ k) * Δ) ≤ D.α t k := by
  calc D.α t₀ k * exp (-(D.γ k) * Δ)
      ≤ D.α t₀ k * exp (-(D.γ k) * (t - t₀)) :=
        mul_le_mul_of_nonneg_left
          (exp_le_exp.mpr (by nlinarith [D.hγ k])) (D.hα_nn t₀ ht₀ k)
    _ ≤ D.α t k := shifted_component_barrier D k t₀ t ht₀ ht_lo

end
