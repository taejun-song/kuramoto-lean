/-
  Kuramoto Stability — Lorentzian Solution to Continuum Bridge
  =============================================================

  Constructs ContinuumPointwiseData from LorentzianSolution.

  The Lyapunov ENVELOPE V(m) = hlyap_coeff · exp(-2Ψ(m)) is
  the ContinuumPointwiseData sequence:

  · hV_nn:    V(m) ≥ 0        (coeff positive × exp positive)
  · hV_anti:  V(m+1) ≤ V(m)   (Ψ non-decreasing → exp(-2Ψ) non-increasing)
  · hV_zero:  V(m) → 0        (Ψ → ∞ + exp(-2·) → 0)

  Then pointwise_convergence (Path B) gives Tendsto V atTop (nhds 0).

  Combined with hlyap: (r(m)² - r*²)² ≤ V(m), the Lyapunov residual → 0.

  0 sorry.
-/

import KuramotoLean.ContinuumGlobalStability
import KuramotoLean.LorentzianInstance

open Filter Topology Real Finset

noncomputable section

/-! ## Ψ → ∞ implies exp(-2Ψ) → 0 -/

/-- Ψ non-decreasing + unbounded → Tendsto Ψ atTop atTop. -/
private theorem psi_tendsto_atTop (S : LorentzianSolution) :
    Tendsto S.Ψ atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨n₀, hn₀⟩ := lorentzian_psi_diverges S b
  exact ⟨n₀, fun m hm => le_of_lt (lt_of_lt_of_le hn₀ (lorentzian_psi_mono_le S n₀ m hm))⟩

/-- exp(-2Ψ(m)) → 0 as m → ∞. -/
private theorem exp_neg_psi_tendsto_zero (S : LorentzianSolution) :
    Tendsto (fun m => Real.exp (-2 * S.Ψ m)) atTop (nhds 0) := by
  have h_neg : Tendsto (fun m : ℕ => (-2 : ℝ) * S.Ψ m) atTop atBot := by
    rw [Filter.tendsto_atTop_atBot]
    intro b
    have hpsi := psi_tendsto_atTop S
    rw [Filter.tendsto_atTop_atTop] at hpsi
    obtain ⟨n, hn⟩ := hpsi ((-b) / 2)
    exact ⟨n, fun m hm => by linarith [hn m hm]⟩
  have h_comp := tendsto_exp_atBot.comp h_neg
  simp only [Function.comp] at h_comp
  exact h_comp

/-! ## ContinuumPointwiseData from LorentzianSolution -/

/-- Construct ContinuumPointwiseData from LorentzianSolution.
    V(m) = hlyap_coeff · exp(-2Ψ(m)) is the Lyapunov envelope:
    · non-negative from positivity of coeff and exp
    · non-increasing from Ψ non-decreasing (each step adds K·r(m)² ≥ 0)
    · converges to 0: ∀ e > 0, eventually V(m) < e (from Ψ → ∞) -/
def LorentzianSolution.toContinuumPointwiseData (S : LorentzianSolution) :
    ContinuumPointwiseData where
  V       := fun m => S.hlyap_coeff * Real.exp (-2 * S.Ψ m)
  hV_nn   := fun m => mul_nonneg (le_of_lt S.hlyap_coeff_pos) (Real.exp_nonneg _)
  hV_anti := fun m => by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt S.hlyap_coeff_pos)
    apply Real.exp_le_exp_of_le
    have hge : 0 ≤ S.K * S.r m ^ 2 :=
      mul_nonneg (le_of_lt S.hK_pos) (sq_nonneg _)
    linarith [S.Ψ_growth m]
  hV_zero := fun e he => by
    have h : Tendsto (fun m => S.hlyap_coeff * Real.exp (-2 * S.Ψ m)) atTop (nhds 0) := by
      have h0 := (exp_neg_psi_tendsto_zero S).const_mul S.hlyap_coeff
      simp only [mul_zero] at h0; exact h0
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h e he
    exact ⟨N, fun m hm => by
      have := hN m hm
      rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (mul_nonneg (le_of_lt S.hlyap_coeff_pos) (Real.exp_nonneg _))] at this
      exact this⟩

/-- Lorentzian Lyapunov envelope → 0 via ContinuumGlobalStability Path B. -/
theorem lorentzian_envelope_via_path_b (S : LorentzianSolution) :
    Tendsto (fun m => S.hlyap_coeff * Real.exp (-2 * S.Ψ m)) atTop (nhds 0) :=
  pointwise_convergence S.toContinuumPointwiseData

/-- The Lyapunov residual (r(m)² - r*²)² converges to 0. -/
theorem lorentzian_residual_tendsto_zero (S : LorentzianSolution) :
    Tendsto (fun m => (S.r m ^ 2 - S.r_star ^ 2) ^ 2) atTop (nhds 0) := by
  have h_env := lorentzian_envelope_via_path_b S
  have h_rstar : S.r_star ^ 2 = 1 - 2 * S.γ / S.K := by
    unfold LorentzianSolution.r_star
    rw [Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))]
  apply squeeze_zero (fun m => sq_nonneg _) _ h_env
  intro m
  have hh := S.hlyap m
  rwa [h_rstar]

end
