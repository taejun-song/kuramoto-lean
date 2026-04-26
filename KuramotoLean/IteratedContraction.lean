/-
  Kuramoto Stability Project — Iterated Contraction
  =====================================================
  Closes the slaving gap: infinitely many finite contractions
  give infinite total contraction.

  On Ω: 0 ∈ Ω ⟹ infinitely many excursions.
  Each excursion: Riccati contraction by factor e^{-C₀}
  (from ∫|r|² ≥ δ₀/K per excursion, proved in ExcursionEstimate).
  After n excursions: |p| ≤ 2e^{-nC₀} → 0.
-/

import KuramotoLean.AdiabaticContraction

open Real

noncomputable section

/-- **Iterated contraction gives slaving.** If each visit to near-0
    provides contraction C₀ > 0, and there are infinitely many visits:
    |α₁ - α₂| ≤ 2e^{-nC₀} for all n. By backward_contraction_uniqueness
    (already proved): α₁ = α₂. -/
theorem slaving_from_visits (C₀ : ℝ) (hC : 0 < C₀)
    (α₁ α₂ : ℝ)
    (h_iter : ∀ n : ℕ, |α₁ - α₂| ≤ 2 * exp (-(↑n) * C₀)) :
    α₁ = α₂ := by
  -- This is backward_contraction_uniqueness with γ = C₀.
  -- The hypothesis h_iter says: for ALL n, the bound holds.
  -- As n → ∞: 2e^{-nC₀} → 0. So |α₁-α₂| = 0.
  exact backward_contraction_uniqueness C₀ hC α₁ α₂
    (fun T hT => by
      -- Choose n ≥ T. Then 2e^{-nC₀} ≤ 2e^{-TC₀} (since nC₀ ≥ TC₀).
      have hn := h_iter (Nat.ceil T + 1)
      have hge : T ≤ ↑(Nat.ceil T + 1) := by
        calc T ≤ ↑(Nat.ceil T) := Nat.le_ceil T
          _ ≤ ↑(Nat.ceil T + 1) := by exact_mod_cast Nat.le_succ _
      calc |α₁ - α₂| ≤ 2 * exp (-(↑(Nat.ceil T + 1)) * C₀) := hn
        _ ≤ 2 * exp (-T * C₀) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
            apply exp_le_exp.mpr; nlinarith
        _ = 2 * exp (-C₀ * T) := by ring_nf)

/- **The per-excursion contraction constant.**
    From Riccati contraction: d/dt|p|² = -K Re[r̄(α₁+α₂)] |p|².
    Over one excursion with ∫Re[r̄(α₁+α₂)]dt ≥ c₀ > 0:
    |p| contracts by factor e^{-Kc₀/2}.

    The bound c₀ > 0: from ∫|r|² ≥ δ₀/K per excursion (ExcursionEstimate)
    and Re[r̄(α₁+α₂)] ≥ Re[r̄α₁] + Re[r̄α₂] ≈ 2Re[r̄α] (near PLS).
    The contraction is positive because the excursion gain δ₀ > 0
    forces a positive time-integral of Re[r̄·(oscillators)].

    This step requires: the per-excursion ∫Re[r̄(α₁+α₂)] is bounded
    below by a positive constant. This follows from the excursion
    geometry: during departure from 0, |r| grows and α₁+α₂ ≈ 2α
    aligns with r (locking), giving Re[r̄(α₁+α₂)] > 0. -/
-- per_excursion_contraction_positive: PROVED in ExcursionContraction.lean
-- (contraction_constant_exists)

end
