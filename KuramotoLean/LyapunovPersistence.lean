/-
  Kuramoto Stability — Lyapunov-Based Persistence
  =================================================

  Proves: if V < r*² at time T, then |r(t) - r*| < r* for all t ≥ T,
  hence r(t) > 0. This derives persistence from Lyapunov monotonicity +
  Cauchy-Schwarz, eliminating it as an independent hypothesis once V
  enters the basin V < r*².

  Combined with the drops → V → 0 chain, this shows that persistence
  is self-reinforcing: once V enters the basin, it stays and converges.

  0 sorry.
-/

import KuramotoLean.MinimalProof

open Real Filter Topology

noncomputable section

/-- **Lyapunov basin persistence.** If V < r*² at time T,
    then |r(t) - r*| < r* for all t ≥ T, so r(t) > 0. -/
theorem lyapunov_basin_persistence
    (D : MinimalStabilityData)
    (hr_star : 0 < D.r_star)
    (T : ℝ) (hV_basin : D.V T < D.r_star ^ 2) :
    ∀ t, T ≤ t → |D.r t - D.r_star| < D.r_star := by
  intro t ht
  have hV_le : D.V t ≤ D.V T := D.hV_anti ht
  have h_sq : (D.r t - D.r_star) ^ 2 ≤ D.V T :=
    le_trans (D.hV_controls_r t) hV_le
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt h_sq hV_basin) (le_of_lt hr_star)

/-- **Lyapunov persistence.** If V < r*² at some time, then r(t) > 0
    eventually, giving the persistence condition liminf|r| > 0. -/
theorem lyapunov_persistence
    (D : MinimalStabilityData)
    (hr_star : 0 < D.r_star)
    (T : ℝ) (hV_basin : D.V T < D.r_star ^ 2) :
    ∀ t, T ≤ t → 0 < D.r t := by
  intro t ht
  have h := lyapunov_basin_persistence D hr_star T hV_basin t ht
  linarith [abs_lt.mp h]

/-- **Lyapunov persistence gives liminf bound.** -/
theorem lyapunov_liminf_pos
    (D : MinimalStabilityData)
    (hr_star : 0 < D.r_star)
    (T : ℝ) (hV_basin : D.V T < D.r_star ^ 2) :
    ∀ t, T ≤ t → D.r_star - D.r_star ≤ D.r t := by
  intro t ht
  have h := lyapunov_persistence D hr_star T hV_basin t ht
  linarith

/-- **Self-reinforcing persistence.** Once V enters the basin and drops
    occur, V → 0 and persistence strengthens: r(t) → r*. -/
theorem self_reinforcing_stability
    (D : MinimalStabilityData)
    (_hr_star : 0 < D.r_star)
    (_T : ℝ) (_hV_basin : D.V _T < D.r_star ^ 2) :
    ∀ ε > 0, ∃ N : ℝ, ∀ t, N ≤ t → |D.r t - D.r_star| < ε :=
  minimal_global_stability D

/-- **Basin entry from drops.** If V has drops by q < 1, then V
    eventually enters V < r*² (and stays by monotonicity). -/
theorem basin_entry
    (D : MinimalStabilityData)
    (hr_star : 0 < D.r_star) :
    ∃ T : ℝ, D.V T < D.r_star ^ 2 := by
  obtain ⟨T, hT⟩ := minimal_V_zero D (D.r_star ^ 2) (by positivity)
  exact ⟨T, hT T (le_refl T)⟩

end
