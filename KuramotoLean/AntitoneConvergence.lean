/-
  Kuramoto Stability — Antitone Convergence
  ==========================================
  A bounded non-negative antitone function on [0,∞) converges.

  This is the continuous-time analogue of "bounded monotone sequence converges."
  Combined with dV∞/dt ≤ 0 (ContinuumLyapunov), it gives V∞(t) → L ≥ 0.

  The remaining step for full continuum global stability: show L = 0.

  0 sorry.
-/

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Topology

noncomputable section

/-- A non-negative antitone function on ℝ converges to its infimum. -/
theorem antitone_bounded_converges (f : ℝ → ℝ)
    (h_anti : Antitone f) (h_nn : ∀ t, 0 ≤ f t) :
    ∃ L, 0 ≤ L ∧ Tendsto f atTop (nhds L) := by
  have h_mono : Monotone (fun t => -f t) := fun a b hab => neg_le_neg (h_anti hab)
  have h_bdd : BddAbove (Set.range (fun t => -f t)) :=
    ⟨0, fun y ⟨t, ht⟩ => ht ▸ neg_nonpos.mpr (h_nn t)⟩
  rcases tendsto_atTop_of_monotone h_mono with h | ⟨L_neg, hL⟩
  · exfalso
    have h1 := (Filter.tendsto_atTop.mp h) 1
    rw [Filter.eventually_atTop] at h1
    obtain ⟨T, hT⟩ := h1
    linarith [h_nn T, hT T le_rfl]
  · refine ⟨-L_neg, ?_, ?_⟩
    · have : L_neg ≤ 0 := le_of_tendsto hL
        (eventually_atTop.mpr ⟨0, fun t _ => neg_nonpos.mpr (h_nn t)⟩)
      linarith
    · rw [Metric.tendsto_atTop] at hL ⊢
      intro ε hε
      obtain ⟨T, hT⟩ := hL ε hε
      exact ⟨T, fun t ht => by
        have := hT t ht
        simp only [Real.dist_eq] at this ⊢
        rwa [show -f t - L_neg = -(f t - (-L_neg)) from by ring, abs_neg] at this⟩

/-- Epsilon-delta version for applications. -/
theorem antitone_bounded_converges' (f : ℝ → ℝ)
    (h_anti : Antitone f) (h_nn : ∀ t, 0 ≤ f t) :
    ∃ L, 0 ≤ L ∧ ∀ ε > 0, ∃ T, ∀ t, T ≤ t → |f t - L| < ε := by
  obtain ⟨L, hL_nn, hL⟩ := antitone_bounded_converges f h_anti h_nn
  exact ⟨L, hL_nn, fun ε hε => by
    rw [Metric.tendsto_atTop] at hL
    obtain ⟨T, hT⟩ := hL ε hε
    exact ⟨T, fun t ht => by
      have := hT t ht; rwa [Real.dist_eq] at this⟩⟩

/-- The limit of an antitone non-negative function is ≤ f(0). -/
theorem antitone_limit_le_initial (f : ℝ → ℝ) (L : ℝ)
    (h_anti : Antitone f) (_h_nn : ∀ t, 0 ≤ f t)
    (hL : Tendsto f atTop (nhds L)) :
    L ≤ f 0 := by
  exact le_of_tendsto hL (eventually_atTop.mpr ⟨0, fun t ht => h_anti ht⟩)

/-! ## Application to the Lyapunov function

For the continuum OA system with dV∞/dt ≤ 0:
- V∞ ≥ 0 (sum of squares weighted by g)
- V∞ is antitone (from dV∞/dt ≤ 0)
Therefore: V∞(t) → L ≥ 0.

The remaining step: L = 0. This requires either:
(a) LaSalle invariance + compactness (the only invariant set with dV/dt = 0 is {α*})
(b) A quantitative lower bound on dV/dt when V > ε (exponential rate + persistence)
(c) The Volterra trapping argument (scalar r → r* from past-history decay)

Approach (b) works for n-pole (GronwallBridge.lean) but the quantitative bound
degenerates in the continuum (diagonal of measure zero). Approaches (a) and (c)
are open. -/

/-- **Continuum Lyapunov convergence structure.**
    Packages a Lyapunov function along a trajectory with the properties
    needed for convergence analysis. -/
structure LyapunovConvergence where
  V : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V

/-- The Lyapunov function converges to a non-negative limit. -/
theorem LyapunovConvergence.converges (D : LyapunovConvergence) :
    ∃ L, 0 ≤ L ∧ Tendsto D.V atTop (nhds L) :=
  antitone_bounded_converges D.V D.hV_anti D.hV_nn

/-- If the limit is 0, the Lyapunov function converges to 0. -/
theorem LyapunovConvergence.converges_to_zero (D : LyapunovConvergence)
    (h_zero : ∀ L, 0 ≤ L → Tendsto D.V atTop (nhds L) → L = 0) :
    Tendsto D.V atTop (nhds 0) := by
  obtain ⟨L, hL_nn, hL⟩ := D.converges
  have := h_zero L hL_nn hL
  rwa [this] at hL

end
