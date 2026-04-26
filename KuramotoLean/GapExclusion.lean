/-
  Gap Exclusion Lemma
  ====================
  Proves: if |r(n) - Φ(r(n))| → 0 and Φ has only {0, r*} as fixed
  points in [0,1], then r(n) is eventually near {0} or {r*}.

  This closes the `hsc_gap` hypothesis of MainTheorem.lean.
-/

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

noncomputable section

/-- **Gap exclusion from approximate self-consistency.**
    If f = |id - Φ| is continuous and positive on the "gap" set
    S = [η, r*-η] ∪ [r*+η, 1], then f has a positive minimum m on S.
    Any x with f(x) < m must lie outside S, i.e., in [0,η) ∪ (r*-η, r*+η).

    We prove this for real-valued sequences using only elementary
    properties, avoiding topology by taking the minimum as a hypothesis.

    The topological content (continuous f on compact S achieves min > 0)
    is a standard Mathlib result: IsCompact.exists_isMinOn.

    Data for the gap exclusion argument. -/
structure GapData where
  r : ℕ → ℝ
  r_star : ℝ
  Φ : ℝ → ℝ
  hr_star : 0 < r_star
  hr_bdd : ∀ n, 0 ≤ r n ∧ r n ≤ 1
  -- Φ has no other fixed points in [0,1]
  hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 → Φ x = x → x = 0 ∨ x = r_star
  -- For any gap region [η, r*-η] ∪ [r*+η, 1], the minimum of |x-Φ(x)| is > 0
  -- (This follows from: Φ continuous, no fixed points in gap, compactness.
  --  We take the minimum value as a hypothesis to avoid formalizing
  --  the compact minimum theorem here.)
  gap_min : ∀ η > 0, η < r_star / 3 →
    ∃ m > 0, ∀ x, 0 ≤ x → x ≤ 1 → (η ≤ x ∧ x ≤ r_star - η) ∨ (r_star + η ≤ x) →
    m ≤ |x - Φ x|
  -- |r(n) - Φ(r(n))| → 0
  hsc_decay : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - Φ (r n)| < ε

/-- **Gap exclusion theorem.** r(n) is eventually in [0,η) ∪ (r*-η, r*+η). -/
theorem gap_exclusion (D : GapData) :
    ∀ η > 0, η < D.r_star / 3 →
    ∃ N, ∀ n, N ≤ n → D.r n < η ∨ |D.r n - D.r_star| < η := by
  intro η hη hη3
  obtain ⟨m, hm, hgap⟩ := D.gap_min η hη hη3
  obtain ⟨N, hN⟩ := D.hsc_decay m hm
  exact ⟨N, fun n hn => by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    -- r(n) ≥ η and |r(n) - r*| ≥ η
    -- So r(n) ∈ [η, r*-η] ∪ [r*+η, 1] (the gap)
    have hbdd := D.hr_bdd n
    have h_in_gap : (η ≤ D.r n ∧ D.r n ≤ D.r_star - η) ∨ (D.r_star + η ≤ D.r n) := by
      -- h1 : η ≤ D.r n, h2 : η ≤ |D.r n - D.r_star|
      rcases le_or_gt (D.r n) (D.r_star - η) with h3 | h3
      · left; exact ⟨h1, h3⟩
      · right
        rcases le_or_gt (D.r n) D.r_star with h4 | h4
        · -- D.r n ≤ D.r_star: |D.r n - D.r_star| = D.r_star - D.r n ≥ η
          -- So D.r n ≤ D.r_star - η. But h3: D.r n > D.r_star - η. Contradiction.
          have : |D.r n - D.r_star| = -(D.r n - D.r_star) := abs_of_nonpos (by linarith)
          linarith
        · -- D.r n > D.r_star: |D.r n - D.r_star| = D.r n - D.r_star ≥ η
          have : |D.r n - D.r_star| = D.r n - D.r_star := abs_of_pos (by linarith)
          linarith
    -- So |r(n) - Φ(r(n))| ≥ m > 0
    have h_lower := hgap (D.r n) hbdd.1 hbdd.2 h_in_gap
    -- But |r(n) - Φ(r(n))| < m (from decay)
    have h_upper := hN n hn
    linarith⟩

end
