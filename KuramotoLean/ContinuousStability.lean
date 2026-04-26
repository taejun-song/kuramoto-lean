/-
  Kuramoto Stability — Continuous-Time Global Stability
  =====================================================
  Eliminates the discrete-time step-size constraint (hL_small: 3L < r*)
  by using IVT for trapping instead of Lipschitz bounds.

  Key advantage: applies to ALL K > K_c without step-size restrictions.
  The continuous trajectory cannot jump across the self-consistency gap.

  Proof chain:
    Φ continuous → gap_min (EVT)
    hsc_decay + gap_min → gap exclusion
    gap exclusion + persistence + IVT → r(t) → r*
-/

import KuramotoLean.MainTheorem
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set

/-! ## Continuous-time KuramotoData: no Lipschitz/step-size hypotheses -/

structure ContinuousKuramotoData where
  r : ℝ → ℝ
  r_star : ℝ
  hr_star : 0 < r_star
  hr_bdd : ∀ t, 0 ≤ r t ∧ r t ≤ 1
  hr_cont : Continuous r
  δ : ℝ
  hδ : 0 < δ
  hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ δ ≤ r t
  Φ : ℝ → ℝ
  hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 →
    Φ x = x → x = 0 ∨ x = r_star
  hΦ_continuous : Continuous Φ
  hsc_decay : ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
    |r t - Φ (r t)| < ε

/-! ## Gap exclusion (continuous time) -/

theorem continuous_gap_exclusion (D : ContinuousKuramotoData) :
    ∀ η > 0, η < D.r_star / 3 →
    ∃ T : ℝ, ∀ t, T ≤ t →
      D.r t < η ∨ |D.r t - D.r_star| < η := by
  intro η hη hη3
  obtain ⟨m, hm, hgap⟩ := gap_min_from_continuity D.r_star D.Φ
    D.hr_star D.hΦ_unique D.hΦ_continuous η hη hη3
  obtain ⟨T, hT⟩ := D.hsc_decay m hm
  exact ⟨T, fun t ht => by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have hbdd := D.hr_bdd t
    have h_in_gap : (η ≤ D.r t ∧ D.r t ≤ D.r_star - η) ∨
        (D.r_star + η ≤ D.r t) := by
      rcases le_or_gt (D.r t) (D.r_star - η) with h3 | h3
      · left; exact ⟨h1, h3⟩
      · right
        rcases le_or_gt (D.r t) D.r_star with h4 | h4
        · have : |D.r t - D.r_star| = -(D.r t - D.r_star) :=
            abs_of_nonpos (by linarith)
          linarith
        · have : |D.r t - D.r_star| = D.r t - D.r_star :=
            abs_of_pos (by linarith)
          linarith
    linarith [hgap (D.r t) hbdd.1 hbdd.2 h_in_gap, hT t ht]⟩

/-! ## IVT-based trapping (replaces Lipschitz trapping) -/

theorem continuous_trapping (D : ContinuousKuramotoData) (η T : ℝ)
    (_hη : 0 < η) (hη3 : η < D.r_star / 3)
    (hgap : ∀ t, T ≤ t → D.r t < η ∨ |D.r t - D.r_star| < η)
    (hstart : |D.r T - D.r_star| < η) :
    ∀ t, T ≤ t → |D.r t - D.r_star| < η := by
  by_contra h
  push Not at h
  obtain ⟨t₁, ht₁, h_not_near⟩ := h
  have h_small : D.r t₁ < η := by
    rcases hgap t₁ ht₁ with h | h
    · exact h
    · linarith
  have h_big : η < D.r T := by
    have := (abs_lt.mp hstart).1; linarith
  obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (right_mem_Icc.mpr ht₁)
      (left_mem_Icc.mpr ht₁)
      D.hr_cont.continuousOn
      continuousOn_const
      (le_of_lt h_small)
      (le_of_lt h_big)
  rcases hgap t₀ (mem_Icc.mp ht₀_mem).1 with h_case | h_case
  · linarith
  · rw [ht₀_eq] at h_case
    have := (abs_lt.mp h_case).1
    linarith

/-! ## Main theorem: continuous-time global stability -/

theorem continuous_global_stability (D : ContinuousKuramotoData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.r t - D.r_star| < ε := by
  intro ε hε
  set η := min (min ε (D.r_star / 4)) D.δ
  have hη_pos : 0 < η :=
    lt_min (lt_min hε (by linarith [D.hr_star])) D.hδ
  have hη_le_ε : η ≤ ε :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_lt_rs3 : η < D.r_star / 3 := by
    have : η ≤ D.r_star / 4 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [D.hr_star]
  have hη_le_δ : η ≤ D.δ := min_le_right _ _
  obtain ⟨T_gap, hgap⟩ :=
    continuous_gap_exclusion D η hη_pos hη_lt_rs3
  obtain ⟨t₀, ht₀, hrt₀⟩ := D.hpersist T_gap
  have hstart : |D.r t₀ - D.r_star| < η := by
    rcases hgap t₀ ht₀ with h | h
    · linarith
    · exact h
  exact ⟨t₀, fun t ht => by
    linarith [continuous_trapping D η t₀ hη_pos hη_lt_rs3
      (fun t h => hgap t (by linarith)) hstart t ht]⟩

end
