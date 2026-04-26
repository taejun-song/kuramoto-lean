/-
  Kuramoto Global Stability — Main Theorem
  ==========================================
  0 sorry. 14-field minimal structure.

  Proof chain:
    Φ continuous → gap_min (EVT)
    hsc_decay + gap_min → gap exclusion → trapping → r → r*
-/

import Mathlib.Topology.Order.Compact
import KuramotoLean.GapExclusion

noncomputable section

open Set

/-! ## Gap minimum from EVT (Weierstrass theorem) -/

theorem gap_min_from_continuity (r_star : ℝ) (Φ : ℝ → ℝ)
    (hr_star : 0 < r_star)
    (hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 →
      Φ x = x → x = 0 ∨ x = r_star)
    (hΦ_continuous : Continuous Φ) :
    ∀ η > 0, η < r_star / 3 →
    ∃ m > 0, ∀ x, 0 ≤ x → x ≤ 1 →
      (η ≤ x ∧ x ≤ r_star - η) ∨
        (r_star + η ≤ x) →
      m ≤ |x - Φ x| := by
  intro η hη hη3
  set f : ℝ → ℝ := fun x => |x - Φ x|
  set S := Icc (0:ℝ) 1 ∩
    (Icc η (r_star - η) ∪ Ici (r_star + η))
  have hf_cont : Continuous f :=
    continuous_abs.comp
      (continuous_id.sub hΦ_continuous)
  have hS_compact : IsCompact S :=
    isCompact_Icc.inter_right
      (IsClosed.union isClosed_Icc isClosed_Ici)
  have hf_pos : ∀ x ∈ S, (0:ℝ) < f x := by
    intro x ⟨⟨hx0, hx1⟩, hx_gap⟩
    have hne : x ≠ Φ x := by
      intro heq
      rcases hΦ_unique x hx0 hx1 heq.symm
        with rfl | rfl
      · rcases hx_gap with h | h
        · exact absurd (mem_Icc.mp h).1
            (by linarith)
        · exact absurd (mem_Ici.mp h)
            (by linarith)
      · rcases hx_gap with h | h
        · exact absurd (mem_Icc.mp h).2
            (by linarith)
        · exact absurd (mem_Ici.mp h)
            (by linarith)
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨m, hm_pos, hm_le⟩ :=
    hS_compact.exists_forall_le'
      hf_cont.continuousOn hf_pos
  exact ⟨m, hm_pos, fun x hx0 hx1 hgap =>
    hm_le x (mem_inter ⟨hx0, hx1⟩ (by
      rcases hgap with ⟨h1, h2⟩ | h
      · exact Or.inl (mem_Icc.mpr ⟨h1, h2⟩)
      · exact Or.inr (mem_Ici.mpr h)))⟩

/-! ## KuramotoData: minimal structure for global stability -/

structure KuramotoData where
  r : ℕ → ℝ
  r_star : ℝ
  hr_star : 0 < r_star
  hr_bdd : ∀ n, 0 ≤ r n ∧ r n ≤ 1
  δ : ℝ
  hδ : 0 < δ
  hpersist : ∀ N, ∃ n, N ≤ n ∧ δ ≤ r n
  L : ℝ
  hL_small : 3 * L < r_star
  hLip : ∀ n, |r (n + 1) - r n| ≤ L
  Φ : ℝ → ℝ
  hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 →
    Φ x = x → x = 0 ∨ x = r_star
  hΦ_continuous : Continuous Φ
  hsc_decay : ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
    |r n - Φ (r n)| < ε

/-! ## Gap exclusion -/

private def toGapData (D : KuramotoData) : GapData where
  r := D.r
  r_star := D.r_star
  Φ := D.Φ
  hr_star := D.hr_star
  hr_bdd := D.hr_bdd
  hΦ_unique := D.hΦ_unique
  gap_min := gap_min_from_continuity D.r_star D.Φ
    D.hr_star D.hΦ_unique D.hΦ_continuous
  hsc_decay := D.hsc_decay

theorem hsc_gap_proved (D : KuramotoData) :
    ∀ η > 0, η < D.r_star / 3 →
    ∃ N, ∀ n, N ≤ n →
      D.r n < η ∨ |D.r n - D.r_star| < η :=
  gap_exclusion (toGapData D)

/-! ## Lipschitz trapping -/

theorem lipschitz_trap (D : KuramotoData) (η : ℝ)
    (_hη : 0 < η) (hη3 : η < D.r_star / 3)
    (N : ℕ)
    (hgap : ∀ n, N ≤ n →
      D.r n < η ∨ |D.r n - D.r_star| < η)
    (hstart : |D.r N - D.r_star| < η) :
    ∀ n, N ≤ n → |D.r n - D.r_star| < η := by
  intro n hn
  induction n with
  | zero =>
    have : N = 0 := by omega
    subst this; exact hstart
  | succ k ih =>
    by_cases hk : N ≤ k
    · have hk_near := ih hk
      rcases hgap (k + 1) (by omega) with h0 | hr
      · exfalso
        have h1 : D.r k - D.r (k + 1) ≤ D.L := by
          calc D.r k - D.r (k + 1)
              ≤ |D.r k - D.r (k + 1)| :=
                le_abs_self _
            _ = |D.r (k + 1) - D.r k| :=
                abs_sub_comm _ _
            _ ≤ D.L := D.hLip k
        have h2 : D.r_star - η < D.r k := by
          have := (abs_lt.mp hk_near).1; linarith
        have h3 : D.L < D.r_star - 2 * η := by
          linarith [D.hL_small]
        linarith
      · exact hr
    · have : N = k + 1 := by omega
      subst this; exact hstart

/-! ## Main theorem -/

theorem global_stability (D : KuramotoData) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
      |D.r n - D.r_star| < ε := by
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
  obtain ⟨N_gap, hgap⟩ :=
    hsc_gap_proved D η hη_pos hη_lt_rs3
  obtain ⟨n₀, hn₀, hrn₀⟩ := D.hpersist N_gap
  have hstart : |D.r n₀ - D.r_star| < η := by
    rcases hgap n₀ hn₀ with h | h
    · linarith
    · exact h
  exact ⟨n₀, fun n hn => by
    linarith [lipschitz_trap D η hη_pos hη_lt_rs3 n₀
      (fun n h => hgap n (by omega))
      hstart n hn]⟩

end
