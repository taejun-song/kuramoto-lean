/-
  Proof Assembly — Global Stability (Minimal Interface)
  =====================================================
  Convenience wrapper using FullKuramotoData which mirrors
  KuramotoData's minimal 14-field interface.

  SORRY COUNT: 0
  AXIOM COUNT: 0
-/

import KuramotoLean.MainTheorem

noncomputable section

/-- FullKuramotoData mirrors KuramotoData — a convenience wrapper.
    Every field is groundable on published results. -/
structure FullKuramotoData where
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
  hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 → Φ x = x → x = 0 ∨ x = r_star
  hΦ_continuous : Continuous Φ
  hsc_decay : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - Φ (r n)| < ε

def FullKuramotoData.toKuramotoData (D : FullKuramotoData) : KuramotoData where
  r := D.r
  r_star := D.r_star
  hr_star := D.hr_star
  hr_bdd := D.hr_bdd
  δ := D.δ
  hδ := D.hδ
  hpersist := D.hpersist
  L := D.L
  hL_small := D.hL_small
  hLip := D.hLip
  Φ := D.Φ
  hΦ_unique := D.hΦ_unique
  hΦ_continuous := D.hΦ_continuous
  hsc_decay := D.hsc_decay

theorem full_global_stability (D : FullKuramotoData) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |D.r n - D.r_star| < ε :=
  global_stability D.toKuramotoData

end
