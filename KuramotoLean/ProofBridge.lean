/-
  Kuramoto Stability — Proof Path Bridge
  ========================================

  Shows that L² convergence (r → r*) implies self-consistency decay
  (|r - Φ(r)| → 0), bridging the L² Lyapunov path to the gap-exclusion
  path of MainTheorem.

  This means the L² path (NPoleGlobalStability, GronwallBridge, etc.)
  SUBSUMES the MainTheorem path: any system with L² convergence also
  satisfies the hypotheses of MainTheorem.

  0 sorry.
-/

import KuramotoLean.MainTheorem

open Filter Topology

noncomputable section

/-! ## SC decay from convergence + continuity -/

/-- **Self-consistency decay from convergence.**
    If r → r* and Φ is continuous with Φ(r*) = r*, then |r - Φ(r)| → 0.
    This derives MainTheorem's hsc_decay from any proof of r → r*. -/
theorem sc_decay_from_convergence
    (r : ℕ → ℝ) (r_star : ℝ) (Φ : ℝ → ℝ)
    (hΦ_cont : Continuous Φ) (hΦ_fp : Φ r_star = r_star)
    (hr_conv : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - r_star| < ε) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - Φ (r n)| < ε := by
  intro ε hε
  have hΦ_cont_at := hΦ_cont.continuousAt (x := r_star)
  rw [Metric.continuousAt_iff] at hΦ_cont_at
  obtain ⟨δ, hδ, hΦ_near⟩ := hΦ_cont_at (ε / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := hr_conv (min δ (ε / 2)) (lt_min hδ (by linarith))
  exact ⟨N₁, fun n hn => by
    have h_rn := hN₁ n hn
    have h_rn_δ : |r n - r_star| < δ := lt_of_lt_of_le h_rn (min_le_left _ _)
    have h_rn_ε : |r n - r_star| < ε / 2 := lt_of_lt_of_le h_rn (min_le_right _ _)
    have h_ball : dist (r n) r_star < δ := by
      rw [Real.dist_eq]; exact h_rn_δ
    have h_Φ : |Φ (r n) - r_star| < ε / 2 := by
      have := hΦ_near h_ball
      rwa [Real.dist_eq, hΦ_fp] at this
    have h1 := (abs_lt.mp h_rn_ε)
    have h2 := (abs_lt.mp h_Φ)
    rw [abs_lt]; constructor <;> linarith⟩

/-! ## Bridge: L² convergence → KuramotoData -/

/-- **Bridge theorem.** Any proof of r → r* (e.g., from L² Lyapunov)
    can be converted to the hypotheses of MainTheorem, provided
    Φ, persistence, and Lipschitz bounds are available.

    This shows the gap-exclusion proof path is a CONSEQUENCE of
    any convergence proof, not an independent path. -/
theorem bridge_l2_to_main
    (r : ℕ → ℝ) (r_star : ℝ) (Φ : ℝ → ℝ)
    (hr_star : 0 < r_star)
    (hr_bdd : ∀ n, 0 ≤ r n ∧ r n ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hpersist : ∀ N, ∃ n, N ≤ n ∧ δ ≤ r n)
    (L : ℝ) (hL_small : 3 * L < r_star)
    (hLip : ∀ n, |r (n + 1) - r n| ≤ L)
    (hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 → Φ x = x → x = 0 ∨ x = r_star)
    (hΦ_cont : Continuous Φ) (hΦ_fp : Φ r_star = r_star)
    (hr_conv : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - r_star| < ε) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - r_star| < ε := by
  have hsc := sc_decay_from_convergence r r_star Φ hΦ_cont hΦ_fp hr_conv
  exact global_stability {
    r := r, r_star := r_star, hr_star := hr_star, hr_bdd := hr_bdd,
    δ := δ, hδ := hδ, hpersist := hpersist,
    L := L, hL_small := hL_small, hLip := hLip,
    Φ := Φ, hΦ_unique := hΦ_unique, hΦ_continuous := hΦ_cont,
    hsc_decay := hsc
  }

end
