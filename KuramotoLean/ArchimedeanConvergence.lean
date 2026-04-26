/-
  Kuramoto Stability — Archimedean Convergence
  ==============================================

  Direct proof that V → 0 using the Archimedean property.
  V monotone + V has no flat spots (additive drop modulus) → V → 0.

  0 sorry.
-/

import KuramotoLean.LaSalleConvergence

open Filter Topology

noncomputable section

private theorem antitone_of_step (V : ℕ → ℝ) (hV : ∀ n, V (n + 1) ≤ V n)
    (a b : ℕ) (hab : a ≤ b) : V b ≤ V a := by
  induction b with
  | zero => simp [show a = 0 from by omega]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hab with heq | hlt
    · rw [heq]
    · exact le_trans (hV k) (ih (by omega))

/-- **Archimedean convergence.** V ≥ 0, V non-increasing, additive drop modulus → V → 0. -/
theorem archimedean_convergence (V : ℕ → ℝ)
    (hV_nn : ∀ n, 0 ≤ V n)
    (hV_anti : ∀ n, V (n + 1) ≤ V n)
    (drop : ℝ → ℝ)
    (hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ)
    (hdrop_bound : ∀ n, ∀ δ > 0, δ ≤ V n → V (n + 1) ≤ V n - drop δ) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → V n < ε := by
  intro ε hε
  by_contra h_not
  push_neg at h_not
  have hV_ge : ∀ n, ε ≤ V n := by
    intro n
    obtain ⟨m, hm, hVm⟩ := h_not n
    exact le_trans hVm (antitone_of_step V hV_anti n m hm)
  have hdrop_each : ∀ n, V (n + 1) ≤ V n - drop ε :=
    fun n => hdrop_bound n ε hε (hV_ge n)
  have hdrop_sum : ∀ k : ℕ, (k : ℝ) * drop ε ≤ V 0 - V k := by
    intro k; induction k with
    | zero => simp
    | succ m ih =>
      have hd := hdrop_each m
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]; linarith
  obtain ⟨k, hk⟩ := Archimedean.arch (V 0) (hdrop_pos ε hε)
  rw [nsmul_eq_mul] at hk
  have h1 := hdrop_sum (k + 1)
  have h2 := hV_nn (k + 1)
  have h3 : ((k + 1 : ℕ) : ℝ) * drop ε = (↑k) * drop ε + drop ε := by push_cast; ring
  have h4 := hdrop_pos ε hε
  linarith

/-- **Archimedean convergence for order parameter.** -/
theorem archimedean_r_convergence (V : ℕ → ℝ) (r : ℕ → ℝ) (r_star : ℝ)
    (hV_nn : ∀ n, 0 ≤ V n)
    (hV_anti : ∀ n, V (n + 1) ≤ V n)
    (drop : ℝ → ℝ)
    (hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ)
    (hdrop_bound : ∀ n, ∀ δ > 0, δ ≤ V n → V (n + 1) ≤ V n - drop δ)
    (hV_controls_r : ∀ n, (r n - r_star) ^ 2 ≤ V n) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |r n - r_star| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := archimedean_convergence V hV_nn hV_anti drop hdrop_pos hdrop_bound
    (ε ^ 2) (by positivity)
  exact ⟨N, fun n hn =>
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt (hV_controls_r n) (hN n hn)) (le_of_lt hε)⟩

end
