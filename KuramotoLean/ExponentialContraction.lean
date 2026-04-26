/-
  Exponential Contraction (Discrete)
  ====================================
  If a non-negative sequence satisfies f(n+1) ≤ c·f(n) with 0 ≤ c,
  then f(n) ≤ f(0)·c^n.

  This provides the discrete-time analogue of the Riccati contraction
  that underlies hslaving_bound.

  0 sorry.
-/

import Mathlib.Tactic

noncomputable section

/-- Geometric decay: if f(n+1) ≤ c·f(n) with 0 ≤ c, then f(n) ≤ f(0)·c^n. -/
private theorem geometric_decay (f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ n, 0 ≤ f n)
    (hstep : ∀ n, f (n + 1) ≤ c * f n) :
    ∀ n, f n ≤ f 0 * c ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    calc f (k + 1) ≤ c * f k := hstep k
      _ ≤ c * (f 0 * c ^ k) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = f 0 * c ^ (k + 1) := by ring

/-- Geometric decay with rate < 1 implies convergence to 0. -/
theorem geometric_decay_to_zero (f : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hc1 : c < 1)
    (hf : ∀ n, 0 ≤ f n)
    (hstep : ∀ n, f (n + 1) ≤ c * f n) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → f n < ε := by
  intro ε hε
  have hdecay := geometric_decay f c hc hf hstep
  have hf0 : 0 ≤ f 0 := hf 0
  by_cases hf0_pos : f 0 = 0
  · exact ⟨0, fun n _ => by
      have := hdecay n
      rw [hf0_pos, zero_mul] at this
      linarith [hf n]⟩
  · have hf0_pos : 0 < f 0 := lt_of_le_of_ne hf0 (Ne.symm hf0_pos)
    have := Filter.Tendsto.mul_const (f 0)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1)
    rw [zero_mul] at this
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N, hN⟩ := this ε hε
    exact ⟨N, fun n hn => by
      have hd := hdecay n
      have hNn := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hNn
      linarith⟩

end
