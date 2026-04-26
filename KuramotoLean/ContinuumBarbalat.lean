/-
  Kuramoto Stability — Continuous Barbalat from Persistence Drops
  ================================================================
  If V : ℝ → ℝ is non-negative, antitone, and drops by a factor
  q < 1 infinitely often, then V → 0.

  This is the continuous-time analogue of barbalat_from_persistence
  (NPoleGlobalStability.lean). Combined with pair coercivity
  (PairCoercivity.lean), it closes the Lyapunov gap: V∞ → 0.

  0 sorry.
-/
import KuramotoLean.AntitoneConvergence

open Filter Topology

noncomputable section

/-! ## Continuous Barbalat from persistence drops

If V ≥ 0 is antitone and drops by factor q < 1 at times
t₁ < t₂ < ⋯, then V → 0.

Proof: choose t_{k+1} ≥ t_k + 1. After k drops:
  V(s) ≤ q^k · V(0)  for all s ≥ t_k + 1
Since q^k → 0, V → 0. -/

/-- **Continuous Barbalat via persistence drops (ε-δ form).**
    V ≥ 0, V antitone, and V(t+1) ≤ q·V(t) infinitely often
    ⟹ V → 0. -/
theorem continuous_barbalat_persistence (V : ℝ → ℝ) (q : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t) (hV_anti : Antitone V)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + 1) ≤ q * V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → V s < ε := by
  suffices h : ∀ k : ℕ, ∃ T : ℝ, ∀ s, T ≤ s → V s ≤ q ^ k * V 0 by
    intro ε hε
    by_cases hV0 : V 0 = 0
    · exact ⟨0, fun s hs => by linarith [hV_anti hs, hV_nn s]⟩
    · have hV0_pos : 0 < V 0 := lt_of_le_of_ne (hV_nn 0) (Ne.symm hV0)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hV0_pos) hq1
      obtain ⟨T, hT⟩ := h k
      exact ⟨T, fun s hs => by
        calc V s ≤ q ^ k * V 0 := hT s hs
          _ < ε / V 0 * V 0 := mul_lt_mul_of_pos_right hk hV0_pos
          _ = ε := div_mul_cancel₀ ε (ne_of_gt hV0_pos)⟩
  intro k
  induction k with
  | zero =>
    exact ⟨0, fun s hs => by simp only [pow_zero, one_mul]; exact hV_anti hs⟩
  | succ k ih =>
    obtain ⟨T, hT⟩ := ih
    obtain ⟨t, ht, hdrop⟩ := hpersist T
    exact ⟨t + 1, fun s hs => by
      calc V s ≤ V (t + 1) := hV_anti hs
        _ ≤ q * V t := hdrop
        _ ≤ q * (q ^ k * V 0) := mul_le_mul_of_nonneg_left (hT t ht) hq0
        _ = q ^ (k + 1) * V 0 := by ring⟩

/-- **Continuous Barbalat (Filter.Tendsto form).** -/
theorem continuous_barbalat_tendsto (V : ℝ → ℝ) (q : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t) (hV_anti : Antitone V)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + 1) ≤ q * V t) :
    Tendsto V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuous_barbalat_persistence V q hV_nn hV_anti
    hq0 hq1 hpersist ε hε
  exact ⟨T, fun s hs => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (hV_nn s)]
    exact hT s hs⟩

/-! ## Application to Lyapunov convergence -/

/-- **Lyapunov function converges to zero from persistence drops.** -/
theorem LyapunovConvergence.zero_from_drops
    (D : LyapunovConvergence) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧ D.V (t + 1) ≤ q * D.V t) :
    Tendsto D.V atTop (nhds 0) :=
  continuous_barbalat_tendsto D.V q D.hV_nn D.hV_anti hq0 hq1 hdrops

/-! ## Generalized drop interval

The unit interval is not essential. If drops occur over intervals
of length Δ > 0, rescale time. -/

/-- **Barbalat with general drop interval Δ.** -/
theorem continuous_barbalat_general (V : ℝ → ℝ) (q Δ : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t) (hV_anti : Antitone V)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (_hΔ : 0 < Δ)
    (hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + Δ) ≤ q * V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → V s < ε := by
  suffices h : ∀ k : ℕ, ∃ T : ℝ, ∀ s, T ≤ s → V s ≤ q ^ k * V 0 by
    intro ε hε
    by_cases hV0 : V 0 = 0
    · exact ⟨0, fun s hs => by linarith [hV_anti hs, hV_nn s]⟩
    · have hV0_pos : 0 < V 0 := lt_of_le_of_ne (hV_nn 0) (Ne.symm hV0)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hV0_pos) hq1
      obtain ⟨T, hT⟩ := h k
      exact ⟨T, fun s hs => by
        calc V s ≤ q ^ k * V 0 := hT s hs
          _ < ε / V 0 * V 0 := mul_lt_mul_of_pos_right hk hV0_pos
          _ = ε := div_mul_cancel₀ ε (ne_of_gt hV0_pos)⟩
  intro k
  induction k with
  | zero =>
    exact ⟨0, fun s hs => by simp only [pow_zero, one_mul]; exact hV_anti hs⟩
  | succ k ih =>
    obtain ⟨T, hT⟩ := ih
    obtain ⟨t, ht, hdrop⟩ := hpersist T
    exact ⟨t + Δ, fun s hs => by
      calc V s ≤ V (t + Δ) := hV_anti hs
        _ ≤ q * V t := hdrop
        _ ≤ q * (q ^ k * V 0) := mul_le_mul_of_nonneg_left (hT t ht) hq0
        _ = q ^ (k + 1) * V 0 := by ring⟩

end
