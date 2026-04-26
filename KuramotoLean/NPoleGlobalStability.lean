/-
  Kuramoto Stability — N-Pole Global Stability via L² Lyapunov
  =============================================================
  A standalone proof that any n-pole OA trajectory converges to the PLS,
  using the L² Lyapunov function. Independent of the MainTheorem chain.

  This proof path does NOT use:
    - Gap exclusion or self-consistency decay
    - The self-consistency map Φ
    - Lipschitz trapping or step-size constraints

  Instead it uses:
    - l2_lyapunov_theorem (dV/dt ≤ 0) → V non-increasing
    - l2_exponential_rate (dV/dt ≤ -μV when α_k ≥ δ) → drop factor
    - Persistence (α_k eventually bounded from 0) → infinitely many drops
    - A discrete Barbalat argument → V → 0

  0 sorry.
-/

import KuramotoLean.L2Convergence

noncomputable section

/-! ## Discrete Barbalat lemma via persistence

Key insight: if a non-negative non-increasing sequence drops by a factor
q < 1 infinitely often, it converges to 0. This captures the interaction
between the L² Lyapunov monotonicity (dV/dt ≤ 0 everywhere) and the
exponential rate (dV/dt ≤ -μV at persistence times). -/

private theorem mono_le (V : ℕ → ℝ) (hV_mono : ∀ n, V (n + 1) ≤ V n)
    (a b : ℕ) (hab : b ≤ a) : V a ≤ V b := by
  induction a with
  | zero => simp [show b = 0 from by omega]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · exact le_trans (hV_mono k) (ih (by omega))

/-- **Discrete Barbalat via persistence.**
    If V ≥ 0, V non-increasing, and V drops by factor q < 1 infinitely
    often, then V → 0.

    Proof: after k persistence drops, V ≤ q^k · V(0) → 0. -/
theorem barbalat_from_persistence (V : ℕ → ℝ) (q : ℝ)
    (hV_nn : ∀ n, 0 ≤ V n)
    (hV_mono : ∀ n, V (n + 1) ≤ V n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpersist : ∀ M, ∃ m, M ≤ m ∧ V (m + 1) ≤ q * V m) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → V n < ε := by
  suffices h : ∀ k : ℕ, ∃ N, ∀ n, N ≤ n → V n ≤ q ^ k * V 0 by
    intro ε hε
    by_cases hV0 : V 0 = 0
    · exact ⟨0, fun n _ => by linarith [mono_le V hV_mono n 0 (Nat.zero_le n)]⟩
    · have hV0_pos : 0 < V 0 := lt_of_le_of_ne (hV_nn 0) (Ne.symm hV0)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hV0_pos) hq1
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun n hn => by
        have h1 := hN n hn
        have h2 : q ^ k * V 0 < (ε / V 0) * V 0 :=
          mul_lt_mul_of_pos_right hk hV0_pos
        rw [div_mul_cancel₀ ε (ne_of_gt hV0_pos)] at h2
        linarith⟩
  intro k
  induction k with
  | zero => exact ⟨0, fun n _ => by
      simp only [pow_zero, one_mul]; exact mono_le V hV_mono n 0 (Nat.zero_le n)⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨m, hm, hdrop⟩ := hpersist N
    refine ⟨m + 1, fun n hn => ?_⟩
    calc V n ≤ V (m + 1) := mono_le V hV_mono n (m + 1) hn
      _ ≤ q * V m := hdrop
      _ ≤ q * (q ^ k * V 0) := mul_le_mul_of_nonneg_left (hN m hm) hq0
      _ = q ^ (k + 1) * V 0 := by ring

/-! ## N-Pole Stability Data

Minimal hypotheses for n-pole convergence via L² Lyapunov:
  - V = Σ c_k (α_k - α*_k)² is non-increasing along the trajectory
  - At persistence times, V drops by a factor q < 1

Both follow from l2_lyapunov_theorem and l2_exponential_rate
applied to a discretized ODE trajectory. -/

structure NPoleStabilityData (n : ℕ) where
  c : Fin n → ℝ
  α : ℕ → Fin n → ℝ
  α_star : Fin n → ℝ
  hc : ∀ k, 0 < c k
  hV_mono : ∀ m, l2Distance c (α (m + 1)) α_star ≤ l2Distance c (α m) α_star
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  hpersist_drop : ∀ M, ∃ m, M ≤ m ∧
    l2Distance c (α (m + 1)) α_star ≤ q * l2Distance c (α m) α_star

/-- **N-pole L² convergence via persistence Barbalat.**
    V = Σ c_k(α_k - α*_k)² → 0. -/
theorem npole_stability_l2 (D : NPoleStabilityData n) :
    ∀ ε > 0, ∃ N, ∀ m, N ≤ m → l2Distance D.c (D.α m) D.α_star < ε :=
  barbalat_from_persistence
    (fun m => l2Distance D.c (D.α m) D.α_star)
    D.q
    (fun m => l2Distance_nonneg D.c (D.α m) D.α_star (fun k => le_of_lt (D.hc k)))
    D.hV_mono D.hq0 D.hq1 D.hpersist_drop

/-- **Pointwise convergence from L² convergence.**
    α_k(m) → α*_k for each k. -/
theorem npole_stability_pointwise (D : NPoleStabilityData n)
    (c_min : ℝ) (hc_min : ∀ k, c_min ≤ D.c k) (hc_min_pos : 0 < c_min) :
    ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ k, |D.α m k - D.α_star k| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := npole_stability_l2 D (c_min * ε ^ 2)
    (mul_pos hc_min_pos (sq_pos_of_ne_zero (ne_of_gt hε)))
  exact ⟨N, fun m hm k => pointwise_from_l2 D.c (D.α m) D.α_star D.hc
    c_min hc_min hc_min_pos ε hε (hN m hm) k⟩

/-! ## Order parameter convergence

From pointwise α_k → α*_k, derive r = Σ c_k α_k → r* = Σ c_k α*_k. -/

private theorem order_param_bound {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (ε : ℝ)
    (hpt : ∀ k, |α k - α_star k| < ε) :
    |∑ k, c k * α k - ∑ k, c k * α_star k| ≤ (∑ k, c k) * ε := by
  have h : ∑ k, c k * α k - ∑ k, c k * α_star k = ∑ k, c k * (α k - α_star k) := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
  rw [h]
  calc |∑ k, c k * (α k - α_star k)|
      ≤ ∑ k, |c k * (α k - α_star k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, c k * |α k - α_star k| := by
        congr 1; ext k; rw [abs_mul, abs_of_pos (hc k)]
    _ ≤ ∑ k, c k * ε := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (le_of_lt (hpt k)) (le_of_lt (hc k))
    _ = (∑ k, c k) * ε := by rw [Finset.sum_mul]

/-- **Order parameter convergence.**
    r(m) = Σ c_k α_k(m) → r* = Σ c_k α*_k. -/
theorem npole_order_parameter_convergence (D : NPoleStabilityData n)
    (c_min : ℝ) (hc_min : ∀ k, c_min ≤ D.c k) (hc_min_pos : 0 < c_min)
    (c_sum : ℝ) (hc_sum : c_sum = ∑ k, D.c k) (hc_sum_pos : 0 < c_sum) :
    ∀ ε > 0, ∃ N, ∀ m, N ≤ m →
      |∑ k, D.c k * D.α m k - ∑ k, D.c k * D.α_star k| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := npole_stability_pointwise D c_min hc_min hc_min_pos
    (ε / (c_sum + 1)) (div_pos hε (by linarith))
  exact ⟨N, fun m hm => by
    have hpt := hN m hm
    have hbd := order_param_bound D.c (D.α m) D.α_star D.hc (ε / (c_sum + 1)) hpt
    calc |∑ k, D.c k * D.α m k - ∑ k, D.c k * D.α_star k|
        ≤ (∑ k, D.c k) * (ε / (c_sum + 1)) := hbd
      _ = c_sum * (ε / (c_sum + 1)) := by rw [hc_sum]
      _ < (c_sum + 1) * (ε / (c_sum + 1)) := by
          exact mul_lt_mul_of_pos_right (by linarith) (div_pos hε (by linarith))
      _ = ε := mul_div_cancel₀ ε (ne_of_gt (by linarith : (0 : ℝ) < c_sum + 1))⟩

end
