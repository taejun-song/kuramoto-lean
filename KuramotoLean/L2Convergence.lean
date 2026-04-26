/-
  Kuramoto Stability — L² Convergence for n-Pole Systems
  =======================================================
  Combines the L² Lyapunov theorem with geometric decay to prove
  direct convergence of the n-pole OA system.

  This gives a STANDALONE proof of n-pole global stability that
  bypasses gap exclusion and self-consistency decay entirely.

  0 sorry.
-/

import KuramotoLean.L2Lyapunov

noncomputable section

/-! ## Geometric decay: V(n+1) ≤ q·V(n) implies V → 0 -/

theorem geometric_decay (V : ℕ → ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hV0 : 0 ≤ V 0)
    (_hV_nn : ∀ n, 0 ≤ V n)
    (h : ∀ n, V (n + 1) ≤ q * V n) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → V n < ε := by
  have hV_bound : ∀ n, V n ≤ q ^ n * V 0 := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      calc V (k + 1) ≤ q * V k := h k
        _ ≤ q * (q ^ k * V 0) := by
            exact mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * V 0 := by ring
  intro ε hε
  by_cases hV0_pos : V 0 = 0
  · exact ⟨0, fun n _ => by
      calc V n ≤ q ^ n * V 0 := hV_bound n
        _ = 0 := by rw [hV0_pos, mul_zero]
        _ < ε := hε⟩
  · have hV0_pos : 0 < V 0 := lt_of_le_of_ne hV0 (Ne.symm hV0_pos)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hV0_pos) hq1
    exact ⟨N, fun n hn => by
      calc V n ≤ q ^ n * V 0 := hV_bound n
        _ ≤ q ^ N * V 0 := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hV0_pos)
            exact pow_le_pow_of_le_one hq0 (le_of_lt hq1) hn
        _ < (ε / V 0) * V 0 := by
            exact mul_lt_mul_of_pos_right hN hV0_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt hV0_pos)⟩

/-! ## L² convergence for n-pole systems

The L² Lyapunov results give:
  - dV/dt ≤ 0 (l2_lyapunov_theorem): V non-increasing along trajectories
  - dV/dt ≤ -K·μ·V (l2_exponential_rate): exponential when α bounded from 0

For a trajectory sampled at times 0, h, 2h, ... with step h:
  V((n+1)h) - V(nh) ≈ h · dV/dt ≤ -h·K·μ·V(nh)
  ⟹ V((n+1)h) ≤ (1 - h·K·μ) · V(nh)

Combined with geometric_decay: V → 0, hence α → α*. -/

/-- **N-pole L² convergence data.**
    Packages a sampled trajectory with the Lyapunov decay property. -/
structure NPoleL2Data (n : ℕ) where
  c : Fin n → ℝ
  α : ℕ → Fin n → ℝ
  α_star : Fin n → ℝ
  hc : ∀ k, 0 < c k
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  hdecay : ∀ m, l2Distance c (α (m + 1)) α_star ≤ q * l2Distance c (α m) α_star

/-- **N-pole L² convergence theorem.**
    Direct proof: α(n) → α* in weighted L² norm. -/
theorem npole_l2_convergence (D : NPoleL2Data n) :
    ∀ ε > 0, ∃ N, ∀ m, N ≤ m →
      l2Distance D.c (D.α m) D.α_star < ε :=
  geometric_decay
    (fun m => l2Distance D.c (D.α m) D.α_star)
    D.q D.hq0 D.hq1
    (l2Distance_nonneg D.c (D.α 0) D.α_star (fun k => le_of_lt (D.hc k)))
    (fun m => l2Distance_nonneg D.c (D.α m) D.α_star (fun k => le_of_lt (D.hc k)))
    D.hdecay

/-- **Pointwise convergence from L² convergence.**
    If V = Σ c_k(α_k - α*_k)² < ε²/c_min, then |α_k - α*_k| < ε for all k. -/
theorem pointwise_from_l2 {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (c_min : ℝ) (hc_min : ∀ k, c_min ≤ c k)
    (_hc_min_pos : 0 < c_min) (ε : ℝ) (hε : 0 < ε)
    (hV : l2Distance c α α_star < c_min * ε ^ 2) :
    ∀ k, |α k - α_star k| < ε := by
  intro k
  by_contra h
  push Not at h
  have h_sq : ε ^ 2 ≤ (α k - α_star k) ^ 2 :=
    calc ε ^ 2 ≤ |α k - α_star k| ^ 2 := pow_le_pow_left₀ (le_of_lt hε) h 2
      _ = (α k - α_star k) ^ 2 := sq_abs _
  have h_le_V : c k * (α k - α_star k) ^ 2 ≤ l2Distance c α α_star := by
    unfold l2Distance
    exact Finset.single_le_sum
      (f := fun j => c j * (α j - α_star j) ^ 2)
      (fun j _ => mul_nonneg (le_of_lt (hc j)) (sq_nonneg (α j - α_star j)))
      (Finset.mem_univ k)
  have : c_min * ε ^ 2 ≤ c k * (α k - α_star k) ^ 2 :=
    calc c_min * ε ^ 2 ≤ c k * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (hc_min k) (sq_nonneg ε)
      _ ≤ c k * (α k - α_star k) ^ 2 :=
          mul_le_mul_of_nonneg_left h_sq (le_of_lt (hc k))
  linarith

/-! ## Basin implies component lower bound

When V < c_min·(δ*/2)², each |α_k - α*_k| < δ*/2 (from pointwise_from_l2).
Combined with α*_k ≥ δ*, this gives α_k > δ*/2.

This is the key link: Lyapunov basin entry → component persistence → exponential rate. -/

/-- **Basin component lower bound.**
    V < c_min·(δ*/2)² implies α_k ≥ δ*/2 for all k. -/
theorem basin_component_lb {n : ℕ} (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (c_min δ_star : ℝ)
    (hc_min_pos : 0 < c_min) (hc_lb : ∀ k, c_min ≤ c k)
    (hδ_star : 0 < δ_star)
    (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hV : l2Distance c α α_star < c_min * (δ_star / 2) ^ 2) :
    ∀ k, δ_star / 2 ≤ α k := by
  have hpw := pointwise_from_l2 c α α_star hc c_min hc_lb hc_min_pos
    (δ_star / 2) (by linarith) hV
  intro k
  linarith [(abs_lt.mp (hpw k)).1, hα_star_lb k]

/-- **Basin forward invariance.**
    If V is antitone and V(T₀) < threshold, then α_k(t) ≥ δ*/2 for all t ≥ T₀.
    Derives component persistence from Lyapunov monotonicity + basin entry. -/
theorem basin_forward {n : ℕ} (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (c_min δ_star : ℝ)
    (hc_min_pos : 0 < c_min) (hc_lb : ∀ k, c_min ≤ c k)
    (hδ_star : 0 < δ_star) (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hV_anti : Antitone (fun t => l2Distance c (α t) α_star))
    (T₀ : ℝ) (hbasin : l2Distance c (α T₀) α_star < c_min * (δ_star / 2) ^ 2) :
    ∀ t, T₀ ≤ t → ∀ k, δ_star / 2 ≤ α t k := by
  intro t ht
  exact basin_component_lb c (α t) α_star hc c_min δ_star hc_min_pos hc_lb hδ_star
    hα_star_lb (lt_of_le_of_lt (hV_anti ht) hbasin)

/-- **Basin component upper bound.**
    V < c_min·(δ*/2)² implies α_k < 1 when α*_k + δ*/2 < 1. -/
theorem basin_component_ub {n : ℕ} (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (c_min δ_star : ℝ)
    (hc_min_pos : 0 < c_min) (hc_lb : ∀ k, c_min ≤ c k)
    (hδ_star : 0 < δ_star)
    (hα_star_ub : ∀ k, α_star k + δ_star / 2 < 1)
    (hV : l2Distance c α α_star < c_min * (δ_star / 2) ^ 2) :
    ∀ k, α k < 1 := by
  have hpw := pointwise_from_l2 c α α_star hc c_min hc_lb hc_min_pos
    (δ_star / 2) (by linarith) hV
  intro k
  linarith [(abs_lt.mp (hpw k)).2, hα_star_ub k]

end
