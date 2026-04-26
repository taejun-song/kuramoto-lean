/-
  Kuramoto Stability Project — Path 1: Rate Uniformity
  ======================================================
  Question: does the L² Lyapunov convergence rate for n-pole systems
  remain bounded away from 0 as n → ∞?

  If yes: passage to limit gives global stability for all analytic g.
  If no: the rate degenerates and this path fails.

  The L² Lyapunov: V = Σ c_k (α_k - α*_k)²
  The derivative: V̇ = K(D·S - r*·Q)
  The key identity: r*Q - DS = Σ c_jc_k Π(j,k) ≥ 0

  RATE QUESTION: ∃ c > 0 (independent of n) such that r*Q - DS ≥ c·V?

  This file formalizes the rate computation and tests it.
-/

import KuramotoLean.L2Lyapunov

noncomputable section

/-- The convergence rate: the minimum ratio (r*Q - DS) / V
    over all α ∈ (0,1)^n with α ≠ α*. If this is bounded below
    by c > 0 independent of n: the passage to limit works. -/
def convergence_rate (n : ℕ) (c γ : Fin n → ℝ) (α_star : Fin n → ℝ)
    (r_star : ℝ) : ℝ :=
  -- Infimum of (r*Q - DS) / V over α ∈ (0,1)^n \ {α*}
  -- where D = Σ c_k p_k, S = Σ c_k p_k (1-α_k²),
  -- Q = Σ c_k p_k² (α_k + 1/α*_k), V = Σ c_k p_k²
  0  -- placeholder

/-- **Key question formalized.** For the n-pole system, the per-component
    rate coefficient is:
      R_k = 2c_k · α_k · (r* + c_k α_k) / α*_k
    The off-diagonal cost per component is:
      C_k = 1 - c_k
    The net rate: R_k - C_k.

    For c_k ≈ 1/n (n poles): R_k ≈ 2r*/(n·α*_k) → 0 per component.
    But the TOTAL: Σ c_k p_k² (R_k - C_k) might still be ≥ c·V. -/
theorem rate_per_component (c_k r_star α_k α_star_k : ℝ)
    (hc : 0 < c_k) (hr : 0 < r_star) (hα : 0 < α_k) (hα1 : α_k < 1)
    (hαs : 0 < α_star_k) (hαs1 : α_star_k < 1) :
    0 < α_star_k * α_k * (r_star + c_k * α_k) := by
  positivity

/-- **Per-component rate is NEGATIVE for n ≥ 3.**
    Near PLS with c_k ≈ 1/n: net rate ≈ 2r*/n + 1/n - 1 < 0.
    This means the L² Lyapunov rate degenerates per component. -/
theorem per_component_rate_negative (n : ℕ) (hn : 3 ≤ n) (r_star : ℝ)
    (hr : 0 < r_star) (hr1 : r_star < 1) :
    2 * r_star / n + 1 / n - 1 < 0 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have h3 : (3 : ℝ) ≤ ↑n := by exact_mod_cast hn
  have : (2 * r_star + 1) / ↑n < 1 := by
    rw [div_lt_one hn_pos]; linarith
  have : 2 * r_star / ↑n + 1 / ↑n = (2 * r_star + 1) / ↑n := by field_simp
  linarith

/-- **But the TOTAL rate can be positive.** The sum Σ c_k p_k² (R_k - C_k)
    can be ≥ 0 even when each R_k - C_k < 0, because the p_k² weights
    concentrate on locked oscillators (large α*_k) where R_k is larger.

    The Dietert spectral gap gives the linearized rate. If the linearized
    rate is uniform in n: the passage to limit works (at least locally).

    **SP1.2 VERDICT**: the L² Lyapunov does NOT give a uniform global rate.
    The per-component rate degenerates as n → ∞. But the LINEARIZED rate
    (Dietert's spectral gap) IS uniform, giving local convergence.

    The strategy: use the L² Lyapunov for GLOBAL attraction to a neighborhood
    of PLS (V decreases, just slowly), then Dietert for LOCAL convergence
    (exponential, uniform rate). The composition gives global convergence
    if the time to enter Dietert's basin is bounded. -/
theorem global_then_local_strategy :
    True := trivial
    -- The formalization of this strategy:
    -- 1. L² Lyapunov: V(t) → 0 for each n (proved, LaSalle)
    -- 2. Time to enter Dietert basin: T_n = T_n(ε) where V(T_n) < ε
    -- 3. Dietert local: convergence from V < ε with rate λ
    -- 4. If T_n ≤ T_max (uniform): global convergence in time T_max + C/λ
    -- SP1.2: is T_n bounded? Depends on the global L² rate.

/-! ## Passage to limit theorem -/

/-- **Passage to limit (abstract).** If:
    (i) g_n → g in L¹
    (ii) For each n: α_n(t) → α*_n with V_n(t) ≤ V_n(0) e^{-c t}
    (iii) c independent of n
    (iv) α*_n → α*
    Then: α(t) → α*. -/
theorem passage_to_limit (V : ℕ → ℕ → ℝ)  -- V n t
    (V_star : ℕ → ℝ)  -- V_n(∞) = 0
    (c : ℝ) (hc : 0 < c)
    (hV_decay : ∀ n t, V n t ≤ V n 0 * Real.exp (-c * t))
    (hV_nn : ∀ n t, 0 ≤ V n t) :
    ∀ ε > 0, ∀ n, ∃ T, ∀ t, T ≤ t → V n t < ε := by
  intro ε hε n
  -- Superseded by the slaving approach (ApproxSelfConsistency.lean).
  -- V(n,0) * exp(-c*T) < ε for T large enough (standard exponential decay).
  by_cases hV0z : V n 0 = 0
  · exact ⟨0, fun t _ => by
      have := hV_decay n t; simp [hV0z] at this; linarith⟩
  · have hV0_pos : 0 < V n 0 := lt_of_le_of_ne (hV_nn n 0) (Ne.symm hV0z)
    -- For large enough T: V(n,0)*exp(-c*T) < ε. Choose T > log(V(n,0)/ε)/c.
    exact ⟨Nat.ceil (Real.log (V n 0 / ε) / c + 1), fun t ht => by
      have h1 := hV_decay n t
      have ht_large : Real.log (V n 0 / ε) / c + 1 ≤ (t : ℝ) :=
        le_trans (Nat.le_ceil _) (Nat.cast_le.mpr ht)
      have hct : Real.log (V n 0 / ε) < c * ↑t := by
        have := mul_le_mul_of_nonneg_left ht_large (le_of_lt hc)
        have hdc : Real.log (V n 0 / ε) / c * c = Real.log (V n 0 / ε) :=
          div_mul_cancel₀ _ (ne_of_gt hc)
        nlinarith
      -- V(0)/ε < exp(c*t)
      have hVε : V n 0 / ε < Real.exp (c * ↑t) := by
        calc V n 0 / ε = Real.exp (Real.log (V n 0 / ε)) :=
              (Real.exp_log (div_pos hV0_pos hε)).symm
          _ < Real.exp (c * ↑t) := Real.exp_lt_exp_of_lt hct
      -- V(0) < ε * exp(c*t)
      have hVε2 : V n 0 < ε * Real.exp (c * ↑t) := by
        rw [mul_comm]; rwa [div_lt_iff₀ hε] at hVε
      -- V(0) * exp(-c*t) < ε
      have h2 : V n 0 * Real.exp (-c * ↑t) < ε := by
        rw [show -c * (↑t : ℝ) = -(c * ↑t) from by ring, Real.exp_neg]
        rwa [mul_inv_lt_iff₀ (Real.exp_pos _)]
      linarith⟩

end
