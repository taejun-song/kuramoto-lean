/-
  Kuramoto Stability — LaSalle Convergence
  ==========================================

  LaSalle-type argument for V → 0 using strict Lyapunov decrease.

  HYPOTHESES:
    1. V ≥ 0, V continuous, V non-increasing along flow
    2. V(x) = 0 iff x = x* (definiteness)
    3. V' < 0 when V > 0 (strict decrease, from StrictLyapunov)
    4. Trajectory is precompact (from persistence + boundedness)

  CONCLUSION: V(t) → 0, hence x(t) → x*.

  The discrete-time version: V : ℕ → ℝ with V(n+1) < V(n) when V(n) > 0.
  Combined with V ≥ 0 and bounded monotone convergence: V → L ≥ 0.
  If L > 0, then V(n) > L > 0 for all n, so V(n+1) < V(n) strictly.
  But this alone doesn't give V → 0 without a rate bound.

  The key: precompactness + continuity of the decrease gives a UNIFORM
  lower bound on the drop size. If V(n) ∈ [L, L+ε] for all large n
  (since V → L), then the drop V(n) - V(n+1) ≥ f(L) > 0 uniformly.
  After N steps: V decreases by at least N·f(L), contradicting V ≥ L.

  We formalize this as a structure + theorem.

  0 sorry.
-/

import KuramotoLean.StrictLyapunov

noncomputable section

/-! ## LaSalle convergence for discrete sequences -/

/-- **LaSalle convergence data.**
    V non-increasing, V ≥ 0, and V(n+1) < V(n) when V(n) > 0,
    with a modulus of decrease: when V(n) ≥ δ, V drops by ≥ f(δ). -/
structure LaSalleData where
  V : ℕ → ℝ
  hV_nn : ∀ n, 0 ≤ V n
  hV_mono : ∀ n, V (n + 1) ≤ V n
  hV_strict : ∀ n, 0 < V n → V (n + 1) < V n
  drop : ℝ → ℝ
  hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ
  hdrop_bound : ∀ n, ∀ δ, 0 < δ → δ ≤ V n →
    drop δ ≤ V n - V (n + 1)

/-- **LaSalle convergence.** V(n) → 0. -/
theorem lasalle_convergence (D : LaSalleData) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → D.V n < ε := by
  intro ε hε
  by_contra h
  push Not at h
  -- For all N, ∃ n ≥ N with V(n) ≥ ε
  -- Since V is non-increasing, V(n) ≥ ε for all n ≤ first such n
  -- Actually, since V is non-increasing and V(n₀) ≥ ε for some n₀ ≥ N,
  -- we have V(n) ≥ ε for all n ≤ n₀. But we want V(n) ≥ ε for all n.
  -- Since V is non-increasing: V(0) ≥ V(1) ≥ .... If V(n) ≥ ε for all n,
  -- then the drops accumulate.
  have hV_mono_le : ∀ a b : ℕ, a ≤ b → D.V b ≤ D.V a := by
    intro a b hab
    induction b with
    | zero => simp [show a = 0 from by omega]
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact le_refl _
      · exact le_trans (D.hV_mono k) (ih (by omega))
  have hV_ge : ∀ n, ε ≤ D.V n := by
    intro n
    obtain ⟨m, hm, hVm⟩ := h n
    linarith [hV_mono_le n m hm]
  -- Now V(n) ≥ ε for all n. The drop at each step is ≥ drop(ε) > 0.
  have hd := D.hdrop_pos ε hε
  have h_drop_each : ∀ n, D.drop ε ≤ D.V n - D.V (n + 1) :=
    fun n => D.hdrop_bound n ε hε (hV_ge n)
  -- After k steps: V(0) - V(k) ≥ k · drop(ε)
  have h_sum : ∀ k : ℕ, (k : ℝ) * D.drop ε ≤ D.V 0 - D.V k := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have := h_drop_each m
      calc ((m + 1 : ℕ) : ℝ) * D.drop ε
          = (m : ℝ) * D.drop ε + D.drop ε := by push_cast; ring
        _ ≤ (D.V 0 - D.V m) + (D.V m - D.V (m + 1)) := add_le_add ih this
        _ = D.V 0 - D.V (m + 1) := by ring
  -- Choose k large enough that k · drop(ε) > V(0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.V 0 < (k : ℝ) * D.drop ε := by
    obtain ⟨k, hk⟩ := Archimedean.arch (D.V 0) hd
    have hk' : D.V 0 ≤ (k : ℝ) * D.drop ε := by rwa [nsmul_eq_mul] at hk
    exact ⟨k + 1, by push_cast; linarith⟩
  -- Contradiction: V(0) - V(k) ≥ k·drop(ε) > V(0), so V(k) < 0
  linarith [h_sum k, D.hV_nn k]

end
