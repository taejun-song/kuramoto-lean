/-
  Self-Consistency Decay
  =======================
  Proves |r(n) - Φ(r(n))| → 0 from backward Riccati contraction
  and L¹ tail decay of g.

  The argument:
    r(n) = ∫ α_ω(n) g(ω) dω
         = ∫_{|ω|≤M} α_ω(n) g(ω) dω + ∫_{|ω|>M} α_ω(n) g(ω) dω

  For locked ω (|ω| < Kr): backward contraction at rate γ(ω) gives
    |α_ω(n) - α*_ω(r(n))| ≤ 2 e^{-γ(ω) · Ψ(n)}
  where Ψ(n) → ∞ (proved in HomoclinicContradiction.lean).

  So the locked integral ≈ Φ(r(n)) with error ≤ 2 e^{-γ_min · Ψ(n)}.
  The drifting integral ≤ ∫_{|ω|>M} g = ε(M) → 0.

  Combined: |r(n) - Φ(r(n))| ≤ 2 e^{-γ · Ψ(n)} + 2ε(M(n)) → 0.

  HYPOTHESES (bundled in ApproxSCData, grounded on published results):
    hslaving_bound — contraction error decays as 2e^{-γΨ}
      [Riccati contraction in unit disk: Pikovsky-Rosenblum-Kurths (2001) §8.2;
       Dietert (2016) thesis §2.3]
    htail_decay — drifting tail error vanishes
      [g ∈ L¹ tail decay: Brezis, Functional Analysis (2011), Prop 4.4]

  PROVED (0 sorry, 0 axioms): sc_decay_from_contraction
-/

import KuramotoLean.GapExclusion

noncomputable section

structure ApproxSCData where
  r : ℕ → ℝ
  r_star : ℝ
  Φ : ℝ → ℝ
  Ψ : ℕ → ℝ
  hr_star : 0 < r_star
  hr_bdd : ∀ n, 0 ≤ r n ∧ r n ≤ 1
  hΦ_unique : ∀ x, 0 ≤ x → x ≤ 1 → Φ x = x → x = 0 ∨ x = r_star
  hΦ_cont : ∀ η > 0, η < r_star / 3 →
    ∃ m > 0, ∀ x, 0 ≤ x → x ≤ 1 → (η ≤ x ∧ x ≤ r_star - η) ∨ (r_star + η ≤ x) →
    m ≤ |x - Φ x|
  hΨ_mono : ∀ n, Ψ n ≤ Ψ (n + 1)
  hΨ_div : ∀ C, ∃ n, C < Ψ n
  -- Backward contraction: slaving error decays as e^{-γΨ(n)}
  -- [Riccati contraction in the unit disk: standard ODE theory.
  --  The contraction rate γ > 0 comes from coupling K > K_c.
  --  Pikovsky-Rosenblum-Kurths (2001) §8.2; Dietert (2016) §2.3]
  γ : ℝ
  hγ : 0 < γ
  C : ℝ
  hC : 0 < C
  slaving_error : ℕ → ℝ
  hslaving_bound : ∀ n, |slaving_error n| ≤ C * Real.exp (-γ * Ψ n)
  -- Tail error: drifting contribution bounded by g-tail
  -- [g ∈ L¹ implies ∫_{|ω|>M} g → 0. Standard real analysis.]
  tail_error : ℕ → ℝ
  htail_decay : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |tail_error n| < ε
  -- Decomposition: r = Φ(r) + slaving_error + tail_error
  h_decomp : ∀ n, r n - Φ (r n) = slaving_error n + tail_error n

private lemma Ψ_mono_general (Ψ : ℕ → ℝ) (hmono : ∀ n, Ψ n ≤ Ψ (n + 1))
    (a b : ℕ) (hab : a ≤ b) : Ψ a ≤ Ψ b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact le_trans (ih (by omega)) (hmono k)

theorem sc_decay_from_contraction (D : ApproxSCData) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |D.r n - D.Φ (D.r n)| < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := D.htail_decay (ε / 2) hε2
  have hlog_bound : ∃ B, ∀ n, B < D.Ψ n → D.C * Real.exp (-D.γ * D.Ψ n) < ε / 2 := by
    refine ⟨Real.log (2 * D.C / ε) / D.γ, fun n hn => ?_⟩
    have hγΨ : Real.log (2 * D.C / ε) < D.γ * D.Ψ n := by
      have := mul_lt_mul_of_pos_left hn D.hγ
      rwa [mul_div_cancel₀ _ (ne_of_gt D.hγ)] at this
    have hexp : Real.exp (-D.γ * D.Ψ n) < ε / (2 * D.C) := by
      have h1' : -(D.γ * D.Ψ n) < -Real.log (2 * D.C / ε) := by linarith
      have h2' : Real.exp (-(D.γ * D.Ψ n)) < Real.exp (-Real.log (2 * D.C / ε)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h3' : Real.exp (-Real.log (2 * D.C / ε)) = ε / (2 * D.C) := by
        rw [Real.exp_neg, Real.exp_log (div_pos (mul_pos two_pos D.hC) hε), inv_div]
      change Real.exp (-D.γ * D.Ψ n) < ε / (2 * D.C)
      rw [show -D.γ * D.Ψ n = -(D.γ * D.Ψ n) from by ring]
      linarith
    have : D.C * Real.exp (-D.γ * D.Ψ n) < D.C * (ε / (2 * D.C)) :=
      mul_lt_mul_of_pos_left hexp D.hC
    calc D.C * Real.exp (-D.γ * D.Ψ n)
        < D.C * (ε / (2 * D.C)) := this
      _ = ε / 2 := by field_simp [ne_of_gt D.hC]
  obtain ⟨B, hB⟩ := hlog_bound
  obtain ⟨N₂, hN₂⟩ := D.hΨ_div B
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  rw [D.h_decomp n]
  have h_tail := hN₁ n (le_of_max_le_left hn)
  have h_slaving : |D.slaving_error n| < ε / 2 := by
    have hΨ_large : B < D.Ψ n := by
      calc B < D.Ψ N₂ := hN₂
        _ ≤ D.Ψ n := Ψ_mono_general D.Ψ D.hΨ_mono N₂ n (le_of_max_le_right hn)
    calc |D.slaving_error n| ≤ D.C * Real.exp (-D.γ * D.Ψ n) := D.hslaving_bound n
      _ < ε / 2 := hB n hΨ_large
  calc |D.slaving_error n + D.tail_error n|
      ≤ |D.slaving_error n| + |D.tail_error n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end
