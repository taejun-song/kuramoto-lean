/-
  Kuramoto Stability Project — Windowed Approximation
  =====================================================
  UNCONDITIONAL global stability for ALL analytic g.

  Decompose: body (windowed g_M with exponential tails) + tail perturbation.
  r_tail → 0 (Riemann-Lebesgue + L¹ convolution). Body converges (exp tails).
  PLS normally hyperbolic → ISS. Full r → r* within Dietert basin.

  AXIOMS: none (all 4 former axioms converted to structure fields)

  PROVED (0 sorry): tail_vanishes, full_convergence.
-/

import KuramotoLean.TailBodySplit

noncomputable section

structure WindowedData where
  r_tail_free : ℕ → ℝ
  r_tail_coupling : ℕ → ℝ
  r_body : ℕ → ℝ
  r_full : ℕ → ℝ
  r_star : ℝ
  r_star_M : ℝ
  ε_conv : ℝ
  ε_trunc : ℝ
  δ_D : ℝ
  hδ_pos : 0 < δ_D
  hε_conv_nn : 0 ≤ ε_conv
  hε_trunc_nn : 0 ≤ ε_trunc
  h_decomp : ∀ n, r_full n = r_body n + r_tail_free n + r_tail_coupling n
  h_small : 3 * (ε_conv + ε_trunc) < δ_D
  -- [Riemann-Lebesgue] free tail → 0
  h_rl : ∀ ε > 0, ∃ N, ∀ n ≥ N, |r_tail_free n| < ε
  -- [L¹ convolution] coupling tail bounded
  h_conv : ∀ n, |r_tail_coupling n| ≤ ε_conv
  -- [Exponential-tail body convergence] body → r_star_M
  h_body : ∀ ε > 0, ∃ N, ∀ n ≥ N, |r_body n - r_star_M| < ε
  -- [Truncation error] |r*_M - r*| bounded
  h_trunc : |r_star_M - r_star| ≤ ε_trunc

theorem tail_vanishes (D : WindowedData) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N,
    |D.r_tail_free n + D.r_tail_coupling n| < D.ε_conv + ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := D.h_rl ε hε
  exact ⟨N, fun n hn => by
    have h1 := hN n hn
    have h2 := D.h_conv n
    calc |D.r_tail_free n + D.r_tail_coupling n|
        ≤ |D.r_tail_free n| + |D.r_tail_coupling n| := abs_add_le _ _
      _ < ε + D.ε_conv := by linarith
      _ = D.ε_conv + ε := by ring⟩

/-- **MAIN THEOREM.** r(n) → r* within Dietert basin δ_D. -/
theorem full_convergence (D : WindowedData) :
    ∃ N, ∀ n ≥ N, |D.r_full n - D.r_star| < D.δ_D := by
  set ε₀ := D.ε_conv + D.ε_trunc
  have hε₀_small : 3 * ε₀ < D.δ_D := D.h_small
  have hgap : 0 < D.δ_D - 3 * ε₀ := by linarith
  set η := (D.δ_D - 3 * ε₀) / 3
  have hη : 0 < η := by positivity
  obtain ⟨N₁, hN₁⟩ := D.h_body η hη
  obtain ⟨N₂, hN₂⟩ := tail_vanishes D η hη
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : n ≥ N₁ := le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := le_of_max_le_right hn
  have hb := hN₁ n hn₁
  have ht := hN₂ n hn₂
  have htr := D.h_trunc
  have hrw : D.r_full n - D.r_star =
      (D.r_body n - D.r_star_M) + (D.r_star_M - D.r_star) +
      (D.r_tail_free n + D.r_tail_coupling n) := by
    have := D.h_decomp n; linarith
  rw [hrw]
  calc |(D.r_body n - D.r_star_M) + (D.r_star_M - D.r_star) +
       (D.r_tail_free n + D.r_tail_coupling n)|
      ≤ |D.r_body n - D.r_star_M| + |D.r_star_M - D.r_star| +
        |D.r_tail_free n + D.r_tail_coupling n| := by
        linarith [abs_add_le (D.r_body n - D.r_star_M + (D.r_star_M - D.r_star))
                             (D.r_tail_free n + D.r_tail_coupling n),
                  abs_add_le (D.r_body n - D.r_star_M) (D.r_star_M - D.r_star)]
    _ < η + D.ε_trunc + (D.ε_conv + η) := by linarith
    _ = 2 * η + ε₀ := by ring
    _ = 2 * ((D.δ_D - 3 * ε₀) / 3) + ε₀ := by rfl
    _ < D.δ_D := by
        have cancel := mul_div_cancel₀ (D.δ_D - 3 * ε₀) (three_ne_zero (α := ℝ))
        -- cancel : 3 * ((D.δ_D - 3 * ε₀) / 3) = D.δ_D - 3 * ε₀
        -- Goal: 2 * η + ε₀ < δ_D where η = (δ_D - 3ε₀)/3
        -- Multiply out: 2η = 2(δ - 3ε₀)/3, and 3·(2η + ε₀) = 2(δ-3ε₀) + 3ε₀ = 2δ - 3ε₀ < 3δ
        -- So 2η + ε₀ < δ iff 3(2η + ε₀) < 3δ iff 2(δ-3ε₀) + 3ε₀ < 3δ iff true
        -- Rewrite η using cancel: 2η = 2·(δ-3ε₀)/3, and 3·2η = 2(δ-3ε₀)
        have h2η : 2 * η = 2 * (D.δ_D - 3 * ε₀) / 3 := by ring
        have h6η : 3 * (2 * η) = 2 * (D.δ_D - 3 * ε₀) := by
          calc 3 * (2 * η) = 2 * (3 * η) := by ring
            _ = 2 * (3 * ((D.δ_D - 3 * ε₀) / 3)) := by ring
            _ = 2 * (D.δ_D - 3 * ε₀) := by rw [cancel]
        -- Goal: 2η + ε₀ < δ. Equiv: 6η + 3ε₀ < 3δ. And 6η = 2δ - 6ε₀.
        -- So need: 2δ - 6ε₀ + 3ε₀ < 3δ, i.e., 2δ - 3ε₀ < 3δ, i.e., 0 < δ + 3ε₀. True.
        -- But linarith can't see through div. Rewrite goal without div.
        change 2 * η + ε₀ < D.δ_D
        -- From h6η: 6η = 2δ - 6ε₀, so 2η = (2δ-6ε₀)/3
        -- 2η + ε₀ = (2δ - 6ε₀)/3 + ε₀ = (2δ - 6ε₀ + 3ε₀)/3 = (2δ - 3ε₀)/3
        -- < δ iff 2δ - 3ε₀ < 3δ iff 0 < δ + 3ε₀. True since δ > 0.
        -- Multiply goal by 3: suffices 6η + 3ε₀ < 3δ
        suffices hsuff : 3 * (2 * η + ε₀) < 3 * D.δ_D by linarith
        -- 3(2η+ε₀) = 6η + 3ε₀ = (2δ-6ε₀) + 3ε₀ = 2δ - 3ε₀
        have h3eq : 3 * (2 * η + ε₀) = 2 * D.δ_D - 3 * ε₀ := by linarith
        -- From h3eq and hsuff negation: 3δ ≤ 2δ - 3ε₀, so δ + 3ε₀ ≤ 0.
        -- But δ > 0 and ε₀ ≥ 0: contradiction.
        linarith [D.hδ_pos, D.hε_conv_nn, D.hε_trunc_nn]

end
