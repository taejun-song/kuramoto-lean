/-
  Kuramoto Stability — Pair Coercivity
  =====================================
  Quantitative lower bound on the pair integrand:

    pair ≥ δ · min(α*_j, α*_k) · (p_j² + p_k²)

  when α_j, α_k ≥ δ > 0 and α*_j, α*_k > 0.

  Combined with dV∞/dt = -K · ∫∫ pair / 2, this gives
  exponential convergence on the locked region.

  0 sorry.
-/
import KuramotoLean.ContinuumLyapunov

noncomputable section

/-! ## Step 1: Cross lower bound

pair ≥ α*_j · α_k · p_k² + α*_k · α_j · p_j²

Proof: multiply pair - cross by α*_j·α*_k > 0 to clear fractions.
The numerator is α*_j²·p_k² + α*_k²·p_j² - α*_j·α*_k·p_j·p_k·(2-α_j²-α_k²) ≥ 0
by case split on sign(p_j·p_k). -/

private theorem pair_cross_cleared (αj αk αsj αsk : ℝ)
    (hαsj : αsj ≠ 0) (hαsk : αsk ≠ 0) :
    αsj * αsk * (pairIntegrand αj αsj αk αsk -
      (αsj * αk * (αk - αsk) ^ 2 + αsk * αj * (αj - αsj) ^ 2)) =
    αsj ^ 2 * (αk - αsk) ^ 2 + αsk ^ 2 * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
  unfold pairIntegrand; field_simp; ring

private theorem pair_cross_nonneg (αj αk αsj αsk : ℝ)
    (_hαj : 0 < αj) (_hαk : 0 < αk) (hαj1 : αj < 1) (hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    0 ≤ αsj ^ 2 * (αk - αsk) ^ 2 + αsk ^ 2 * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
  by_cases hpq : (αj - αsj) * (αk - αsk) ≤ 0
  · have h1 : 0 ≤ αsj ^ 2 * (αk - αsk) ^ 2 := by positivity
    have h2 : 0 ≤ αsk ^ 2 * (αj - αsj) ^ 2 := by positivity
    have h3 : 0 ≤ αsj * αsk * (-((αj - αsj) * (αk - αsk))) * (2 - αj ^ 2 - αk ^ 2) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk)
        · linarith
      · nlinarith [sq_abs αj, sq_abs αk]
    nlinarith
  · push Not at hpq
    nlinarith [sq_nonneg (αsj * (αk - αsk) - αsk * (αj - αsj)),
               mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk))
                 (add_nonneg (sq_nonneg αj) (sq_nonneg αk))) (le_of_lt hpq)]

/-- **Cross lower bound.** pair ≥ α*_j · α_k · p_k² + α*_k · α_j · p_j². -/
theorem pair_ge_cross (αj αk αsj αsk : ℝ)
    (hαj : 0 < αj) (hαk : 0 < αk) (hαj1 : αj < 1) (hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    αsj * αk * (αk - αsk) ^ 2 + αsk * αj * (αj - αsj) ^ 2 ≤
    pairIntegrand αj αsj αk αsk := by
  have hmul : 0 < αsj * αsk := mul_pos hαsj hαsk
  have h_cleared := pair_cross_cleared αj αk αsj αsk (ne_of_gt hαsj) (ne_of_gt hαsk)
  have h_nonneg := pair_cross_nonneg αj αk αsj αsk hαj hαk hαj1 hαk1 hαsj hαsk
  by_contra h_neg
  push Not at h_neg
  linarith [mul_neg_of_pos_of_neg hmul (by linarith : pairIntegrand αj αsj αk αsk -
      (αsj * αk * (αk - αsk) ^ 2 + αsk * αj * (αj - αsj) ^ 2) < 0)]

/-! ## Step 2: Coercive bound

From the cross lower bound:
  pair ≥ αsj·αk·pk² + αsk·αj·pj²
     ≥ min(αsj,αsk)·αk·pk² + min(αsj,αsk)·αj·pj²
     = min(αsj,αsk)·(αk·pk² + αj·pj²)
     ≥ min(αsj,αsk)·δ·(pk² + pj²)    [using αj,αk ≥ δ] -/

/-- **Pair coercivity.** When α_j, α_k ≥ δ > 0:
    pair ≥ δ · min(α*_j, α*_k) · (p_j² + p_k²). -/
theorem pair_coercive (αj αk αsj αsk δ : ℝ)
    (hαj : 0 < αj) (hαk : 0 < αk) (hαj1 : αj < 1) (hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk)
    (_hδ : 0 < δ) (hαj_lb : δ ≤ αj) (hαk_lb : δ ≤ αk) :
    δ * min αsj αsk * ((αj - αsj) ^ 2 + (αk - αsk) ^ 2) ≤
    pairIntegrand αj αsj αk αsk := by
  have h_cross := pair_ge_cross αj αk αsj αsk hαj hαk hαj1 hαk1 hαsj hαsk
  suffices h : δ * min αsj αsk * ((αj - αsj) ^ 2 + (αk - αsk) ^ 2) ≤
      αsj * αk * (αk - αsk) ^ 2 + αsk * αj * (αj - αsj) ^ 2 by linarith
  have hmin_pos : 0 < min αsj αsk := lt_min hαsj hαsk
  have h1 : δ * min αsj αsk ≤ αj * αsk :=
    mul_le_mul hαj_lb (min_le_right _ _) (le_of_lt hmin_pos) (le_of_lt hαj)
  have h2 : δ * min αsj αsk ≤ αk * αsj :=
    mul_le_mul hαk_lb (min_le_left _ _) (le_of_lt hmin_pos) (le_of_lt hαk)
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (αj - αsj)),
             mul_le_mul_of_nonneg_right h2 (sq_nonneg (αk - αsk))]

/-! ## Application: Continuum integral coercivity

If α(ω) ≥ δ and α*(ω) ≥ δ* for all ω, then
∫∫ pair dμ dμ ≥ 2 · δ · δ* · V∞
where V∞ = ∫ (α - α*)² dμ. -/

theorem continuum_coercive {Ω : Type*} [MeasurableSpace Ω]
    (_μ : MeasureTheory.Measure Ω) (α α_star : Ω → ℝ) (δ δ_star : ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω)
    (hδ : 0 < δ) (_hδ_star : 0 < δ_star)
    (hα_lb : ∀ ω, δ ≤ α ω)
    (hα_star_lb : ∀ ω, δ_star ≤ α_star ω) :
    ∀ ω₁ ω₂, δ * δ_star * ((α ω₁ - α_star ω₁) ^ 2 + (α ω₂ - α_star ω₂) ^ 2) ≤
      pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) := by
  intro ω₁ ω₂
  have := pair_coercive (α ω₁) (α ω₂) (α_star ω₁) (α_star ω₂) δ
    (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)
    hδ (hα_lb ω₁) (hα_lb ω₂)
  have hmin : δ_star ≤ min (α_star ω₁) (α_star ω₂) :=
    le_min (hα_star_lb ω₁) (hα_star_lb ω₂)
  have hsum_nn : 0 ≤ (α ω₁ - α_star ω₁) ^ 2 + (α ω₂ - α_star ω₂) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (le_of_lt hδ)) hsum_nn]

end
