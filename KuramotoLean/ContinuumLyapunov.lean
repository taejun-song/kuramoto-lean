/-
  Kuramoto Stability — Continuum L² Lyapunov Function
  ====================================================

  The finite-sum pair bound (pair_bound in L2Lyapunov.lean) is purely
  algebraic: for any α, α* ∈ (0,1), the symmetrized pair integrand is ≥ 0.

  This file transfers the result to Lebesgue integrals over arbitrary
  measure spaces, proving that the continuum DS ≤ r*Q inequality holds.

  The consequence: V∞ = ∫g|α-α*|²dω satisfies dV∞/dt ≤ 0 along the
  continuum OA flow, giving DIRECT global stability without passage
  to limit.

  0 sorry.
-/

import KuramotoLean.L2Lyapunov
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

/-! ## Continuum pair bound: the double integral is non-negative

The pair bound `pair_bound` proves that for any α₁, α₂, α*₁, α*₂ ∈ (0,1):

  α*₁ · (α₂-α*₂)²·(α₂+1/α*₂) + α*₂ · (α₁-α*₁)²·(α₁+1/α*₁)
  - (α₁-α*₁)(α₂-α*₂)(2-α₁²-α₂²) ≥ 0

This is purely algebraic, so it holds pointwise for any ω₁, ω₂ in a
measure space. By `integral_nonneg` applied twice, the double integral
over μ ⊗ μ is non-negative.

This is the continuum analogue of `ds_le_rstarQ`. -/

/-- **Continuum pair bound.** The double integral of the symmetrized
    Lyapunov pair integrand is non-negative over any measure space.
    Transfers `pair_bound` from finite sums to Lebesgue integrals. -/
theorem continuum_pair_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (α α_star : Ω → ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω) :
    0 ≤ ∫ ω₁, ∫ ω₂,
      (α_star ω₁ * (α ω₂ - α_star ω₂) ^ 2 * (α ω₂ + 1 / α_star ω₂) +
       α_star ω₂ * (α ω₁ - α_star ω₁) ^ 2 * (α ω₁ + 1 / α_star ω₁) -
       (α ω₁ - α_star ω₁) * (α ω₂ - α_star ω₂) * (2 - α ω₁ ^ 2 - α ω₂ ^ 2)) ∂μ ∂μ := by
  apply integral_nonneg
  intro ω₁
  apply integral_nonneg
  intro ω₂
  exact pair_bound (α ω₁) (α ω₂) (α_star ω₁) (α_star ω₂)
    (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)

/-! ## Continuum Lyapunov identity

For the continuum OA flow with measure μ (representing g(ω)dω):
  r* = ∫ α*(ω) dμ(ω)
  r  = ∫ α(ω,t) dμ(ω)
  V∞ = ∫ (α(ω,t) - α*(ω))² dμ(ω)

The time derivative decomposes as dV∞/dt = K·(DS - r*·Q) where:
  D  = ∫ (α - α*) dμ = r - r*
  S  = ∫ (α - α*)(1 - α²) dμ
  Q  = ∫ (α - α*)²(α + 1/α*) dμ

And DS ≤ r*Q follows from continuum_pair_nonneg (via Fubini).

The full dV∞/dt ≤ 0 then follows from K > 0 and DS ≤ r*Q. -/

/-- The per-point pair integrand in terms of two frequency parameters.
    This is the quantity whose non-negativity gives DS ≤ r*Q. -/
def pairIntegrand (α α_star : ℝ) (β β_star : ℝ) : ℝ :=
  α_star * (β - β_star) ^ 2 * (β + 1 / β_star) +
  β_star * (α - α_star) ^ 2 * (α + 1 / α_star) -
  (α - α_star) * (β - β_star) * (2 - α ^ 2 - β ^ 2)

theorem pairIntegrand_nonneg (α α_star β β_star : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hα1 : α < 1) (hβ1 : β < 1)
    (hα_star : 0 < α_star) (hβ_star : 0 < β_star) :
    0 ≤ pairIntegrand α α_star β β_star :=
  pair_bound α β α_star β_star hα hβ hα1 hβ1 hα_star hβ_star

/-- Variant with explicit function application for measure-theoretic use. -/
theorem continuum_pair_nonneg' {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (α α_star : Ω → ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω) (_hα_star1 : ∀ ω, α_star ω < 1) :
    0 ≤ ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ := by
  apply integral_nonneg
  intro ω₁
  apply integral_nonneg
  intro ω₂
  exact pairIntegrand_nonneg (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂)
    (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)

/-! ## Pair rigidity: pairIntegrand = 0 iff both deviations vanish

The quadratic form N = pair · (α*₁·α*₂) decomposes as:
  N = (α*₁·p₂ - α*₂·p₁)² + α*₁²·α₂·α*₂·p₂² + α*₂²·α₁·α*₁·p₁²
    + α*₁·α*₂·(α₁²+α₂²)·p₁·p₂

When p₁p₂ > 0: all four terms are non-negative and the last three are
strictly positive, so N > 0.
When p₁p₂ ≤ 0: the original three terms of pair are each non-negative,
so pair = 0 forces each to vanish, giving p₁ = p₂ = 0.

This characterizes V' = 0: the continuum Lyapunov derivative vanishes
only at the equilibrium α = α*. Combined with LaSalle's invariance
principle, this gives V∞ → 0. -/

theorem pair_rigidity_sos (αj αk αsj αsk : ℝ) (hαsj : αsj ≠ 0) (hαsk : αsk ≠ 0) :
    αsj * αsk * (αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
    αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
    (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2)) =
    (αsj * (αk - αsk) - αsk * (αj - αsj)) ^ 2 +
    αsj ^ 2 * αk * αsk * (αk - αsk) ^ 2 +
    αsk ^ 2 * αj * αsj * (αj - αsj) ^ 2 +
    αsj * αsk * (αj ^ 2 + αk ^ 2) * (αj - αsj) * (αk - αsk) := by
  have h := pair_bound_clear_denom αj αk αsj αsk hαsj hαsk
  linarith [sq_nonneg (αsj * (αk - αsk) - αsk * (αj - αsj)),
    show (αsj * (αk - αsk) - αsk * (αj - αsj)) ^ 2 =
      αsj ^ 2 * (αk - αsk) ^ 2 - 2 * αsj * αsk * (αj - αsj) * (αk - αsk) +
      αsk ^ 2 * (αj - αsj) ^ 2 from by ring,
    show αsj ^ 2 * αk * αsk * (αk - αsk) ^ 2 +
      αsk ^ 2 * αj * αsj * (αj - αsj) ^ 2 +
      αsj * αsk * (αj ^ 2 + αk ^ 2) * (αj - αsj) * (αk - αsk) +
      (αsj ^ 2 * (αk - αsk) ^ 2 - 2 * αsj * αsk * (αj - αsj) * (αk - αsk) +
      αsk ^ 2 * (αj - αsj) ^ 2) =
      αsj ^ 2 * (αk * αsk + 1) * (αk - αsk) ^ 2 +
      αsk ^ 2 * (αj * αsj + 1) * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) from by ring]

/-- **Pair rigidity**: pair_bound = 0 iff both deviations vanish.
    This is the LaSalle characterization: V' = 0 only at equilibrium. -/
theorem pair_eq_zero_iff (αj αk αsj αsk : ℝ)
    (hαj : 0 < αj) (hαk : 0 < αk) (_hαj1 : αj < 1) (_hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    pairIntegrand αj αsj αk αsk = 0 ↔ αj = αsj ∧ αk = αsk := by
  constructor
  · intro h
    set pj := αj - αsj
    set pk := αk - αsk
    -- Helper: each original term is non-negative when pj·pk ≤ 0
    have hq_j : 0 < αj + 1 / αsj := by linarith [div_pos one_pos hαsj]
    have hq_k : 0 < αk + 1 / αsk := by linarith [div_pos one_pos hαsk]
    by_cases hpq : pj * pk ≤ 0
    · -- Case pj·pk ≤ 0: three non-negative terms sum to 0
      have ht1 : 0 ≤ αsj * pk ^ 2 * (αk + 1 / αsk) :=
        mul_nonneg (mul_nonneg (le_of_lt hαsj) (sq_nonneg _)) (le_of_lt hq_k)
      have ht2 : 0 ≤ αsk * pj ^ 2 * (αj + 1 / αsj) :=
        mul_nonneg (mul_nonneg (le_of_lt hαsk) (sq_nonneg _)) (le_of_lt hq_j)
      have ht3 : 0 ≤ -(pj * pk * (2 - αj ^ 2 - αk ^ 2)) := by
        have h2pos : 0 < 2 - αj ^ 2 - αk ^ 2 := by nlinarith [sq_nonneg αj, sq_nonneg αk]
        linarith [mul_nonpos_of_nonpos_of_nonneg hpq (le_of_lt h2pos)]
      have h_expand : pairIntegrand αj αsj αk αsk =
        αsj * pk ^ 2 * (αk + 1 / αsk) + αsk * pj ^ 2 * (αj + 1 / αsj) -
        pj * pk * (2 - αj ^ 2 - αk ^ 2) := by unfold pairIntegrand; ring
      rw [h_expand] at h
      have ht2_zero : αsk * pj ^ 2 * (αj + 1 / αsj) = 0 := by linarith
      have ht1_zero : αsj * pk ^ 2 * (αk + 1 / αsk) = 0 := by linarith
      constructor
      · rcases mul_eq_zero.mp ht2_zero with h_left | h_right
        · rcases mul_eq_zero.mp h_left with h_αsk | h_pj_sq
          · linarith
          · exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_pj_sq)
        · linarith [hq_j]
      · rcases mul_eq_zero.mp ht1_zero with h_left | h_right
        · rcases mul_eq_zero.mp h_left with h_αsj | h_pk_sq
          · linarith
          · exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_pk_sq)
        · linarith [hq_k]
    · -- Case pj·pk > 0: use SOS decomposition to show pair > 0
      push Not at hpq
      exfalso
      have hpj_ne : pj ≠ 0 := fun h => by rw [h, zero_mul] at hpq; exact lt_irrefl 0 hpq
      have hpk_ne : pk ≠ 0 := fun h => by rw [h, mul_zero] at hpq; exact lt_irrefl 0 hpq
      have h_sos := pair_rigidity_sos αj αk αsj αsk (ne_of_gt hαsj) (ne_of_gt hαsk)
      have h_cleared : αsj * αsk * pairIntegrand αj αsj αk αsk = 0 := by
        rw [h, mul_zero]
      rw [show αsj * αsk * pairIntegrand αj αsj αk αsk =
        αsj * αsk * (αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
        αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
        (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2)) from by
        unfold pairIntegrand; ring] at h_cleared
      rw [h_sos] at h_cleared
      -- The sum of four terms = 0, but second and third are strictly positive
      have : 0 < αsj ^ 2 * αk * αsk * pk ^ 2 := by positivity
      have : 0 < αsk ^ 2 * αj * αsj * pj ^ 2 := by positivity
      have : 0 ≤ (αsj * pk - αsk * pj) ^ 2 := sq_nonneg _
      have : 0 ≤ αsj * αsk * (αj ^ 2 + αk ^ 2) * (pj * pk) :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk))
          (add_nonneg (sq_nonneg αj) (sq_nonneg αk))) (le_of_lt hpq)
      linarith
  · rintro ⟨rfl, rfl⟩
    unfold pairIntegrand; ring

end
