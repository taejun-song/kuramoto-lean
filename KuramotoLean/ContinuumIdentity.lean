/-
  Kuramoto Stability — Continuum Product Integral Identity
  =========================================================

  The product-of-integrals identity:
    (∫ f dμ) * (∫ g dμ) = ∫ ω₁, ∫ ω₂, f(ω₁) * g(ω₂) dμ₂ dμ₁

  And the algebraic decomposition of the pair integrand into two
  asymmetric terms, each corresponding to one expansion of r*Q - DS.

  0 sorry.
-/

import KuramotoLean.ContinuumLyapunov
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Product integral identity -/

/-- **(∫ f)(∫ g) = ∫∫ f·g.** The product of integrals equals the
    iterated integral of the product. No integrability needed. -/
theorem integral_mul_integral (f g : Ω → ℝ) :
    (∫ ω₁, f ω₁ ∂μ) * (∫ ω₂, g ω₂ ∂μ) =
    ∫ ω₁, ∫ ω₂, f ω₁ * g ω₂ ∂μ ∂μ := by
  simp_rw [integral_const_mul, integral_mul_const]

/-! ## Pair integrand decomposition

  The symmetrized pair integrand decomposes as the sum of two
  "asymmetric" terms, each encoding one product-integral expansion
  of r*Q - DS. This is the algebraic bridge between the Lyapunov
  identity dV/dt = K(DS - r*Q) and the pair bound ∫∫ pair ≥ 0. -/

/-- The pair integrand equals the sum of two asymmetric terms:
    Term₁₂ = α*₁ p₂² q₂ - p₁ p₂(1-α₂²)  (first form of r*Q-DS)
    Term₂₁ = α*₂ p₁² q₁ - p₁ p₂(1-α₁²)  (second form of r*Q-DS)
    where p = α - α*, q = α + 1/α*. -/
theorem pair_integrand_decomp (α₁ α₂ αs₁ αs₂ : ℝ) :
    αs₁ * (α₂ - αs₂) ^ 2 * (α₂ + 1 / αs₂) +
    αs₂ * (α₁ - αs₁) ^ 2 * (α₁ + 1 / αs₁) -
    (α₁ - αs₁) * (α₂ - αs₂) * (2 - α₁ ^ 2 - α₂ ^ 2) =
    (αs₁ * ((α₂ - αs₂) ^ 2 * (α₂ + 1 / αs₂)) -
     (α₁ - αs₁) * ((α₂ - αs₂) * (1 - α₂ ^ 2))) +
    (αs₂ * ((α₁ - αs₁) ^ 2 * (α₁ + 1 / αs₁)) -
     (α₁ - αs₁) * (α₂ - αs₂) * (1 - α₁ ^ 2)) := by ring

/-- Each asymmetric term is the integrand of r*Q - DS when written
    as a double integral via the product-integral identity.

    r*Q = (∫ α* dμ)(∫ p²q dμ) = ∫∫ α*(ω₁)·p(ω₂)²·q(ω₂)
    DS  = (∫ p dμ)(∫ p(1-α²) dμ) = ∫∫ p(ω₁)·p(ω₂)·(1-α(ω₂)²)

    So the first asymmetric term is:
    α*₁·p₂²·q₂ - p₁·p₂·(1-α₂²) = r*Q - DS integrand (form 1)

    The second is the ω₁↔ω₂ swap:
    α*₂·p₁²·q₁ - p₁·p₂·(1-α₁²) = r*Q - DS integrand (form 2) -/
theorem pair_bound_from_products
    (α α_star : Ω → ℝ)
    (hα : ∀ ω, 0 < α ω) (hα1 : ∀ ω, α ω < 1)
    (hα_star : ∀ ω, 0 < α_star ω) :
    0 ≤ ∫ ω₁, ∫ ω₂,
      ((α_star ω₁ * ((α ω₂ - α_star ω₂) ^ 2 * (α ω₂ + 1 / α_star ω₂)) -
        (α ω₁ - α_star ω₁) * ((α ω₂ - α_star ω₂) * (1 - α ω₂ ^ 2))) +
       (α_star ω₂ * ((α ω₁ - α_star ω₁) ^ 2 * (α ω₁ + 1 / α_star ω₁)) -
        (α ω₁ - α_star ω₁) * (α ω₂ - α_star ω₂) * (1 - α ω₁ ^ 2))) ∂μ ∂μ := by
  apply integral_nonneg; intro ω₁
  apply integral_nonneg; intro ω₂
  suffices 0 ≤ α_star ω₁ * (α ω₂ - α_star ω₂) ^ 2 * (α ω₂ + 1 / α_star ω₂) +
      α_star ω₂ * (α ω₁ - α_star ω₁) ^ 2 * (α ω₁ + 1 / α_star ω₁) -
      (α ω₁ - α_star ω₁) * (α ω₂ - α_star ω₂) * (2 - α ω₁ ^ 2 - α ω₂ ^ 2) by
    convert this using 1
    ring
  exact pair_bound (α ω₁) (α ω₂) (α_star ω₁) (α_star ω₂)
    (hα ω₁) (hα ω₂) (hα1 ω₁) (hα1 ω₂) (hα_star ω₁) (hα_star ω₂)

/-! ## Fubini Lyapunov Identity

Under integrability, ∫∫ pairIntegrand = 2(r*Q - DS).
The pair integrand decomposes as Term₁₂ + Term₂₁, each integrating to
r*Q - DS via the product-integral identity. -/

/-- Inner integral of Term₁₂ for fixed ω₁. -/
private theorem inner_term12 (α αs : Ω → ℝ)
    (h_pq : Integrable (fun ω => (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω)) μ)
    (h_ps : Integrable (fun ω => (α ω - αs ω) * (1 - α ω ^ 2)) μ)
    (ω₁ : Ω) :
    ∫ ω₂, (αs ω₁ * ((α ω₂ - αs ω₂) ^ 2 * (α ω₂ + 1 / αs ω₂)) -
       (α ω₁ - αs ω₁) * ((α ω₂ - αs ω₂) * (1 - α ω₂ ^ 2))) ∂μ =
    αs ω₁ * (∫ ω, (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω) ∂μ) -
    (α ω₁ - αs ω₁) * (∫ ω, (α ω - αs ω) * (1 - α ω ^ 2) ∂μ) := by
  rw [integral_sub (h_pq.const_mul _) (h_ps.const_mul _)]
  simp_rw [integral_const_mul]

/-- Inner integral of Term₂₁ for fixed ω₁. -/
private theorem inner_term21 (α αs : Ω → ℝ)
    (h_αs : Integrable αs μ)
    (h_p : Integrable (fun ω => α ω - αs ω) μ)
    (ω₁ : Ω) :
    ∫ ω₂, (αs ω₂ * ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁)) -
       (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) * (1 - α ω₁ ^ 2)) ∂μ =
    (α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁) * (∫ ω, αs ω ∂μ) -
    (α ω₁ - αs ω₁) * (1 - α ω₁ ^ 2) * (∫ ω, (α ω - αs ω) ∂μ) := by
  have h1 : Integrable (fun ω₂ => αs ω₂ *
      ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁))) μ :=
    h_αs.mul_const _
  have h2 : Integrable (fun ω₂ => (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) *
      (1 - α ω₁ ^ 2)) μ :=
    (h_p.const_mul _).mul_const _
  rw [integral_sub h1 h2]
  simp_rw [integral_mul_const, integral_const_mul]; ring

/-- **Fubini Lyapunov identity.** Under integrability,
    ∫∫ (Term₁₂ + Term₂₁) = 2((∫α*)(∫p²q) - (∫p)(∫p(1-α²)))

    This connects the pair bound to the Lyapunov derivative:
    dV∞/dt = K(DS - r*Q) = -K/2 · ∫∫ pair ≤ 0. -/
theorem pair_fubini_identity (α αs : Ω → ℝ)
    (h_pq : Integrable (fun ω => (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω)) μ)
    (h_ps : Integrable (fun ω => (α ω - αs ω) * (1 - α ω ^ 2)) μ)
    (h_αs : Integrable αs μ)
    (h_p : Integrable (fun ω => α ω - αs ω) μ)
    (h_out12 : Integrable (fun ω₁ =>
      αs ω₁ * (∫ ω, (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω) ∂μ) -
      (α ω₁ - αs ω₁) * (∫ ω, (α ω - αs ω) * (1 - α ω ^ 2) ∂μ)) μ)
    (h_out21 : Integrable (fun ω₁ =>
      (α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁) * (∫ ω, αs ω ∂μ) -
      (α ω₁ - αs ω₁) * (1 - α ω₁ ^ 2) * (∫ ω, (α ω - αs ω) ∂μ)) μ) :
    ∫ ω₁, ∫ ω₂,
      ((αs ω₁ * ((α ω₂ - αs ω₂) ^ 2 * (α ω₂ + 1 / αs ω₂)) -
        (α ω₁ - αs ω₁) * ((α ω₂ - αs ω₂) * (1 - α ω₂ ^ 2))) +
       (αs ω₂ * ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁)) -
        (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) * (1 - α ω₁ ^ 2))) ∂μ ∂μ =
    2 * ((∫ ω, αs ω ∂μ) * (∫ ω, (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω) ∂μ) -
         (∫ ω, (α ω - αs ω) ∂μ) * (∫ ω, (α ω - αs ω) * (1 - α ω ^ 2) ∂μ)) := by
  set Q := ∫ ω, (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω) ∂μ
  set S := ∫ ω, (α ω - αs ω) * (1 - α ω ^ 2) ∂μ
  set rs := ∫ ω, αs ω ∂μ
  set D := ∫ ω, (α ω - αs ω) ∂μ
  -- Step 1: Split inner integral using inner_term12 and inner_term21
  have h12 := inner_term12 α αs h_pq h_ps
  have h21 := inner_term21 α αs h_αs h_p
  -- Step 2: Compute inner integrals
  have h_inner : ∀ ω₁,
      ∫ ω₂, ((αs ω₁ * ((α ω₂ - αs ω₂) ^ 2 * (α ω₂ + 1 / αs ω₂)) -
        (α ω₁ - αs ω₁) * ((α ω₂ - αs ω₂) * (1 - α ω₂ ^ 2))) +
       (αs ω₂ * ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁)) -
        (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) * (1 - α ω₁ ^ 2))) ∂μ =
      (αs ω₁ * Q - (α ω₁ - αs ω₁) * S) +
      ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁) * rs -
       (α ω₁ - αs ω₁) * (1 - α ω₁ ^ 2) * D) := by
    intro ω₁
    have hi12 : Integrable (fun ω₂ =>
        αs ω₁ * ((α ω₂ - αs ω₂) ^ 2 * (α ω₂ + 1 / αs ω₂)) -
        (α ω₁ - αs ω₁) * ((α ω₂ - αs ω₂) * (1 - α ω₂ ^ 2))) μ :=
      (h_pq.const_mul _).sub (h_ps.const_mul _)
    have hi21 : Integrable (fun ω₂ =>
        αs ω₂ * ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁)) -
        (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) * (1 - α ω₁ ^ 2)) μ :=
      (h_αs.mul_const _).sub ((h_p.const_mul _).mul_const _)
    rw [integral_add hi12 hi21, h12 ω₁, h21 ω₁]
  simp_rw [h_inner]
  -- Step 3: Split outer integral
  rw [integral_add h_out12 h_out21]
  -- Step 4: Compute each outer integral
  have hA1 : Integrable (fun ω₁ => αs ω₁ * Q) μ := h_αs.mul_const _
  have hA2 : Integrable (fun ω₁ => (α ω₁ - αs ω₁) * S) μ := h_p.mul_const _
  have hB1 : Integrable (fun ω₁ =>
      (α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁) * rs) μ := h_pq.mul_const _
  have hB2 : Integrable (fun ω₁ =>
      (α ω₁ - αs ω₁) * (1 - α ω₁ ^ 2) * D) μ := h_ps.mul_const _
  rw [integral_sub hA1 hA2, integral_sub hB1 hB2]
  simp_rw [integral_mul_const]
  ring

end
