/-
  Kuramoto Stability Project — Riccati Contraction
  ===================================================
  The OA Riccati at frequency ω driven by signal r(t):
    ∂_t α = -iωα + (K/2)(r - r̄α²)

  Two solutions α₁, α₂ driven by the SAME r(t):
    ∂_t(α₁-α₂) = -iω(α₁-α₂) - (K/2)r̄(α₁²-α₂²)
                = -iω(α₁-α₂) - (K/2)r̄(α₁+α₂)(α₁-α₂)

  Set p = α₁ - α₂. Then:
    ∂_t p = [-iω - (K/2)r̄(α₁+α₂)] p

  This is LINEAR in p. The coefficient: -iω - (K/2)r̄(α₁+α₂).
  The real part: Re[-iω - (K/2)r̄(α₁+α₂)] = -Re[(K/2)r̄(α₁+α₂)]
    = -(K/2)Re[r̄(α₁+α₂)]

  For |α₁|, |α₂| ≤ 1: |α₁+α₂| ≤ 2. The contraction rate:
    d/dt |p|² = 2 Re[p̄ ∂_t p] = 2|p|² Re[-iω-(K/2)r̄(α₁+α₂)]
             = -K|p|² Re[r̄(α₁+α₂)]

  The contraction: Re[r̄(α₁+α₂)] > 0 when the phases of α₁,α₂
  are aligned with r. The TIME-AVERAGE of Re[r̄(α₁+α₂)] is > 0
  whenever |r| is not identically 0.

  KEY INSIGHT: d/dt|p|² = -K Re[r̄(α₁+α₂)] |p|²
  The coefficient -K Re[r̄(α₁+α₂)] has the SAME SIGN structure
  as the d/dt|α|² = K Re[r̄α](1-|α|²) equation.

  For α₁ ≈ α₂ ≈ α (near PLS): Re[r̄(α₁+α₂)] ≈ 2Re[r̄α] > 0
  for locked oscillators. So p → 0: contraction.
-/

import KuramotoLean.OADynamics

open Complex

noncomputable section

/-- The difference equation: if α₁, α₂ satisfy the OA Riccati with
    the same r, then p = α₁ - α₂ satisfies
    ∂_t p = [-iω - (K/2)r̄(α₁+α₂)] p.
    This is the LINEARIZED equation for the difference. -/
theorem difference_equation (ω K : ℝ) (r α₁ α₂ : ℂ) :
    OADyn.oaVelocity ω K r α₁ - OADyn.oaVelocity ω K r α₂ =
    (-Complex.I * (ω : ℂ) - (↑(K / 2) : ℂ) * starRingEnd ℂ r * (α₁ + α₂)) *
    (α₁ - α₂) := by
  simp only [OADyn.oaVelocity]
  ring

/-- The contraction rate: d/dt|p|² = -K Re[r̄(α₁+α₂)] |p|²
    (from the difference equation + rotation cancellation). -/
theorem contraction_rate (ω K : ℝ) (r α₁ α₂ : ℂ) :
    let p := α₁ - α₂
    let v := OADyn.oaVelocity ω K r α₁ - OADyn.oaVelocity ω K r α₂
    2 * (starRingEnd ℂ p * v).re =
    -K * (starRingEnd ℂ r * (α₁ + α₂)).re * Complex.normSq p := by
  -- v = [-iω - (K/2)r̄(α₁+α₂)] p
  -- conj(p) v = conj(p)[-iω - (K/2)r̄(α₁+α₂)]p
  -- = [-iω - (K/2)r̄(α₁+α₂)] |p|²
  -- (rotation -iω drops out from Re)
  -- Re[conj(p)v] = -Re[(K/2)r̄(α₁+α₂)] |p|²
  -- 2Re[conj(p)v] = -K Re[r̄(α₁+α₂)] |p|²
  rw [difference_equation]
  simp only [starRingEnd_self_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, sq]
  ring

/-- **RICCATI CONTRACTION SIGN.** When Re[r̄(α₁+α₂)] > 0:
    d/dt|p|² < 0 (the difference shrinks). This holds when
    the phases of α₁+α₂ are aligned with r. -/
theorem contraction_sign (ω K : ℝ) (r α₁ α₂ : ℂ)
    (hK : 0 < K) (hR : 0 < (starRingEnd ℂ r * (α₁ + α₂)).re)
    (hp : α₁ ≠ α₂) :
    2 * (starRingEnd ℂ (α₁ - α₂) *
      (OADyn.oaVelocity ω K r α₁ - OADyn.oaVelocity ω K r α₂)).re < 0 := by
  rw [contraction_rate]
  have hns : 0 < Complex.normSq (α₁ - α₂) := by
    rw [Complex.normSq_pos]
    exact sub_ne_zero.mpr hp
  have := mul_pos hK hR
  have := mul_pos this hns
  linarith

end
