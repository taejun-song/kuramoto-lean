/-
  Complex OA Locked Equilibrium — Formula and Properties
  =======================================================
  For the complex OA equation ż = -iωz + (K/2)r(1-z²) on the symmetric
  subspace (η = r ∈ ℝ), the per-oscillator equilibrium satisfies:

    (Kr/2)z² + iωz - Kr/2 = 0

  Locked oscillators (|ω| < Kr) have equilibrium on the unit circle:
    z*(ω) = (√(K²r² - ω²) - iω) / (Kr),   |z*| = 1

  Properties proved (19 theorems, 0 sorry):
    1. z* solves complexOaRHS = 0 (equilibrium equation)
    2. |z*| = 1 (boundary equilibrium)
    3. 0 < Re(z*) ≤ 1 for locked oscillators, Re(z*) < 1 when ω ≠ 0
    4. Exponential stability: Re(linearized eigenvalue) = -√(K²r²-ω²) < 0
    5. Re(z*) monotone in r (lockedEquilRe_mono)
    6. F(r) = ∫ Re(z*) g dμ: F(0)=0, F≥0, F≤∫g, F monotone in r
-/

import KuramotoLean.ComplexOA
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Locked equilibrium formula -/

/-- The real part of the locked equilibrium: Re(z*) = √(K²r² - ω²)/(Kr). -/
def lockedEquilRe (ω K r : ℝ) : ℝ :=
  Real.sqrt (K ^ 2 * r ^ 2 - ω ^ 2) / (K * r)

/-- The imaginary part of the locked equilibrium: Im(z*) = -ω/(Kr). -/
def lockedEquilIm (ω K r : ℝ) : ℝ :=
  -ω / (K * r)

/-- The locked equilibrium as a complex number:
    z*(ω) = (√(K²r²-ω²) - iω) / (Kr). -/
def lockedEquil (ω K r : ℝ) : ℂ :=
  ((Real.sqrt (K ^ 2 * r ^ 2 - ω ^ 2) : ℂ) - Complex.I * (ω : ℂ)) / ((K * r : ℝ) : ℂ)

theorem lockedEquil_re (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r) :
    (lockedEquil ω K r).re = lockedEquilRe ω K r := by
  unfold lockedEquil lockedEquilRe
  simp [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_ofReal, Complex.sub_re, Complex.mul_re]
  have hKr : (K * r) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (mul_pos hK hr))
  field_simp

theorem lockedEquil_im (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r) :
    (lockedEquil ω K r).im = lockedEquilIm ω K r := by
  unfold lockedEquil lockedEquilIm
  simp [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_ofReal, Complex.sub_im, Complex.mul_im]
  have hKr : (K * r) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (mul_pos hK hr))
  field_simp

/-! ## |z*| = 1 for locked oscillators -/

theorem lockedEquil_normSq (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    Complex.normSq (lockedEquil ω K r) = 1 := by
  unfold lockedEquil
  have hKr : 0 < K * r := mul_pos hK hr
  rw [map_div₀, Complex.normSq_ofReal, div_eq_one_iff_eq
    (by positivity : (K * r) * (K * r) ≠ 0)]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ K ^ 2 * r ^ 2 - ω ^ 2 by linarith)]

/-! ## Re(z*) > 0 -/

theorem lockedEquilRe_pos (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    0 < lockedEquilRe ω K r := by
  unfold lockedEquilRe
  exact div_pos (Real.sqrt_pos.mpr (by linarith)) (mul_pos hK hr)

/-! ## Re(z*) < 1 -/

theorem lockedEquilRe_lt_one (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω_ne : ω ≠ 0) (hω_locked : ω ^ 2 < K ^ 2 * r ^ 2) :
    lockedEquilRe ω K r < 1 := by
  unfold lockedEquilRe
  rw [div_lt_one (mul_pos hK hr)]
  calc Real.sqrt (K ^ 2 * r ^ 2 - ω ^ 2)
      < Real.sqrt (K ^ 2 * r ^ 2) := by
        apply Real.sqrt_lt_sqrt (by linarith)
        have : 0 < ω ^ 2 := by positivity
        linarith
    _ = K * r := by
        have : K ^ 2 * r ^ 2 = (K * r) ^ 2 := by ring
        rw [this, Real.sqrt_sq (le_of_lt (mul_pos hK hr))]

theorem lockedEquilRe_le_one (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    lockedEquilRe ω K r ≤ 1 := by
  rcases eq_or_ne ω 0 with rfl | hne
  · unfold lockedEquilRe
    have : K ^ 2 * r ^ 2 - (0 : ℝ) ^ 2 = (K * r) ^ 2 := by ring
    rw [this, Real.sqrt_sq (le_of_lt (mul_pos hK hr)),
        div_self (ne_of_gt (mul_pos hK hr))]
  · exact le_of_lt (lockedEquilRe_lt_one ω K r hK hr hne hω)

/-! ## z* solves the equilibrium equation -/

theorem lockedEquil_is_equil (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    complexOaRHS ω K (r : ℂ) (lockedEquil ω K r) = 0 := by
  set D : ℝ := Real.sqrt (K ^ 2 * r ^ 2 - ω ^ 2)
  have hD_sq : D ^ 2 = K ^ 2 * r ^ 2 - ω ^ 2 := Real.sq_sqrt (by linarith)
  have hKr_pos : 0 < K * r := mul_pos hK hr
  have hKr_ne : ((K * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hKr_pos
  suffices h : 2 * ((K * r : ℝ) : ℂ) * complexOaRHS ω K (r : ℂ) (lockedEquil ω K r) = 0 by
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero hKr_ne)
  unfold complexOaRHS lockedEquil
  have hr_star : starRingEnd ℂ ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) :=
    RCLike.conj_ofReal r
  rw [hr_star]
  field_simp
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have hD_c : ((D : ℝ) : ℂ) ^ 2 = (↑K : ℂ) ^ 2 * (↑r : ℂ) ^ 2 - (↑ω : ℂ) ^ 2 := by
    have : ((D ^ 2 : ℝ) : ℂ) = ((K ^ 2 * r ^ 2 - ω ^ 2 : ℝ) : ℂ) := by exact_mod_cast hD_sq
    push_cast at this ⊢; exact this
  push_cast
  linear_combination (↑K * ↑r * (↑ω : ℂ) ^ 2) * hI2 - (↑K * (↑r : ℂ)) * hD_c

/-! ## Linearized stability -/

/-- The linearized eigenvalue at the locked equilibrium.
    λ = -iω - Kr·z* has Re(λ) = -Kr·Re(z*) = -√(K²r² - ω²) < 0. -/
theorem lockedEquil_stability_rate (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (_hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    -(K * r * lockedEquilRe ω K r) = -Real.sqrt (K ^ 2 * r ^ 2 - ω ^ 2) := by
  unfold lockedEquilRe
  have hKr : K * r ≠ 0 := ne_of_gt (mul_pos hK hr)
  field_simp

theorem lockedEquil_stability_neg (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    -(K * r * lockedEquilRe ω K r) < 0 := by
  rw [lockedEquil_stability_rate ω K r hK hr hω]
  linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < K ^ 2 * r ^ 2 - ω ^ 2 by linarith)]

/-! ## Re(z*) monotone in r -/

/-- Re(z*)² = 1 - ω²/(K²r²), enabling monotonicity arguments. -/
theorem lockedEquilRe_sq (ω K r : ℝ) (_hK : 0 < K) (_hr : 0 < r)
    (_hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    lockedEquilRe ω K r ^ 2 = (K ^ 2 * r ^ 2 - ω ^ 2) / (K ^ 2 * r ^ 2) := by
  unfold lockedEquilRe
  rw [div_pow, Real.sq_sqrt (by linarith)]
  congr 1; ring

theorem lockedEquilRe_mono {r₁ r₂ : ℝ} (ω K : ℝ) (hK : 0 < K)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr : r₁ ≤ r₂)
    (hω : ω ^ 2 < K ^ 2 * r₁ ^ 2) :
    lockedEquilRe ω K r₁ ≤ lockedEquilRe ω K r₂ := by
  have hω₂ : ω ^ 2 < K ^ 2 * r₂ ^ 2 := by
    nlinarith [pow_le_pow_left₀ (le_of_lt hr₁) hr 2, sq_nonneg K]
  have h₁ := lockedEquilRe_pos ω K r₁ hK hr₁ hω
  have h₂ := lockedEquilRe_pos ω K r₂ hK hr₂ hω₂
  have hsq₁ := lockedEquilRe_sq ω K r₁ hK hr₁ hω
  have hsq₂ := lockedEquilRe_sq ω K r₂ hK hr₂ hω₂
  have hmono : lockedEquilRe ω K r₁ ^ 2 ≤ lockedEquilRe ω K r₂ ^ 2 := by
    rw [hsq₁, hsq₂]
    have h1p : (0 : ℝ) < K ^ 2 * r₁ ^ 2 := by positivity
    have h2p : (0 : ℝ) < K ^ 2 * r₂ ^ 2 := by positivity
    rw [div_le_div_iff₀ h1p h2p]
    have h_r_sq := pow_le_pow_left₀ (le_of_lt hr₁) hr 2
    nlinarith [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h_r_sq (sq_nonneg K)) (sq_nonneg ω)]
  have hle := Real.sqrt_le_sqrt hmono
  rwa [Real.sqrt_sq (le_of_lt h₁), Real.sqrt_sq (le_of_lt h₂)] at hle

/-! ## Self-consistency function -/

/-- F(r) = ∫_{locked} Re(z*(ω)) g(ω) dμ(ω).
    This is the self-consistency integral: r* is a fixed point F(r*) = r*. -/
def selfConsistencyF (ω_freq : Ω → ℝ) (K r : ℝ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (if (ω_freq ω) ^ 2 < K ^ 2 * r ^ 2
         then lockedEquilRe (ω_freq ω) K r * g ω
         else 0) ∂μ

/-- At a fixed point r* = F(r*), the equilibrium z*(ω) with r = r*
    satisfies the self-consistency equation. -/
theorem selfConsistencyF_at_fixed_point (ω_freq : Ω → ℝ) (K r_star : ℝ)
    (g : Ω → ℝ)
    (h_fixed : selfConsistencyF ω_freq K r_star g μ = r_star) :
    r_star = ∫ ω, (if (ω_freq ω) ^ 2 < K ^ 2 * r_star ^ 2
                    then lockedEquilRe (ω_freq ω) K r_star * g ω
                    else 0) ∂μ :=
  h_fixed.symm

theorem selfConsistencyF_zero (ω_freq : Ω → ℝ) (K : ℝ) (g : Ω → ℝ) :
    selfConsistencyF ω_freq K 0 g μ = 0 := by
  unfold selfConsistencyF
  have h : ∀ ω, ¬((ω_freq ω) ^ 2 < K ^ 2 * (0 : ℝ) ^ 2) := by
    intro ω
    simp only [mul_zero, sq (0 : ℝ), not_lt]
    exact sq_nonneg _
  simp only [h, ite_false, integral_zero]

private theorem scF_integrand_nonneg (ω_val K r g_val : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hg : 0 ≤ g_val) :
    0 ≤ (if ω_val ^ 2 < K ^ 2 * r ^ 2
         then lockedEquilRe ω_val K r * g_val else 0) := by
  split_ifs with h
  · exact mul_nonneg (le_of_lt (lockedEquilRe_pos _ _ _ hK hr h)) hg
  · exact le_refl _

private theorem scF_integrand_le_g (ω_val K r g_val : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hg : 0 ≤ g_val) :
    (if ω_val ^ 2 < K ^ 2 * r ^ 2
     then lockedEquilRe ω_val K r * g_val else 0) ≤ g_val := by
  split_ifs with h
  · calc lockedEquilRe ω_val K r * g_val
        ≤ 1 * g_val := mul_le_mul_of_nonneg_right
          (lockedEquilRe_le_one _ _ _ hK hr h) hg
      _ = g_val := one_mul _
  · exact hg

private theorem scF_integrand_mono (ω_val K r₁ r₂ g_val : ℝ) (hK : 0 < K)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr : r₁ ≤ r₂) (hg : 0 ≤ g_val) :
    (if ω_val ^ 2 < K ^ 2 * r₁ ^ 2
     then lockedEquilRe ω_val K r₁ * g_val else 0) ≤
    (if ω_val ^ 2 < K ^ 2 * r₂ ^ 2
     then lockedEquilRe ω_val K r₂ * g_val else 0) := by
  by_cases h₁ : ω_val ^ 2 < K ^ 2 * r₁ ^ 2
  · have h₂ : ω_val ^ 2 < K ^ 2 * r₂ ^ 2 :=
      lt_of_lt_of_le h₁ (by nlinarith [sq_nonneg K, pow_le_pow_left₀ (le_of_lt hr₁) hr 2])
    simp only [if_pos h₁, if_pos h₂]
    exact mul_le_mul_of_nonneg_right (lockedEquilRe_mono _ _ hK hr₁ hr₂ hr h₁) hg
  · simp only [if_neg h₁]
    split_ifs with h₂
    · exact mul_nonneg (le_of_lt (lockedEquilRe_pos _ _ _ hK hr₂ h₂)) hg
    · exact le_refl _

theorem selfConsistencyF_nonneg (ω_freq : Ω → ℝ) (K r : ℝ)
    (g : Ω → ℝ) (hK : 0 < K) (hr : 0 < r) (hg : ∀ ω, 0 ≤ g ω) :
    0 ≤ selfConsistencyF ω_freq K r g μ := by
  unfold selfConsistencyF
  exact integral_nonneg fun ω => scF_integrand_nonneg _ _ _ _ hK hr (hg ω)

theorem selfConsistencyF_le_integral (ω_freq : Ω → ℝ) (K r : ℝ)
    (g : Ω → ℝ) (hK : 0 < K) (hr : 0 < r)
    (hg : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ) :
    selfConsistencyF ω_freq K r g μ ≤ ∫ ω, g ω ∂μ := by
  unfold selfConsistencyF
  exact integral_mono_of_nonneg
    (ae_of_all μ fun ω => scF_integrand_nonneg _ _ _ _ hK hr (hg ω))
    hg_int
    (ae_of_all μ fun ω => scF_integrand_le_g _ _ _ _ hK hr (hg ω))

theorem selfConsistencyF_mono (ω_freq : Ω → ℝ) (K : ℝ)
    (g : Ω → ℝ) (hK : 0 < K) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr : r₁ ≤ r₂) (hg : ∀ ω, 0 ≤ g ω)
    (h_int : Integrable (fun ω => if (ω_freq ω) ^ 2 < K ^ 2 * r₂ ^ 2
        then lockedEquilRe (ω_freq ω) K r₂ * g ω else 0) μ) :
    selfConsistencyF ω_freq K r₁ g μ ≤ selfConsistencyF ω_freq K r₂ g μ := by
  unfold selfConsistencyF
  exact integral_mono_of_nonneg
    (ae_of_all μ fun ω => scF_integrand_nonneg _ _ _ _ hK hr₁ (hg ω))
    h_int
    (ae_of_all μ fun ω => scF_integrand_mono _ _ _ _ _ hK hr₁ hr₂ hr (hg ω))

end
