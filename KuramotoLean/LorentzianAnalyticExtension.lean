/-
  Kuramoto Stability — Lorentzian Analytic Extension
  ==================================================

  Proves that the Lorentzian frequency distribution
    g(ω) = γ / π / (ω² + γ²)
  admits a complex analytic extension to the horizontal strip
    S_γ = {z : ℂ | |Im z| < γ}.

  Key step: z² + γ² ≠ 0 in S_γ because z² + γ² = (z + iγ)(z - iγ),
  and ±iγ have |Im| = γ, which is excluded from S_γ.

  The Lorentzian is itself a rational function, so g_approx n = g
  yields zero error (≤ C·exp(-cn) trivially). No approximation theory needed.

  0 sorry, 0 axioms.
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex Real Set

noncomputable section

/-- The Lorentzian frequency distribution: g(ω) = γ / π / (ω² + γ²). -/
def lorentzianFreqDist (γ ω : ℝ) : ℝ := γ / Real.pi / (ω ^ 2 + γ ^ 2)

/-- Complex extension of the Lorentzian: g_ext(z) = (γ/π) / (z² + γ²). -/
def lorentzianFreqDistExt (γ : ℝ) (z : ℂ) : ℂ :=
  ((γ / Real.pi : ℝ) : ℂ) / (z ^ 2 + (γ : ℂ) ^ 2)

/-- The complex extension restricts to the real distribution on ℝ. -/
theorem lorentzianFreqDistExt_real (γ ω : ℝ) :
    lorentzianFreqDistExt γ (ω : ℂ) = (lorentzianFreqDist γ ω : ℂ) := by
  simp only [lorentzianFreqDistExt, lorentzianFreqDist]
  push_cast
  ring

/-- The denominator z² + γ² is nonzero throughout the strip {z | |Im z| < γ}.
    Proof: if z² + γ² = 0, extract re/im parts: 2·z.re·z.im = 0.
    Case z.re = 0: z.im² = γ², so |z.im| = γ, contradicting |z.im| < γ.
    Case z.im = 0: z.re² + γ² = 0, impossible since γ > 0. -/
lemma lorentzian_denom_ne_zero {γ : ℝ} (hγ : 0 < γ) {z : ℂ} (hz : |z.im| < γ) :
    z ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
  intro h
  have h_re := congr_arg Complex.re h
  have h_im := congr_arg Complex.im h
  simp only [Complex.add_re, Complex.zero_re, sq, Complex.mul_re, Complex.ofReal_re,
             Complex.ofReal_im, mul_zero, sub_zero] at h_re
  simp only [Complex.add_im, Complex.zero_im, sq, Complex.mul_im, Complex.ofReal_re,
             Complex.ofReal_im, mul_zero, zero_mul, add_zero] at h_im
  -- h_re : z.re * z.re - z.im * z.im + γ * γ = 0
  -- h_im : z.re * z.im + z.im * z.re = 0
  rw [mul_comm z.im z.re] at h_im
  have h_prod : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp h_prod with hre0 | him0
  · -- z.re = 0 → z.im² = γ², contradicting |z.im| < γ
    have hre2 : z.re * z.re = 0 := by rw [hre0]; ring
    have hzim_sq : z.im ^ 2 = γ ^ 2 := by simp only [sq]; linarith
    linarith [sq_lt_sq' (abs_lt.mp hz).1 (abs_lt.mp hz).2]
  · -- z.im = 0 → z.re² + γ² = 0, impossible
    have hzim2 : z.im * z.im = 0 := by rw [him0]; ring
    nlinarith [mul_self_nonneg z.re, mul_pos hγ hγ]

/-- The Lorentzian complex extension is analytic on the strip {z | |Im z| < γ}. -/
theorem lorentzianFreqDistExt_analyticOnNhd (γ : ℝ) (hγ : 0 < γ) :
    AnalyticOnNhd ℂ (lorentzianFreqDistExt γ) {z : ℂ | |z.im| < γ} := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  unfold lorentzianFreqDistExt
  have h_denom : AnalyticAt ℂ (fun w : ℂ => w ^ 2 + (γ : ℂ) ^ 2) z :=
    (analyticAt_id.pow 2).add analyticAt_const
  have h_ne : (fun w : ℂ => w ^ 2 + (γ : ℂ) ^ 2) z ≠ 0 :=
    lorentzian_denom_ne_zero hγ hz
  exact analyticAt_const.div h_denom h_ne

/-! ## Consequence: Lorentzian g admits exponential rational approximations -/

/-- For the Lorentzian distribution (itself a rational function), the trivial approximation
    g_approx n = g has zero error, which satisfies ≤ C·exp(-cn) for any C, c > 0.
    This is proved WITHOUT the rational_approximation_rate axiom — no Padé/AAK theory needed
    since the Lorentzian is already rational. -/
theorem lorentzian_rational_approx (γ : ℝ) (hγ : 0 < γ) :
    ∃ (g_approx : ℕ → ℝ → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n : ℕ, ∀ ω : ℝ, |lorentzianFreqDist γ ω - g_approx n ω| ≤ C * Real.exp (-(c * n)) :=
  ⟨fun _ => lorentzianFreqDist γ, 1, 1, one_pos, one_pos, fun n ω => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (le_of_lt one_pos) (Real.exp_nonneg _)⟩

end
