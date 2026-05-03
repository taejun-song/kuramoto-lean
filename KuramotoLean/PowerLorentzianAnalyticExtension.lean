/-
  Kuramoto Stability — Power Lorentzian Analytic Extension
  =========================================================

  The "power Lorentzian" (or Pearson type VII) frequency distribution
    g_{a,n}(ω) = C / (ω² + a)^n
  with C ∈ ℝ, a > 0, n ≥ 1 is a rational function whose only poles in
  ℂ are at z = ±i√a.  Since |Im(±i√a)| = √a, the function is analytic
  on the horizontal strip {z : ℂ | |Im z| < √a}.

  Special cases
  - n=1, a=γ², C=γ/π : Lorentzian (LorentzianAnalyticExtension)
  - n=2, a=3, C=6/(√3·π) : Student's t(ν=3)
  - n=3, a=5, C=...    : Student's t(ν=5)
  - n=k, a=ν, ...      : Student's t(ν=2k-1) up to normalization

  Since g_{a,n} is itself rational, the rational approximation error is
  ZERO for all n: g_approx m = g_{a,n}.  No Padé/AAK axiom needed.

  0 sorry, 0 axiom.
-/

import KuramotoLean.LorentzianAnalyticExtension
import Mathlib.Analysis.Analytic.Constructions

open Complex Real Set

noncomputable section

/-- Power Lorentzian frequency distribution: g(ω) = C / (ω² + a)^n. -/
def powerLorentzianFreqDist (C a : ℝ) (n : ℕ) (ω : ℝ) : ℝ :=
  C / (ω ^ 2 + a) ^ n

/-- Complex extension: g_ext(z) = C / (z² + a)^n. -/
def powerLorentzianFreqDistExt (C a : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (C : ℂ) / (z ^ 2 + (a : ℂ)) ^ n

/-- The complex extension restricts to the real distribution on ℝ. -/
theorem powerLorentzianFreqDistExt_real (C a : ℝ) (n : ℕ) (ω : ℝ) :
    powerLorentzianFreqDistExt C a n (ω : ℂ) = (powerLorentzianFreqDist C a n ω : ℂ) := by
  simp only [powerLorentzianFreqDistExt, powerLorentzianFreqDist]
  push_cast
  ring

/-- The denominator (z² + a)^n is nonzero in the strip {|Im z| < √a}.
    Proof: (z²+a)^n = 0 implies z²+a = 0 (ℂ integral domain), i.e. z²+(√a)² = 0.
    This contradicts lorentzian_denom_ne_zero with γ = √a and |z.im| < √a. -/
lemma power_lorentzian_denom_ne_zero {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : |z.im| < Real.sqrt a) :
    (z ^ 2 + (a : ℂ)) ^ n ≠ 0 := by
  apply pow_ne_zero
  have hγ : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h1 : z ^ 2 + (Real.sqrt a : ℂ) ^ 2 ≠ 0 := lorentzian_denom_ne_zero hγ hz
  have h2 : (Real.sqrt a : ℂ) ^ 2 = (a : ℂ) := by
    have : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
    exact_mod_cast this
  rwa [h2] at h1

/-- The power Lorentzian extension is analytic on the strip {|Im z| < √a}. -/
theorem powerLorentzianFreqDistExt_analyticOnNhd
    (C a : ℝ) (n : ℕ) (hn : 0 < n) (ha : 0 < a) :
    AnalyticOnNhd ℂ (powerLorentzianFreqDistExt C a n) {z : ℂ | |z.im| < Real.sqrt a} := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  unfold powerLorentzianFreqDistExt
  have h_denom : AnalyticAt ℂ (fun w : ℂ => (w ^ 2 + (a : ℂ)) ^ n) z :=
    ((analyticAt_id.pow 2).add analyticAt_const).pow n
  have h_ne : (fun w : ℂ => (w ^ 2 + (a : ℂ)) ^ n) z ≠ 0 :=
    power_lorentzian_denom_ne_zero hn ha hz
  exact analyticAt_const.div h_denom h_ne

/-! ## Consequence: power Lorentzians have axiom-free rational approximations -/

/-- For any power Lorentzian, zero-error rational approximation holds.
    Since g_{a,n} is itself rational, g_approx m = g gives zero error. -/
theorem power_lorentzian_rational_approx (C a : ℝ) (n : ℕ) (hn : 0 < n) (ha : 0 < a) :
    ∃ (g_approx : ℕ → ℝ → ℝ) (B b : ℝ), 0 < B ∧ 0 < b ∧
      ∀ m : ℕ, ∀ ω : ℝ,
        |powerLorentzianFreqDist C a n ω - g_approx m ω| ≤ B * Real.exp (-(b * m)) :=
  ⟨fun _ => powerLorentzianFreqDist C a n, 1, 1, one_pos, one_pos, fun m ω => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (le_of_lt one_pos) (Real.exp_nonneg _)⟩

/-! ## Lorentzian as a special case -/

/-- The Lorentzian is a power Lorentzian with n=1, a=γ², C=γ/π. -/
theorem lorentzian_is_power_lorentzian (γ ω : ℝ) :
    lorentzianFreqDist γ ω = powerLorentzianFreqDist (γ / Real.pi) (γ ^ 2) 1 ω := by
  simp [lorentzianFreqDist, powerLorentzianFreqDist]

/-- The Lorentzian extension is a power Lorentzian extension with n=1, a=γ², C=γ/π. -/
theorem lorentzianExt_is_power_lorentzianExt (γ : ℝ) (z : ℂ) :
    lorentzianFreqDistExt γ z = powerLorentzianFreqDistExt (γ / Real.pi) (γ ^ 2) 1 z := by
  simp [lorentzianFreqDistExt, powerLorentzianFreqDistExt]

end
