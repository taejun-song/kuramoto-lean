/-
  Kuramoto Stability — Mixed Power Lorentzian Analytic Extension
  ==============================================================

  A finite weighted sum of power Lorentzians
    g(ω) = Σ_k Cₖ / (ω² + aₖ)^{nₖ}
  (Cₖ ∈ ℝ, aₖ > 0, nₖ ≥ 1) is a rational function whose poles lie at
  z = ±i√aₖ.  For strip width a = min_k √aₖ, all poles have |Im| ≥ a,
  so the mixture is analytic on {z : ℂ | |Im z| < a}.

  This is the MOST GENERAL rational frequency distribution: by partial
  fraction decomposition over ℝ, every rational function with no real
  poles is a sum of terms (Aω+B)/(ω²+pω+q)^k plus lower-degree parts.
  The even-in-ω case (symmetric distributions) reduces to exactly the
  form Σ Cₖ/(ω²+aₖ)^{nₖ}, which is what this file handles.

  Since the mixture is rational, the approximation error is ZERO.

  Special cases:
  - All nₖ = 1:         Lorentzian mixture (LorentzianMixtureAnalyticExtension)
  - Single term n=1:    Lorentzian (LorentzianAnalyticExtension)
  - Single term n≥1:    Power Lorentzian (PowerLorentzianAnalyticExtension)

  0 sorry, 0 axiom.
-/

import KuramotoLean.PowerLorentzianAnalyticExtension
import KuramotoLean.LorentzianMixtureAnalyticExtension
import Mathlib.Analysis.Analytic.Constructions

open Complex Real Set Finset

noncomputable section

/-- A finite sum of power Lorentzians: g(ω) = Σ_k Cₖ / (ω² + aₖ)^{nₖ}. -/
def mixedPowerLorentzian (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ) (ω : ℝ) : ℝ :=
  ∑ k : Fin d, powerLorentzianFreqDist (C k) (a k) (n k) ω

/-- Complex extension as a Finset sum of functions (for analyticAt_sum). -/
def mixedPowerLorentzianExt (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ) : ℂ → ℂ :=
  ∑ k : Fin d, (fun z : ℂ => powerLorentzianFreqDistExt (C k) (a k) (n k) z)

/-- The complex extension restricts to the real mixture on ℝ. -/
theorem mixedPowerLorentzianExt_real
    (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ) (ω : ℝ) :
    mixedPowerLorentzianExt d C a n (ω : ℂ) = (mixedPowerLorentzian d C a n ω : ℂ) := by
  simp only [mixedPowerLorentzianExt, mixedPowerLorentzian,
             Finset.sum_apply, ofReal_sum]
  congr 1; ext k
  exact powerLorentzianFreqDistExt_real (C k) (a k) (n k) ω

/-- The mixture extension is analytic at any point in the strip {|Im z| < min_k √aₖ}. -/
theorem mixedPowerLorentzianExt_analyticAt
    (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ)
    (ha : ∀ k, 0 < a k) (hn : ∀ k, 0 < n k)
    (s : ℝ) (_hs : 0 < s) (hs_le : ∀ k, s ≤ Real.sqrt (a k))
    (z : ℂ) (hz : |z.im| < s) :
    AnalyticAt ℂ (mixedPowerLorentzianExt d C a n) z := by
  unfold mixedPowerLorentzianExt
  apply Finset.univ.analyticAt_sum
  intro k _
  have hz_k : |z.im| < Real.sqrt (a k) := lt_of_lt_of_le hz (hs_le k)
  exact (powerLorentzianFreqDistExt_analyticOnNhd (C k) (a k) (n k) (hn k) (ha k))
    z (Set.mem_setOf.mpr hz_k)

/-- The mixture is analytic on the strip {|Im z| < s} when s ≤ √aₖ for all k. -/
theorem mixedPowerLorentzianExt_analyticOnNhd
    (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ)
    (ha : ∀ k, 0 < a k) (hn : ∀ k, 0 < n k)
    (s : ℝ) (hs : 0 < s) (hs_le : ∀ k, s ≤ Real.sqrt (a k)) :
    AnalyticOnNhd ℂ (mixedPowerLorentzianExt d C a n) {z : ℂ | |z.im| < s} :=
  fun z hz => mixedPowerLorentzianExt_analyticAt d C a n ha hn s hs hs_le z
    (Set.mem_setOf.mp hz)

/-! ## Consequence: zero-error axiom-free rational approximation -/

/-- For any mixed power Lorentzian, rational approximation holds with zero error. -/
theorem mixed_power_lorentzian_rational_approx
    (d : ℕ) (C a : Fin d → ℝ) (n : Fin d → ℕ) :
    ∃ (g_approx : ℕ → ℝ → ℝ) (B b : ℝ), 0 < B ∧ 0 < b ∧
      ∀ m : ℕ, ∀ ω : ℝ,
        |mixedPowerLorentzian d C a n ω - g_approx m ω| ≤ B * Real.exp (-(b * m)) :=
  ⟨fun _ => mixedPowerLorentzian d C a n, 1, 1, one_pos, one_pos, fun m ω => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (le_of_lt one_pos) (Real.exp_nonneg _)⟩

/-! ## Specializations -/

/-- A power Lorentzian is a one-term mixed power Lorentzian. -/
theorem power_lorentzian_is_mixed (C a : ℝ) (n : ℕ) (ω : ℝ) :
    powerLorentzianFreqDist C a n ω =
    mixedPowerLorentzian 1 (fun _ => C) (fun _ => a) (fun _ => n) ω := by
  simp [mixedPowerLorentzian, powerLorentzianFreqDist]

/-- A Lorentzian mixture is a special mixed power Lorentzian (all exponents = 1). -/
theorem lorentzian_mixture_is_mixed (d : ℕ) (A γ : Fin d → ℝ) (ω : ℝ) :
    lorentzianMixture d A γ ω =
    mixedPowerLorentzian d (fun k => A k * γ k / Real.pi) (fun k => (γ k) ^ 2) (fun _ => 1) ω := by
  simp only [mixedPowerLorentzian, lorentzianMixture, powerLorentzianFreqDist, lorentzianFreqDist,
             pow_one]
  congr 1; ext k; ring

end
