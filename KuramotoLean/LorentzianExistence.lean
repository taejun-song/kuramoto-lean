/-
  Kuramoto Stability — Lorentzian ODE Global Existence via Explicit Formula
  =========================================================================

  The Lorentzian ODE  ṙ = (K/2 - γ)r - (K/2)r³  is a Bernoulli equation.
  Under the substitution  w = 1/r²,  it becomes the linear ODE:

      w' = -(K - 2γ)·w + K   (with μ = K/2 - γ > 0)

  with explicit solution:

      w(t) = (1/r₀² - B)·exp(-(K-2γ)t) + B,     B = K/(K-2γ)
      r(t) = √(w(t)⁻¹)

  Main result: `lorentzian_continuous_solution_exists` constructs a
  LorentzianContinuousSolution from any (K, γ, r₀) with K > 2γ, r₀ ∈ (0,1).

  0 sorry.
-/

import KuramotoLean.LorentzianFromODE
import KuramotoLean.ExplicitRate
import KuramotoLean.ComparisonGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.ODE.PicardLindelof

open Real Filter Set

noncomputable section

/-! ## The Bernoulli transform: w(t) = A·exp(-(K-2γ)t) + B -/

/-- Explicit solution to the linear ODE w' = -(K-2γ)w + K with w(0) = 1/r₀². -/
def w_func (K γ r₀ : ℝ) (t : ℝ) : ℝ :=
  (1 / r₀ ^ 2 - K / (K - 2 * γ)) * Real.exp (-(K - 2 * γ) * t) + K / (K - 2 * γ)

lemma w_func_zero (K γ r₀ : ℝ) : w_func K γ r₀ 0 = 1 / r₀ ^ 2 := by
  simp [w_func]

/-- w(t) > 0 for t ≥ 0 (convex combination of 1/r₀² and B, both positive). -/
lemma w_func_pos (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    0 < w_func K γ r₀ t := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  have hB : 0 < K / (K - 2 * γ) := div_pos hK hd
  have hr₀_sq : 0 < 1 / r₀ ^ 2 := by positivity
  have he_le : Real.exp (-(K - 2 * γ) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have he_pos : 0 < Real.exp (-(K - 2 * γ) * t) := Real.exp_pos _
  have hrw : w_func K γ r₀ t =
      1 / r₀ ^ 2 * Real.exp (-(K - 2 * γ) * t) +
      K / (K - 2 * γ) * (1 - Real.exp (-(K - 2 * γ) * t)) := by
    simp only [w_func]; ring
  rw [hrw]
  linarith [mul_pos hr₀_sq he_pos, mul_nonneg hB.le (by linarith : 0 ≤ 1 - Real.exp (-(K-2*γ)*t))]

/-- w(t) > 1 for t ≥ 0 (implies r(t) < 1). -/
lemma w_func_gt_one (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    1 < w_func K γ r₀ t := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  have hB : 1 < K / (K - 2 * γ) := (one_lt_div hd).mpr (by linarith)
  have hr₀_sq_pos : (0 : ℝ) < r₀ ^ 2 := by positivity
  have hr₀_sq : 1 < 1 / r₀ ^ 2 := by
    rw [lt_div_iff₀ hr₀_sq_pos, one_mul]
    nlinarith [sq_nonneg (1 - r₀)]
  have he_le : Real.exp (-(K - 2 * γ) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have he_pos : 0 < Real.exp (-(K - 2 * γ) * t) := Real.exp_pos _
  have hrw : w_func K γ r₀ t =
      1 / r₀ ^ 2 * Real.exp (-(K - 2 * γ) * t) +
      K / (K - 2 * γ) * (1 - Real.exp (-(K - 2 * γ) * t)) := by
    simp only [w_func]; ring
  rw [hrw]
  -- w(t) = (1/r₀²)·e + B·(1-e) > 1·e + 1·(1-e) = 1
  have h1 : 1 * Real.exp (-(K - 2 * γ) * t) ≤
      1 / r₀ ^ 2 * Real.exp (-(K - 2 * γ) * t) :=
    mul_le_mul_of_nonneg_right hr₀_sq.le he_pos.le
  have h2 : 1 * (1 - Real.exp (-(K - 2 * γ) * t)) ≤
      K / (K - 2 * γ) * (1 - Real.exp (-(K - 2 * γ) * t)) :=
    mul_le_mul_of_nonneg_right hB.le (by linarith)
  -- Need strictness from h1 (since 1/r₀² > 1 strictly and e > 0)
  have h1_strict : 1 * Real.exp (-(K - 2 * γ) * t) <
      1 / r₀ ^ 2 * Real.exp (-(K - 2 * γ) * t) :=
    mul_lt_mul_of_pos_right hr₀_sq he_pos
  linarith [h1_strict, h2]

/-! ## HasDerivAt for w_func -/

/-- w satisfies the linear ODE w'(t) = -(K-2γ)·w(t) + K. -/
lemma w_func_hasDerivAt (K γ r₀ : ℝ) (hKγ : 2 * γ < K) (t : ℝ) :
    HasDerivAt (w_func K γ r₀) (-(K - 2 * γ) * w_func K γ r₀ t + K) t := by
  have hK2γ_ne : K - 2 * γ ≠ 0 := by linarith
  have hinner : HasDerivAt (fun y => -(K - 2 * γ) * y) (-(K - 2 * γ)) t := by
    have h := (hasDerivAt_id t).const_mul (-(K - 2 * γ))
    simp only [id_eq, mul_one] at h; exact h
  have he : HasDerivAt (fun s => Real.exp (-(K - 2 * γ) * s))
      (Real.exp (-(K - 2 * γ) * t) * (-(K - 2 * γ))) t :=
    (Real.hasDerivAt_exp _).comp t hinner
  have hsum := (he.const_mul (1 / r₀ ^ 2 - K / (K - 2 * γ))).add
      (hasDerivAt_const t (K / (K - 2 * γ)))
  have hfun : ((fun y : ℝ => (1 / r₀ ^ 2 - K / (K - 2 * γ)) * Real.exp (-(K - 2 * γ) * y)) +
      fun _ => K / (K - 2 * γ)) = w_func K γ r₀ := by
    funext s; simp [Pi.add_apply, w_func]
  have hval : (1 / r₀ ^ 2 - K / (K - 2 * γ)) * (Real.exp (-(K - 2 * γ) * t) *
      (-(K - 2 * γ))) + 0 = -(K - 2 * γ) * w_func K γ r₀ t + K := by
    rw [show w_func K γ r₀ t = (1 / r₀ ^ 2 - K / (K - 2 * γ)) *
        Real.exp (-(K - 2 * γ) * t) + K / (K - 2 * γ) from rfl]
    field_simp [hK2γ_ne, show K - γ * 2 ≠ 0 from by linarith]
    ring
  rw [hfun] at hsum
  rwa [hval] at hsum

/-! ## Explicit solution r(t) = √(w(t)⁻¹) -/

/-- The explicit Lorentzian ODE solution. -/
def lorentzian_explicit (K γ r₀ : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((w_func K γ r₀ t)⁻¹)

/-- **r* is a fixed point of the Lorentzian ODE**: the ODE velocity field vanishes at r*.
    lorentzianODE K γ r* = 0 because K/2·r*² = K/2-γ (proved by substituting r*²=1-2γ/K). -/
theorem lorentzian_rstar_is_fixed_point (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) :
    lorentzianODE K γ (Real.sqrt (1 - 2 * γ / K)) = 0 := by
  simp only [lorentzianODE]
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hcube : Real.sqrt (1 - 2 * γ / K) ^ 3 =
      (1 - 2 * γ / K) * Real.sqrt (1 - 2 * γ / K) := by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_add, hrstar_sq]; ring
  rw [hcube]
  field_simp [ne_of_gt hK]; ring

/-- **ODE positive below r***: for r ∈ (0, r*), the Lorentzian velocity ṙ > 0.
    ṙ = (K/2)·r·(r*²-r²) > 0 because r > 0 and r² < r*². -/
theorem lorentzian_ode_pos_below_rstar (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr_pos : 0 < r) (hr_lt : r < Real.sqrt (1 - 2 * γ / K)) :
    0 < lorentzianODE K γ r := by
  rw [lorentzian_ode_factored K γ r (ne_of_gt hK)]
  apply mul_pos (mul_pos (by linarith) hr_pos)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr_sq_lt : r ^ 2 < Real.sqrt (1 - 2 * γ / K) ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < Real.sqrt (1 - 2*γ/K) - r)
                       (by linarith : 0 < Real.sqrt (1 - 2*γ/K) + r)]
  linarith [hrstar_sq ▸ hr_sq_lt]

/-- **ODE negative above r***: for r ∈ (r*, 1), the Lorentzian velocity ṙ < 0.
    ṙ = (K/2)·r·(r*²-r²) < 0 because r > r* > 0 and r² > r*². -/
theorem lorentzian_ode_neg_above_rstar (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr_gt : Real.sqrt (1 - 2 * γ / K) < r) (hr_lt : r < 1) :
    lorentzianODE K γ r < 0 := by
  rw [lorentzian_ode_factored K γ r (ne_of_gt hK)]
  have hrstar_pos := Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hr_pos : 0 < r := hrstar_pos.trans hr_gt
  apply mul_neg_of_pos_of_neg (mul_pos (by linarith) hr_pos)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr_sq_gt : Real.sqrt (1 - 2 * γ / K) ^ 2 < r ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < r - Real.sqrt (1 - 2*γ/K))
                       (by linarith : 0 < r + Real.sqrt (1 - 2*γ/K))]
  linarith [hrstar_sq ▸ hr_sq_gt]

/-- **Exact initial-data separation**: the w-function difference is proportional to exp(-μt).
    The B = K/(K-2γ) terms cancel exactly; only the initial-data difference 1/r₀²-1/r₀'² survives. -/
theorem w_func_diff (K γ r₀ r₀' : ℝ) (t : ℝ) :
    w_func K γ r₀ t - w_func K γ r₀' t =
      (1 / r₀ ^ 2 - 1 / r₀' ^ 2) * Real.exp (-(K - 2 * γ) * t) := by
  simp only [w_func]; ring

/-- **w-function convergence**: |w(t,r₀) - w(t,r₀')| → 0 as t → ∞. -/
theorem w_func_diff_tendsto (K γ r₀ r₀' : ℝ) (hKγ : 2 * γ < K) :
    Tendsto (fun t => |w_func K γ r₀ t - w_func K γ r₀' t|) atTop (nhds 0) := by
  simp_rw [w_func_diff, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hmu : 0 < K - 2 * γ := by linarith
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(K - 2 * γ) * t)) atTop (nhds 0) := by
    have h1 := tendsto_id.const_mul_atTop hmu
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr (fun t => by
      simp only [Function.comp, id]; congr 1; ring)
  have hmul := hexp.const_mul |1 / r₀ ^ 2 - 1 / r₀' ^ 2|
  simp only [mul_zero] at hmul
  exact hmul

/-- r(0) = r₀. -/
lemma lorentzian_explicit_init (K γ r₀ : ℝ) (hr₀ : 0 < r₀) :
    lorentzian_explicit K γ r₀ 0 = r₀ := by
  simp only [lorentzian_explicit, w_func_zero, one_div, inv_inv]
  exact Real.sqrt_sq hr₀.le

/-- r(t) > 0. -/
lemma lorentzian_explicit_pos (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    0 < lorentzian_explicit K γ r₀ t := by
  simp only [lorentzian_explicit, Real.sqrt_pos]
  exact inv_pos.mpr (w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht)

/-- r(t)² = w(t)⁻¹. -/
lemma lorentzian_explicit_sq (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ^ 2 = (w_func K γ r₀ t)⁻¹ := by
  simp only [lorentzian_explicit]
  rw [Real.sq_sqrt (inv_nonneg.mpr (w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht).le)]

/-- r(t) < 1. -/
lemma lorentzian_explicit_lt_one (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t < 1 := by
  have hw_gt : 1 < w_func K γ r₀ t :=
    w_func_gt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hw_pos : 0 < w_func K γ r₀ t :=
    w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  simp only [lorentzian_explicit]
  rw [← Real.sqrt_one]
  apply Real.sqrt_lt_sqrt (inv_nonneg.mpr hw_pos.le)
  -- Need: (w t)⁻¹ < 1, follows from 1 < w t
  have hmul : w_func K γ r₀ t * (w_func K γ r₀ t)⁻¹ = 1 :=
    mul_inv_cancel₀ hw_pos.ne'
  nlinarith [inv_pos.mpr hw_pos,
             mul_pos hw_pos (inv_pos.mpr hw_pos),
             mul_pos (show 0 < w_func K γ r₀ t - 1 from by linarith) (inv_pos.mpr hw_pos)]

/-! ## Key algebraic identity -/

/-- If r²·w = 1, the Bernoulli derivative formula equals lorentzianODE. -/
private lemma bernoulli_deriv_eq (K γ : ℝ) (w r : ℝ)
    (hr_pos : 0 < r) (hw_pos : 0 < w) (hrw : r ^ 2 * w = 1) :
    (-(-(K - 2 * γ) * w + K) / w ^ 2) / (2 * r) = lorentzianODE K γ r := by
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hw_ne : w ≠ 0 := hw_pos.ne'
  have h1 : r ^ 2 * w ^ 2 = w := by
    have : r ^ 2 * w ^ 2 = r ^ 2 * w * w := by ring
    rw [this, hrw, one_mul]
  have h2 : r ^ 4 * w ^ 2 = 1 := by
    have : r ^ 4 * w ^ 2 = (r ^ 2 * w) ^ 2 := by ring
    rw [this, hrw]; norm_num
  unfold lorentzianODE
  rw [div_div]
  have hdenom : w ^ 2 * (2 * r) ≠ 0 :=
    (mul_pos (pow_pos hw_pos 2) (by linarith)).ne'
  rw [div_eq_iff hdenom]
  linear_combination -(K - 2 * γ) * h1 + K * h2

/-! ## The explicit solution satisfies the ODE -/

/-- The explicit solution satisfies the Lorentzian ODE. -/
theorem lorentzian_explicit_hasDerivAt (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K) (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (lorentzian_explicit K γ r₀)
      (lorentzianODE K γ (lorentzian_explicit K γ r₀ t)) t := by
  simp only [lorentzian_explicit]
  set w := w_func K γ r₀ with hw_def
  have hw_pos : 0 < w t := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  -- HasDerivAt for w⁻¹
  have hinv_deriv : HasDerivAt (fun t => (w t)⁻¹)
      (-(-(K - 2 * γ) * w t + K) / (w t) ^ 2) t :=
    (w_func_hasDerivAt K γ r₀ hKγ t).inv hw_pos.ne'
  -- HasDerivAt for √(w⁻¹)
  have hinv_ne : (w t)⁻¹ ≠ 0 := (inv_pos.mpr hw_pos).ne'
  have hsqrt : HasDerivAt (fun t => Real.sqrt ((w t)⁻¹))
      ((-(-(K - 2 * γ) * w t + K) / (w t) ^ 2) / (2 * Real.sqrt ((w t)⁻¹))) t :=
    hinv_deriv.sqrt hinv_ne
  -- Relate r² and w: √(w⁻¹)² * w = 1
  have hrw : Real.sqrt ((w t)⁻¹) ^ 2 * w t = 1 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hw_pos.le)]; field_simp
  have hr_pos : 0 < Real.sqrt ((w t)⁻¹) := by
    rw [Real.sqrt_pos]; exact inv_pos.mpr hw_pos
  -- Combine: use Bernoulli identity to convert derivative to lorentzianODE
  have hkey := bernoulli_deriv_eq K γ (w t) (Real.sqrt ((w t)⁻¹)) hr_pos hw_pos hrw
  exact hkey ▸ hsqrt

/-! ## Continuity -/

lemma lorentzian_explicit_continuousOn (K γ r₀ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    ContinuousOn (lorentzian_explicit K γ r₀) (Ici 0) := by
  change ContinuousOn (fun t => Real.sqrt ((w_func K γ r₀ t)⁻¹)) (Ici 0)
  apply ContinuousOn.sqrt
  apply ContinuousOn.inv₀
  · change ContinuousOn (fun t => (1 / r₀ ^ 2 - K / (K - 2 * γ)) *
          Real.exp (-(K - 2 * γ) * t) + K / (K - 2 * γ)) (Ici 0)
    fun_prop
  · intro t ht
    exact (w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht).ne'

/-! ## Main theorem -/

/-- **Global ODE existence**: for K > 2γ and r₀ ∈ (0,1), there exists a
    LorentzianContinuousSolution with r(0) = r₀, constructed via the explicit
    Bernoulli formula r(t) = √(w(t)⁻¹). -/
theorem lorentzian_continuous_solution_exists (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    ∃ S : LorentzianContinuousSolution, S.K = K ∧ S.γ = γ ∧ S.r 0 = r₀ :=
  ⟨{ K := K
     γ := γ
     hK_pos := hK
     hγ_pos := hγ
     hK_gt := hKγ
     r := lorentzian_explicit K γ r₀
     hr_ode := fun t ht =>
       lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
     hr_cont :=
       lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
     hr_init_pos := by
       rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hr₀_pos
     hr_init_lt := by
       rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hr₀_lt },
   rfl, rfl, lorentzian_explicit_init K γ r₀ hr₀_pos⟩

/-- **End-to-end convergence for the explicit Bernoulli solution**:
    for K > 2γ and r₀ ∈ (0,1), the explicit solution r(t) = √(w(t)⁻¹)
    converges to r* = √(1 - 2γ/K) at integer sampling times. -/
theorem lorentzian_explicit_convergence (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |lorentzian_explicit K γ r₀ n - Real.sqrt (1 - 2 * γ / K)| < ε := by
  exact lorentzian_convergence_from_ode
    { K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
      r := lorentzian_explicit K γ r₀,
      hr_ode := fun t ht =>
        lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht,
      hr_cont := lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt,
      hr_init_pos := by rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hr₀_pos,
      hr_init_lt := by rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hr₀_lt }

/-! ## Explicit exponential rate bound -/

/-- The squared order-parameter error decays exponentially:
    (r(t)² - r*²)² ≤ A²·exp(-2μt), where A = 1/r₀²-B and μ = K-2γ.
    Proof: r²-r*² = -(w⁻¹-B⁻¹) = A·exp(-μt)/(w·B) and w·B > 1. -/
theorem lorentzian_explicit_sq_diff_bound (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t ^ 2 - (1 - 2 * γ / K)) ^ 2 ≤
      (1 / r₀ ^ 2 - K / (K - 2 * γ)) ^ 2 * Real.exp (-2 * (K - 2 * γ) * t) := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  have hB_pos : (0 : ℝ) < K / (K - 2 * γ) := div_pos hK hd
  set w := w_func K γ r₀ t with hw_def
  have hw_pos : 0 < w := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hw_gt : 1 < w := w_func_gt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr2 : lorentzian_explicit K γ r₀ t ^ 2 = w⁻¹ :=
    lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hrstar : (1 - 2 * γ / K) = (K / (K - 2 * γ))⁻¹ := by
    field_simp [hK.ne', hd.ne']
  -- B - w = -(A·exp(-μt)) where A = 1/r₀²-B
  have hBw : K / (K - 2 * γ) - w =
      -((1 / r₀ ^ 2 - K / (K - 2 * γ)) * Real.exp (-(K - 2 * γ) * t)) := by
    simp only [hw_def, w_func]; ring
  -- Key: (w⁻¹-B⁻¹)·(w·B) = B-w = -(A·exp(-μt))
  have hprod : (w⁻¹ - (K / (K - 2 * γ))⁻¹) * (w * (K / (K - 2 * γ))) =
      -(1 / r₀ ^ 2 - K / (K - 2 * γ)) * Real.exp (-(K - 2 * γ) * t) := by
    have hw_ne := hw_pos.ne'
    have hB_ne := hB_pos.ne'
    rw [show (w⁻¹ - (K/(K-2*γ))⁻¹) * (w * (K/(K-2*γ))) = K/(K-2*γ) - w from by
      field_simp [hw_ne, hB_ne]]
    linarith [hBw]
  -- (w⁻¹-B⁻¹)²·(w·B)² = (A·exp(-μt))²
  have hkey : (w⁻¹ - (K / (K - 2 * γ))⁻¹) ^ 2 * (w * (K / (K - 2 * γ))) ^ 2 =
      (1 / r₀ ^ 2 - K / (K - 2 * γ)) ^ 2 * Real.exp (-2 * (K - 2 * γ) * t) := by
    calc (w⁻¹ - (K/(K-2*γ))⁻¹) ^ 2 * (w * (K/(K-2*γ))) ^ 2
        = ((w⁻¹ - (K/(K-2*γ))⁻¹) * (w * (K/(K-2*γ)))) ^ 2 := by ring
      _ = (-(1/r₀^2-K/(K-2*γ)) * Real.exp (-(K-2*γ)*t)) ^ 2 := by rw [hprod]
      _ = (1/r₀^2-K/(K-2*γ))^2 * Real.exp (-2*(K-2*γ)*t) := by
          rw [mul_pow, neg_sq, sq (Real.exp (-(K-2*γ)*t)), ← Real.exp_add]
          congr 1; ring
  -- w·B > 1 → (w·B)² ≥ 1
  have hwB2 : 1 ≤ (w * (K / (K - 2 * γ))) ^ 2 := by
    have hB_gt : 1 < K / (K - 2 * γ) := (one_lt_div hd).mpr (by linarith)
    have hwB_gt : 1 < w * (K / (K - 2 * γ)) := by nlinarith
    nlinarith [sq_nonneg (w * (K / (K - 2 * γ)) - 1)]
  -- (w⁻¹-B⁻¹)² ≤ (w⁻¹-B⁻¹)²·(w·B)² = RHS
  rw [hr2, hrstar]
  calc (w⁻¹ - (K / (K - 2 * γ))⁻¹) ^ 2
      ≤ (w⁻¹ - (K / (K - 2 * γ))⁻¹) ^ 2 * (w * (K / (K - 2 * γ))) ^ 2 :=
        le_mul_of_one_le_right (sq_nonneg _) hwB2
    _ = (1 / r₀ ^ 2 - K / (K - 2 * γ)) ^ 2 * Real.exp (-2 * (K - 2 * γ) * t) := hkey

/-- **Continuous-time convergence**: the explicit Bernoulli solution
    r(t) = √(w(t)⁻¹) converges to r* = √(1 - 2γ/K) as t → ∞ (continuous time). -/
theorem lorentzian_explicit_tendsto (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    Tendsto (lorentzian_explicit K γ r₀) atTop
      (nhds (Real.sqrt (1 - 2 * γ / K))) := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  have hB_pos : (0 : ℝ) < K / (K - 2 * γ) := div_pos hK hd
  -- exp(-(K-2γ)t) → 0
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(K - 2 * γ) * t)) atTop (nhds 0) := by
    have hmul : Tendsto (fun t : ℝ => (K - 2 * γ) * t) atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro b
      refine ⟨b / (K - 2 * γ), fun y hy => ?_⟩
      nlinarith [(div_le_iff₀ hd).mp hy]
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
    have heq : ((fun x : ℝ => Real.exp (-x)) ∘ fun t => (K - 2 * γ) * t) =
        fun t : ℝ => Real.exp (-(K - 2 * γ) * t) := by
      ext t; simp only [Function.comp]; congr 1; ring
    rwa [heq] at hcomp
  -- w(t) → B = K/(K-2γ)
  have hw : Tendsto (w_func K γ r₀) atTop (nhds (K / (K - 2 * γ))) := by
    change Tendsto (fun t : ℝ => (1 / r₀ ^ 2 - K / (K - 2 * γ)) *
        Real.exp (-(K - 2 * γ) * t) + K / (K - 2 * γ)) atTop _
    have h0 : Tendsto (fun t : ℝ => (1 / r₀ ^ 2 - K / (K - 2 * γ)) *
        Real.exp (-(K - 2 * γ) * t)) atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℝ => 1 / r₀ ^ 2 - K / (K - 2 * γ)) atTop
          (nhds (1 / r₀ ^ 2 - K / (K - 2 * γ))) := tendsto_const_nhds
      have h := hc.mul hexp
      simpa [mul_zero] using h
    have h1 : Tendsto (fun _ : ℝ => K / (K - 2 * γ)) atTop (nhds (K / (K - 2 * γ))) :=
      tendsto_const_nhds
    simpa using h0.add h1
  -- w⁻¹ → B⁻¹
  have hinv : Tendsto (fun t => (w_func K γ r₀ t)⁻¹) atTop (nhds (K / (K - 2 * γ))⁻¹) := by
    have hg : Tendsto (Inv.inv : ℝ → ℝ) (nhds (K / (K - 2 * γ))) (nhds (K / (K - 2 * γ))⁻¹) :=
      continuousAt_inv₀ hB_pos.ne'
    exact hg.comp hw
  -- √(w⁻¹) → √(B⁻¹) = r*
  have hsqrt : Tendsto (fun t => Real.sqrt ((w_func K γ r₀ t)⁻¹)) atTop
      (nhds (Real.sqrt (K / (K - 2 * γ))⁻¹)) := by
    have hg : Tendsto Real.sqrt (nhds (K / (K - 2 * γ))⁻¹)
        (nhds (Real.sqrt (K / (K - 2 * γ))⁻¹)) :=
      Real.continuous_sqrt.continuousAt
    exact hg.comp hinv
  have hstar : Real.sqrt (K / (K - 2 * γ))⁻¹ = Real.sqrt (1 - 2 * γ / K) := by
    congr 1; field_simp [hK.ne', hd.ne']
  change Tendsto (fun t => Real.sqrt ((w_func K γ r₀ t)⁻¹)) atTop _
  rwa [hstar] at hsqrt

/-- **Explicit exponential rate for |r(t) - r*|**:
    |r(t) - r*| ≤ A·exp(-μt)/r*, where A = |1/r₀²-B|, B = K/(K-2γ), μ = K-2γ.
    Proof: |r-r*| = |r²-r*²|/(r+r*) ≤ |r²-r*²|/r* ≤ A·exp(-μt)/r*. -/
theorem lorentzian_explicit_rate (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) /
        Real.sqrt (1 - 2 * γ / K) := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  set r := lorentzian_explicit K γ r₀ t
  set r_star := Real.sqrt (1 - 2 * γ / K)
  have hrstar_pos : 0 < r_star :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hr_pos : 0 < r :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  -- |r²-r*²| ≤ |A|·exp(-μt) from sq_diff_bound via sqrt
  have hA_nn : 0 ≤ |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have heq : (|1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t)) ^ 2 =
      (1 / r₀ ^ 2 - K / (K - 2 * γ)) ^ 2 * Real.exp (-2 * (K - 2 * γ) * t) := by
    rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add]; congr 1; ring
  have hrstar_sq : r_star ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hsq_diff : |r ^ 2 - r_star ^ 2| ≤
      |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) := by
    have hbound : (r ^ 2 - r_star ^ 2) ^ 2 ≤
        (1 / r₀ ^ 2 - K / (K - 2 * γ)) ^ 2 * Real.exp (-2 * (K - 2 * γ) * t) := by
      rw [hrstar_sq]
      exact lorentzian_explicit_sq_diff_bound K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
    have hsq2 : (r ^ 2 - r_star ^ 2) ^ 2 ≤
        (|1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t)) ^ 2 :=
      heq.symm ▸ hbound
    have h1 : Real.sqrt ((r ^ 2 - r_star ^ 2) ^ 2) ≤
        Real.sqrt ((|1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t)) ^ 2) :=
      Real.sqrt_le_sqrt hsq2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hA_nn] at h1
  -- |r-r*| = |r²-r*²| / (r+r*) ≤ |r²-r*²| / r*
  have hsum_pos : 0 < r + r_star := add_pos hr_pos hrstar_pos
  have hfact : |r ^ 2 - r_star ^ 2| = |r - r_star| * (r + r_star) := by
    rw [show r ^ 2 - r_star ^ 2 = (r - r_star) * (r + r_star) from by ring,
        abs_mul, abs_of_pos hsum_pos]
  have h_le : |r - r_star| * r_star ≤ |r ^ 2 - r_star ^ 2| := by
    rw [hfact]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (le_of_lt hr_pos)) (abs_nonneg _)
  rw [le_div_iff₀ hrstar_pos]
  exact h_le.trans hsq_diff

/-- **ODE uniqueness**: any LorentzianContinuousSolution equals the explicit Bernoulli
    formula at every t ≥ 0. Proof: both satisfy the same Lipschitz ODE with the same
    initial value, so Gronwall (ODE_solution_unique_of_mem_Icc_right) gives equality. -/
theorem LorentzianContinuousSolution.eq_explicit
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 < t) :
    S.r t = lorentzian_explicit S.K S.γ (S.r 0) t := by
  set r₀ := S.r 0
  have hr₀_pos : 0 < r₀ := S.hr_init_pos
  have hr₀_lt : r₀ < 1 := S.hr_init_lt
  set lipK : NNReal := ⟨2 * S.K, by linarith [S.hK_pos]⟩
  have hLip : ∀ s ∈ Set.Ico 0 t,
      LipschitzOnWith lipK (lorentzianODE S.K S.γ) (Set.Icc 0 1) :=
    fun s _ => lorentzianODE_lipschitzOnWith S.K S.γ S.hK_pos S.hK_gt (le_of_lt S.hγ_pos)
  have hf_cont : ContinuousOn S.r (Set.Icc 0 t) :=
    S.hr_cont.mono Set.Icc_subset_Ici_self
  have hf_deriv : ∀ s ∈ Set.Ico 0 t,
      HasDerivWithinAt S.r (lorentzianODE S.K S.γ (S.r s)) (Set.Ici s) s :=
    fun s hs => (S.hr_ode s hs.1).hasDerivWithinAt
  have hf_bdd : ∀ s ∈ Set.Ico 0 t, S.r s ∈ Set.Icc 0 1 :=
    fun s hs => ⟨le_of_lt (S.r_pos s hs.1), le_of_lt (S.r_lt_one s hs.1)⟩
  have hg_cont : ContinuousOn (lorentzian_explicit S.K S.γ r₀) (Set.Icc 0 t) :=
    (lorentzian_explicit_continuousOn S.K S.γ r₀ S.hK_pos S.hγ_pos S.hK_gt
      hr₀_pos hr₀_lt).mono Set.Icc_subset_Ici_self
  have hg_deriv : ∀ s ∈ Set.Ico 0 t,
      HasDerivWithinAt (lorentzian_explicit S.K S.γ r₀)
        (lorentzianODE S.K S.γ (lorentzian_explicit S.K S.γ r₀ s)) (Set.Ici s) s :=
    fun s hs =>
      (lorentzian_explicit_hasDerivAt S.K S.γ r₀ S.hK_pos S.hγ_pos S.hK_gt
        hr₀_pos hr₀_lt s hs.1).hasDerivWithinAt
  have hg_bdd : ∀ s ∈ Set.Ico 0 t,
      lorentzian_explicit S.K S.γ r₀ s ∈ Set.Icc 0 1 :=
    fun s hs => ⟨le_of_lt (lorentzian_explicit_pos S.K S.γ r₀ S.hK_pos S.hγ_pos S.hK_gt
        hr₀_pos hr₀_lt s hs.1),
      le_of_lt (lorentzian_explicit_lt_one S.K S.γ r₀ S.hK_pos S.hγ_pos S.hK_gt
        hr₀_pos hr₀_lt s hs.1)⟩
  have hinit : S.r 0 = lorentzian_explicit S.K S.γ r₀ 0 :=
    (lorentzian_explicit_init S.K S.γ r₀ hr₀_pos).symm
  have hEqOn := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => lorentzianODE S.K S.γ) (s := fun _ => Set.Icc 0 1)
    (K := lipK) (f := S.r) (g := lorentzian_explicit S.K S.γ r₀)
    hLip hf_cont hf_deriv hf_bdd hg_cont hg_deriv hg_bdd hinit
  exact hEqOn ⟨le_of_lt ht, le_refl t⟩

/-- **ODE uniqueness at t ≥ 0**: extends eq_explicit to include t = 0 (the initial time).
    For t = 0: S.r 0 = r₀ = lorentzian_explicit ... 0 by init. For t > 0: eq_explicit. -/
theorem LorentzianContinuousSolution.eq_explicit_of_nonneg
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    S.r t = lorentzian_explicit S.K S.γ (S.r 0) t := by
  rcases ht.eq_or_lt with rfl | ht_pos
  · exact (lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos).symm
  · exact S.eq_explicit t ht_pos

/-- **Uniqueness of ODE solutions**: two `LorentzianContinuousSolution`s with the same
    parameters and initial condition are equal for all t ≥ 0. Proof: both equal the
    explicit Bernoulli formula via eq_explicit_of_nonneg. -/
theorem LorentzianContinuousSolution.unique (S₁ S₂ : LorentzianContinuousSolution)
    (hK : S₁.K = S₂.K) (hγ : S₁.γ = S₂.γ) (hr₀ : S₁.r 0 = S₂.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    S₁.r t = S₂.r t := by
  rw [S₁.eq_explicit_of_nonneg t ht, S₂.eq_explicit_of_nonneg t ht, hK, hγ, hr₀]

/-- **Two-solution distance bound**: |r(t,r₀) - r(t,r₀')| ≤ (|A_r₀|+|A_r₀'|)·exp(-μt)/r*
    via the triangle inequality through r*. -/
theorem lorentzian_explicit_dist_bound (K γ r₀ r₀' : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀'_pos : 0 < r₀') (hr₀'_lt : r₀' < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
      (|1 / r₀ ^ 2 - K / (K - 2 * γ)| + |1 / r₀' ^ 2 - K / (K - 2 * γ)|) *
        Real.exp (-(K - 2 * γ) * t) / Real.sqrt (1 - 2 * γ / K) := by
  have h1 := lorentzian_explicit_rate K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h2 := lorentzian_explicit_rate K γ r₀' hK hγ hKγ hr₀'_pos hr₀'_lt t ht
  set r_star := Real.sqrt (1 - 2 * γ / K)
  have hrstar_pos : 0 < r_star :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  -- Triangle through r*: |r - r'| ≤ |r - r*| + |r' - r*|
  have htri : |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
      |lorentzian_explicit K γ r₀ t - r_star| +
        |lorentzian_explicit K γ r₀' t - r_star| := by
    have h := dist_triangle (lorentzian_explicit K γ r₀ t) r_star
                (lorentzian_explicit K γ r₀' t)
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at h
    linarith [abs_sub_comm r_star (lorentzian_explicit K γ r₀' t)]
  -- Chain with rate bounds
  calc |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t|
      ≤ |lorentzian_explicit K γ r₀ t - r_star| +
          |lorentzian_explicit K γ r₀' t - r_star| := htri
    _ ≤ |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) / r_star +
          |1 / r₀' ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) / r_star :=
          add_le_add h1 h2
    _ = (|1 / r₀ ^ 2 - K / (K - 2 * γ)| + |1 / r₀' ^ 2 - K / (K - 2 * γ)|) *
          Real.exp (-(K - 2 * γ) * t) / r_star := by ring

/-- **Universal rate bound**: any LorentzianContinuousSolution satisfies
    |r(t) - r*| ≤ |A|·exp(-μt)/r* for t > 0.
    Follows from ODE uniqueness (eq_explicit) + lorentzian_explicit_rate. -/
theorem LorentzianContinuousSolution.rate_bound
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
      |1 / S.r 0 ^ 2 - S.K / (S.K - 2 * S.γ)| * Real.exp (-(S.K - 2 * S.γ) * t) /
        Real.sqrt (1 - 2 * S.γ / S.K) := by
  rw [S.eq_explicit t ht]
  exact lorentzian_explicit_rate S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt t (le_of_lt ht)

/-- **Rate in terms of initial displacement**: B = 1/r*², so |A| = |r*²-r₀²|/(r₀²r*²).
    The rate bound becomes |r(t)-r*| ≤ |r*²-r₀²|·exp(-μt)/(r₀²·r*³). -/
theorem lorentzian_explicit_rate_initial (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      |Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2| * Real.exp (-(K - 2 * γ) * t) /
        (r₀ ^ 2 * Real.sqrt (1 - 2 * γ / K) ^ 3) := by
  have hd : (0 : ℝ) < K - 2 * γ := by linarith
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq : (0 : ℝ) < r₀ ^ 2 := sq_pos_of_pos hr₀_pos
  -- Key: B = 1/r*², so |1/r₀²-B| = |r*²-r₀²|/(r₀²·r*²)
  have hrsq_pos : 0 < Real.sqrt (1 - 2 * γ / K) ^ 2 := sq_pos_of_pos hrstar_pos
  have hA_eq : |1 / r₀ ^ 2 - K / (K - 2 * γ)| =
      |Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2| / (r₀ ^ 2 * Real.sqrt (1 - 2 * γ / K) ^ 2) := by
    have h_num_eq : 1 / r₀ ^ 2 - K / (K - 2 * γ) =
        (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) / (r₀ ^ 2 * Real.sqrt (1 - 2 * γ / K) ^ 2) := by
      rw [hrstar_sq]; field_simp [hK.ne', hd.ne', hr₀_sq.ne']
    rw [h_num_eq, abs_div]
    congr 1
    exact abs_of_pos (mul_pos hr₀_sq hrsq_pos)
  -- Use lorentzian_explicit_rate and substitute hA_eq
  have hrate := lorentzian_explicit_rate K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  rw [hA_eq] at hrate
  have hrstar3 : Real.sqrt (1 - 2 * γ / K) ^ 3 =
      Real.sqrt (1 - 2 * γ / K) ^ 2 * Real.sqrt (1 - 2 * γ / K) := by ring
  calc |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)|
      ≤ |Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2| /
          (r₀ ^ 2 * Real.sqrt (1 - 2 * γ / K) ^ 2) *
          Real.exp (-(K - 2 * γ) * t) / Real.sqrt (1 - 2 * γ / K) := hrate
    _ = |Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2| * Real.exp (-(K - 2 * γ) * t) /
          (r₀ ^ 2 * Real.sqrt (1 - 2 * γ / K) ^ 3) := by
            rw [hrstar3]; field_simp [hr₀_sq.ne', hrsq_pos.ne', hrstar_pos.ne']

/-- The derivative of the Lorentzian ODE vector field at r* is -(K-2γ).
    This confirms that the Bernoulli rate μ = K-2γ equals the linearized rate:
    the explicit formula achieves the optimal exponential rate. -/
theorem lorentzian_ode_hasDerivAt_rstar (K γ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) :
    HasDerivAt (lorentzianODE K γ) (-(K - 2 * γ)) (Real.sqrt (1 - 2 * γ / K)) := by
  set r_star := Real.sqrt (1 - 2 * γ / K)
  have hrstar_sq : r_star ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hderiv : HasDerivAt (fun r => (K / 2 - γ) * r - K / 2 * r ^ 3)
      ((K / 2 - γ) - K / 2 * (3 * r_star ^ 2)) r_star := by
    have h1 : HasDerivAt (fun r => (K / 2 - γ) * r) (K / 2 - γ) r_star := by
      have h := (hasDerivAt_id r_star).const_mul (K / 2 - γ)
      simp only [mul_one, id] at h
      exact h
    have h2 : HasDerivAt (fun r => K / 2 * r ^ 3) (K / 2 * (3 * r_star ^ 2)) r_star := by
      have h := (hasDerivAt_pow 3 r_star).const_mul (K / 2)
      simp only [Nat.cast_ofNat] at h
      convert h using 1
    exact h1.sub h2
  have hconv : lorentzianODE K γ = fun r => (K / 2 - γ) * r - K / 2 * r ^ 3 := by
    ext r; simp [lorentzianODE]
  rw [hconv]
  convert hderiv using 1
  rw [hrstar_sq]
  field_simp [ne_of_gt hK]
  ring

/-- **Local stability with explicit Lyapunov constant**: for r₀ within r*/2 of r*,
    |r(t)-r*| ≤ 10·|r₀-r*|·exp(-μt)/r*⁴. The constant 10/r*⁴ comes from:
    |r*²-r₀²| ≤ (5r*/2)·|r₀-r*| and r₀² ≥ r*²/4 (both from nearness). -/
theorem lorentzian_local_stability (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_near : |r₀ - Real.sqrt (1 - 2 * γ / K)| < Real.sqrt (1 - 2 * γ / K) / 2)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      10 * |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-(K - 2 * γ) * t) /
        Real.sqrt (1 - 2 * γ / K) ^ 4 := by
  set r_star := Real.sqrt (1 - 2 * γ / K)
  have hrstar_pos : 0 < r_star := Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hr₀_lb : r_star / 2 < r₀ := by
    have h := abs_lt.mp hr₀_near; linarith [h.1]
  have hr₀_ub : r₀ < 3 * r_star / 2 := by
    have h := abs_lt.mp hr₀_near; linarith [h.2]
  have hr₀_sq_pos : (0 : ℝ) < r₀ ^ 2 := sq_pos_of_pos hr₀_pos
  have hrstar3_pos : (0 : ℝ) < r_star ^ 3 := by positivity
  have hrstar4_pos : (0 : ℝ) < r_star ^ 4 := by positivity
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-(K - 2 * γ) * t) := Real.exp_nonneg _
  have hδ_nn : (0 : ℝ) ≤ |r₀ - r_star| := abs_nonneg _
  -- |r*+r₀| ≤ 5r*/2 from r₀ < 3r*/2
  have hsum_bound : r_star + r₀ ≤ 5 * r_star / 2 := by linarith
  have hsum_pos : 0 < r_star + r₀ := by linarith
  -- r₀² ≥ r*²/4 from r₀ > r*/2
  have hr₀_sq_lb : r_star ^ 2 / 4 ≤ r₀ ^ 2 := by nlinarith [sq_nonneg (r₀ - r_star / 2)]
  -- |r*²-r₀²| = |r*-r₀|·(r*+r₀)
  have hfact : |r_star ^ 2 - r₀ ^ 2| = |r₀ - r_star| * (r_star + r₀) := by
    rw [show r_star ^ 2 - r₀ ^ 2 = -(r₀ - r_star) * (r_star + r₀) from by ring,
        abs_mul, abs_neg, abs_of_pos hsum_pos]
  calc |lorentzian_explicit K γ r₀ t - r_star|
      ≤ |r_star ^ 2 - r₀ ^ 2| * Real.exp (-(K - 2 * γ) * t) / (r₀ ^ 2 * r_star ^ 3) :=
        lorentzian_explicit_rate_initial K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
    _ ≤ 10 * |r₀ - r_star| * Real.exp (-(K - 2 * γ) * t) / r_star ^ 4 := by
        rw [hfact]
        rw [div_le_div_iff₀ (mul_pos hr₀_sq_pos hrstar3_pos) hrstar4_pos]
        -- Goal: |r₀-r*| * (r*+r₀) * exp * r*⁴ ≤ 10 * |r₀-r*| * exp * r₀² * r*³
        -- Step 1: (r*+r₀) ≤ 5r*/2 → LHS ≤ δ*(5r*/2)*exp*r*⁴ = (5/2)δ·exp·r*⁵
        -- Step 2: r₀² ≥ r*²/4 → RHS ≥ 10δ·exp·(r*²/4)·r*³ = (5/2)δ·exp·r*⁵
        have h1 : |r₀ - r_star| * (r_star + r₀) * Real.exp (-(K - 2 * γ) * t) * r_star ^ 4 ≤
            |r₀ - r_star| * (5 * r_star / 2) * Real.exp (-(K - 2 * γ) * t) * r_star ^ 4 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsum_bound hδ_nn) hexp_nn)
            (le_of_lt hrstar4_pos)
        have h2 : 10 * |r₀ - r_star| * Real.exp (-(K - 2 * γ) * t) * (r_star ^ 2 / 4) * r_star ^ 3 ≤
            10 * |r₀ - r_star| * Real.exp (-(K - 2 * γ) * t) * r₀ ^ 2 * r_star ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr₀_sq_lb
              (mul_nonneg (mul_nonneg (by norm_num) hδ_nn) hexp_nn))
            (le_of_lt hrstar3_pos)
        nlinarith

/-- **Key governing identity**: d(r²)/dt = K·r²·(r*²-r²).
    This is the algebraic engine behind ALL Lyapunov monotonicity: r² increases
    when r < r* and decreases when r > r*, with rate proportional to K·r²·|r*²-r²|. -/
theorem lorentzian_explicit_sq_hasDerivAt (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => lorentzian_explicit K γ r₀ s ^ 2)
      (K * lorentzian_explicit K γ r₀ t ^ 2 *
        (Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2)) t := by
  have hr : HasDerivAt (lorentzian_explicit K γ r₀)
      (lorentzianODE K γ (lorentzian_explicit K γ r₀ t)) t :=
    lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := hr.pow 2
  simp only [Nat.cast_ofNat, pow_one] at h
  convert h using 1
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  rw [hrstar_sq]
  simp only [lorentzianODE]
  field_simp [hK.ne']
  ring

/-- When r₀² < r*² = 1-2γ/K, the solution satisfies r(t)² < r*² for all t ≥ 0.
    Proof: A = 1/r₀²-B > 0 → w(t) = A·exp(-μt)+B > B → r(t)² = 1/w(t) < 1/B = r*². -/
theorem lorentzian_explicit_sq_lt_rstar (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ^ 2 < 1 - 2 * γ / K := by
  rw [lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht]
  have hd : (0:ℝ) < K - 2 * γ := by linarith
  have hB_pos : (0:ℝ) < K / (K - 2 * γ) := div_pos hK hd
  have hw_pos : 0 < w_func K γ r₀ t := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hB_inv : (K / (K - 2 * γ))⁻¹ = 1 - 2 * γ / K := by
    field_simp [hK.ne', hd.ne']
  rw [← hB_inv]
  rw [inv_lt_inv₀ hw_pos hB_pos]
  -- Goal: K/(K-2γ) < w_func K γ r₀ t
  have hA_pos : 0 < 1 / r₀ ^ 2 - K / (K - 2 * γ) := by
    rw [sub_pos, div_lt_div_iff₀ hd (sq_pos_of_pos hr₀_pos)]
    have hmul := mul_lt_mul_of_pos_left hr₀_sq_lt hK
    have hsimp : K * (1 - 2 * γ / K) = K - 2 * γ := by field_simp [hK.ne']
    linarith
  simp only [w_func]
  linarith [mul_pos hA_pos (Real.exp_pos (-(K - 2 * γ) * t))]

/-- V(t) = r*² - r(t)² satisfies V' = -K·r²·V.
    Combined with r² > 0, this gives V monotone decreasing when V > 0 (r < r*)
    and monotone increasing when V < 0 (r > r*), confirming r(t) → r* from both sides. -/
theorem lorentzian_explicit_v_hasDerivAt (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ s ^ 2)
      (-(K * lorentzian_explicit K γ r₀ t ^ 2 *
        (Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2))) t := by
  have h := lorentzian_explicit_sq_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hconst : HasDerivAt (fun _ => Real.sqrt (1 - 2 * γ / K) ^ 2) 0 t :=
    hasDerivAt_const t _
  convert hconst.sub h using 1; ring

/-- When r₀² < r*², the solution r(t)² is non-decreasing from r₀²: r(t)² ≥ r₀².
    Proof: A > 0 → exp(-μt) ≤ 1 → w(t) ≤ A+B = 1/r₀² → w(t)⁻¹ ≥ r₀². -/
theorem lorentzian_explicit_sq_ge_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (t : ℝ) (ht : 0 ≤ t) :
    r₀ ^ 2 ≤ lorentzian_explicit K γ r₀ t ^ 2 := by
  rw [lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht]
  have hd : (0:ℝ) < K - 2 * γ := by linarith
  have hw_pos : 0 < w_func K γ r₀ t := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr0sq_pos : (0:ℝ) < r₀ ^ 2 := sq_pos_of_pos hr₀_pos
  have hA_pos : 0 < 1 / r₀ ^ 2 - K / (K - 2 * γ) := by
    rw [sub_pos, div_lt_div_iff₀ hd hr0sq_pos]
    have hmul := mul_lt_mul_of_pos_left hr₀_sq_lt hK
    have hsimp : K * (1 - 2 * γ / K) = K - 2 * γ := by field_simp [hK.ne']
    linarith
  have hexp_le : Real.exp (-(K - 2 * γ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hw_le : w_func K γ r₀ t ≤ 1 / r₀ ^ 2 := by
    simp only [w_func]
    linarith [mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA_pos)]
  have hineq := inv_anti₀ hw_pos hw_le
  simp only [one_div, inv_inv] at hineq
  exact hineq

/-- V(t) = r*²-r(t)² decays exponentially: V(t) ≤ V(0)·exp(-K·r₀²·t).
    Proof: V' = -K·r²·V and r² ≥ r₀² (sq_ge_init), so V' ≤ -(K·r₀²)·V;
    comparison_decay then gives the bound. -/
theorem lorentzian_v_exponential_decay (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2 ≤
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) *
        Real.exp (-(K * r₀ ^ 2) * t) := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  set V := fun s => Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ s ^ 2 with hV_def
  set V' := fun s => -(K * lorentzian_explicit K γ r₀ s ^ 2 *
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ s ^ 2)) with hV'_def
  have hVt := comparison_decay V V' (K * r₀ ^ 2)
    (continuousOn_const.sub ((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).pow 2))
    (fun s hs => lorentzian_explicit_v_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s (le_of_lt hs))
    (fun s hs => by
      simp only [V', V]
      have hsq_ge := lorentzian_explicit_sq_ge_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt s (le_of_lt hs)
      have hlt := lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt s (le_of_lt hs)
      have hV_nn : 0 ≤ Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ s ^ 2 := by
        rw [hrstar_sq]; linarith
      nlinarith [mul_nonneg (mul_nonneg (le_of_lt hK) (sub_nonneg.mpr hsq_ge)) hV_nn])
    t ht
  have hV0 : V 0 = Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2 := by
    simp only [hV_def]
    rw [lorentzian_explicit_init K γ r₀ hr₀_pos]
  calc Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2
      = V t := rfl
    _ ≤ V 0 * Real.exp (-(K * r₀ ^ 2) * t) := hVt
    _ = (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * r₀ ^ 2) * t) := by
        rw [hV0]

/-- |r(t) - r*| ≤ (r*² - r₀²)·exp(-K·r₀²·t) / r*.
    Follows from V-decay via r*² - r(t)² = (r*-r(t))·(r*+r(t)) ≥ r*·|r(t)-r*|. -/
theorem lorentzian_r_from_v_decay (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * r₀ ^ 2) * t) /
        Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) := by
    apply Real.sqrt_pos_of_pos
    rw [sub_pos, div_lt_one hK]; linarith
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  have hr_pos : 0 < lorentzian_explicit K γ r₀ t :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt_rstar : lorentzian_explicit K γ r₀ t < Real.sqrt (1 - 2 * γ / K) := by
    rw [← Real.sqrt_sq (le_of_lt hr_pos)]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    exact lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have hV_decay := lorentzian_v_exponential_decay K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have habs : |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| =
      Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t := by
    rw [abs_of_neg (sub_neg.mpr hr_lt_rstar)]
    ring
  rw [habs]
  rw [le_div_iff₀ hrstar_pos]
  calc (Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t) * Real.sqrt (1 - 2 * γ / K)
      ≤ (Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t) *
        (Real.sqrt (1 - 2 * γ / K) + lorentzian_explicit K γ r₀ t) :=
        mul_le_mul_of_nonneg_left (by linarith [le_of_lt hr_pos])
          (sub_nonneg.mpr (le_of_lt hr_lt_rstar))
    _ = Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2 := by ring
    _ ≤ (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * r₀ ^ 2) * t) := hV_decay


/-- When r₀² > r*², the solution satisfies r(t)² > r*² for all t ≥ 0.
    Proof: A < 0 → w(t) < B → w(t)⁻¹ > B⁻¹ = r*². -/
theorem lorentzian_explicit_sq_gt_rstar (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * γ / K) ^ 2 < lorentzian_explicit K γ r₀ t ^ 2 := by
  rw [lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht]
  have hd : (0:ℝ) < K - 2 * γ := by linarith
  have hB_pos : (0:ℝ) < K / (K - 2 * γ) := div_pos hK hd
  have hw_pos : 0 < w_func K γ r₀ t := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hB_inv : (K / (K - 2 * γ))⁻¹ = 1 - 2 * γ / K := by field_simp [hK.ne', hd.ne']
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  rw [hrstar_sq, ← hB_inv]
  rw [inv_lt_inv₀ hB_pos hw_pos]
  have hA_neg : 1 / r₀ ^ 2 - K / (K - 2 * γ) < 0 := by
    rw [sub_neg, div_lt_div_iff₀ (sq_pos_of_pos hr₀_pos) hd]
    have hmul := mul_lt_mul_of_pos_left hr₀_sq_gt hK
    have hsimp : K * (1 - 2 * γ / K) = K - 2 * γ := by field_simp [hK.ne']
    linarith
  simp only [w_func]
  linarith [mul_neg_of_neg_of_pos hA_neg (Real.exp_pos (-(K - 2 * γ) * t))]

/-- When r₀² > r*², the solution r(t)² is non-increasing from r₀²: r(t)² ≤ r₀².
    Proof: A < 0 → exp(-μt) ≤ 1 → w(t) ≥ A+B = 1/r₀² → w(t)⁻¹ ≤ r₀². -/
theorem lorentzian_explicit_sq_le_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ^ 2 ≤ r₀ ^ 2 := by
  rw [lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht]
  have hd : (0:ℝ) < K - 2 * γ := by linarith
  have hw_pos : 0 < w_func K γ r₀ t := w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr0sq_pos : (0:ℝ) < r₀ ^ 2 := sq_pos_of_pos hr₀_pos
  have hA_neg : 1 / r₀ ^ 2 - K / (K - 2 * γ) < 0 := by
    rw [sub_neg, div_lt_div_iff₀ (sq_pos_of_pos hr₀_pos) hd]
    have hmul := mul_lt_mul_of_pos_left hr₀_sq_gt hK
    have hsimp : K * (1 - 2 * γ / K) = K - 2 * γ := by field_simp [hK.ne']
    linarith
  have hexp_le : Real.exp (-(K - 2 * γ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hw_ge : 1 / r₀ ^ 2 ≤ w_func K γ r₀ t := by
    simp only [w_func]
    linarith [mul_le_mul_of_nonpos_left hexp_le (le_of_lt hA_neg)]
  have hineq := inv_anti₀ (div_pos one_pos hr0sq_pos) hw_ge
  simp only [one_div, inv_inv] at hineq
  exact hineq

/-- Above-equilibrium Gronwall V-decay: when r₀² > r*²,
    r(t)²-r*² ≤ (r₀²-r*²)·exp(-K·r*²·t).
    Proof: W = r(t)²-r*² ≥ 0 satisfies W' = -K·r²·W ≤ -(K·r*²)·W since r² ≥ r*². -/
theorem lorentzian_w_exponential_decay (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2 ≤
      (r₀ ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2) *
        Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) ^ 2) * t) := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) := by
    apply Real.sqrt_pos_of_pos; rw [sub_pos, div_lt_one hK]; linarith
  -- W = r²-r*², derivative K·r²·(r*²-r²) (from neg of v_hasDerivAt)
  set W := fun s => lorentzian_explicit K γ r₀ s ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2 with hW_def
  set W' := fun s => K * lorentzian_explicit K γ r₀ s ^ 2 *
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ s ^ 2) with hW'_def
  have hWt := comparison_decay W W' (K * Real.sqrt (1 - 2 * γ / K) ^ 2)
    (((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).pow 2).sub continuousOn_const)
    (fun s hs => by
      have h := lorentzian_explicit_sq_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s (le_of_lt hs)
      have hconst : HasDerivAt (fun _ => Real.sqrt (1 - 2 * γ / K) ^ 2) 0 s := hasDerivAt_const _ _
      convert h.sub hconst using 1; ring)
    (fun s hs => by
      simp only [W, W']
      have hsq_ge := lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt s (le_of_lt hs)
      nlinarith [sq_nonneg (lorentzian_explicit K γ r₀ s ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2),
                 mul_pos hK (sq_pos_of_pos hrstar_pos)])
    t ht
  have hW0 : W 0 = r₀ ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2 := by
    simp only [hW_def]
    rw [lorentzian_explicit_init K γ r₀ hr₀_pos]
  calc lorentzian_explicit K γ r₀ t ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2
      = W t := rfl
    _ ≤ W 0 * Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) ^ 2) * t) := hWt
    _ = (r₀ ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2) *
          Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) ^ 2) * t) := by rw [hW0]

/-- |r(t) - r*| ≤ (r₀² - r*²)·exp(-K·r*²·t) / r* (above-equilibrium case).
    Same algebra as r_from_v_decay but using w_exponential_decay. -/
theorem lorentzian_r_from_w_decay (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      (r₀ ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2) *
        Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) ^ 2) * t) /
        Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) := by
    apply Real.sqrt_pos_of_pos; rw [sub_pos, div_lt_one hK]; linarith
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  have hr_pos : 0 < lorentzian_explicit K γ r₀ t :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_gt_rstar : Real.sqrt (1 - 2 * γ / K) < lorentzian_explicit K γ r₀ t := by
    rw [← Real.sqrt_sq (le_of_lt hr_pos)]
    apply Real.sqrt_lt_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
    rw [← hrstar_sq]
    exact lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt t ht
  have hW_decay := lorentzian_w_exponential_decay K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt t ht
  have habs : |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| =
      lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K) :=
    abs_of_pos (sub_pos.mpr hr_gt_rstar)
  rw [habs, le_div_iff₀ hrstar_pos]
  calc (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) * Real.sqrt (1 - 2 * γ / K)
      ≤ (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) *
        (lorentzian_explicit K γ r₀ t + Real.sqrt (1 - 2 * γ / K)) :=
        mul_le_mul_of_nonneg_left (by linarith [le_of_lt hrstar_pos])
          (sub_nonneg.mpr (le_of_lt hr_gt_rstar))
    _ = lorentzian_explicit K γ r₀ t ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2 := by ring
    _ ≤ (r₀ ^ 2 - Real.sqrt (1 - 2 * γ / K) ^ 2) *
          Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) ^ 2) * t) := hW_decay


/-- Unified exponential rate: for all r₀ ∈ (0,1) with r₀² ≠ r*²,
    |r(t)-r*| ≤ |r₀²-r*²|·exp(-K·min(r₀²,r*²)·t)/r*.
    Combines V-decay (r₀<r*, rate K·r₀²) and W-decay (r₀>r*, rate K·r*²). -/
theorem lorentzian_unified_rate (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ^ 2 ≠ 1 - 2 * γ / K)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      |r₀ ^ 2 - (1 - 2 * γ / K)| *
        Real.exp (-(K * min (r₀ ^ 2) (1 - 2 * γ / K)) * t) /
        Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  rcases lt_or_gt_of_ne hr₀_ne with h | h
  · -- Case r₀² < r*²
    have hlt : r₀ ^ 2 < 1 - 2 * γ / K := h
    have hbound := lorentzian_r_from_v_decay K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hlt t ht
    rw [abs_of_neg (sub_neg.mpr hlt), min_eq_left (le_of_lt hlt)]
    simp only [neg_sub, hrstar_sq] at hbound ⊢
    linarith
  · -- Case r₀² > r*²
    have hgt : 1 - 2 * γ / K < r₀ ^ 2 := h
    have hbound := lorentzian_r_from_w_decay K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hgt t ht
    rw [abs_of_pos (sub_pos.mpr hgt), min_eq_right (le_of_lt hgt)]
    simp only [hrstar_sq] at hbound ⊢
    linarith

/-- The above-equilibrium Gronwall rate K·r*² equals the linearized rate K-2γ.
    This confirms the W-decay rate is optimal at r* (matches linear stability). -/
theorem lorentzian_rate_eq_linearized (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) :
    K * Real.sqrt (1 - 2 * γ / K) ^ 2 = K - 2 * γ := by
  rw [Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)]
  field_simp [hK.ne']

/-- Uniform V-decay: for r₀ ≥ δ > 0 (below r*), the V-bound holds with rate K·δ².
    Enables uniform-in-r₀ convergence on any interval [δ, r*). -/
theorem lorentzian_v_decay_uniform (K γ r₀ δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2 ≤
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * δ ^ 2) * t) := by
  have hV := lorentzian_v_exponential_decay K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have hV_nn : 0 ≤ Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2 := by
    have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
      Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
    rw [hrstar_sq]; linarith
  have hexp_mono : Real.exp (-(K * r₀ ^ 2) * t) ≤ Real.exp (-(K * δ ^ 2) * t) := by
    apply Real.exp_le_exp.mpr
    have hδsq : δ ^ 2 ≤ r₀ ^ 2 := pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_le 2
    nlinarith [mul_nonneg (le_of_lt hK) ht]
  calc Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2
      ≤ (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * r₀ ^ 2) * t) := hV
    _ ≤ (Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2) * Real.exp (-(K * δ ^ 2) * t) :=
        mul_le_mul_of_nonneg_left hexp_mono hV_nn

/-- Uniform |r(t)-r*| bound on compact below-r* interval [δ, r*-ε]:
    |r(t)-r*| ≤ (r*²-δ²)·exp(-K·δ²·t)/r*.
    Rate K·δ² is uniform across r₀ ∈ [δ, r*). -/
theorem lorentzian_uniform_r_decay (K γ r₀ δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - δ ^ 2) * Real.exp (-(K * δ ^ 2) * t) /
        Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) := by
    apply Real.sqrt_pos_of_pos; rw [sub_pos, div_lt_one hK]; linarith
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
  have hr_pos : 0 < lorentzian_explicit K γ r₀ t :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt_rstar : lorentzian_explicit K γ r₀ t < Real.sqrt (1 - 2 * γ / K) := by
    rw [← Real.sqrt_sq (le_of_lt hr_pos)]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    exact lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have hVu := lorentzian_v_decay_uniform K γ r₀ δ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt
                hδ_pos hδ_le t ht
  -- (r*²-δ²)·exp ≥ (r*²-r₀²)·exp ≥ V(t) = r*²-r(t)²
  have hδsq_le : r₀ ^ 2 ≥ δ ^ 2 := pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_le 2
  have hcoeff : Real.sqrt (1 - 2 * γ / K) ^ 2 - r₀ ^ 2 ≤
      Real.sqrt (1 - 2 * γ / K) ^ 2 - δ ^ 2 := by linarith
  have hcoeff_nn : 0 ≤ Real.sqrt (1 - 2 * γ / K) ^ 2 - δ ^ 2 := by
    rw [hrstar_sq]; nlinarith [pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_le 2, hr₀_sq_lt]
  have hVub : Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2 ≤
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - δ ^ 2) * Real.exp (-(K * δ ^ 2) * t) :=
    le_trans hVu (mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _))
  have habs : |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| =
      Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t := by
    rw [abs_of_neg (sub_neg.mpr hr_lt_rstar)]; ring
  rw [habs, le_div_iff₀ hrstar_pos]
  calc (Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t) * Real.sqrt (1 - 2 * γ / K)
      ≤ (Real.sqrt (1 - 2 * γ / K) - lorentzian_explicit K γ r₀ t) *
        (Real.sqrt (1 - 2 * γ / K) + lorentzian_explicit K γ r₀ t) :=
        mul_le_mul_of_nonneg_left (by linarith [le_of_lt hr_pos])
          (sub_nonneg.mpr (le_of_lt hr_lt_rstar))
    _ = Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2 := by ring
    _ ≤ (Real.sqrt (1 - 2 * γ / K) ^ 2 - δ ^ 2) * Real.exp (-(K * δ ^ 2) * t) := hVub

/-- **Continuous-time convergence for any ODE solution**: any `LorentzianContinuousSolution`
    converges to r* = √(1-2γ/K) as t → ∞. Combines ODE uniqueness (eq_explicit) with
    the explicit Bernoulli convergence (lorentzian_explicit_tendsto). -/
theorem LorentzianContinuousSolution.tendsto (S : LorentzianContinuousSolution) :
    Tendsto S.r atTop (nhds (Real.sqrt (1 - 2 * S.γ / S.K))) := by
  apply (lorentzian_explicit_tendsto S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt).congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact (S.eq_explicit t ht).symm

/-- **Discrete-time Filter.Tendsto for any ODE solution**: r(n) → r* as n → ∞ over ℕ.
    Follows from the continuous-time tendsto by composition with ℕ → ℝ coercion. -/
theorem LorentzianContinuousSolution.tendsto_nat (S : LorentzianContinuousSolution) :
    Tendsto (fun n : ℕ => S.r n) atTop (nhds (Real.sqrt (1 - 2 * S.γ / S.K))) :=
  S.tendsto.comp tendsto_natCast_atTop_atTop

/-- **Discrete-time convergence for the explicit Bernoulli solution** (Filter.Tendsto form):
    lorentzian_explicit K γ r₀ n → r* as n : ℕ → ∞. -/
theorem lorentzian_explicit_tendsto_nat (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    Tendsto (fun n : ℕ => lorentzian_explicit K γ r₀ n) atTop
      (nhds (Real.sqrt (1 - 2 * γ / K))) :=
  (lorentzian_explicit_tendsto K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).comp
    tendsto_natCast_atTop_atTop

/-- **Parameter-only continuous-time convergence**: for any K > 2γ and r₀ ∈ (0,1),
    there exists a solution r : ℝ → ℝ of the Lorentzian ODE with r(0) = r₀ and
    r(t) → r* = √(1-2γ/K) as t → ∞. Proof: existence from explicit Bernoulli formula,
    convergence from LorentzianContinuousSolution.tendsto. Zero external hypotheses. -/
theorem lorentzian_ode_continuous_convergence (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    ∃ r : ℝ → ℝ, r 0 = r₀ ∧
      Tendsto r atTop (nhds (Real.sqrt (1 - 2 * γ / K))) := by
  obtain ⟨S, hSK, hSγ, hSr₀⟩ :=
    lorentzian_continuous_solution_exists K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
  refine ⟨S.r, hSr₀, ?_⟩
  have htend := S.tendsto
  rw [hSK, hSγ] at htend
  exact htend

/-- **Global stability of the Lorentzian OA equilibrium** (complete billboard theorem):
    For K > 2γ and r₀ ∈ (0,1), the explicit Bernoulli formula r(t) = √(w(t)⁻¹)
    gives the unique ODE solution with r(0)=r₀, satisfying:
    (1) r(t) ∈ (0,1) for all t ≥ 0 (positivity + boundedness)
    (2) r(t) → r* = √(1-2γ/K) as t → ∞ (global stability)
    (3) |r(t)-r*| ≤ |A|·exp(-(K-2γ)t)/r* (explicit exponential rate μ = K-2γ)
    Proved from parameters (K,γ,r₀) alone — zero external hypotheses. -/
theorem lorentzian_ode_global_stability (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    let r := lorentzian_explicit K γ r₀
    let r_star := Real.sqrt (1 - 2 * γ / K)
    (∀ t ≥ 0, r t ∈ Set.Ioo 0 1) ∧
    Tendsto r atTop (nhds r_star) ∧
    (∀ t ≥ 0, |r t - r_star| ≤
      |1 / r₀ ^ 2 - K / (K - 2 * γ)| * Real.exp (-(K - 2 * γ) * t) / r_star) := by
  refine ⟨fun t ht => ⟨lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht,
    lorentzian_explicit_lt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht⟩,
    lorentzian_explicit_tendsto K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt,
    fun t ht => lorentzian_explicit_rate K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht⟩

/-- **Exponential synchronization**: any two Lorentzian ODE solutions merge as t → ∞.
    |r(t,r₀) - r(t,r₀')| → 0. Proof: triangle through r* — both solutions tend to r*,
    so their difference tends to r* - r* = 0. -/
theorem lorentzian_explicit_dist_tendsto (K γ r₀ r₀' : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀'_pos : 0 < r₀') (hr₀'_lt : r₀' < 1) :
    Tendsto (fun t => |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t|)
      atTop (nhds 0) := by
  have h1 := lorentzian_explicit_tendsto K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
  have h2 := lorentzian_explicit_tendsto K γ r₀' hK hγ hKγ hr₀'_pos hr₀'_lt
  have h := h1.sub h2
  simp only [sub_self] at h
  have h' := h.norm
  simp only [norm_zero] at h'
  simp_rw [Real.norm_eq_abs] at h'
  exact h'

/-- **Parameter monotonicity in K**: the Lorentzian equilibrium r* = √(1-2γ/K)
    is strictly increasing in K. More coupling → larger partially locked state. -/
theorem lorentzian_rstar_mono_K (K₁ K₂ γ : ℝ)
    (hγ : 0 < γ) (hKγ₁ : 2 * γ < K₁) (hKγ₂ : 2 * γ < K₂) (hK : K₁ < K₂) :
    Real.sqrt (1 - 2 * γ / K₁) < Real.sqrt (1 - 2 * γ / K₂) := by
  apply Real.sqrt_lt_sqrt (le_of_lt (lorentzian_rstar_pos K₁ γ (by linarith) hKγ₁))
  have hK₁ : (0 : ℝ) < K₁ := by linarith
  have hK₂ : (0 : ℝ) < K₂ := by linarith
  have hdiv : 2 * γ / K₂ < 2 * γ / K₁ := by
    rw [div_lt_div_iff₀ hK₂ hK₁]; nlinarith
  linarith

/-- **Parameter monotonicity in γ**: the Lorentzian equilibrium r* = √(1-2γ/K)
    is strictly decreasing in γ. More damping → smaller partially locked state. -/
theorem lorentzian_rstar_anti_gamma (K γ₁ γ₂ : ℝ)
    (hK : 0 < K) (hKγ₁ : 2 * γ₁ < K) (hKγ₂ : 2 * γ₂ < K) (hγ : γ₁ < γ₂) :
    Real.sqrt (1 - 2 * γ₂ / K) < Real.sqrt (1 - 2 * γ₁ / K) := by
  apply Real.sqrt_lt_sqrt (le_of_lt (lorentzian_rstar_pos K γ₂ hK hKγ₂))
  have hdiv : 2 * γ₁ / K < 2 * γ₂ / K := by
    rw [div_lt_div_iff₀ hK hK]; nlinarith
  linarith

/-- **r* < 1 always**: the Lorentzian equilibrium r* = √(1-2γ/K) is strictly below 1
    for all supercritical (K,γ). The PLS is never full synchronization in the Lorentzian case. -/
theorem lorentzian_rstar_lt_one (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) :
    Real.sqrt (1 - 2 * γ / K) < 1 := by
  calc Real.sqrt (1 - 2 * γ / K)
      < Real.sqrt 1 := Real.sqrt_lt_sqrt
          (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
          (by linarith [div_pos (by linarith : 0 < 2 * γ) hK])
    _ = 1 := Real.sqrt_one

/-- **Strong coupling limit**: r*(K,γ) → 1 as K → ∞ (γ fixed). In the limit of
    infinite coupling the PLS approaches full synchronization. -/
theorem lorentzian_rstar_tendsto_one (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun K => Real.sqrt (1 - 2 * γ / K)) atTop (nhds 1) := by
  have h0 : Tendsto (fun K : ℝ => 2 * γ / K) atTop (nhds 0) := by
    have hinv : Tendsto (fun K : ℝ => K⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hmul := hinv.const_mul (2 * γ)
    simp only [mul_zero] at hmul
    exact hmul.congr (fun K => by ring)
  have h1 : Tendsto (fun K : ℝ => 1 - 2 * γ / K) atTop (nhds 1) := by
    have hc : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using hc.sub h0
  simpa [Real.sqrt_one] using continuous_sqrt.continuousAt.tendsto.comp h1

/-- **Bifurcation birth point**: r* = √(1-2γ/K) → 0 as K → (2γ)⁺.
    Together with `lorentzian_rstar_tendsto_one` this completes the bifurcation picture:
    r*(K) is born at K = 2γ with r* = 0 and increases monotonically to 1 as K → ∞. -/
theorem lorentzian_rstar_tendsto_zero (γ : ℝ) (hγ : 0 < γ) :
    Filter.Tendsto (fun K => Real.sqrt (1 - 2 * γ / K))
      (nhdsWithin (2 * γ) (Set.Ioi (2 * γ))) (nhds 0) := by
  have h2γ_ne : (2 * γ : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hcont_inner : ContinuousAt (fun K : ℝ => 1 - 2 * γ / K) (2 * γ) :=
    continuousAt_const.sub (continuousAt_const.div continuousAt_id h2γ_ne)
  have hval : (fun K : ℝ => 1 - 2 * γ / K) (2 * γ) = 0 := by
    simp only []; rw [div_self h2γ_ne, sub_self]
  have h_inner : Filter.Tendsto (fun K : ℝ => 1 - 2 * γ / K)
      (nhdsWithin (2 * γ) (Set.Ioi (2 * γ))) (nhds 0) := by
    rw [← hval]; exact hcont_inner.continuousWithinAt
  simpa [Real.sqrt_zero] using continuous_sqrt.continuousAt.tendsto.comp h_inner

/-- **Linearized rate at origin**: the derivative of the Lorentzian ODE vector field at r=0
    is K/2-γ. For K > 2γ this is positive, confirming the origin is linearly unstable. -/
theorem lorentzian_ode_hasDerivAt_zero (K γ : ℝ) :
    HasDerivAt (lorentzianODE K γ) (K / 2 - γ) 0 := by
  have hderiv : HasDerivAt (fun r => (K / 2 - γ) * r - K / 2 * r ^ 3)
      ((K / 2 - γ) - K / 2 * (3 * (0 : ℝ) ^ 2)) 0 := by
    have h1 : HasDerivAt (fun r => (K / 2 - γ) * r) (K / 2 - γ) 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).const_mul (K / 2 - γ)
      simp only [mul_one, id] at h; exact h
    have h2 : HasDerivAt (fun r => K / 2 * r ^ 3) (K / 2 * (3 * (0 : ℝ) ^ 2)) 0 := by
      have h := (hasDerivAt_pow 3 (0 : ℝ)).const_mul (K / 2)
      simp only [Nat.cast_ofNat] at h; convert h using 1
    exact h1.sub h2
  have hconv : lorentzianODE K γ = fun r => (K / 2 - γ) * r - K / 2 * r ^ 3 := by
    ext r; simp [lorentzianODE]
  rw [hconv]; convert hderiv using 1; ring

/-- **ODE negative above 1**: for r > 1, the Lorentzian velocity ṙ < 0.
    Combined with ode_neg_above_rstar, this shows ṙ < 0 for ALL r > r*, not just r ∈ (r*,1).
    In particular, the region r ≤ 1 is forward-invariant under the ODE. -/
theorem lorentzian_ode_neg_above_one (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) (hr : 1 < r) :
    lorentzianODE K γ r < 0 := by
  rw [lorentzian_ode_factored K γ r (ne_of_gt hK)]
  have hr_pos : 0 < r := lt_trans one_pos hr
  apply mul_neg_of_pos_of_neg (mul_pos (by linarith) hr_pos)
  have hlt : 1 - 2 * γ / K < 1 := by linarith [div_pos (by linarith : 0 < 2 * γ) hK]
  have hr_sq : (1 : ℝ) < r ^ 2 := by nlinarith
  linarith

/-- **Positive derivative below r***: for r₀ < r* and t ≥ 0, the Lorentzian explicit solution
    has positive derivative: d/dt r(t) > 0. Hence r is strictly increasing along the trajectory. -/
theorem lorentzian_explicit_pos_deriv (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    0 < deriv (lorentzian_explicit K γ r₀) t := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_lt : r₀ < 1 := hr₀_lt_rstar.trans (lorentzian_rstar_lt_one K γ hK hγ hKγ)
  have hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K :=
    calc r₀ ^ 2 < Real.sqrt (1 - 2 * γ / K) ^ 2 :=
          sq_lt_sq' (by linarith [hrstar_pos]) hr₀_lt_rstar
      _ = 1 - 2 * γ / K := hrstar_sq
  have hr_pos : 0 < lorentzian_explicit K γ r₀ t :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt_rstar : lorentzian_explicit K γ r₀ t < Real.sqrt (1 - 2 * γ / K) := by
    rw [← Real.sqrt_sq (le_of_lt hr_pos)]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    exact lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  rw [(lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht).deriv]
  exact lorentzian_ode_pos_below_rstar K γ (lorentzian_explicit K γ r₀ t)
      hK hγ hKγ hr_pos hr_lt_rstar

/-- **Strict monotone increase below r***: for r₀ < r*, the explicit solution is strictly
    increasing: r(s) < r(t) for 0 ≤ s < t. Follows from positive derivative everywhere. -/
theorem lorentzian_explicit_strictly_increasing (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    lorentzian_explicit K γ r₀ s < lorentzian_explicit K γ r₀ t := by
  have hr₀_lt : r₀ < 1 := hr₀_lt_rstar.trans (lorentzian_rstar_lt_one K γ hK hγ hKγ)
  have hcont : ContinuousOn (lorentzian_explicit K γ r₀) (Set.Icc s t) :=
    (lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).mono
      (fun x hx => le_trans hs hx.1)
  have hderiv_pos : ∀ u ∈ interior (Set.Icc s t), 0 < deriv (lorentzian_explicit K γ r₀) u := by
    rw [interior_Icc]
    intro u ⟨hs_u, _⟩
    exact lorentzian_explicit_pos_deriv K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt_rstar u
        (le_trans hs (le_of_lt hs_u))
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc s t) hcont hderiv_pos
  exact hmono (Set.left_mem_Icc.mpr (le_of_lt hst)) (Set.right_mem_Icc.mpr (le_of_lt hst)) hst

/-- **Strictly increasing trajectory for any ODE solution**: if S.r 0 < r*, then S.r s < S.r t
    for any 0 ≤ s < t. Lifts strictly_increasing to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.strictly_increasing (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    S.r s < S.r t := by
  rw [S.eq_explicit_of_nonneg s hs, S.eq_explicit_of_nonneg t (hs.trans hst.le)]
  exact lorentzian_explicit_strictly_increasing S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos hr₀_lt_rstar hs hst

/-- **Order-preserving flow**: the Lorentzian ODE flow is order-preserving in the initial condition.
    If r₀ < r₀' then r(t, r₀) < r(t, r₀') for all t ≥ 0. Proof via Bernoulli w_func_diff:
    r₀ < r₀' → 1/r₀²>1/r₀'² → w(r₀)>w(r₀') → 1/w(r₀)<1/w(r₀') → r(r₀)<r(r₀'). -/
theorem lorentzian_explicit_order_preserving (K γ r₀ r₀' : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀'_pos : 0 < r₀') (hr₀'_lt : r₀' < 1)
    (h : r₀ < r₀') (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t < lorentzian_explicit K γ r₀' t := by
  simp only [lorentzian_explicit]
  have hr₀_sq_pos : (0 : ℝ) < r₀ ^ 2 := sq_pos_of_pos hr₀_pos
  have hr₀'_sq_pos : (0 : ℝ) < r₀' ^ 2 := sq_pos_of_pos hr₀'_pos
  have hr_sq : r₀ ^ 2 < r₀' ^ 2 := sq_lt_sq' (by linarith [hr₀'_pos]) h
  have h_coeff : 0 < 1 / r₀ ^ 2 - 1 / r₀' ^ 2 := by
    rw [sub_pos, div_lt_div_iff₀ hr₀'_sq_pos hr₀_sq_pos]; nlinarith
  have hdiff := w_func_diff K γ r₀ r₀' t
  have hw_gt : w_func K γ r₀' t < w_func K γ r₀ t := by
    linarith [mul_pos h_coeff (Real.exp_pos (-(K - 2 * γ) * t))]
  have hw_pos : 0 < w_func K γ r₀ t :=
    w_func_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hw'_pos : 0 < w_func K γ r₀' t :=
    w_func_pos K γ r₀' hK hγ hKγ hr₀'_pos hr₀'_lt t ht
  apply Real.sqrt_lt_sqrt (inv_nonneg.mpr hw_pos.le)
  exact (inv_lt_inv₀ hw_pos hw'_pos).mpr hw_gt

/-- **Negative derivative above r***: for r₀ ∈ (r*, 1) and t ≥ 0, the Lorentzian solution
    has negative derivative: d/dt r(t) < 0. Hence r is strictly decreasing along the trajectory. -/
theorem lorentzian_explicit_neg_deriv (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (lorentzian_explicit K γ r₀) t < 0 := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2 :=
    hrstar_sq ▸ sq_lt_sq' (by linarith) hr₀_gt_rstar
  have hr_pos : 0 < lorentzian_explicit K γ r₀ t :=
    lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt_one : lorentzian_explicit K γ r₀ t < 1 :=
    lorentzian_explicit_lt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_gt_rstar : Real.sqrt (1 - 2 * γ / K) < lorentzian_explicit K γ r₀ t := by
    rw [← Real.sqrt_sq (le_of_lt hr_pos)]
    apply Real.sqrt_lt_sqrt (by rw [sub_nonneg, div_le_one hK]; linarith)
    rw [← hrstar_sq]
    exact lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt t ht
  rw [(lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht).deriv]
  exact lorentzian_ode_neg_above_rstar K γ (lorentzian_explicit K γ r₀ t)
      hK hγ hKγ hr_gt_rstar hr_lt_one

/-- **Strict monotone decrease above r***: for r₀ ∈ (r*, 1), the explicit solution is strictly
    decreasing: r(t) < r(s) for 0 ≤ s < t. Follows from negative derivative everywhere. -/
theorem lorentzian_explicit_strictly_decreasing (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    lorentzian_explicit K γ r₀ t < lorentzian_explicit K γ r₀ s := by
  have hcont : ContinuousOn (lorentzian_explicit K γ r₀) (Set.Icc s t) :=
    (lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).mono
      (fun x hx => le_trans hs hx.1)
  have hderiv_neg : ∀ u ∈ interior (Set.Icc s t), deriv (lorentzian_explicit K γ r₀) u < 0 := by
    rw [interior_Icc]
    intro u ⟨hs_u, _⟩
    exact lorentzian_explicit_neg_deriv K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_gt_rstar u
        (le_trans hs (le_of_lt hs_u))
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc s t) hcont hderiv_neg
  exact hanti (Set.left_mem_Icc.mpr (le_of_lt hst)) (Set.right_mem_Icc.mpr (le_of_lt hst)) hst

/-- **Strictly decreasing trajectory for any ODE solution**: if S.r 0 > r*, then S.r t < S.r s
    for any 0 ≤ s < t. Lifts strictly_decreasing to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.strictly_decreasing (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    S.r t < S.r s := by
  rw [S.eq_explicit_of_nonneg s hs, S.eq_explicit_of_nonneg t (hs.trans hst.le)]
  exact lorentzian_explicit_strictly_decreasing S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar hs hst

/-- **Unique positive fixed point**: for K > 2γ, r* = √(1-2γ/K) is the only positive root
    of the Lorentzian ODE. Any r > 0 with ṙ = 0 must equal r*. -/
theorem lorentzian_unique_pos_fixed_point (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr_pos : 0 < r) (hfixed : lorentzianODE K γ r = 0) :
    r = Real.sqrt (1 - 2 * γ / K) := by
  rw [lorentzian_ode_factored K γ r (ne_of_gt hK)] at hfixed
  rcases mul_eq_zero.mp hfixed with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · linarith
    · linarith
  · have hr_sq : r ^ 2 = 1 - 2 * γ / K := by linarith
    rw [← Real.sqrt_sq hr_pos.le, hr_sq]

/-- **Fixed points of the ODE**: for K > 2γ and r ≥ 0, ṙ = 0 if and only if r = 0 or r = r*.
    This is the complete characterization of equilibria on the non-negative half-line. -/
theorem lorentzian_fixed_point_iff (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K) (hr : 0 ≤ r) :
    lorentzianODE K γ r = 0 ↔ r = 0 ∨ r = Real.sqrt (1 - 2 * γ / K) := by
  constructor
  · intro hfixed
    rcases eq_or_lt_of_le hr with rfl | hr_pos
    · exact Or.inl rfl
    · exact Or.inr (lorentzian_unique_pos_fixed_point K γ r hK hγ hKγ hr_pos hfixed)
  · rintro (rfl | rfl)
    · simp [lorentzianODE]
    · exact lorentzian_rstar_is_fixed_point K γ hK hγ hKγ

/-- **Solution avoids equilibrium**: if r₀ ≠ r*, then r(t) ≠ r* for all t ≥ 0.
    Equivalently, the orbit starting away from r* never reaches r* in finite time. -/
theorem lorentzian_explicit_ne_rstar (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ≠ Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_ne_sq : r₀ ^ 2 ≠ 1 - 2 * γ / K := by
    intro h
    exact hr₀_ne (by rw [← Real.sqrt_sq hr₀_pos.le, h])
  rcases lt_or_gt_of_ne hr₀_ne_sq with h | h
  · have hr_lt := lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
    intro heq; rw [heq, hrstar_sq] at hr_lt; exact lt_irrefl _ hr_lt
  · have hr_gt := lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
    intro heq; rw [heq, hrstar_sq] at hr_gt; exact lt_irrefl _ hr_gt

/-- **Orbit never reaches r* for any ODE solution**: if S.r 0 ≠ r*, then S.r t ≠ r* for all t ≥ 0.
    The trajectory stays permanently away from the equilibrium until t → ∞.
    Lifts lorentzian_explicit_ne_rstar to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.ne_rstar (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t ≠ Real.sqrt (1 - 2 * S.γ / S.K) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_ne_rstar S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t ht

/-- **Square difference stays positive**: if r₀ ≠ r*, then (r(t)²-r*²) ≠ 0 for all t ≥ 0.
    Equivalently, the Lyapunov function V(t) = (r²-r*²)² > 0 until r → r*. -/
theorem lorentzian_sq_diff_ne_zero (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ^ 2 - (1 - 2 * γ / K) ≠ 0 := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_ne_sq : r₀ ^ 2 ≠ 1 - 2 * γ / K := by
    intro h; exact hr₀_ne (by rw [← Real.sqrt_sq hr₀_pos.le, h])
  rcases lt_or_gt_of_ne hr₀_ne_sq with h | h
  · have hr_lt := lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
    linarith [hrstar_sq ▸ hr_lt]
  · have hr_gt := lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
    linarith [hrstar_sq ▸ hr_gt]

/-- **Semigroup property for w**: the Bernoulli transform satisfies the semigroup identity.
    w(t₁+t₂, r₀) = w(t₂, r(t₁, r₀)). The key step: 1/r(t₁)² = w(t₁) (from lorentzian_explicit_sq). -/
theorem lorentzian_w_semigroup (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) :
    w_func K γ r₀ (t₁ + t₂) = w_func K γ (lorentzian_explicit K γ r₀ t₁) t₂ := by
  have hr₁_sq := lorentzian_explicit_sq K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t₁ ht₁
  have hkey : 1 / lorentzian_explicit K γ r₀ t₁ ^ 2 - K / (K - 2 * γ) =
      (1 / r₀ ^ 2 - K / (K - 2 * γ)) * Real.exp (-(K - 2 * γ) * t₁) := by
    rw [hr₁_sq, one_div, inv_inv]; simp only [w_func]; ring
  simp only [w_func, hkey]
  rw [show -(K - 2 * γ) * (t₁ + t₂) = -(K - 2 * γ) * t₁ + -(K - 2 * γ) * t₂ from by ring,
      Real.exp_add]
  ring

/-- **Semigroup property for the ODE flow**: the explicit solution satisfies the semigroup law.
    r(t₁+t₂, r₀) = r(t₂, r(t₁, r₀)). Equivalently, time-shifting is the same as re-initializing. -/
theorem lorentzian_explicit_semigroup (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) :
    lorentzian_explicit K γ r₀ (t₁ + t₂) =
      lorentzian_explicit K γ (lorentzian_explicit K γ r₀ t₁) t₂ := by
  have h := lorentzian_w_semigroup K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t₁ t₂ ht₁
  simp only [lorentzian_explicit, h]

/-- **Abstract semigroup property**: S.r (t₁ + t₂) = lorentzian_explicit K γ (S.r t₁) t₂
    for any 0 ≤ t₁. The ODE flow composed with itself equals the flow from the intermediate point.
    Lifts lorentzian_explicit_semigroup to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.semigroup (S : LorentzianContinuousSolution)
    (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    S.r (t₁ + t₂) = lorentzian_explicit S.K S.γ (S.r t₁) t₂ := by
  rw [S.eq_explicit_of_nonneg (t₁ + t₂) (by linarith),
      S.eq_explicit_of_nonneg t₁ ht₁,
      lorentzian_explicit_semigroup S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
        S.hr_init_pos S.hr_init_lt t₁ t₂ ht₁]

/-- **One-sided invariance (below)**: when r₀ < r*, the trajectory stays below r* for all t ≥ 0.
    The sublevel set {r < r*} is forward-invariant under the Lorentzian ODE. -/
theorem lorentzian_explicit_lt_rstar_of_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t < Real.sqrt (1 - 2 * γ / K) := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K :=
    hrstar_sq ▸ sq_lt_sq' (by linarith) hr₀_lt_rstar
  have hr_sq_lt := lorentzian_explicit_sq_lt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := Real.sqrt_lt_sqrt (sq_nonneg (lorentzian_explicit K γ r₀ t)) hr_sq_lt
  rwa [Real.sqrt_sq hr_pos.le] at h

/-- **One-sided invariance (above)**: when r* < r₀, the trajectory stays above r* for all t ≥ 0.
    The superlevel set {r > r*} is forward-invariant under the Lorentzian ODE. -/
theorem lorentzian_explicit_gt_rstar_of_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * γ / K) < lorentzian_explicit K γ r₀ t := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2 :=
    hrstar_sq ▸ sq_lt_sq' (by linarith) hr₀_gt_rstar
  have hr_sq_gt := lorentzian_explicit_sq_gt_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt t ht
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := Real.sqrt_lt_sqrt (sq_nonneg (Real.sqrt (1 - 2 * γ / K))) hr_sq_gt
  rwa [Real.sqrt_sq hrstar_pos.le, Real.sqrt_sq hr_pos.le] at h

/-- **Sublevel set invariance for any ODE solution**: if S.r 0 < r*, then S.r t < r* for all t ≥ 0.
    Lifts lt_rstar_of_init to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.lt_rstar_of_init (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t < Real.sqrt (1 - 2 * S.γ / S.K) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_lt_rstar_of_init S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_lt_rstar t ht

/-- **Superlevel set invariance for any ODE solution**: if r* < S.r 0, then r* < S.r t for all t ≥ 0.
    Lifts gt_rstar_of_init to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.gt_rstar_of_init (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * S.γ / S.K) < S.r t := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_gt_rstar_of_init S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar t ht

/-- **Trajectory above initial value**: when r₀ < r*, r₀ ≤ r(t) for all t ≥ 0.
    Solution is non-decreasing from r₀ toward r*. -/
theorem lorentzian_explicit_ge_r0 (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    r₀ ≤ lorentzian_explicit K γ r₀ t := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq_lt : r₀ ^ 2 < 1 - 2 * γ / K :=
    hrstar_sq ▸ sq_lt_sq' (by linarith) hr₀_lt_rstar
  have hr_sq_ge := lorentzian_explicit_sq_ge_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_lt t ht
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := Real.sqrt_le_sqrt hr_sq_ge
  rwa [Real.sqrt_sq hr₀_pos.le, Real.sqrt_sq hr_pos.le] at h

/-- **Trajectory below initial value**: when r* < r₀, r(t) ≤ r₀ for all t ≥ 0.
    Solution is non-increasing from r₀ toward r*. -/
theorem lorentzian_explicit_le_r0 (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    lorentzian_explicit K γ r₀ t ≤ r₀ := by
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hr₀_sq_gt : 1 - 2 * γ / K < r₀ ^ 2 :=
    hrstar_sq ▸ sq_lt_sq' (by linarith) hr₀_gt_rstar
  have hr_sq_le := lorentzian_explicit_sq_le_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_sq_gt t ht
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := Real.sqrt_le_sqrt hr_sq_le
  rwa [Real.sqrt_sq hr_pos.le, Real.sqrt_sq hr₀_pos.le] at h

/-- **Trajectory non-decreasing for any ODE solution**: if S.r 0 < r*, then S.r 0 ≤ S.r t.
    Lifts ge_r0 to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.ge_init_of_lt_rstar (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    S.r 0 ≤ S.r t := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_explicit_ge_r0 S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_lt_rstar t ht

/-- **Trajectory non-increasing for any ODE solution**: if r* < S.r 0, then S.r t ≤ S.r 0.
    Lifts le_r0 to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.le_init_of_gt_rstar (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t ≤ S.r 0 := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_explicit_le_r0 S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar t ht

/-- **Distance to equilibrium is strictly decreasing**: for r₀ ≠ r* and 0 ≤ s < t,
    |r(t)-r*| < |r(s)-r*|. The ODE drives all trajectories strictly toward r* in absolute distance. -/
theorem lorentzian_explicit_dist_strict_decreasing (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| <
    |lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)| := by
  rcases lt_or_gt_of_ne hr₀_ne with h | h
  · have hlt_s := lorentzian_explicit_lt_rstar_of_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h s hs
    have hlt_t := lorentzian_explicit_lt_rstar_of_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t
        (hs.trans hst.le)
    have hinc := lorentzian_explicit_strictly_increasing K γ r₀ hK hγ hKγ hr₀_pos h hs hst
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  · have hgt_s := lorentzian_explicit_gt_rstar_of_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h s hs
    have hgt_t := lorentzian_explicit_gt_rstar_of_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t
        (hs.trans hst.le)
    have hdec := lorentzian_explicit_strictly_decreasing K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h hs hst
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-- **Equilibrium trajectory**: the explicit solution initialized at r* stays at r* for all time.
    The Bernoulli amplitude A = 1/r*²-B = 0, so w(t) = B = 1/r*² and r(t) = r*. -/
theorem lorentzian_explicit_rstar_const (K γ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (t : ℝ) :
    lorentzian_explicit K γ (Real.sqrt (1 - 2 * γ / K)) t =
      Real.sqrt (1 - 2 * γ / K) := by
  have hd : (0:ℝ) < K - 2 * γ := by linarith
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have heq : 1 / Real.sqrt (1 - 2 * γ / K) ^ 2 = K / (K - 2 * γ) := by
    rw [hrstar_sq]; field_simp [hK.ne', hd.ne']
  have hw : w_func K γ (Real.sqrt (1 - 2 * γ / K)) t = K / (K - 2 * γ) := by
    simp only [w_func, heq, sub_self, zero_mul, zero_add]
  simp only [lorentzian_explicit, hw]
  congr 1; field_simp [hK.ne', hd.ne']

/-- **Lyapunov stability**: r* is Lyapunov stable with δ = ε.
    For any ε > 0, any trajectory starting within ε of r* stays within ε for all t ≥ 0. -/
theorem lorentzian_explicit_lyapunov_stable (K γ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r₀ : ℝ, 0 < r₀ → r₀ < 1 →
      |r₀ - Real.sqrt (1 - 2 * γ / K)| < δ →
      ∀ t : ℝ, 0 ≤ t →
        |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε := by
  refine ⟨ε, hε, fun r₀ hr₀_pos hr₀_lt hr₀_near t ht => ?_⟩
  rcases eq_or_ne r₀ (Real.sqrt (1 - 2 * γ / K)) with rfl | hr₀_ne
  · rw [lorentzian_explicit_rstar_const K γ hK hγ hKγ t, sub_self, abs_zero]; exact hε
  · rcases eq_or_lt_of_le ht with rfl | ht_pos
    · rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hr₀_near
    · calc |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)|
            < |lorentzian_explicit K γ r₀ 0 - Real.sqrt (1 - 2 * γ / K)| :=
              lorentzian_explicit_dist_strict_decreasing K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
                hr₀_ne le_rfl ht_pos
          _ = |r₀ - Real.sqrt (1 - 2 * γ / K)| := by
              rw [lorentzian_explicit_init K γ r₀ hr₀_pos]
          _ < ε := hr₀_near

/-- **Lyapunov function HasDerivAt**: d/dt (r(t)-r*)² = 2(r(t)-r*)·ṙ(t). -/
theorem lorentzian_lyapunov_v_hasDerivAt (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (2 * (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) *
        lorentzianODE K γ (lorentzian_explicit K γ r₀ t)) t := by
  have h := (lorentzian_explicit_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
      |>.sub_const (Real.sqrt (1 - 2 * γ / K))).pow 2
  convert h using 1
  push_cast; ring

/-- **Lyapunov derivative is negative**: for r₀ ≠ r*, d/dt (r(t)-r*)² < 0 for all t ≥ 0.
    The squared distance to equilibrium is a strict Lyapunov function. -/
theorem lorentzian_lyapunov_v_deriv_neg (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2) t < 0 := by
  rw [(lorentzian_lyapunov_v_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht).deriv]
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt := lorentzian_explicit_lt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_ne := lorentzian_explicit_ne_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht
  rcases lt_or_gt_of_ne hr_ne with h | h
  · have hpos := lorentzian_ode_pos_below_rstar K γ (lorentzian_explicit K γ r₀ t)
        hK hγ hKγ hr_pos h
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg two_pos (by linarith)) hpos
  · have hneg := lorentzian_ode_neg_above_rstar K γ (lorentzian_explicit K γ r₀ t)
        hK hγ hKγ h hr_lt
    exact mul_neg_of_pos_of_neg (mul_pos two_pos (by linarith)) hneg

/-- **V = (r-r*)² is strictly anti-monotone**: for r₀ ≠ r* and 0 ≤ s < t,
    (r(t)-r*)² < (r(s)-r*)². The Lyapunov function strictly decreases along all non-equilibrium trajectories. -/
theorem lorentzian_lyapunov_v_strict_anti (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 <
    (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2 := by
  have hcont : ContinuousOn
      (fun u => (lorentzian_explicit K γ r₀ u - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (Set.Icc s t) :=
    ((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).mono
        (fun x hx => hs.trans hx.1)).sub continuousOn_const |>.pow 2
  have hderiv_neg :
      ∀ u ∈ interior (Set.Icc s t),
        deriv (fun u => (lorentzian_explicit K γ r₀ u - Real.sqrt (1 - 2 * γ / K)) ^ 2) u < 0 := by
    rw [interior_Icc]
    intro u ⟨hsu, _⟩
    exact lorentzian_lyapunov_v_deriv_neg K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne u
        (hs.trans (le_of_lt hsu))
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc s t) hcont hderiv_neg
  exact hanti (Set.left_mem_Icc.mpr hst.le) (Set.right_mem_Icc.mpr hst.le) hst

/-- **V(0) = (r₀ - r*)²**: the Lyapunov function equals the initial squared distance. -/
theorem lorentzian_lyapunov_v_at_zero (K γ r₀ : ℝ) (hr₀_pos : 0 < r₀) :
    (lorentzian_explicit K γ r₀ 0 - Real.sqrt (1 - 2 * γ / K)) ^ 2 =
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 := by
  rw [lorentzian_explicit_init K γ r₀ hr₀_pos]

/-- **V bounded by initial value**: for r₀ ≠ r* and t > 0, V(t) < V(0) = (r₀-r*)². -/
theorem lorentzian_lyapunov_v_lt_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 < t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 <
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 := by
  have h := lorentzian_lyapunov_v_strict_anti K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne
      le_rfl ht
  rwa [lorentzian_lyapunov_v_at_zero K γ r₀ hr₀_pos] at h

/-- **V → 0 as t → ∞**: the Lyapunov function converges to 0, reflecting r(t) → r*. -/
theorem lorentzian_lyapunov_v_tendsto_zero (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    Filter.Tendsto (fun t => (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      Filter.atTop (nhds 0) := by
  have h := (lorentzian_explicit_tendsto K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
      |>.sub_const (Real.sqrt (1 - 2 * γ / K))).pow 2
  simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h
  exact h

/-- **V' ODE**: d/dt (r-r*)² = -K·r·(r+r*)·(r-r*)², expressing V' in terms of V itself.
    Proof: chain rule gives V' = 2(r-r*)·ṙ; lorentzian_ode_factored gives ṙ = (K/2)r(r*²-r²);
    then 2(r-r*)·(K/2)r(r*²-r²) = -Kr(r+r*)(r-r*)² by ring. -/
theorem lorentzian_lyapunov_v_deriv_formula (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (-(K * lorentzian_explicit K γ r₀ t *
         (lorentzian_explicit K γ r₀ t + Real.sqrt (1 - 2 * γ / K)) *
         (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2)) t := by
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hode : lorentzianODE K γ (lorentzian_explicit K γ r₀ t) =
      K / 2 * lorentzian_explicit K γ r₀ t *
      (Real.sqrt (1 - 2 * γ / K) ^ 2 - lorentzian_explicit K γ r₀ t ^ 2) := by
    rw [lorentzian_ode_factored K γ (lorentzian_explicit K γ r₀ t) (ne_of_gt hK)]
    congr 1; linarith [hrstar_sq]
  convert lorentzian_lyapunov_v_hasDerivAt K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht using 1
  rw [hode]; ring

/-- **Below-r* Lyapunov exponential bound**: when r₀ < r*, V(t) = (r(t)-r*)² ≤ V(0)·exp(-K·r₀·r*·t).
    Uses V'=-(K·r·(r+r*)·V) and r(t)≥r₀ to bound K·r·(r+r*)≥K·r₀·r*, then comparison_decay. -/
theorem lorentzian_lyapunov_v_exp_bound_below (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
      Real.exp (-(K * r₀ * Real.sqrt (1 - 2 * γ / K)) * t) := by
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hVt := comparison_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (fun s => -(K * lorentzian_explicit K γ r₀ s *
        (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) *
        (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2))
      (K * r₀ * Real.sqrt (1 - 2 * γ / K))
      (((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).sub
          continuousOn_const).pow 2)
      (fun s hs => lorentzian_lyapunov_v_deriv_formula K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs.le)
      (fun s hs => by
        simp only []
        have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs.le
        have hr_ge := lorentzian_explicit_ge_r0 K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
            hr₀_lt_rstar s hs.le
        have h1 : r₀ * Real.sqrt (1 - 2 * γ / K) ≤
            lorentzian_explicit K γ r₀ s * (lorentzian_explicit K γ r₀ s +
            Real.sqrt (1 - 2 * γ / K)) :=
          (mul_le_mul_of_nonneg_right hr_ge hrs_pos.le).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hr_pos.le) hr_pos.le)
        have hcoeff_nn : 0 ≤ K * lorentzian_explicit K γ r₀ s *
            (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) -
            K * r₀ * Real.sqrt (1 - 2 * γ / K) := by nlinarith
        nlinarith [mul_nonneg hcoeff_nn
          (sq_nonneg (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)))])
      t ht
  have hVt' : (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
      (lorentzian_explicit K γ r₀ 0 - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
      Real.exp (-(K * r₀ * Real.sqrt (1 - 2 * γ / K)) * t) := hVt
  rwa [lorentzian_lyapunov_v_at_zero K γ r₀ hr₀_pos] at hVt'

/-- **Above-r* Lyapunov exponential bound**: when r* < r₀, V(t) = (r(t)-r*)² ≤ V(0)·exp(-2K·r*²·t).
    Uses V'=-(K·r·(r+r*)·V) and r(t)≥r* to bound K·r·(r+r*)≥2K·r*², then comparison_decay. -/
theorem lorentzian_lyapunov_v_exp_bound_above (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
      Real.exp (-(2 * K * (1 - 2 * γ / K)) * t) := by
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  have hVt := comparison_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (fun s => -(K * lorentzian_explicit K γ r₀ s *
        (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) *
        (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2))
      (2 * K * (1 - 2 * γ / K))
      (((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).sub
          continuousOn_const).pow 2)
      (fun s hs => lorentzian_lyapunov_v_deriv_formula K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs.le)
      (fun s hs => by
        simp only []
        have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs.le
        have hr_gt := lorentzian_explicit_gt_rstar_of_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
            hr₀_gt_rstar s hs.le
        -- K·r·(r+r*) ≥ K·r*·2r* = 2K·r*² since r≥r* and r+r*≥2r*
        have h1 : 2 * K * (1 - 2 * γ / K) ≤ K * lorentzian_explicit K γ r₀ s *
            (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) := by
          have hrs_le : Real.sqrt (1 - 2 * γ / K) ≤ lorentzian_explicit K γ r₀ s := hr_gt.le
          have hsum : Real.sqrt (1 - 2 * γ / K) + Real.sqrt (1 - 2 * γ / K) ≤
              lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K) := by linarith
          have hprod : Real.sqrt (1 - 2 * γ / K) * (Real.sqrt (1 - 2 * γ / K) +
              Real.sqrt (1 - 2 * γ / K)) ≤
              lorentzian_explicit K γ r₀ s * (lorentzian_explicit K γ r₀ s +
              Real.sqrt (1 - 2 * γ / K)) :=
            mul_le_mul hrs_le hsum (by linarith) (le_of_lt hr_pos)
          nlinarith [mul_le_mul_of_nonneg_left hprod hK.le, hrstar_sq]
        have hcoeff_nn : 0 ≤ K * lorentzian_explicit K γ r₀ s *
            (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) -
            2 * K * (1 - 2 * γ / K) := by linarith
        nlinarith [mul_nonneg hcoeff_nn
          (sq_nonneg (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)))])
      t ht
  have hVt' : (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
      (lorentzian_explicit K γ r₀ 0 - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
      Real.exp (-(2 * K * (1 - 2 * γ / K)) * t) := hVt
  rwa [lorentzian_lyapunov_v_at_zero K γ r₀ hr₀_pos] at hVt'

/-- **Unified Lyapunov exponential bound**: V(t) ≤ V(0)·exp(-K·min(r₀,r*)·r*·t) for r₀ ≠ r*.
    Below r*: min=r₀, rate K·r₀·r* from v_exp_bound_below.
    Above r*: min=r*, rate K·r*²≤2K·r*² from v_exp_bound_above + exp monotonicity. -/
theorem lorentzian_lyapunov_v_exp_bound (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
      Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
        Real.sqrt (1 - 2 * γ / K)) * t) := by
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hrstar_sq : Real.sqrt (1 - 2 * γ / K) ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hKγ))
  rcases lt_or_gt_of_ne hr₀_ne with h | h
  · rw [min_eq_left h.le]
    exact lorentzian_lyapunov_v_exp_bound_below K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
  · rw [min_eq_right h.le]
    calc (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2
        ≤ (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
          Real.exp (-(2 * K * (1 - 2 * γ / K)) * t) :=
          lorentzian_lyapunov_v_exp_bound_above K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt h t ht
      _ ≤ (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
          Real.exp (-(K * Real.sqrt (1 - 2 * γ / K) *
            Real.sqrt (1 - 2 * γ / K)) * t) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          apply Real.exp_le_exp.mpr
          have hrs_sq : Real.sqrt (1 - 2 * γ / K) * Real.sqrt (1 - 2 * γ / K) =
              1 - 2 * γ / K := by rw [← sq]; exact hrstar_sq
          have hkey_t : K * Real.sqrt (1 - 2 * γ / K) * Real.sqrt (1 - 2 * γ / K) * t =
              K * (1 - 2 * γ / K) * t := by linear_combination K * t * hrs_sq
          linarith [mul_nonneg (mul_nonneg hK.le (lorentzian_rstar_pos K γ hK hKγ).le) ht]

/-- **V exponential bound for any ODE solution**: for any LorentzianContinuousSolution S,
    (S.r t - r*)² ≤ (S.r 0 - r*)²·exp(-K·min(S.r 0, r*)·r*·t) when S.r 0 ≠ r*.
    Uses eq_explicit_of_nonneg to reduce to the explicit formula, then v_exp_bound. -/
theorem LorentzianContinuousSolution.v_exp_bound (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               Real.sqrt (1 - 2 * S.γ / S.K)) * t) := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_exp_bound S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t ht

/-- **Distance bound for any ODE solution**: for any LorentzianContinuousSolution S with
    S.r 0 ≠ r*, |S.r t - r*| ≤ |S.r 0 - r*|·exp(-K·min(S.r 0, r*)·r*/2·t).
    Uses Solution.v_exp_bound + order_parameter_exp_decay. -/
theorem LorentzianContinuousSolution.r_dist_bound (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  have h := order_parameter_exp_decay
      (fun s => (S.r s - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      S.r
      (Real.sqrt (1 - 2 * S.γ / S.K))
      ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      (S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) * Real.sqrt (1 - 2 * S.γ / S.K))
      (sq_nonneg _)
      (fun s hs => S.v_exp_bound hr₀_ne s hs)
      (fun _ => le_refl _)
      t ht
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Below-r* distance bound**: |r(t)-r*| ≤ |r₀-r*|·exp(-K·r₀·r*/2·t) for r₀ < r*.
    Applies order_parameter_exp_decay with V = (r-r*)² and v_exp_bound_below. -/
theorem lorentzian_lyapunov_r_dist_below (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    Real.sqrt ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2) *
      Real.exp (-(K * r₀ * Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  have hV₀_nn : 0 ≤ (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 := sq_nonneg _
  have h := order_parameter_exp_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (K * r₀ * Real.sqrt (1 - 2 * γ / K))
      hV₀_nn
      (fun s hs => lorentzian_lyapunov_v_exp_bound_below K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
          hr₀_lt_rstar s hs)
      (fun s => le_refl _)
      t ht
  linarith [h]

/-- **Cleaner form of the below-r* distance bound**: |r(t)-r*| ≤ |r₀-r*|·exp(-K·r₀·r*/2·t).
    Simplifies v_exp_bound_below via √((r₀-r*)²) = |r₀-r*|. -/
theorem lorentzian_lyapunov_r_dist_below' (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
      Real.exp (-(K * r₀ * Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  have h := lorentzian_lyapunov_r_dist_below K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
      hr₀_lt_rstar t ht
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Above-r* distance bound**: |r(t)-r*| ≤ |r₀-r*|·exp(-K·r*²·t) for r* < r₀.
    Uses v_exp_bound_above (rate 2K·r*²) + order_parameter_exp_decay, then drops factor 2 via
    exp(-2K·r*²·t/2) = exp(-K·r*²·t) and simplifies √((r₀-r*)²) = |r₀-r*|. -/
theorem lorentzian_lyapunov_r_dist_above (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
      Real.exp (-(K * (1 - 2 * γ / K)) * t) := by
  have hrstar_nn : 0 ≤ 1 - 2 * γ / K := le_of_lt (lorentzian_rstar_pos K γ hK hKγ)
  have h := order_parameter_exp_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (2 * K * (1 - 2 * γ / K))
      (sq_nonneg _)
      (fun s hs => lorentzian_lyapunov_v_exp_bound_above K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
          hr₀_gt_rstar s hs)
      (fun s => le_refl _)
      t ht
  simp only [Real.sqrt_sq_eq_abs] at h
  calc |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)|
      ≤ |r₀ - Real.sqrt (1 - 2 * γ / K)| *
        Real.exp (-(2 * K * (1 - 2 * γ / K)) / 2 * t) := h
    _ = |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-(K * (1 - 2 * γ / K)) * t) := by
        ring_nf

/-- **Explicit convergence time (below r*)**: for r₀ < r*, t > log((r₀-r*)²/ε²)/(K·r₀·r*)
    implies |r(t)-r*| < ε. First Lyapunov-derived convergence time for the Lorentzian ODE. -/
theorem lorentzian_lyapunov_convergence_time_below (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 / ε ^ 2) /
             (K * r₀ * Real.sqrt (1 - 2 * γ / K)) < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε := by
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hV₀_pos : 0 < (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hr₀_lt_rstar))
  have hμ_pos : 0 < K * r₀ * Real.sqrt (1 - 2 * γ / K) :=
    mul_pos (mul_pos hK hr₀_pos) hrs_pos
  exact explicit_convergence_time
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (K * r₀ * Real.sqrt (1 - 2 * γ / K))
      ε hμ_pos hV₀_pos hε
      (fun s hs => lorentzian_lyapunov_v_exp_bound_below K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
          hr₀_lt_rstar s hs)
      (fun s => le_refl _)
      t ht htime

/-- **Explicit convergence time (above r*)**: for r* < r₀ < 1, t > log((r₀-r*)²/ε²)/(2K·r*²)
    implies |r(t)-r*| < ε. Analog of convergence_time_below for the supercritical regime.
    Rate 2K·r*² = 2(K-2γ) is twice the linearized rate (faster than below). -/
theorem lorentzian_lyapunov_convergence_time_above (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 / ε ^ 2) /
             (2 * K * (1 - 2 * γ / K)) < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε := by
  have hV₀_pos : 0 < (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hr₀_gt_rstar))
  have hμ_pos : 0 < 2 * K * (1 - 2 * γ / K) :=
    mul_pos (mul_pos two_pos hK) (lorentzian_rstar_pos K γ hK hKγ)
  exact explicit_convergence_time
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (2 * K * (1 - 2 * γ / K))
      ε hμ_pos hV₀_pos hε
      (fun s hs => lorentzian_lyapunov_v_exp_bound_above K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
          hr₀_gt_rstar s hs)
      (fun s => le_refl _)
      t ht htime

/-- **V is antitone**: for r₀ ≠ r* and 0 ≤ s ≤ t, V(t) ≤ V(s). Weak version of v_strict_anti,
    useful for monotonicity arguments without strict inequalities. -/
theorem lorentzian_lyapunov_v_antitone (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2 := by
  rcases lt_or_eq_of_le hst with h | h
  · exact le_of_lt (lorentzian_lyapunov_v_strict_anti K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
        hr₀_ne hs h)
  · rw [h]

/-- **Unified convergence time**: for r₀ ≠ r*, t > log(V₀/ε²)/(K·min(r₀,r*)·r*)
    implies |r(t)-r*| < ε. Covers both subcritical and supercritical regimes. -/
theorem lorentzian_lyapunov_convergence_time (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 / ε ^ 2) /
             (K * min r₀ (Real.sqrt (1 - 2 * γ / K)) * Real.sqrt (1 - 2 * γ / K)) < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε := by
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hV₀_pos : 0 < (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hr₀_ne)
  have hμ_pos : 0 < K * min r₀ (Real.sqrt (1 - 2 * γ / K)) * Real.sqrt (1 - 2 * γ / K) :=
    mul_pos (mul_pos hK (lt_min hr₀_pos hrs_pos)) hrs_pos
  exact explicit_convergence_time
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (K * min r₀ (Real.sqrt (1 - 2 * γ / K)) * Real.sqrt (1 - 2 * γ / K))
      ε hμ_pos hV₀_pos hε
      (fun s hs => lorentzian_lyapunov_v_exp_bound K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne s hs)
      (fun s => le_refl _)
      t ht htime

/-- **Unified distance bound**: |r(t)-r*| ≤ |r₀-r*|·exp(-K·min(r₀,r*)·r*/2·t).
    Combines r_dist_below (min=r₀, rate K·r₀·r*/2) and r_dist_above (min=r*, rate K·r*²/2)
    into a single statement covering all r₀ ≠ r*. -/
theorem lorentzian_lyapunov_r_dist (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
      Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
                  Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  have h := order_parameter_exp_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (K * min r₀ (Real.sqrt (1 - 2 * γ / K)) * Real.sqrt (1 - 2 * γ / K))
      (sq_nonneg _)
      (fun s hs => lorentzian_lyapunov_v_exp_bound K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne s hs)
      (fun s => le_refl _)
      t ht
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **V coefficient upper bound**: K·r(t)·(r(t)+r*) ≤ 2·K for all t ≥ 0.
    Since r(t) ∈ (0,1) and r* ∈ (0,1), r(t)·(r(t)+r*) ≤ 1·2 = 2.
    Gives a lower bound on V': V'(t) ≥ -2K·V(t) (V cannot decay faster than exp(-2Kt)). -/
theorem lorentzian_lyapunov_v_coeff_le (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    K * lorentzian_explicit K γ r₀ t *
    (lorentzian_explicit K γ r₀ t + Real.sqrt (1 - 2 * γ / K)) ≤ 2 * K := by
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hr_lt1 := lorentzian_explicit_lt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hrs_lt1 := lorentzian_rstar_lt_one K γ hK hγ hKγ
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have h1 : lorentzian_explicit K γ r₀ t ≤ 1 := le_of_lt hr_lt1
  have h2 : Real.sqrt (1 - 2 * γ / K) ≤ 1 := le_of_lt hrs_lt1
  nlinarith [mul_le_mul h1 h1 hr_pos.le (by linarith : (0:ℝ) ≤ 1),
             mul_le_mul h1 h2 hrs_pos.le (by linarith : (0:ℝ) ≤ 1)]

/-- **V' lower bound**: the HasDerivAt value of V = (r(t)-r*)² satisfies V'(t) ≥ -2K·V(t).
    Follows from K·r·(r+r*) ≤ 2K (v_coeff_le) and V ≥ 0. Gives V(t) ≥ V(0)·exp(-2Kt). -/
theorem lorentzian_lyapunov_v_deriv_ge (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 < t) :
    -(2 * K) * (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    -(K * lorentzian_explicit K γ r₀ t *
       (lorentzian_explicit K γ r₀ t + Real.sqrt (1 - 2 * γ / K)) *
       (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2) := by
  have hcoeff := lorentzian_lyapunov_v_coeff_le K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht.le
  nlinarith [sq_nonneg (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K))]

/-- **V coefficient positive**: K·r(t)·(r(t)+r*) > 0 for all t ≥ 0.
    Confirms the Lyapunov coefficient is strictly positive: the factor in V'=-(coeff)·V is positive
    everywhere, so V' < 0 whenever V > 0. -/
theorem lorentzian_lyapunov_v_coeff_pos (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < K * lorentzian_explicit K γ r₀ t *
    (lorentzian_explicit K γ r₀ t + Real.sqrt (1 - 2 * γ / K)) := by
  have hr_pos := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hrs_pos : 0 < Real.sqrt (1 - 2 * γ / K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  exact mul_pos (mul_pos hK hr_pos) (by linarith)

/-- **V > 0 when r₀ ≠ r***: the Lyapunov function V = (r(t)-r*)² is strictly positive
    for all t ≥ 0 when r₀ ≠ r*. Follows from lorentzian_explicit_ne_rstar. -/
theorem lorentzian_lyapunov_v_pos (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    0 < (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
  sq_pos_of_ne_zero (sub_ne_zero.mpr
    (lorentzian_explicit_ne_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht))

/-- **V positivity for any ODE solution**: V(t) = (S.r t - r*)² > 0 for all t ≥ 0 when S.r 0 ≠ r*.
    The orbit never reaches r* in finite time. Lifts v_pos to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_pos (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    0 < (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_v_pos S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t ht

/-- **V lower exponential bound**: V(t) ≥ V(0)·exp(-2K·t) for all t ≥ 0.
    Dual of the upper bound: since V'≥-2K·V (v_deriv_ge), comparison_growth gives the lower bound.
    Establishes that the Lyapunov function cannot vanish faster than exp(-2Kt). -/
theorem lorentzian_lyapunov_v_lb (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 * Real.exp (-(2 * K) * t) ≤
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 := by
  have hV_cont : ContinuousOn
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2) (Ici 0) :=
    ((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).sub
       continuousOn_const).pow 2
  have hVt := comparison_growth
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (fun s => -(K * lorentzian_explicit K γ r₀ s *
               (lorentzian_explicit K γ r₀ s + Real.sqrt (1 - 2 * γ / K)) *
               (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2))
      (-(2 * K))
      hV_cont
      (fun s hs => lorentzian_lyapunov_v_deriv_formula K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs.le)
      (fun s hs => by linarith [lorentzian_lyapunov_v_deriv_ge K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt s hs])
      t ht
  simp only [] at hVt
  rwa [lorentzian_explicit_init K γ r₀ hr₀_pos] at hVt

/-- **Distance lower bound**: |r(t)-r*| ≥ |r₀-r*|·exp(-K·t) for all t ≥ 0.
    Follows from v_lb by taking square roots: sqrt(V(t)) ≥ sqrt(V(0)·exp(-2Kt)) = |r₀-r*|·exp(-Kt).
    Together with lorentzian_lyapunov_r_dist (upper bound), gives exponential trapping of the
    distance: it decays no slower than exp(-Kt) and no faster than exp(-K·min r₀ r*·r*·t/2). -/
theorem lorentzian_lyapunov_r_dist_lb (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-K * t) ≤
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| := by
  have hvlb := lorentzian_lyapunov_v_lb K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hsqrt_exp : Real.sqrt (Real.exp (-(2 * K) * t)) = Real.exp (-K * t) := by
    have h1 : Real.exp (-(2 * K) * t) = Real.exp (-K * t) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  calc |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-K * t)
      = Real.sqrt ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2) *
          Real.sqrt (Real.exp (-(2 * K) * t)) := by
          rw [Real.sqrt_sq_eq_abs, hsqrt_exp]
    _ = Real.sqrt ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 * Real.exp (-(2 * K) * t)) :=
          (Real.sqrt_mul (sq_nonneg _) _).symm
    _ ≤ Real.sqrt ((lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2) :=
          Real.sqrt_le_sqrt hvlb
    _ = |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| :=
          Real.sqrt_sq_eq_abs _

/-- **V lower exponential bound for any ODE solution**: V(t) ≥ V(0)·exp(-2K·t) for all t ≥ 0.
    Lifts v_lb to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_lb (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 * Real.exp (-(2 * S.K) * t) ≤
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_lb S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt t ht

/-- **Distance lower bound for any ODE solution**: |S.r t - r*| ≥ |S.r 0 - r*|·exp(-K·t).
    Lifts r_dist_lb to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.dist_lb (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_r_dist_lb S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt t ht

/-- **Two-sided exponential trap**: for r₀ ≠ r*, the distance |r(t)-r*| is sandwiched between
    two explicit exponential rates for all t ≥ 0:
      |r₀-r*|·exp(-K·t) ≤ |r(t)-r*| ≤ |r₀-r*|·exp(-K·min(r₀,r*)·r*/2·t).
    The upper rate K·min(r₀,r*)·r*/2 ≤ K/2 (sharp for r₀ near r*: both → (K-2γ)/2).
    The lower rate K is universal — valid for all trajectories regardless of starting point. -/
theorem lorentzian_lyapunov_r_trap (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-K * t) ≤
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ∧
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
               Real.sqrt (1 - 2 * γ / K)) / 2 * t) :=
  ⟨lorentzian_lyapunov_r_dist_lb K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht,
   lorentzian_lyapunov_r_dist K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht⟩

/-- **Two-sided exponential trap for any ODE solution**: for S.r 0 ≠ r*, the distance
    |S.r t - r*| satisfies |S.r 0-r*|·exp(-K·t) ≤ |S.r t-r*| ≤ |S.r 0-r*|·exp(-K·min(r₀,r*)·r*/2·t).
    Combines dist_lb (lower) and r_dist_bound (upper). -/
theorem LorentzianContinuousSolution.dist_trap (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ∧
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) :=
  ⟨S.dist_lb t ht, S.r_dist_bound hr₀_ne t ht⟩

/-- **Below-r* two-sided trap**: for r₀ < r*, the distance |r(t)-r*| satisfies
    |r₀-r*|·exp(-K·t) ≤ |r(t)-r*| ≤ |r₀-r*|·exp(-K·r₀·r*/2·t).
    Specializes r_trap using the sharper below-r* upper bound (rate K·r₀·r*/2). -/
theorem lorentzian_lyapunov_r_trap_below (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_lt_rstar : r₀ < Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-K * t) ≤
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ∧
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * r₀ * Real.sqrt (1 - 2 * γ / K)) / 2 * t) :=
  ⟨lorentzian_lyapunov_r_dist_lb K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht,
   lorentzian_lyapunov_r_dist_below' K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_lt_rstar t ht⟩

/-- **Above-r* two-sided trap**: for r* < r₀, the distance |r(t)-r*| satisfies
    |r₀-r*|·exp(-K·t) ≤ |r(t)-r*| ≤ |r₀-r*|·exp(-K·r*²·t).
    Specializes r_trap using the above-r* upper bound (rate K·r*²). -/
theorem lorentzian_lyapunov_r_trap_above (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * γ / K) < r₀)
    (t : ℝ) (ht : 0 ≤ t) :
    |r₀ - Real.sqrt (1 - 2 * γ / K)| * Real.exp (-K * t) ≤
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ∧
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * (1 - 2 * γ / K)) * t) :=
  ⟨lorentzian_lyapunov_r_dist_lb K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht,
   lorentzian_lyapunov_r_dist_above K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_gt_rstar t ht⟩

/-- **Two-trajectory distance bound**: for r₀, r₀' ∈ (0,1) both ≠ r*, the distance between
    two Lorentzian solutions satisfies |r(t,r₀) - r(t,r₀')| ≤ |r₀-r*|·exp(-μ·t) + |r₀'-r*|·exp(-μ'·t)
    where μ = K·min(r₀,r*)·r*/2 and μ' = K·min(r₀',r*)·r*/2.
    Follows from the triangle inequality |r(t,r₀)-r(t,r₀')| ≤ |r(t,r₀)-r*| + |r(t,r₀')-r*|
    and the individual unified distance bounds. -/
theorem lorentzian_lyapunov_two_traj_dist (K γ r₀ r₀' : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀'_pos : 0 < r₀') (hr₀'_lt : r₀' < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (hr₀'_ne : r₀' ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
               Real.sqrt (1 - 2 * γ / K)) / 2 * t) +
    |r₀' - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * min r₀' (Real.sqrt (1 - 2 * γ / K)) *
                Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  set rs := Real.sqrt (1 - 2 * γ / K)
  have htri : |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
      |lorentzian_explicit K γ r₀ t - rs| + |lorentzian_explicit K γ r₀' t - rs| := by
    have := abs_sub_le (lorentzian_explicit K γ r₀ t) rs (lorentzian_explicit K γ r₀' t)
    linarith [abs_sub_comm (lorentzian_explicit K γ r₀' t) rs]
  exact htri.trans (add_le_add
    (lorentzian_lyapunov_r_dist K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht)
    (lorentzian_lyapunov_r_dist K γ r₀' hK hγ hKγ hr₀'_pos hr₀'_lt hr₀'_ne t ht))

/-- **Strict contraction of distance**: for r₀ ≠ r* and t > 0, the distance to equilibrium
    is strictly smaller than the initial distance: |r(t)-r*| < |r₀-r*|.
    Follows from v_lt_init by taking square roots via Real.sqrt_lt_sqrt + sqrt_sq_eq_abs. -/
theorem lorentzian_lyapunov_r_strict_contraction (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| <
    |r₀ - Real.sqrt (1 - 2 * γ / K)| := by
  have hV_lt := lorentzian_lyapunov_v_lt_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht
  have h := Real.sqrt_lt_sqrt (sq_nonneg _) hV_lt
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h

/-- **Strict distance contraction for any ODE solution**: |S.r t - r*| < |S.r 0 - r*| for t > 0
    when S.r 0 ≠ r*. The orbit moves strictly closer to r* at every positive time.
    Lifts r_strict_contraction to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.r_strict_contraction (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| <
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  rw [S.eq_explicit_of_nonneg t ht.le, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_r_strict_contraction S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t ht

/-- **Ball forward invariance**: the open ball B(r*, ε) is forward-invariant — if r₀ is within ε
    of r*, the solution r(t) remains within ε of r* for all t ≥ 0. This is Lyapunov stability
    with identity Lyapunov function δ = ε. Follows from r_strict_contraction (t > 0) and
    lorentzian_explicit_rstar_const (r₀ = r* case) and explicit_init (t = 0 case). -/
theorem lorentzian_lyapunov_r_ball_fwd_inv (K γ r₀ ε : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hε : |r₀ - Real.sqrt (1 - 2 * γ / K)| < ε)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε := by
  set rs := Real.sqrt (1 - 2 * γ / K)
  rcases eq_or_ne r₀ rs with rfl | hne
  · rw [lorentzian_explicit_rstar_const K γ hK hγ hKγ t]; exact hε
  · rcases eq_or_lt_of_le ht with rfl | ht_pos
    · rw [lorentzian_explicit_init K γ r₀ hr₀_pos]; exact hε
    · exact (lorentzian_lyapunov_r_strict_contraction K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
          hne t ht_pos).trans hε

/-- **Distance tends to zero**: |r(t)-r*| → 0 as t → ∞. Lyapunov form of lorentzian_explicit_tendsto:
    follows from v_tendsto_zero by applying sqrt and sqrt_sq_eq_abs, using continuity of sqrt at 0. -/
theorem lorentzian_lyapunov_dist_tendsto_zero (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    Filter.Tendsto (fun t => |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)|)
      Filter.atTop (nhds 0) := by
  have hV := lorentzian_lyapunov_v_tendsto_zero K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
  have h := (lorentzian_explicit_tendsto K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
    |>.sub_const (Real.sqrt (1 - 2 * γ / K)))
  simp only [sub_self] at h
  have h2 := h.abs
  simp only [abs_zero] at h2
  exact h2

/-- **Distance tends to zero for any ODE solution**: |S.r t - r*| → 0 as t → ∞.
    Lifts dist_tendsto_zero to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.dist_tendsto_zero (S : LorentzianContinuousSolution) :
    Filter.Tendsto (fun t => |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)|)
      Filter.atTop (nhds 0) := by
  have h := S.tendsto.sub_const (Real.sqrt (1 - 2 * S.γ / S.K))
  simp only [sub_self] at h
  have h2 := h.abs
  simp only [abs_zero] at h2
  exact h2

/-- **V/V(0) two-sided ratio bound**: when r₀ ≠ r*, the ratio V(t)/V(0) satisfies
    exp(-2K·t) ≤ V(t)/V(0) ≤ exp(-K·min(r₀,r*)·r*·t).
    Packages v_lb (lower) and v_exp_bound (upper) into a single division statement. -/
theorem lorentzian_lyapunov_v_ratio_bound (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(2 * K) * t) ≤
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 /
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 ∧
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 /
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
              Real.sqrt (1 - 2 * γ / K)) * t) := by
  have hV0_pos : 0 < (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hr₀_ne)
  have hlb := lorentzian_lyapunov_v_lb K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have hub := lorentzian_lyapunov_v_exp_bound K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t ht
  constructor
  · apply (le_div_iff₀ hV0_pos).mpr
    linarith [mul_comm (Real.exp (-(2 * K) * t)) ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)]
  · apply (div_le_iff₀ hV0_pos).mpr
    linarith [mul_comm (Real.exp (-(K * min r₀ (Real.sqrt (1 - 2 * γ / K)) *
        Real.sqrt (1 - 2 * γ / K)) * t)) ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)]

/-- **V non-increasing (unconditional)**: V(t) = (r(t)-r*)² is AntitoneOn [0,∞) for ANY r₀ ∈ (0,1),
    including r₀ = r* (where V ≡ 0). Extends v_antitone (which requires r₀ ≠ r*) to all r₀. -/
theorem lorentzian_lyapunov_v_nonincreasing (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    AntitoneOn (fun t => (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (Set.Ici 0) := by
  rcases eq_or_ne r₀ (Real.sqrt (1 - 2 * γ / K)) with rfl | hne
  · simp only [lorentzian_explicit_rstar_const K γ hK hγ hKγ, sub_self, sq, zero_mul]
    exact antitoneOn_const
  · exact fun s hs t ht hst =>
      lorentzian_lyapunov_v_antitone K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hne hs hst

/-- **V non-increasing for any ODE solution**: V(t) = (S.r t - r*)² is AntitoneOn [0,∞)
    for any LorentzianContinuousSolution, including S.r 0 = r* (where V ≡ 0).
    Lifts v_nonincreasing to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_nonincreasing (S : LorentzianContinuousSolution) :
    AntitoneOn (fun t => (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2) (Set.Ici 0) := by
  intro s hs t ht hst
  simp only []
  rw [S.eq_explicit_of_nonneg s (Set.mem_Ici.mp hs),
      S.eq_explicit_of_nonneg t (Set.mem_Ici.mp ht)]
  exact lorentzian_lyapunov_v_nonincreasing S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hs ht hst

/-- **V universally bounded by V(0) for any ODE solution**: V(t) ≤ (S.r 0 - r*)² for all t ≥ 0.
    Corollary of v_nonincreasing at s = 0. No r₀ ≠ r* assumption needed. -/
theorem LorentzianContinuousSolution.v_le_init (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 :=
  S.v_nonincreasing (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-- **Sublevel set forward invariance**: once V(t₀) ≤ c, we have V(t) ≤ c for all t ≥ t₀ ≥ 0.
    Direct corollary of v_nonincreasing (V is AntitoneOn [0,∞)). -/
theorem lorentzian_lyapunov_sublevel_fwd_inv (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (c : ℝ) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t)
    (hV : (lorentzian_explicit K γ r₀ t₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤ c) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤ c :=
  (lorentzian_lyapunov_v_nonincreasing K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
    (Set.mem_Ici.mpr ht₀) (Set.mem_Ici.mpr (ht₀.trans ht)) ht).trans hV

/-- **V universally bounded by V(0)**: V(t) ≤ V(0) = (r₀-r*)² for all t ≥ 0 and any r₀.
    Follows from sublevel_fwd_inv at t₀ = 0 with c = V(0). No r₀ ≠ r* assumption needed. -/
theorem lorentzian_lyapunov_v_le_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 :=
  lorentzian_lyapunov_sublevel_fwd_inv K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt
    ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
    0 t le_rfl ht
    (by rw [lorentzian_explicit_init K γ r₀ hr₀_pos])

/-- **Distance universally bounded by initial**: |r(t)-r*| ≤ |r₀-r*| for all t ≥ 0 and any r₀.
    Follows from v_le_init by taking square roots via sqrt_le_sqrt + sqrt_sq_eq_abs. -/
theorem lorentzian_lyapunov_dist_le_init (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| := by
  have hV := lorentzian_lyapunov_v_le_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  have h := Real.sqrt_le_sqrt hV
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h

/-- **Ball membership**: r(t) ∈ [r*-|r₀-r*|, r*+|r₀-r*|] for all t ≥ 0.
    Rephrases dist_le_init as symmetric interval membership via abs_le. -/
theorem lorentzian_lyapunov_r_in_ball (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * γ / K) - |r₀ - Real.sqrt (1 - 2 * γ / K)| ≤
    lorentzian_explicit K γ r₀ t ∧
    lorentzian_explicit K γ r₀ t ≤
    Real.sqrt (1 - 2 * γ / K) + |r₀ - Real.sqrt (1 - 2 * γ / K)| := by
  have h := lorentzian_lyapunov_dist_le_init K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t ht
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Distance ≤ initial distance for any ODE solution**: |S.r t - r*| ≤ |S.r 0 - r*| for all t ≥ 0.
    Corollary of S.v_le_init via Real.sqrt_le_sqrt + sqrt_sq_eq_abs. -/
theorem LorentzianContinuousSolution.dist_le_init (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  have h := Real.sqrt_le_sqrt (S.v_le_init t ht)
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h

/-- **Ball membership for any ODE solution**: S.r t ∈ [r*-|r₀-r*|, r*+|r₀-r*|] for all t ≥ 0.
    Corollary of dist_le_init via abs_le. -/
theorem LorentzianContinuousSolution.r_in_ball (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * S.γ / S.K) - |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| ≤ S.r t ∧
    S.r t ≤ Real.sqrt (1 - 2 * S.γ / S.K) + |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  have h := S.dist_le_init t ht
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Lyapunov stability for any ODE solution**: if |S.r 0 - r*| < ε, then |S.r t - r*| < ε
    for all t ≥ 0. The open ε-ball around r* is forward-invariant.
    Follows immediately from dist_le_init: |S.r t - r*| ≤ |S.r 0 - r*| < ε. -/
theorem LorentzianContinuousSolution.lyapunov_stable (S : LorentzianContinuousSolution)
    (ε : ℝ) (hε : |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| < ε)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε :=
  (S.dist_le_init t ht).trans_lt hε

/-- **V interval decay**: for 0 ≤ t₀ ≤ t₀+Δ, V(t₀+Δ) ≤ V(t₀)·exp(-K·min(r(t₀),r*)·r*·Δ).
    Uses the semigroup property to shift the starting time to t₀: the trajectory from r(t₀) satisfies
    the same ODE, so v_exp_bound applies with r₁ = r(t₀) in place of r₀. -/
theorem lorentzian_lyapunov_v_interval_decay (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (t₀ Δ : ℝ) (ht₀ : 0 ≤ t₀) (hΔ : 0 ≤ Δ) :
    (lorentzian_explicit K γ r₀ (t₀ + Δ) - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (lorentzian_explicit K γ r₀ t₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
    Real.exp (-(K * min (lorentzian_explicit K γ r₀ t₀) (Real.sqrt (1 - 2 * γ / K)) *
               Real.sqrt (1 - 2 * γ / K)) * Δ) := by
  set rs := Real.sqrt (1 - 2 * γ / K)
  set r₁ := lorentzian_explicit K γ r₀ t₀
  have hr₁_pos : 0 < r₁ := lorentzian_explicit_pos K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t₀ ht₀
  have hr₁_lt : r₁ < 1 := lorentzian_explicit_lt_one K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t₀ ht₀
  have hr₁_ne : r₁ ≠ rs :=
    lorentzian_explicit_ne_rstar K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt hr₀_ne t₀ ht₀
  have hsemi := lorentzian_explicit_semigroup K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t₀ Δ ht₀
  rw [hsemi]
  exact lorentzian_lyapunov_v_exp_bound K γ r₁ hK hγ hKγ hr₁_pos hr₁_lt hr₁_ne Δ hΔ

/-- **V persistence drop**: if r(t) ≥ δ for all t ∈ [t₀, t₀+Δ], then
    V(t₀+Δ) ≤ V(t₀)·exp(-K·δ·r*·Δ). Uses comparison_decay_interval with the V' ODE
    and the lower rate bound K·r·(r+r*) ≥ K·δ·r* (from r ≥ δ and r+r* ≥ r*). -/
theorem lorentzian_lyapunov_v_persistence_drop (K γ r₀ δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hδ_pos : 0 < δ)
    (t₀ Δ : ℝ) (ht₀ : 0 ≤ t₀) (hΔ : 0 ≤ Δ)
    (h_persist : ∀ t, t₀ ≤ t → t ≤ t₀ + Δ → δ ≤ lorentzian_explicit K γ r₀ t) :
    (lorentzian_explicit K γ r₀ (t₀ + Δ) - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (lorentzian_explicit K γ r₀ t₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
    Real.exp (-(K * δ * Real.sqrt (1 - 2 * γ / K)) * Δ) := by
  set rs := Real.sqrt (1 - 2 * γ / K)
  have hrs_pos : 0 < rs := Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  have hV_cont : ContinuousOn (fun s => (lorentzian_explicit K γ r₀ s - rs) ^ 2)
      (Set.Icc t₀ (t₀ + Δ)) :=
    ((lorentzian_explicit_continuousOn K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt).mono
      (fun t ht => le_trans ht₀ (Set.mem_Icc.mp ht).1) |>.sub continuousOn_const).pow 2
  exact comparison_decay_interval
    (fun s => (lorentzian_explicit K γ r₀ s - rs) ^ 2)
    (fun s => -(K * lorentzian_explicit K γ r₀ s *
        (lorentzian_explicit K γ r₀ s + rs) *
        (lorentzian_explicit K γ r₀ s - rs) ^ 2))
    (K * δ * rs) t₀ Δ hΔ
    hV_cont
    (fun t ht_lo _ =>
      lorentzian_lyapunov_v_deriv_formula K γ r₀ hK hγ hKγ hr₀_pos hr₀_lt t
        (le_trans ht₀ (le_of_lt ht_lo)))
    (fun t ht_lo ht_hi => by
      simp only []
      have hrt_ge : δ ≤ lorentzian_explicit K γ r₀ t :=
        h_persist t (le_of_lt ht_lo) (le_of_lt ht_hi)
      have hrt_pos : 0 < lorentzian_explicit K γ r₀ t :=
        lt_of_lt_of_le hδ_pos hrt_ge
      have hcoeff : K * δ * rs ≤ K * lorentzian_explicit K γ r₀ t *
          (lorentzian_explicit K γ r₀ t + rs) :=
        calc K * δ * rs
            ≤ K * lorentzian_explicit K γ r₀ t * rs :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hrt_ge hK.le) hrs_pos.le
          _ ≤ K * lorentzian_explicit K γ r₀ t * (lorentzian_explicit K γ r₀ t + rs) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hrt_pos.le)
                (mul_pos hK hrt_pos).le
      nlinarith [sq_nonneg (lorentzian_explicit K γ r₀ t - rs)])

/-- **V uniform exponential decay from global persistence**: if r(t) ≥ δ for all t ≥ 0,
    then V(t) ≤ V(0)·exp(-K·δ·r*·t). Global form of v_persistence_drop at t₀=0. -/
theorem lorentzian_lyapunov_v_uniform_exp_decay (K γ r₀ δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ lorentzian_explicit K γ r₀ t)
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 ≤
    (r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 *
    Real.exp (-(K * δ * Real.sqrt (1 - 2 * γ / K)) * t) := by
  have h := lorentzian_lyapunov_v_persistence_drop K γ r₀ δ hK hγ hKγ hr₀_pos hr₀_lt hδ_pos
    0 t le_rfl ht (fun s hs1 _ => h_persist s hs1)
  rwa [zero_add, lorentzian_lyapunov_v_at_zero K γ r₀ hr₀_pos] at h

/-- **V interval decay for any ODE solution**: V(t₀+Δ) ≤ V(t₀)·exp(-K·min(r(t₀),r*)·r*·Δ)
    for any LorentzianContinuousSolution, with t₀ ≥ 0 and Δ ≥ 0.
    Lifts v_interval_decay to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_interval_decay (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t₀ Δ : ℝ) (ht₀ : 0 ≤ t₀) (hΔ : 0 ≤ Δ) :
    (S.r (t₀ + Δ) - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r t₀ - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * min (S.r t₀) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               Real.sqrt (1 - 2 * S.γ / S.K)) * Δ) := by
  rw [S.eq_explicit_of_nonneg (t₀ + Δ) (by linarith), S.eq_explicit_of_nonneg t₀ ht₀,
      S.eq_explicit_of_nonneg 0 le_rfl, lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_interval_decay S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t₀ Δ ht₀ hΔ

/-- **V persistence drop for any ODE solution**: if S.r t ≥ δ for all t ∈ [t₀, t₀+Δ],
    then V(t₀+Δ) ≤ V(t₀)·exp(-K·δ·r*·Δ).
    Lifts v_persistence_drop to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_persistence_drop (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (t₀ Δ : ℝ) (ht₀ : 0 ≤ t₀) (hΔ : 0 ≤ Δ)
    (h_persist : ∀ t, t₀ ≤ t → t ≤ t₀ + Δ → δ ≤ S.r t) :
    (S.r (t₀ + Δ) - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r t₀ - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * δ * Real.sqrt (1 - 2 * S.γ / S.K)) * Δ) := by
  rw [S.eq_explicit_of_nonneg (t₀ + Δ) (by linarith), S.eq_explicit_of_nonneg t₀ ht₀,
      S.eq_explicit_of_nonneg 0 le_rfl, lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_persistence_drop S.K S.γ (S.r 0) δ S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hδ_pos t₀ Δ ht₀ hΔ
    (fun t ht_lo ht_hi => (S.eq_explicit_of_nonneg t (le_trans ht₀ ht_lo)) ▸ h_persist t ht_lo ht_hi)

/-- **Uniform V decay for any ODE solution from persistence**: if S.r t ≥ δ for all t ≥ 0,
    then V(t) ≤ V(0)·exp(-K·δ·r*·t). Lifts v_uniform_exp_decay to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.v_uniform_exp_decay (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * δ * Real.sqrt (1 - 2 * S.γ / S.K)) * t) := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_uniform_exp_decay S.K S.γ (S.r 0) δ S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hδ_pos
    (fun s hs => (S.eq_explicit_of_nonneg s hs) ▸ h_persist s hs)
    t ht

/-- **Distance decay from global persistence**: if r(t) ≥ δ for all t ≥ 0,
    then |r(t)-r*| ≤ |r₀-r*|·exp(-K·δ·r*/2·t). Derives from v_uniform_exp_decay
    via order_parameter_exp_decay (sqrt of V bound + sqrt_sq_eq_abs). -/
theorem lorentzian_lyapunov_r_dist_from_persist (K γ r₀ δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ lorentzian_explicit K γ r₀ t)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r₀ - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * δ * Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  have h := order_parameter_exp_decay
      (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (lorentzian_explicit K γ r₀)
      (Real.sqrt (1 - 2 * γ / K))
      ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
      (K * δ * Real.sqrt (1 - 2 * γ / K))
      (sq_nonneg _)
      (lorentzian_lyapunov_v_uniform_exp_decay K γ r₀ δ hK hγ hKγ hr₀_pos hr₀_lt hδ_pos h_persist)
      (fun _ => le_refl _)
      t ht
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Distance decay from persistence for ODE solution**: if S.r t ≥ δ for all t ≥ 0,
    then |S.r t - r*| ≤ |S.r 0 - r*|·exp(-K·δ·r*/2·t).
    Lifts r_dist_from_persist to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.r_dist_from_persist (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * δ * Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_r_dist_from_persist S.K S.γ (S.r 0) δ S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hδ_pos
    (fun s hs => (S.eq_explicit_of_nonneg s hs) ▸ h_persist s hs)
    t ht

/-- **Convergence time from global persistence**: if r(t) ≥ δ for all t ≥ 0 and r₀ ≠ r*,
    then t > log(V₀/ε²)/(K·δ·r*) implies |r(t)-r*| < ε.
    Explicit T = log((r₀-r*)²/ε²)/(K·δ·r*). -/
theorem lorentzian_lyapunov_convergence_time_from_persist (K γ r₀ δ ε : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀_ne : r₀ ≠ Real.sqrt (1 - 2 * γ / K))
    (hδ_pos : 0 < δ) (hε : 0 < ε)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ lorentzian_explicit K γ r₀ t)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2 / ε ^ 2) /
             (K * δ * Real.sqrt (1 - 2 * γ / K)) < t) :
    |lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)| < ε :=
  explicit_convergence_time
    (fun s => (lorentzian_explicit K γ r₀ s - Real.sqrt (1 - 2 * γ / K)) ^ 2)
    (lorentzian_explicit K γ r₀)
    (Real.sqrt (1 - 2 * γ / K))
    ((r₀ - Real.sqrt (1 - 2 * γ / K)) ^ 2)
    (K * δ * Real.sqrt (1 - 2 * γ / K))
    ε
    (mul_pos (mul_pos hK hδ_pos) (Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hr₀_ne))
    hε
    (lorentzian_lyapunov_v_uniform_exp_decay K γ r₀ δ hK hγ hKγ hr₀_pos hr₀_lt hδ_pos h_persist)
    (fun _ => le_refl _)
    t ht htime

/-- **Convergence time from persistence for ODE solution**: if S.r t ≥ δ for all t ≥ 0
    and S.r 0 ≠ r*, then t > log(V₀/ε²)/(K·δ·r*) implies |S.r t - r*| < ε.
    Lifts convergence_time_from_persist to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.convergence_time_from_persist
    (S : LorentzianContinuousSolution)
    (δ ε : ℝ)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (hδ_pos : 0 < δ) (hε : 0 < ε)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 / ε ^ 2) /
             (S.K * δ * Real.sqrt (1 - 2 * S.γ / S.K)) < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_convergence_time_from_persist S.K S.γ (S.r 0) δ ε
    S.hK_pos S.hγ_pos S.hK_gt S.hr_init_pos S.hr_init_lt hr₀_ne hδ_pos hε
    (fun s hs => (S.eq_explicit_of_nonneg s hs) ▸ h_persist s hs)
    t ht htime

/-- **Two-trajectory synchronization from persistence**: if both r(t,r₀) and r(t,r₀') stay ≥ δ,
    then |r(t,r₀) - r(t,r₀')| ≤ (|r₀-r*| + |r₀'-r*|)·exp(-K·δ·r*/2·t).
    Triangle inequality through r* + two applications of r_dist_from_persist. -/
theorem lorentzian_lyapunov_two_traj_sync_from_persist (K γ r₀ r₀' δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hr₀'_pos : 0 < r₀') (hr₀'_lt : r₀' < 1)
    (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ lorentzian_explicit K γ r₀ t)
    (h_persist' : ∀ t, 0 ≤ t → δ ≤ lorentzian_explicit K γ r₀' t)
    (t : ℝ) (ht : 0 ≤ t) :
    |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
    (|r₀ - Real.sqrt (1 - 2 * γ / K)| + |r₀' - Real.sqrt (1 - 2 * γ / K)|) *
    Real.exp (-(K * δ * Real.sqrt (1 - 2 * γ / K)) / 2 * t) := by
  set rs := Real.sqrt (1 - 2 * γ / K)
  have htri : |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t| ≤
      |lorentzian_explicit K γ r₀ t - rs| + |lorentzian_explicit K γ r₀' t - rs| := by
    have := abs_sub_le (lorentzian_explicit K γ r₀ t) rs (lorentzian_explicit K γ r₀' t)
    linarith [abs_sub_comm (lorentzian_explicit K γ r₀' t) rs]
  have hd := lorentzian_lyapunov_r_dist_from_persist K γ r₀ δ hK hγ hKγ hr₀_pos hr₀_lt hδ_pos h_persist t ht
  have hd' := lorentzian_lyapunov_r_dist_from_persist K γ r₀' δ hK hγ hKγ hr₀'_pos hr₀'_lt hδ_pos h_persist' t ht
  calc |lorentzian_explicit K γ r₀ t - lorentzian_explicit K γ r₀' t|
      ≤ |lorentzian_explicit K γ r₀ t - rs| + |lorentzian_explicit K γ r₀' t - rs| := htri
    _ ≤ |r₀ - rs| * Real.exp (-(K * δ * rs) / 2 * t) +
        |r₀' - rs| * Real.exp (-(K * δ * rs) / 2 * t) := add_le_add hd hd'
    _ = (|r₀ - rs| + |r₀' - rs|) * Real.exp (-(K * δ * rs) / 2 * t) := by ring

/-- **Two-trajectory synchronization for ODE solutions from persistence**: if both S.r t ≥ δ
    and S'.r t ≥ δ for all t ≥ 0, and S.K = S'.K, S.γ = S'.γ, then
    |S.r t - S'.r t| ≤ (|S.r 0 - r*| + |S'.r 0 - r*|)·exp(-K·δ·r*/2·t).
    Lifts two_traj_sync_from_persist to LorentzianContinuousSolution. -/
theorem LorentzianContinuousSolution.two_traj_sync_from_persist
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (h_persist' : ∀ t, 0 ≤ t → δ ≤ S'.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    (|S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| +
     |S'.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)|) *
    Real.exp (-(S.K * δ * Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have htri : |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := by
    have := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  have hd := S.r_dist_from_persist δ hδ_pos h_persist t ht
  have hd' : |S'.r t - rs| ≤ |S'.r 0 - rs| * Real.exp (-(S.K * δ * rs) / 2 * t) := by
    have h := S'.r_dist_from_persist δ hδ_pos h_persist' t ht
    rwa [← hK_eq, ← hγ_eq] at h
  calc |S.r t - S'.r t|
      ≤ |S.r t - rs| + |S'.r t - rs| := htri
    _ ≤ |S.r 0 - rs| * Real.exp (-(S.K * δ * rs) / 2 * t) +
        |S'.r 0 - rs| * Real.exp (-(S.K * δ * rs) / 2 * t) := add_le_add hd hd'
    _ = (|S.r 0 - rs| + |S'.r 0 - rs|) * Real.exp (-(S.K * δ * rs) / 2 * t) := by ring

/-- **Strict distance decrease**: |r(t)-r*| < |r(s)-r*| for 0 ≤ s < t when r₀ ≠ r*.
    The trajectory strictly approaches equilibrium at every step. -/
theorem LorentzianContinuousSolution.dist_strict_decreasing (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| <
    |S.r s - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  rw [S.eq_explicit_of_nonneg t (hs.trans hst.le), S.eq_explicit_of_nonneg s hs]
  exact lorentzian_explicit_dist_strict_decreasing S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne hs hst

/-- **Strict Lyapunov anti-tone**: V(t) < V(s) for 0 ≤ s < t when r₀ ≠ r*.
    The squared distance to equilibrium decreases strictly along trajectories. -/
theorem LorentzianContinuousSolution.v_strict_anti (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 <
    (S.r s - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 := by
  rw [S.eq_explicit_of_nonneg t (hs.trans hst.le), S.eq_explicit_of_nonneg s hs]
  exact lorentzian_lyapunov_v_strict_anti S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne hs hst

/-- **V strictly less than initial value**: V(t) < V(0) = (r₀-r*)² for t > 0 when r₀ ≠ r*.
    Sharper than v_le_init: the bound is strict for positive time. -/
theorem LorentzianContinuousSolution.v_lt_init' (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 < t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 <
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht.le, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_lt_init S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne t ht

/-- **V tends to zero**: (r(t)-r*)² → 0 as t → ∞.
    Lyapunov form of convergence: V → 0 encodes r(t) → r*. -/
theorem LorentzianContinuousSolution.v_tendsto_zero (S : LorentzianContinuousSolution) :
    Filter.Tendsto (fun t => (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      Filter.atTop (nhds 0) := by
  have h := S.tendsto.sub_const (Real.sqrt (1 - 2 * S.γ / S.K))
  simp only [sub_self] at h
  have h2 := h.pow 2
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h2
  exact h2

/-- **Order preservation**: if S.r 0 < S'.r 0 with identical parameters, then S.r t < S'.r t.
    The explicit Lorentzian flow strictly preserves initial ordering for all t ≥ 0. -/
theorem LorentzianContinuousSolution.order_preserving
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (hr₀_lt : S.r 0 < S'.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t < S'.r t := by
  rw [S.eq_explicit_of_nonneg t ht, S'.eq_explicit_of_nonneg t ht, ← hK_eq, ← hγ_eq]
  exact lorentzian_explicit_order_preserving S.K S.γ (S.r 0) (S'.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt S'.hr_init_pos S'.hr_init_lt hr₀_lt t ht

/-- **Forward invariance of ε-ball**: if |S.r 0 - r*| < ε, then |S.r t - r*| < ε for all t ≥ 0.
    The open ball around r* is positively invariant under the Lorentzian flow. -/
theorem LorentzianContinuousSolution.r_ball_fwd_inv (S : LorentzianContinuousSolution)
    (ε : ℝ) (hε : |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| < ε)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_r_ball_fwd_inv S.K S.γ (S.r 0) ε S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hε t ht

/-- **Sublevel set forward invariance**: once V(t₀) ≤ c, then V(t) ≤ c for all t ≥ t₀ ≥ 0.
    Direct corollary of v_nonincreasing (V is AntitoneOn [0,∞)). -/
theorem LorentzianContinuousSolution.sublevel_fwd_inv (S : LorentzianContinuousSolution)
    (c : ℝ) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t)
    (hV : (S.r t₀ - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤ c) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤ c :=
  (S.v_nonincreasing (Set.mem_Ici.mpr ht₀) (Set.mem_Ici.mpr (ht₀.trans ht)) ht).trans hV

/-- **Below-r* two-sided trap**: for S.r 0 < r*, the distance |S.r t - r*| satisfies
    |S.r 0-r*|·exp(-K·t) ≤ |S.r t-r*| ≤ |S.r 0-r*|·exp(-K·S.r 0·r*/2·t).
    Lower bound from dist_lb; upper from r_dist_bound + min_eq_left (S.r 0 < r*). -/
theorem LorentzianContinuousSolution.trap_below (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ∧
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * S.r 0 * Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  constructor
  · exact S.dist_lb t ht
  · have h := S.r_dist_bound (ne_of_lt hr₀_lt_rstar) t ht
    simp only [min_eq_left (le_of_lt hr₀_lt_rstar)] at h
    exact h

/-- **Above-r* two-sided trap**: for r* < S.r 0, the distance |S.r t - r*| satisfies
    |S.r 0-r*|·exp(-K·t) ≤ |S.r t-r*| ≤ |S.r 0-r*|·exp(-K·(1-2γ/K)·t).
    Lower bound from dist_lb; upper bound from lorentzian_lyapunov_r_dist_above. -/
theorem LorentzianContinuousSolution.trap_above (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ∧
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * (1 - 2 * S.γ / S.K)) * t) := by
  constructor
  · exact S.dist_lb t ht
  · rw [S.eq_explicit_of_nonneg t ht]
    exact lorentzian_lyapunov_r_dist_above S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
      S.hr_init_pos S.hr_init_lt hr₀_gt_rstar t ht

/-- **Two-trajectory distance bound**: for S.r 0 ≠ r* and S'.r 0 ≠ r* (same K, γ),
    |S.r t - S'.r t| ≤ dist(S.r 0, r*)·exp(-μt) + dist(S'.r 0, r*)·exp(-μ't).
    Follows from triangle inequality and individual r_dist_bound bounds. -/
theorem LorentzianContinuousSolution.two_traj_dist
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (hr₀'_ne : S'.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) +
    |S'.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S'.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
                Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have htri : |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := by
    have := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  have hd := S.r_dist_bound hr₀_ne t ht
  have hd' : |S'.r t - rs| ≤ |S'.r 0 - rs| *
      Real.exp (-(S.K * min (S'.r 0) rs * rs) / 2 * t) := by
    have hne' : S'.r 0 ≠ Real.sqrt (1 - 2 * S'.γ / S'.K) := by
      rw [← hγ_eq, ← hK_eq]; exact hr₀'_ne
    have h := S'.r_dist_bound hne' t ht
    rwa [← hK_eq, ← hγ_eq] at h
  exact htri.trans (add_le_add hd hd')

/-- **V ratio two-sided bound**: for S.r 0 ≠ r*, the ratio V(t)/V(0) satisfies
    exp(-2K·t) ≤ V(t)/V(0) ≤ exp(-K·min(r₀,r*)·r*·t).
    Combines v_lb (lower) and v_exp_bound (upper) via div_iff. -/
theorem LorentzianContinuousSolution.v_ratio_bound (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(2 * S.K) * t) ≤
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 /
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ∧
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 /
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
              Real.sqrt (1 - 2 * S.γ / S.K)) * t) := by
  have hV0_pos : 0 < (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hr₀_ne)
  constructor
  · rw [le_div_iff₀ hV0_pos, mul_comm]
    exact S.v_lb t ht
  · rw [div_le_iff₀ hV0_pos]
    have h := S.v_exp_bound hr₀_ne t ht
    linarith [mul_comm (Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
        Real.sqrt (1 - 2 * S.γ / S.K)) * t)) ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)]

/-- **V = 0 iff r = r***: the Lyapunov function V = (r(t)-r*)² vanishes exactly at equilibrium.
    Combined with v_pos: V(t) = 0 cannot hold for t ≥ 0 when r₀ ≠ r*. -/
theorem lorentzian_lyapunov_v_eq_zero_iff (K γ r₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : 2 * γ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K)) ^ 2 = 0 ↔
    lorentzian_explicit K γ r₀ t = Real.sqrt (1 - 2 * γ / K) := by
  constructor
  · intro h; nlinarith [sq_nonneg (lorentzian_explicit K γ r₀ t - Real.sqrt (1 - 2 * γ / K))]
  · intro h; rw [h, sub_self, sq, zero_mul]

/-- **Convergence time (below r*)**: for S.r 0 < r*, once t > log(V₀/ε²)/(K·S.r 0·r*),
    the distance |S.r t - r*| < ε. Lifts convergence_time_below to any ODE solution. -/
theorem LorentzianContinuousSolution.convergence_time_below (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 / ε ^ 2) /
             (S.K * S.r 0 * Real.sqrt (1 - 2 * S.γ / S.K)) < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_convergence_time_below S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_lt_rstar ε hε t ht htime

/-- **Convergence time (above r*)**: for r* < S.r 0, once t > log(V₀/ε²)/(2K·(1-2γ/K)),
    the distance |S.r t - r*| < ε. Lifts convergence_time_above to any ODE solution. -/
theorem LorentzianContinuousSolution.convergence_time_above (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 / ε ^ 2) /
             (2 * S.K * (1 - 2 * S.γ / S.K)) < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_convergence_time_above S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar ε hε t ht htime

/-- **Unified convergence time**: for S.r 0 ≠ r*, once t > log(V₀/ε²)/(K·min(r₀,r*)·r*),
    the distance |S.r t - r*| < ε. Covers both below and above r* cases. -/
theorem LorentzianContinuousSolution.convergence_time (S : LorentzianContinuousSolution)
    (hr₀_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t)
    (htime : Real.log ((S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 / ε ^ 2) /
             (S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
              Real.sqrt (1 - 2 * S.γ / S.K)) < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_convergence_time S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_ne ε hε t ht htime

/-- **Two-solution distance tends to zero**: |S.r t - S'.r t| → 0 as t → ∞
    for any two ODE solutions with identical parameters K, γ.
    Follows from individual dist_tendsto_zero via triangle inequality + squeeze. -/
theorem LorentzianContinuousSolution.dist_tendsto
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ) :
    Filter.Tendsto (fun t => |S.r t - S'.r t|) Filter.atTop (nhds 0) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hS := S.dist_tendsto_zero
  have hS' : Filter.Tendsto (fun t => |S'.r t - rs|) Filter.atTop (nhds 0) := by
    have h := S'.dist_tendsto_zero
    rwa [← hK_eq, ← hγ_eq] at h
  have hsum : Filter.Tendsto (fun t => |S.r t - rs| + |S'.r t - rs|)
      Filter.atTop (nhds 0) := by
    have := hS.add hS'; simpa using this
  have htri : ∀ t, |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := fun t => by
    have := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · filter_upwards with t; exact abs_nonneg _
  · filter_upwards with t; exact htri t

/-- **r² sublevel set forward-invariant (below r*)**: r₀² < r*² → r(t)² < r*² for all t ≥ 0.
    The Lorentzian flow preserves the region {r² < r*²}. -/
theorem LorentzianContinuousSolution.sq_lt_rstar (S : LorentzianContinuousSolution)
    (hr₀_sq_lt : S.r 0 ^ 2 < 1 - 2 * S.γ / S.K)
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t ^ 2 < 1 - 2 * S.γ / S.K := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_sq_lt_rstar S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_sq_lt t ht

/-- **r² superlevel set forward-invariant (above r*)**: r*² < r₀² → r*² < r(t)² for all t ≥ 0.
    The Lorentzian flow preserves the region {r² > r*²}. -/
theorem LorentzianContinuousSolution.sq_gt_rstar (S : LorentzianContinuousSolution)
    (hr₀_sq_gt : 1 - 2 * S.γ / S.K < S.r 0 ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1 - 2 * S.γ / S.K) ^ 2 < S.r t ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_sq_gt_rstar S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_sq_gt t ht

/-- **r² non-decreasing from r₀² (below r*)**: r₀² < r*² → r₀² ≤ r(t)² for all t ≥ 0.
    The square of the order parameter grows monotonically when below the equilibrium. -/
theorem LorentzianContinuousSolution.sq_ge_init (S : LorentzianContinuousSolution)
    (hr₀_sq_lt : S.r 0 ^ 2 < 1 - 2 * S.γ / S.K)
    (t : ℝ) (ht : 0 ≤ t) :
    S.r 0 ^ 2 ≤ S.r t ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_sq_ge_init S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_sq_lt t ht

/-- **r² non-increasing from r₀² (above r*)**: r*² < r₀² → r(t)² ≤ r₀² for all t ≥ 0.
    The square of the order parameter decreases monotonically when above the equilibrium. -/
theorem LorentzianContinuousSolution.sq_le_init (S : LorentzianContinuousSolution)
    (hr₀_sq_gt : 1 - 2 * S.γ / S.K < S.r 0 ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    S.r t ^ 2 ≤ S.r 0 ^ 2 := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_sq_le_init S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_sq_gt t ht

/-- **Sharper V bound (below r*)**: for S.r 0 < r*, V(t) ≤ V(0)·exp(-K·S.r 0·r*·t).
    Tighter than v_exp_bound which uses min(r₀, r*) = r₀; here the coefficient is K·r₀·r* directly. -/
theorem LorentzianContinuousSolution.v_exp_bound_below (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * S.r 0 * Real.sqrt (1 - 2 * S.γ / S.K)) * t) := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_exp_bound_below S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_lt_rstar t ht

/-- **Sharper V bound (above r*)**: for r* < S.r 0, V(t) ≤ V(0)·exp(-2K·(1-2γ/K)·t).
    Rate 2K·r*² = 2(K-2γ) is the linearized rate at r*. Tighter than v_exp_bound for r₀ > r*. -/
theorem LorentzianContinuousSolution.v_exp_bound_above (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(2 * S.K * (1 - 2 * S.γ / S.K)) * t) := by
  rw [S.eq_explicit_of_nonneg t ht, S.eq_explicit_of_nonneg 0 le_rfl,
      lorentzian_explicit_init S.K S.γ (S.r 0) S.hr_init_pos]
  exact lorentzian_lyapunov_v_exp_bound_above S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar t ht

/-- **Weak V antitone**: for 0 ≤ s ≤ t, V(t) ≤ V(s). Weak version of v_strict_anti (no hr₀_ne).
    Holds trivially at r₀ = r* (V ≡ 0) and by v_strict_anti for r₀ ≠ r*. -/
theorem LorentzianContinuousSolution.v_antitone (S : LorentzianContinuousSolution)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r s - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 :=
  S.v_nonincreasing (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hst)) hst

/-- **Below-r* distance bound**: for r₀ < r*, |r(t)-r*| ≤ |r₀-r*|·exp(-K·r₀·r*/2·t).
    Sharper than r_dist_bound when r₀ < r*: rate K·r₀·r*/2 instead of K·min(r₀,r*)·r*/2. -/
theorem LorentzianContinuousSolution.dist_bound_below (S : LorentzianContinuousSolution)
    (hr₀_lt_rstar : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * S.r 0 * Real.sqrt (1 - 2 * S.γ / S.K)) / 2 * t) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_r_dist_below' S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_lt_rstar t ht

/-- **Above-r* distance bound**: for r* < r₀, |r(t)-r*| ≤ |r₀-r*|·exp(-K·(1-2γ/K)·t).
    Rate K·r*² = K-2γ is the linearized decay rate. Sharper than r_dist_bound for r₀ > r*. -/
theorem LorentzianContinuousSolution.dist_bound_above (S : LorentzianContinuousSolution)
    (hr₀_gt_rstar : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * (1 - 2 * S.γ / S.K)) * t) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_lyapunov_r_dist_above S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt hr₀_gt_rstar t ht

/-- **Bernoulli amplitude square bound**: (r(t)²-r*²)² ≤ A²·exp(-2μt) where A = 1/r₀²-B.
    The square difference decays like the Bernoulli linearization amplitude squared. -/
theorem LorentzianContinuousSolution.sq_diff_bound (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (1 / S.r 0 ^ 2 - S.K / (S.K - 2 * S.γ)) ^ 2 *
    Real.exp (-2 * (S.K - 2 * S.γ) * t) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_sq_diff_bound S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt t ht

/-- **Rate in terms of initial displacement**: |r(t)-r*| ≤ |r*²-r₀²|·exp(-μt)/(r₀²·r*³).
    Expresses the rate bound via the physical displacement r*²-r₀² rather than the amplitude A. -/
theorem LorentzianContinuousSolution.rate_initial (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |Real.sqrt (1 - 2 * S.γ / S.K) ^ 2 - S.r 0 ^ 2| *
    Real.exp (-(S.K - 2 * S.γ) * t) /
    (S.r 0 ^ 2 * Real.sqrt (1 - 2 * S.γ / S.K) ^ 3) := by
  rw [S.eq_explicit_of_nonneg t ht]
  exact lorentzian_explicit_rate_initial S.K S.γ (S.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt t ht

/-- **Bernoulli two-solution distance bound**: |S.r t - S'.r t| ≤ (|A|+|A'|)·exp(-μt)/r*
    where A = 1/S.r 0²-K/(K-2γ), A' = 1/S'.r 0²-K/(K-2γ), μ = K-2γ.
    Tighter than two_traj_dist near r*; uses the Bernoulli formula directly at optimal rate μ. -/
theorem LorentzianContinuousSolution.dist_bound_explicit
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    (|1 / S.r 0 ^ 2 - S.K / (S.K - 2 * S.γ)| +
     |1 / S'.r 0 ^ 2 - S.K / (S.K - 2 * S.γ)|) *
    Real.exp (-(S.K - 2 * S.γ) * t) /
    Real.sqrt (1 - 2 * S.γ / S.K) := by
  rw [S.eq_explicit_of_nonneg t ht, S'.eq_explicit_of_nonneg t ht, ← hK_eq, ← hγ_eq]
  exact lorentzian_explicit_dist_bound S.K S.γ (S.r 0) (S'.r 0) S.hK_pos S.hγ_pos S.hK_gt
    S.hr_init_pos S.hr_init_lt S'.hr_init_pos S'.hr_init_lt t ht

/-- **Lyapunov HasDerivAt (abstract ODE)**: V=(r-r*)² has derivative 2(r-r*)·ṙ
    for any ODE solution, proved directly from S.hr_ode (not via eq_explicit). -/
theorem LorentzianContinuousSolution.v_hasDerivAt (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (S.r s - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      (2 * (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) *
        lorentzianODE S.K S.γ (S.r t)) t := by
  have h := (S.hr_ode t ht |>.sub_const (Real.sqrt (1 - 2 * S.γ / S.K))).pow 2
  convert h using 1
  push_cast; ring

/-- **Lyapunov derivative formula**: d/dt (r-r*)² = -K·r·(r+r*)·(r-r*)²
    for any ODE solution. The derivative is -K·r·(r+r*)·V, showing V decays self-similarly. -/
theorem LorentzianContinuousSolution.v_deriv_formula (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (S.r s - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      (-(S.K * S.r t * (S.r t + Real.sqrt (1 - 2 * S.γ / S.K)) *
         (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)) t := by
  have h := S.v_hasDerivAt t ht
  have hode : lorentzianODE S.K S.γ (S.r t) =
      S.K / 2 * S.r t *
      (Real.sqrt (1 - 2 * S.γ / S.K) ^ 2 - (S.r t) ^ 2) := by
    rw [lorentzian_ode_factored S.K S.γ (S.r t) (ne_of_gt S.hK_pos)]
    congr 1; congr 1
    exact (Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))).symm
  rw [hode] at h
  convert h using 1; ring

/-- **V=0 characterizes equilibrium**: (r(t)-r*)²=0 iff r(t)=r* for any ODE solution. -/
theorem LorentzianContinuousSolution.v_eq_zero_iff (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 = 0 ↔
    S.r t = Real.sqrt (1 - 2 * S.γ / S.K) := by
  constructor
  · intro h; nlinarith [sq_nonneg (S.r t - Real.sqrt (1 - 2 * S.γ / S.K))]
  · intro h; rw [h, sub_self, sq, zero_mul]

/-- **Gronwall V-bound from abstract ODE**: V(a+Δ) ≤ V(a)·exp(-K·δ·(δ+r*)·Δ)
    when S.r ≥ δ on [a, a+Δ]. Proved directly from v_deriv_formula + comparison_decay_interval,
    no eq_explicit needed. Rate K·δ·(δ+r*) is tighter than v_persistence_drop's K·δ·r*. -/
theorem LorentzianContinuousSolution.v_gronwall_from_ode
    (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : 0 ≤ Δ)
    (h_persist : ∀ u, a ≤ u → u ≤ a + Δ → δ ≤ S.r u) :
    (S.r (a + Δ) - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r a - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * δ * (δ + Real.sqrt (1 - 2 * S.γ / S.K))) * Δ) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K) with hrs_def
  set μ := S.K * δ * (δ + rs) with hμ_def
  have hrs_pos : 0 < rs := Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  set V : ℝ → ℝ := fun u => (S.r u - rs) ^ 2
  have hV_cont : ContinuousOn V (Set.Icc a (a + Δ)) := by
    apply ContinuousOn.pow
    apply ContinuousOn.sub _ continuousOn_const
    exact S.hr_cont.mono (fun u hu => ha.trans hu.1)
  have hV_hasderiv : ∀ u, a < u → u < a + Δ → HasDerivAt V
      (-(S.K * S.r u * (S.r u + rs) * V u)) u :=
    fun u hu _ => S.v_deriv_formula u (ha.trans hu.le)
  have hV_bound : ∀ u, a < u → u < a + Δ → -(S.K * S.r u * (S.r u + rs) * V u) ≤ -μ * V u := by
    intro u hau _
    have hr_ge := h_persist u hau.le (le_of_lt ‹u < a + Δ›)
    have hr_pos := (S.r_pos u (ha.trans hau.le)).le
    have hVu_nn : 0 ≤ V u := sq_nonneg _
    simp only [V, μ]
    nlinarith [sq_nonneg (S.r u - rs), mul_nonneg S.hK_pos.le hVu_nn,
              mul_nonneg (mul_nonneg S.hK_pos.le (by nlinarith : 0 ≤ S.r u * (S.r u + rs) - δ * (δ + rs)))
                hVu_nn]
  exact comparison_decay_interval V (fun u => -(S.K * S.r u * (S.r u + rs) * V u))
    μ a Δ hΔ hV_cont hV_hasderiv hV_bound

/-- **Uniform V decay from abstract ODE**: V(t) ≤ V(0)·exp(-K·δ·(δ+r*)·t)
    when S.r ≥ δ for all t ≥ 0. Corollary of v_gronwall_from_ode with a=0, Δ=t. -/
theorem LorentzianContinuousSolution.v_uniform_from_ode
    (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 ≤
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 *
    Real.exp (-(S.K * δ * (δ + Real.sqrt (1 - 2 * S.γ / S.K))) * t) := by
  have h := S.v_gronwall_from_ode δ hδ_pos 0 t le_rfl ht
    (fun u hu1 hu2 => h_persist u hu1)
  simpa using h

/-- **Dist bound from abstract ODE Gronwall**: |S.r t - r*| ≤ |S.r 0 - r*|·exp(-K·δ·(δ+r*)/2·t)
    when S.r ≥ δ for all t ≥ 0. Upgrades the rate in r_dist_from_persist from K·δ·r*/2 to K·δ·(δ+r*)/2. -/
theorem LorentzianContinuousSolution.dist_from_gronwall
    (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * δ * (δ + Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  set μ := S.K * δ * (δ + rs)
  have hV := S.v_uniform_from_ode δ hδ_pos h_persist t ht
  have hbound : |S.r t - rs| ^ 2 ≤ |S.r 0 - rs| ^ 2 * Real.exp (-μ * t) := by
    rwa [sq_abs, sq_abs]
  have key : (|S.r 0 - rs| * Real.exp (-(μ / 2) * t)) ^ 2 =
      |S.r 0 - rs| ^ 2 * Real.exp (-μ * t) := by
    rw [mul_pow]; congr 1; rw [sq, ← Real.exp_add]; congr 1; ring
  have hnn : 0 ≤ |S.r 0 - rs| * Real.exp (-(μ / 2) * t) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq hnn]
  apply Real.sqrt_le_sqrt
  rw [key]; exact hbound

/-- **Two-trajectory sync from abstract ODE Gronwall**: |S.r t - S'.r t| ≤
    (|S.r 0 - r*| + |S'.r 0 - r*|)·exp(-K·δ·(δ+r*)/2·t)
    when both solutions satisfy r≥δ globally. Triangle inequality + dist_from_gronwall.
    Rate K·δ·(δ+r*)/2 is tighter than two_traj_sync_from_persist's K·δ·r*/2. -/
theorem LorentzianContinuousSolution.two_traj_from_gronwall
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t)
    (h_persist' : ∀ t, 0 ≤ t → δ ≤ S'.r t)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    (|S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| +
     |S'.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)|) *
    Real.exp (-(S.K * δ * (δ + Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hS := S.dist_from_gronwall δ hδ_pos h_persist t ht
  have hS' : |S'.r t - rs| ≤
      |S'.r 0 - rs| * Real.exp (-(S.K * δ * (δ + rs) / 2) * t) := by
    have h := S'.dist_from_gronwall δ hδ_pos h_persist' t ht
    rwa [← hK_eq, ← hγ_eq] at h
  have htri : |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := by
    have := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  calc |S.r t - S'.r t|
      ≤ |S.r t - rs| + |S'.r t - rs| := htri
    _ ≤ |S.r 0 - rs| * Real.exp (-(S.K * δ * (δ + rs) / 2) * t) +
        |S'.r 0 - rs| * Real.exp (-(S.K * δ * (δ + rs) / 2) * t) :=
        add_le_add hS hS'
    _ = (|S.r 0 - rs| + |S'.r 0 - rs|) *
        Real.exp (-(S.K * δ * (δ + rs) / 2) * t) := by ring

/-- **V deriv nonpos from abstract ODE** (no eq_explicit): V' = -(K·r·(r+r*)·V) ≤ 0 at any t ≥ 0.
    Direct consequence of v_deriv_formula + r > 0 + r+r* > 0 + V ≥ 0.
    Used to establish V monotonicity without going through antitoneOn machinery. -/
theorem LorentzianContinuousSolution.v_deriv_nonpos
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    -(S.K * S.r t * (S.r t + Real.sqrt (1 - 2 * S.γ / S.K)) *
      (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2) ≤ 0 := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hr_pos := S.r_pos t ht
  have h_sum : 0 < S.r t + rs := by linarith
  have h1 : 0 ≤ S.K * S.r t * (S.r t + rs) * (S.r t - rs) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg S.hK_pos.le hr_pos.le) h_sum.le) (sq_nonneg _)
  linarith

/-- **V non-increasing from abstract ODE** (no eq_explicit): V = (S.r t - r*)² is AntitoneOn [0,∞).
    Uses antitoneOn_of_hasDerivWithinAt_nonpos with HasDerivWithinAt from v_deriv_formula
    and v_deriv_nonpos for the ≤ 0 bound. Alternative proof of v_nonincreasing. -/
theorem LorentzianContinuousSolution.v_nonincreasing_from_ode
    (S : LorentzianContinuousSolution) :
    AntitoneOn (fun t => (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      (Set.Ici (0 : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    ((S.hr_cont.sub continuousOn_const).pow 2)
  · intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    exact (S.v_deriv_formula t ht.le).hasDerivWithinAt
  · intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    exact S.v_deriv_nonpos t ht.le

/-- **Dist le init from abstract ODE** (no eq_explicit): |S.r t - r*| ≤ |S.r 0 - r*| for all t ≥ 0.
    Corollary of v_nonincreasing_from_ode via Real.sqrt_le_sqrt. Alternative proof of dist_le_init. -/
theorem LorentzianContinuousSolution.dist_le_init_from_ode
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  have hV := S.v_nonincreasing_from_ode (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hV

/-- **V deriv strictly negative at non-equilibrium** (no eq_explicit): when S.r t ≠ r*,
    V'(t) = -(K·r·(r+r*)·V) < 0 strictly — V = (r-r*)² > 0 so the product is positive.
    Enables strict monotonicity of V off the equilibrium. -/
theorem LorentzianContinuousSolution.v_deriv_neg_at_nonequil
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) (hr_ne : S.r t ≠ Real.sqrt (1 - 2 * S.γ / S.K)) :
    -(S.K * S.r t * (S.r t + Real.sqrt (1 - 2 * S.γ / S.K)) *
      (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2) < 0 := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hr_pos := S.r_pos t ht
  have h_sum : 0 < S.r t + rs := by linarith
  have hV_pos : 0 < (S.r t - rs) ^ 2 := by
    apply sq_pos_of_ne_zero; exact sub_ne_zero.mpr hr_ne
  nlinarith [mul_pos (mul_pos (mul_pos S.hK_pos hr_pos) h_sum) hV_pos]

/-- **Dist bound below r***: when S.r 0 < r*, monotonicity gives S.r t ≥ S.r 0 globally,
    so δ = S.r 0 works in dist_from_gronwall. Rate K·r₀·(r₀+r*)/2 strictly exceeds the
    explicit-formula rate K·r₀·r*/2 from dist_bound_below. NO eq_explicit used. -/
theorem LorentzianContinuousSolution.dist_from_gronwall_below
    (S : LorentzianContinuousSolution)
    (h_below : S.r 0 < Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * S.r 0 * (S.r 0 + Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) :=
  S.dist_from_gronwall (S.r 0) S.hr_init_pos
    (fun u hu => S.ge_init_of_lt_rstar h_below u hu) t ht

/-- **Dist bound above r***: when r* < S.r 0, gt_rstar_of_init gives S.r t > r* globally,
    so δ = r* works in dist_from_gronwall. Rate K·r*·(r*+r*)/2 = K·r*² = K-2γ matches
    the explicit-formula rate from dist_bound_above. NO eq_explicit used. -/
theorem LorentzianContinuousSolution.dist_from_gronwall_above
    (S : LorentzianContinuousSolution)
    (h_above : Real.sqrt (1 - 2 * S.γ / S.K) < S.r 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * Real.sqrt (1 - 2 * S.γ / S.K) *
      (Real.sqrt (1 - 2 * S.γ / S.K) + Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) :=
  S.dist_from_gronwall (Real.sqrt (1 - 2 * S.γ / S.K))
    (Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))
    (fun u hu => le_of_lt (S.gt_rstar_of_init h_above u hu)) t ht

/-- **V strictly antitone from abstract ODE** (uses ne_rstar): when S.r 0 ≠ r*,
    V = (S.r t - r*)² is StrictAntiOn [0, ∞). Proof via strictAntiOn_of_hasDerivWithinAt_neg:
    HasDerivWithinAt from v_deriv_formula; strict negativity from v_deriv_neg_at_nonequil + ne_rstar.
    A StrictAntiOn reformulation of v_strict_anti via the derivative path. -/
theorem LorentzianContinuousSolution.v_strict_anti_from_ode
    (S : LorentzianContinuousSolution)
    (h0_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K)) :
    StrictAntiOn (fun t => (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      (Set.Ici (0 : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici _)
    ((S.hr_cont.sub continuousOn_const).pow 2)
  · intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    exact (S.v_deriv_formula t ht.le).hasDerivWithinAt
  · intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    exact S.v_deriv_neg_at_nonequil t ht.le (S.ne_rstar h0_ne t ht.le)

/-- **Strict distance decrease from abstract ODE**: when S.r 0 ≠ r* and t > 0,
    |S.r t - r*| < |S.r 0 - r*| strictly. Corollary of v_strict_anti_from_ode via
    sqrt strict monotonicity: V(t) < V(0) implies √V(t) < √V(0). -/
theorem LorentzianContinuousSolution.dist_strict_lt_init_from_ode
    (S : LorentzianContinuousSolution)
    (h0_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 < t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| <
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  have hV := S.v_strict_anti_from_ode h0_ne
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) hV

/-- **Abs dist StrictAntiOn from abstract ODE**: |S.r t - r*| is StrictAntiOn [0, ∞) when S.r 0 ≠ r*.
    For any 0 ≤ s < t, |S.r t - r*| < |S.r s - r*| strictly.
    Corollary of v_strict_anti_from_ode via sqrt strict monotonicity. -/
theorem LorentzianContinuousSolution.abs_dist_strict_anti_from_ode
    (S : LorentzianContinuousSolution)
    (h0_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K)) :
    StrictAntiOn (fun t => |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)|)
      (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  simp only []
  have hV := S.v_strict_anti_from_ode h0_ne hs ht hst
  simp only [] at hV
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) hV

/-- **V lower bound from abstract ODE** (NO eq_explicit): V(t) ≥ V(0)·exp(-2K·t) for all t ≥ 0.
    Uses comparison_growth with slope bound V' = -K·r·(r+r*)·V ≥ -2K·V,
    since r < 1 and r* < 1 give r·(r+r*) < 2. Alternative proof of v_lb without eq_explicit. -/
theorem LorentzianContinuousSolution.v_lb_from_ode
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    (S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 * Real.exp (-(2 * S.K) * t) ≤
    (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2 := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  set V : ℝ → ℝ := fun u => (S.r u - rs) ^ 2
  have hrs_pos : 0 < rs :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hrs_lt_one : rs < 1 :=
    lorentzian_rstar_lt_one S.K S.γ S.hK_pos S.hγ_pos S.hK_gt
  have hV_cont : ContinuousOn V (Set.Ici 0) :=
    (S.hr_cont.sub continuousOn_const).pow 2
  have hV_hasderiv : ∀ u, 0 < u → HasDerivAt V (-(S.K * S.r u * (S.r u + rs) * V u)) u :=
    fun u hu => S.v_deriv_formula u hu.le
  have hV_bound : ∀ u, 0 < u → -(2 * S.K) * V u ≤ -(S.K * S.r u * (S.r u + rs) * V u) := by
    intro u hu
    have hr_pos := S.r_pos u hu.le
    have hr_lt_one := S.r_lt_one u hu.le
    have hVu : 0 ≤ V u := sq_nonneg _
    have h_coeff : S.r u * (S.r u + rs) ≤ 2 := by nlinarith
    have h1 : S.K * S.r u * (S.r u + rs) * V u ≤ 2 * S.K * V u := by
      calc S.K * S.r u * (S.r u + rs) * V u
          = S.K * (S.r u * (S.r u + rs)) * V u := by ring
        _ ≤ S.K * 2 * V u :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_coeff S.hK_pos.le) hVu
        _ = 2 * S.K * V u := by ring
    linarith
  have hresult := comparison_growth V (fun u => -(S.K * S.r u * (S.r u + rs) * V u))
    (-(2 * S.K)) hV_cont hV_hasderiv hV_bound t ht
  simp only [neg_mul] at hresult ⊢
  linarith

/-- **V deriv strictly negative from abstract ODE** (uses ne_rstar): when S.r 0 ≠ r*,
    V'(t) < 0 for ALL t ≥ 0 — since ne_rstar gives S.r t ≠ r* for all t, enabling
    v_deriv_neg_at_nonequil globally. Named all-t version of v_deriv_neg_at_nonequil. -/
theorem LorentzianContinuousSolution.v_deriv_neg_from_ode
    (S : LorentzianContinuousSolution)
    (h0_ne : S.r 0 ≠ Real.sqrt (1 - 2 * S.γ / S.K))
    (t : ℝ) (ht : 0 ≤ t) :
    -(S.K * S.r t * (S.r t + Real.sqrt (1 - 2 * S.γ / S.K)) *
      (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2) < 0 :=
  S.v_deriv_neg_at_nonequil t ht (S.ne_rstar h0_ne t ht)

/-- **Dist lower bound from abstract ODE** (NO eq_explicit): |S.r t - r*| ≥ |S.r 0 - r*|·exp(-K·t).
    Uses v_lb_from_ode + sqrt algebra (same pattern as lorentzian_lyapunov_r_dist_lb).
    Together with dist_le_init_from_ode, gives two-sided trap: the distance cannot
    decay faster than exp(-Kt) and cannot exceed the initial distance. -/
theorem LorentzianContinuousSolution.dist_lb_from_ode
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hvlb := S.v_lb_from_ode t ht
  have hsqrt_exp : Real.sqrt (Real.exp (-(2 * S.K) * t)) = Real.exp (-S.K * t) := by
    have h1 : Real.exp (-(2 * S.K) * t) = Real.exp (-S.K * t) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, Real.sqrt_sq (Real.exp_pos _).le]
  calc |S.r 0 - rs| * Real.exp (-S.K * t)
      = Real.sqrt ((S.r 0 - rs) ^ 2) * Real.sqrt (Real.exp (-(2 * S.K) * t)) := by
          rw [Real.sqrt_sq_eq_abs, hsqrt_exp]
    _ = Real.sqrt ((S.r 0 - rs) ^ 2 * Real.exp (-(2 * S.K) * t)) :=
          (Real.sqrt_mul (sq_nonneg _) _).symm
    _ ≤ Real.sqrt ((S.r t - rs) ^ 2) := Real.sqrt_le_sqrt hvlb
    _ = |S.r t - rs| := Real.sqrt_sq_eq_abs _

/-- **Two-sided distance trap from abstract ODE** (NO eq_explicit): the distance satisfies
    |S.r 0-r*|·exp(-K·t) ≤ |S.r t-r*| ≤ |S.r 0-r*|.
    Combines dist_lb_from_ode (lower) and dist_le_init_from_ode (upper). The lower rate K is
    universal. Analogous to dist_trap but proved without eq_explicit. -/
theorem LorentzianContinuousSolution.dist_trap_from_ode
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| * Real.exp (-S.K * t) ≤
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ∧
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| :=
  ⟨S.dist_lb_from_ode t ht, S.dist_le_init_from_ode t ht⟩

/-- **V tends to 0 under persistence** (NO eq_explicit): when S.r ≥ δ globally,
    V(t) = (S.r t - r*)² → 0 as t → ∞. Proved via v_uniform_from_ode + squeeze_zero' + exp→0.
    First convergence result in the abstract ODE chain. -/
theorem LorentzianContinuousSolution.v_tendsto_from_persist_ode
    (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t) :
    Filter.Tendsto (fun t => (S.r t - Real.sqrt (1 - 2 * S.γ / S.K)) ^ 2)
      Filter.atTop (nhds 0) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs := Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  set mu_rate := S.K * δ * (δ + rs)
  have hmu_pos : 0 < mu_rate := mul_pos (mul_pos S.hK_pos hδ_pos) (by linarith)
  have hVbound : ∀ t, 0 ≤ t → (S.r t - rs) ^ 2 ≤ (S.r 0 - rs) ^ 2 * Real.exp (-mu_rate * t) :=
    fun t ht => S.v_uniform_from_ode δ hδ_pos h_persist t ht
  have hexp_tendsto : Tendsto (fun t : ℝ => (S.r 0 - rs) ^ 2 * Real.exp (-mu_rate * t))
      atTop (nhds 0) := by
    have hmul : Tendsto (fun t : ℝ => mu_rate * t) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b =>
        ⟨b / mu_rate, fun y hy => by have := (div_le_iff₀ hmu_pos).mp hy; linarith⟩
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
    have heq : (fun x : ℝ => Real.exp (-x)) ∘ (fun t => mu_rate * t) =
        fun t : ℝ => Real.exp (-mu_rate * t) := by
      ext t; simp [Function.comp, neg_mul]
    rw [heq] at hcomp
    simpa [mul_zero] using tendsto_const_nhds.mul hcomp
  apply squeeze_zero'
  · filter_upwards [] with _ using sq_nonneg _
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; exact hVbound t ht
  · exact hexp_tendsto

/-- **Convergence under persistence** (NO eq_explicit): when S.r ≥ δ globally,
    S.r t → r* as t → ∞. Proved via v_tendsto_from_persist_ode + sqrt + dist metric.
    First full convergence result from the abstract ODE chain. -/
theorem LorentzianContinuousSolution.tendsto_from_persist_ode
    (S : LorentzianContinuousSolution)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_persist : ∀ t, 0 ≤ t → δ ≤ S.r t) :
    Filter.Tendsto S.r Filter.atTop (nhds (Real.sqrt (1 - 2 * S.γ / S.K))) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hV_tendsto := S.v_tendsto_from_persist_ode δ hδ_pos h_persist
  have hdist_tendsto : Tendsto (fun t => |S.r t - rs|) atTop (nhds 0) := by
    simp_rw [← Real.sqrt_sq_eq_abs]
    simpa using hV_tendsto.sqrt
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hdist_tendsto) ε hε
  exact ⟨N, fun t ht => by
    have h := hN t ht
    simp only [Real.dist_eq, sub_zero, abs_abs] at h
    rwa [Real.dist_eq]⟩

/-- **Unified exponential distance bound from abstract ODE** (NO eq_explicit):
    For any r(0) ∈ (0,1), |S.r t - r*| ≤ |S.r 0 - r*|·exp(-μt) where
    μ = K·min(r₀,r*)·(min(r₀,r*)+r*)/2 ≥ 0.
    Proof: case split on r(0) vs r*:
    (1) r(0) < r*: min = r(0), apply dist_from_gronwall_below;
    (2) r(0) = r*: both sides 0, trivial;
    (3) r(0) > r*: min = r*, apply dist_from_gronwall_above.
    Unifies below/above rate bounds into a single abstract ODE inequality. NO eq_explicit. -/
theorem LorentzianContinuousSolution.dist_bound_from_ode_unified
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
      (min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) +
       Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  rcases lt_trichotomy (S.r 0) rs with h | h | h
  · rw [min_eq_left h.le]; exact S.dist_from_gronwall_below h t ht
  · rw [S.r_constant_at_rstar h t ht, h, min_self, sub_self, abs_zero, zero_mul]
  · rw [min_eq_right h.le]; exact S.dist_from_gronwall_above h t ht

/-- **Filter.Tendsto convergence from abstract ODE** (NO eq_explicit):
    For any LorentzianContinuousSolution, S.r t → r* = √(1-2γ/K) as t → ∞.
    Proof: case-split on r(0) vs r*; derive persistence from monotonicity; apply
    tendsto_from_persist_ode. No reference to the explicit Bernoulli formula.
    Closes the abstract ODE chain at the Filter.Tendsto level. -/
theorem LorentzianContinuousSolution.tendsto_from_ode
    (S : LorentzianContinuousSolution) :
    Filter.Tendsto S.r Filter.atTop (nhds (Real.sqrt (1 - 2 * S.γ / S.K))) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  rcases lt_trichotomy (S.r 0) rs with h | h | h
  · -- r(0) < r*: non-decreasing → r(t) ≥ r(0) > 0
    exact S.tendsto_from_persist_ode (S.r 0) S.hr_init_pos
      (fun t ht => S.r_nondecreasing_of_below h 0 t le_rfl ht)
  · -- r(0) = r*: r is constant at r*
    have hr_const := S.r_constant_at_rstar h
    rw [Metric.tendsto_atTop]
    intro ε hε
    exact ⟨0, fun t ht => by
      rw [hr_const t ht, Real.dist_eq, sub_self, abs_zero]; exact hε⟩
  · -- r(0) > r*: r stays above r* → persistence with δ = r*
    exact S.tendsto_from_persist_ode rs hrs_pos
      (fun t ht => S.r_ge_rstar_of_above h t ht)

/-- **ṙ = 0 iff at equilibrium** (NO eq_explicit): for t ≥ 0,
    lorentzianODE K γ (r t) = 0 ↔ r t = r* = √(1-2γ/K).
    Proof: lorentzian_fixed_point_unique + r(t) > 0 rules out the zero equilibrium. -/
theorem LorentzianContinuousSolution.deriv_eq_zero_iff_rstar
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    lorentzianODE S.K S.γ (S.r t) = 0 ↔ S.r t = Real.sqrt (1 - 2 * S.γ / S.K) := by
  constructor
  · intro h
    rcases lorentzian_fixed_point_unique S.K S.γ (S.r t) S.hK_pos S.hK_gt h with hr0 | hrstar
    · exact absurd hr0 (ne_of_gt (S.r_pos t ht))
    · have := (Real.sqrt_sq (le_of_lt (S.r_pos t ht))).symm
      rw [hrstar] at this; exact this
  · intro h; rw [h]
    exact lorentzian_rstar_is_fixed_point S.K S.γ S.hK_pos S.hγ_pos S.hK_gt

/-- **ṙ < 0 above r*** (NO eq_explicit): r(t) > r* implies ṙ(t) = lorentzianODE K γ (r t) < 0.
    The ODE pushes back toward r* from above. -/
theorem LorentzianContinuousSolution.deriv_neg_above
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t)
    (h : Real.sqrt (1 - 2 * S.γ / S.K) < S.r t) :
    lorentzianODE S.K S.γ (S.r t) < 0 := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs := Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hrs_sq : rs ^ 2 = 1 - 2 * S.γ / S.K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))
  apply lorentzian_ode_neg S.K S.γ (S.r t) S.hK_pos (S.r_pos t ht)
  nlinarith [S.r_pos t ht, hrs_pos, hrs_sq, sq_nonneg (S.r t - rs)]

/-- **ṙ > 0 below r*** (NO eq_explicit): 0 < r(t) < r* implies ṙ(t) = lorentzianODE K γ (r t) > 0.
    The ODE pushes toward r* from below. -/
theorem LorentzianContinuousSolution.deriv_pos_below
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t)
    (h : S.r t < Real.sqrt (1 - 2 * S.γ / S.K)) :
    lorentzianODE S.K S.γ (S.r t) > 0 := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have hrs_pos : 0 < rs := Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hrs_sq : rs ^ 2 = 1 - 2 * S.γ / S.K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))
  apply lorentzian_ode_pos S.K S.γ (S.r t) S.hK_pos S.hK_gt (S.r_pos t ht)
  nlinarith [S.r_pos t ht, hrs_pos, hrs_sq, sq_nonneg (S.r t - rs)]

/-- **w-transform convergence** (NO eq_explicit): w(t) = 1/r(t)² → B = K/(K-2γ).
    The Bernoulli-transformed variable w(t) = 1/r(t)² converges to the w-equilibrium B.
    Proof: r(t) → r*, r(t) > 0 for all t ≥ 0, so w(t) → 1/r*² = K/(K-2γ). -/
theorem LorentzianContinuousSolution.w_tendsto (S : LorentzianContinuousSolution) :
    Filter.Tendsto (fun t => 1 / S.r t ^ 2) Filter.atTop (nhds (S.K / (S.K - 2 * S.γ))) := by
  have hd : (0 : ℝ) < S.K - 2 * S.γ := by linarith [S.hK_gt]
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * S.γ / S.K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  have hrstar_sq : (1 : ℝ) / Real.sqrt (1 - 2 * S.γ / S.K) ^ 2 = S.K / (S.K - 2 * S.γ) := by
    rw [Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))]
    field_simp [ne_of_gt hd, ne_of_gt S.hK_pos]
  rw [← hrstar_sq]
  have hcont : ContinuousAt (fun r : ℝ => 1 / r ^ 2) (Real.sqrt (1 - 2 * S.γ / S.K)) := by
    apply ContinuousAt.div continuousAt_const (continuous_pow 2).continuousAt
    exact (pow_pos hrstar_pos 2).ne'
  exact hcont.tendsto.comp S.tendsto_from_ode

/-- **Squared order parameter convergence** (NO eq_explicit):
    r(t)² → r*² = 1 - 2γ/K as t → ∞.  Proof: square tendsto_from_ode via Tendsto.pow. -/
theorem LorentzianContinuousSolution.r_sq_tendsto (S : LorentzianContinuousSolution) :
    Filter.Tendsto (fun t => S.r t ^ 2) Filter.atTop (nhds (1 - 2 * S.γ / S.K)) := by
  have h := S.tendsto_from_ode.pow 2
  rwa [Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))] at h

/-- **ODE velocity → 0 as t → ∞** (NO eq_explicit):
    ṙ(t) = lorentzianODE K γ (r t) → 0 as t → ∞.
    Proof: r(t) → r* by tendsto_from_ode; lorentzianODE is continuous; lorentzianODE(r*) = 0. -/
theorem LorentzianContinuousSolution.deriv_tendsto_zero (S : LorentzianContinuousSolution) :
    Filter.Tendsto (fun t => lorentzianODE S.K S.γ (S.r t)) Filter.atTop (nhds 0) := by
  have hrstar : lorentzianODE S.K S.γ (Real.sqrt (1 - 2 * S.γ / S.K)) = 0 :=
    lorentzian_rstar_is_fixed_point S.K S.γ S.hK_pos S.hγ_pos S.hK_gt
  rw [← hrstar]
  have hcont : Continuous (lorentzianODE S.K S.γ) := by unfold lorentzianODE; fun_prop
  exact hcont.continuousAt.tendsto.comp S.tendsto_from_ode

/-- **Explicit rate from raw ODE hypotheses** (NO eq_explicit):
    Any continuous solution of the Lorentzian ODE with r(0) ∈ (0,1) satisfies
    |r(t) - r*| ≤ |r(0) - r*| · exp(-μt) where μ = K·min(r₀,r*)·(min(r₀,r*)+r*)/2.
    One-line proof: wrap into LorentzianContinuousSolution, apply dist_bound_from_ode_unified.
    The abstract ODE chain provides a quantitative convergence rate — no explicit formula. -/
theorem lorentzian_ode_convergence_rate_raw (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K)
    (r : ℝ → ℝ)
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_cont : ContinuousOn r (Set.Ici 0))
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    |r t - Real.sqrt (1 - 2 * γ / K)| ≤
    |r 0 - Real.sqrt (1 - 2 * γ / K)| *
    Real.exp (-(K * min (r 0) (Real.sqrt (1 - 2 * γ / K)) *
      (min (r 0) (Real.sqrt (1 - 2 * γ / K)) +
       Real.sqrt (1 - 2 * γ / K)) / 2) * t) :=
  ({ K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
     r := r, hr_ode := hr_ode, hr_cont := hr_cont,
     hr_init_pos := hr_init_pos, hr_init_lt := hr_init_lt
   } : LorentzianContinuousSolution).dist_bound_from_ode_unified t ht

/-- **ε-T convergence from abstract ODE** (NO eq_explicit):
    For any ε > 0, there exists T such that |S.r t - r*| < ε for all t ≥ T.
    This is the ε-T reformulation of tendsto_from_ode.
    Proof: one line — extract T from Metric.tendsto_atTop applied to tendsto_from_ode. -/
theorem LorentzianContinuousSolution.convergence_time_from_ode
    (S : LorentzianContinuousSolution) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t, T ≤ t →
      |S.r t - Real.sqrt (1 - 2 * S.γ / S.K)| < ε := by
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp S.tendsto_from_ode ε hε
  exact ⟨T, fun t ht => by simpa [Real.dist_eq] using hT t ht⟩

/-- **Global stability from raw ODE hypotheses** (NO eq_explicit, NO existence construction):
    Any continuous solution r of the Lorentzian ODE with r(0) ∈ (0,1) converges to r*.
    Takes the ODE directly (not via an explicit construction) and produces Filter.Tendsto.
    Proof: wrap into LorentzianContinuousSolution; apply tendsto_from_ode.
    Uses the abstract ODE chain exclusively — the Bernoulli formula is not referenced. -/
theorem lorentzian_ode_global_stability_raw (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K)
    (r : ℝ → ℝ)
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_cont : ContinuousOn r (Set.Ici 0))
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1) :
    Filter.Tendsto r Filter.atTop (nhds (Real.sqrt (1 - 2 * γ / K))) :=
  ({ K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
     r := r, hr_ode := hr_ode, hr_cont := hr_cont,
     hr_init_pos := hr_init_pos, hr_init_lt := hr_init_lt
   } : LorentzianContinuousSolution).tendsto_from_ode

/-- **Two-trajectory synchronization from abstract ODE** (NO eq_explicit):
    Any two solutions S, S' of the same Lorentzian ODE (same K, γ) with r(0) ∈ (0,1)
    synchronize: |S.r t - S'.r t| → 0 as t → ∞.
    Proof: both converge to the same r* by tendsto_from_ode; difference → 0; abs → 0. -/
theorem LorentzianContinuousSolution.two_traj_tendsto_from_ode
    (S S' : LorentzianContinuousSolution)
    (hKK : S.K = S'.K) (hγγ : S.γ = S'.γ) :
    Filter.Tendsto (fun t => |S.r t - S'.r t|) Filter.atTop (nhds 0) := by
  have hS := S.tendsto_from_ode
  have hS' : Filter.Tendsto S'.r Filter.atTop
      (nhds (Real.sqrt (1 - 2 * S.γ / S.K))) := by
    convert S'.tendsto_from_ode using 2; rw [hKK, hγγ]
  have hsub := hS.sub hS'
  simp only [sub_self] at hsub
  simpa [abs_zero] using hsub.abs

/-- **Two-trajectory synchronization (raw form)** (NO eq_explicit):
    Any two continuous solutions r, r' of the same Lorentzian ODE with r(0), r'(0) ∈ (0,1)
    satisfy |r t - r' t| → 0. -/
theorem lorentzian_ode_two_traj_sync_raw (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K)
    (r r' : ℝ → ℝ)
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_cont : ContinuousOn r (Set.Ici 0))
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1)
    (hr'_ode : ∀ t, 0 ≤ t → HasDerivAt r' (lorentzianODE K γ (r' t)) t)
    (hr'_cont : ContinuousOn r' (Set.Ici 0))
    (hr'_init_pos : 0 < r' 0) (hr'_init_lt : r' 0 < 1) :
    Filter.Tendsto (fun t => |r t - r' t|) Filter.atTop (nhds 0) :=
  (({ K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
      r := r, hr_ode := hr_ode, hr_cont := hr_cont,
      hr_init_pos := hr_init_pos, hr_init_lt := hr_init_lt
    } : LorentzianContinuousSolution)).two_traj_tendsto_from_ode
    ({ K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
       r := r', hr_ode := hr'_ode, hr_cont := hr'_cont,
       hr_init_pos := hr'_init_pos, hr_init_lt := hr'_init_lt
     } : LorentzianContinuousSolution) rfl rfl

/-- **Monotone corridor from abstract ODE** (NO eq_explicit):
    S.r t is always between S.r 0 and r* — the trajectory is sandwiched in the
    corridor [min(S.r 0, r*), max(S.r 0, r*)] for all t ≥ 0.
    Case split: (1) below: r_nondecreasing_of_below + lt_rstar_of_init;
                (2) equal: r_constant_at_rstar;
                (3) above: r_nonincreasing_of_above + gt_rstar_of_init. -/
theorem LorentzianContinuousSolution.r_in_corridor_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) ≤ S.r t ∧
    S.r t ≤ max (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  rcases lt_trichotomy (S.r 0) rs with h | h | h
  · constructor
    · rw [min_eq_left h.le]
      exact S.ge_init_of_lt_rstar h t ht
    · rw [max_eq_right h.le]
      exact (S.lt_rstar_of_init h t ht).le
  · constructor
    · rw [h, min_self]; exact (S.r_constant_at_rstar h t ht).symm.le
    · rw [h, max_self]; exact (S.r_constant_at_rstar h t ht).le
  · constructor
    · rw [min_eq_right h.le]
      exact (S.gt_rstar_of_init h t ht).le
    · rw [max_eq_left h.le]
      exact S.le_init_of_gt_rstar h t ht

/-- **Positivity from abstract ODE** (NO eq_explicit):
    S.r t > 0 for all t ≥ 0. Proof: r_in_corridor_from_ode gives r(t) ≥ min(r(0),r*) > 0. -/
theorem LorentzianContinuousSolution.r_pos_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) : 0 < S.r t := by
  have hcorr := (S.r_in_corridor_from_ode t ht).1
  have hrstar_pos : 0 < Real.sqrt (1 - 2 * S.γ / S.K) :=
    Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)
  exact lt_of_lt_of_le (lt_min S.hr_init_pos hrstar_pos) hcorr

/-- **Upper bound < 1 from abstract ODE** (NO eq_explicit):
    S.r t < 1 for all t ≥ 0. Proof: r_in_corridor_from_ode gives r(t) ≤ max(r(0),r*) < 1. -/
theorem LorentzianContinuousSolution.r_lt_one_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) : S.r t < 1 := by
  have hcorr := (S.r_in_corridor_from_ode t ht).2
  have hrstar_lt : Real.sqrt (1 - 2 * S.γ / S.K) < 1 :=
    lorentzian_rstar_lt_one S.K S.γ S.hK_pos S.hγ_pos S.hK_gt
  exact lt_of_le_of_lt hcorr (max_lt S.hr_init_lt hrstar_lt)

/-- **Open interval membership from abstract ODE** (NO eq_explicit):
    S.r t ∈ Set.Ioo 0 1 for all t ≥ 0. Bundles r_pos_from_ode and r_lt_one_from_ode. -/
theorem LorentzianContinuousSolution.r_mem_Ioo_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    S.r t ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨S.r_pos_from_ode t ht, S.r_lt_one_from_ode t ht⟩

/-- **Closed interval membership from abstract ODE** (NO eq_explicit):
    S.r t ∈ Set.Icc 0 1 for all t ≥ 0. Weaker form; often used as a hypothesis. -/
theorem LorentzianContinuousSolution.r_mem_Icc_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    S.r t ∈ Set.Icc (0 : ℝ) 1 :=
  Set.Ioo_subset_Icc_self (S.r_mem_Ioo_from_ode t ht)

/-- **Two-trajectory triangle bound from abstract ODE** (NO eq_explicit):
    |S.r t - S'.r t| ≤ |S.r 0 - r*| + |S'.r 0 - r*| for all t ≥ 0.
    Proof: triangle inequality + dist_le_init_from_ode for each trajectory.
    Weaker than two_traj_dist (no exponential) but requires no ne_rstar hypothesis. -/
theorem LorentzianContinuousSolution.two_traj_dist_le_sum_from_ode
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| +
    |S'.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have htri : |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := by
    have := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  have hd := S.dist_le_init_from_ode t ht
  have hd' : |S'.r t - rs| ≤ |S'.r 0 - rs| := by
    have hrs_eq : rs = Real.sqrt (1 - 2 * S'.γ / S'.K) := by
      simp only [rs]; rw [← hK_eq, ← hγ_eq]
    rw [hrs_eq]
    exact S'.dist_le_init_from_ode t ht
  linarith

/-- **Two-trajectory exponential sync from abstract ODE** (NO eq_explicit):
    |S.r t - S'.r t| ≤ |S.r 0-r*|·exp(-μ₁t) + |S'.r 0-r*|·exp(-μ₂t) for same (K,γ).
    Proof: triangle + dist_bound_from_ode_unified for each. Tighter than two_traj_dist
    (uses min·(min+r*)/2 rate) and needs no ne_rstar hypothesis. NO eq_explicit -/
theorem LorentzianContinuousSolution.two_traj_dist_from_ode
    (S S' : LorentzianContinuousSolution)
    (hK_eq : S.K = S'.K) (hγ_eq : S.γ = S'.γ)
    (t : ℝ) (ht : 0 ≤ t) :
    |S.r t - S'.r t| ≤
    |S.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
               (min (S.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) +
                Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) +
    |S'.r 0 - Real.sqrt (1 - 2 * S.γ / S.K)| *
    Real.exp (-(S.K * min (S'.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) *
                (min (S'.r 0) (Real.sqrt (1 - 2 * S.γ / S.K)) +
                 Real.sqrt (1 - 2 * S.γ / S.K)) / 2) * t) := by
  set rs := Real.sqrt (1 - 2 * S.γ / S.K)
  have htri : |S.r t - S'.r t| ≤ |S.r t - rs| + |S'.r t - rs| := by
    have h1 := abs_sub_le (S.r t) rs (S'.r t)
    linarith [abs_sub_comm (S'.r t) rs]
  have hd := S.dist_bound_from_ode_unified t ht
  have hd' : |S'.r t - rs| ≤ |S'.r 0 - rs| *
      Real.exp (-(S.K * min (S'.r 0) rs * (min (S'.r 0) rs + rs) / 2) * t) := by
    have h := S'.dist_bound_from_ode_unified t ht
    rw [← hK_eq, ← hγ_eq] at h
    exact h
  exact le_trans htri (add_le_add hd hd')

/-- **ODE velocity bound from abstract ODE** (NO eq_explicit):
    The ODE velocity |ṙ(t)| = |lorentzianODE K γ (r t)| ≤ K - γ for all t ≥ 0.
    Proof: r_mem_Icc_from_ode gives r(t) ∈ [0,1]; lorentzian_ode_abs_le gives the bound. -/
theorem LorentzianContinuousSolution.velocity_bound_from_ode
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    |lorentzianODE S.K S.γ (S.r t)| ≤ S.K - S.γ :=
  lorentzian_ode_abs_le S.K S.γ (S.r t) S.hK_pos S.hγ_pos S.hK_gt
    (S.r_mem_Icc_from_ode t ht).1 (S.r_mem_Icc_from_ode t ht).2

/-- **Continuous-time Lipschitz bound from abstract ODE** (NO eq_explicit):
    |S.r (t + s) - S.r t| ≤ (K - γ) · s for t ≥ 0, s ≥ 0.
    Proof: MVT on [t, t+s] with velocity bound velocity_bound_from_ode. -/
theorem LorentzianContinuousSolution.r_lipschitz_from_ode
    (S : LorentzianContinuousSolution) (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |S.r (t + s) - S.r t| ≤ (S.K - S.γ) * s := by
  have h_deriv : ∀ x ∈ Set.Icc t (t + s),
      HasDerivWithinAt S.r (lorentzianODE S.K S.γ (S.r x)) (Set.Icc t (t + s)) x :=
    fun x hx => (S.hr_ode x (le_trans ht hx.1)).hasDerivWithinAt
  have h_bound : ∀ x ∈ Set.Ico t (t + s),
      ‖lorentzianODE S.K S.γ (S.r x)‖ ≤ S.K - S.γ := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact S.velocity_bound_from_ode x (le_trans ht hx.1)
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment'
    h_deriv h_bound (t + s) (Set.right_mem_Icc.mpr (by linarith))
  rw [Real.norm_eq_abs, show (t + s) - t = s from by ring] at h_mvt
  linarith [mul_nonneg (by linarith [S.hK_pos, S.hγ_pos, S.hK_gt] : 0 ≤ S.K - S.γ) hs]

/-- **Complete Lorentzian ODE global stability (billboard theorem)**:
    Given K > 2γ > 0 and any continuous ODE solution r : ℝ → ℝ with r(0) ∈ (0,1):
    (1) r(t) ∈ (0,1) for all t ≥ 0  (domain invariance)
    (2) r(t) → r* = √(1-2γ/K)       (global stability)
    (3) |r(t)-r*| ≤ |r(0)-r*|·exp(-μt) where μ = K·min(r₀,r*)·(min(r₀,r*)+r*)/2
    This is the complete abstract-ODE result, requiring no existence construction. -/
theorem lorentzian_ode_global_stability_complete (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K)
    (r : ℝ → ℝ)
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_cont : ContinuousOn r (Set.Ici 0))
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1) :
    (∀ t, 0 ≤ t → r t ∈ Set.Ioo (0 : ℝ) 1) ∧
    Filter.Tendsto r Filter.atTop (nhds (Real.sqrt (1 - 2 * γ / K))) ∧
    (∀ t, 0 ≤ t → |r t - Real.sqrt (1 - 2 * γ / K)| ≤
      |r 0 - Real.sqrt (1 - 2 * γ / K)| *
      Real.exp (-(K * min (r 0) (Real.sqrt (1 - 2 * γ / K)) *
                  (min (r 0) (Real.sqrt (1 - 2 * γ / K)) +
                   Real.sqrt (1 - 2 * γ / K)) / 2) * t)) := by
  let S : LorentzianContinuousSolution :=
    { K := K, γ := γ, hK_pos := hK, hγ_pos := hγ, hK_gt := hKγ,
      r := r, hr_ode := hr_ode, hr_cont := hr_cont,
      hr_init_pos := hr_init_pos, hr_init_lt := hr_init_lt }
  exact ⟨fun t ht => S.r_mem_Ioo_from_ode t ht,
         S.tendsto_from_ode,
         fun t ht => S.dist_bound_from_ode_unified t ht⟩

/-- **Local ODE existence via Picard-Lindelöf** (NO eq_explicit, NO Bernoulli formula):
    For any r₀ and K, γ > 0, there exists ε > 0 and an ODE solution α on (-ε,ε) with α(0) = r₀.
    Uses Mathlib's `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`.
    Connects Mathlib's PL theorem to the Lorentzian ODE; global existence already proved via
    the explicit Bernoulli formula in `lorentzian_continuous_solution_exists`. -/
theorem lorentzian_ode_local_existence (K γ r₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → ℝ, α 0 = r₀ ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (lorentzianODE K γ (α t)) t := by
  have hf : ContDiffAt ℝ 1 (lorentzianODE K γ) r₀ :=
    ((show ContDiff ℝ ⊤ (lorentzianODE K γ) from
        by unfold lorentzianODE; fun_prop).contDiffAt).of_le le_top
  obtain ⟨α, hα₀, ε, hε, hα_deriv⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ hf 0
  simp only [zero_sub, zero_add] at hα_deriv
  exact ⟨ε, hε, α, hα₀, hα_deriv⟩

end
