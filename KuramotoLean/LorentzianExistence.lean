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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

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

end
