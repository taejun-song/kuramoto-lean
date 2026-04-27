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

end
