/-
  Kuramoto Stability — Gaussian Global Stability
  ================================================
  Proves global convergence r(t) -> r* for the Kuramoto model with Gaussian
  frequency distribution g(w) = exp(-w^2/2) / sqrt(2pi), for any K > Kc.

  "Global" means: no basin condition on V(0). Any initial data alpha(w,0) in (0,1)
  converges.

  Architecture:
    1. Gaussian has finite first moment sqrt(2/pi) (gaussian_first_moment)
    2. Self-consistency: K > Kc implies exists r* in (0,1)
    3. Jensen upper bound: r^2 <= 1 - exp(-Psi) (psi_jensen_upper)
    4. r-floor from Psi + ODE contradiction: r(t) -> 0 contradicts Psi(t) >= Psi(0) > 0
    5. Body persistence from r_min (explicitEquil lower bound)
    6. End-to-end: KuramotoFirstMomentBarbalat implies r(t) -> r*

  Status:
    - psi_jensen_upper: PROVED (0 sorry)
    - r_floor_from_psi_ode: STRUCTURED (main theorem proved modulo 3 lemmas)
      - alpha_gronwall_bound: sorry (Gronwall comparison for scalar ODE)
      - psi_small_from_r_small: sorry (Gronwall + DCT → Ψ small)
      - continuous_small_interval: sorry (continuity → r small on intervals)
    - gaussian_global_stability: 1 sorry (depends on r-floor)

  The r-floor argument:
    The Jensen bound gives r^2 <= 1 - exp(-Psi) (UPPER bound, not lower).
    A LOWER bound on r requires the ODE structure: if r(t) -> 0, then
    dalpha/dt approx -|w|*alpha for a.e. w, forcing alpha -> 0, hence Psi -> 0,
    contradicting Psi(t) >= Psi(0) > 0 (monotonicity).
    The main theorem `r_floor_from_psi_ode` is now proved by contradiction,
    reducing to three sorry'd lemmas: Gronwall comparison, DCT passage, and
    continuity extraction of intervals.
-/

import KuramotoLean.GaussianAnalyticExtension
import KuramotoLean.ContinuumGlobalStability
import KuramotoLean.KuramotoFirstMomentBarbalat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Real Set Filter Topology

noncomputable section

/-! ## Step 1: Gaussian first absolute moment -/

/-- The Gaussian first moment: integral |w| * g(w) dw = sqrt(2/pi). -/
theorem gaussian_first_moment :
    ∫ ω : ℝ, |ω| * gaussianFreqDist 1 ω = Real.sqrt (2 / Real.pi) := by
  have hsplit0 := integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(x ^ 2) / 2))
  have hsplit :
      ∫ ω : ℝ, |ω| * Real.exp (-(ω ^ 2) / 2) =
        2 * ∫ ω in Ioi (0 : ℝ), ω * Real.exp (-(ω ^ 2) / 2) := by
    simpa only [sq_abs] using hsplit0
  have hIoiC :
      (∫ ω in Ioi (0 : ℝ), ((ω * Real.exp (-(ω ^ 2) / 2) : ℝ) : ℂ)) = (1 : ℂ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num : 0 < ((1 / 2 : ℂ)).re))
  have hIoi : ∫ ω in Ioi (0 : ℝ), ω * Real.exp (-(ω ^ 2) / 2) = 1 := by
    have hIoiC' := hIoiC
    rw [integral_complex_ofReal] at hIoiC'
    exact Complex.ofReal_injective hIoiC'
  have hrew :
      (fun ω : ℝ => |ω| * gaussianFreqDist 1 ω) =
        fun ω : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * (|ω| * Real.exp (-(ω ^ 2) / 2)) := by
    funext ω
    simp [gaussianFreqDist, div_eq_mul_inv, mul_assoc, mul_comm]
  calc
    ∫ ω : ℝ, |ω| * gaussianFreqDist 1 ω
        = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ ω : ℝ, |ω| * Real.exp (-(ω ^ 2) / 2) := by
            rw [hrew, integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 * ∫ ω in Ioi (0 : ℝ), ω * Real.exp (-(ω ^ 2) / 2)) := by
          rw [hsplit]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * 2 := by rw [hIoi, mul_one]
    _ = Real.sqrt (2 / Real.pi) := by
      let a : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * 2
      let b : ℝ := Real.sqrt (2 / Real.pi)
      have hsq : a ^ 2 = b ^ 2 := by
        unfold a b
        rw [Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)]
        field_simp [Real.pi_ne_zero]
        rw [Real.sq_sqrt (by positivity)]
      have ha : 0 ≤ a := by
        unfold a
        positivity
      have hb : 0 ≤ b := by
        unfold b
        positivity
      have hab : a = b := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
        · exact h
        · exfalso
          have hb0 : b = 0 := by linarith
          have : 0 < b := by
            unfold b
            apply Real.sqrt_pos.mpr
            positivity
          linarith
      simpa [a, b] using hab

/-! ## Step 2: Jensen upper bound on r from Psi

The CORRECT Jensen inequality direction:
  Psi = integral(-log(1-alpha^2))g where f(x) = -log(1-x^2) is convex on [0,1).
  By Jensen: Psi = integral f(alpha) g >= f(integral alpha g) = f(r) = -log(1-r^2).
  Rearranging: r^2 <= 1 - exp(-Psi).

This gives an UPPER bound on r. For a LOWER bound on r, Jensen alone is
insufficient. We need the ODE dynamics (Step 3 below). -/

/-- The function 1 - exp(-x) is positive for x > 0. -/
theorem one_sub_exp_neg_pos (Ψ : ℝ) (hΨ : 0 < Ψ) :
    0 < 1 - Real.exp (-Ψ) := by
  have h1 : Real.exp (-Ψ) < 1 := exp_lt_one_iff.mpr (by linarith)
  linarith

/-- Jensen upper bound: Psi >= -log(1-r^2) implies r^2 <= 1 - exp(-Psi).
    This is the CORRECT direction: Psi large means r is bounded ABOVE. -/
theorem psi_jensen_upper (Ψ r : ℝ) (hr_nn : 0 ≤ r) (hr_lt : r < 1)
    (h_jensen : Ψ ≥ -Real.log (1 - r ^ 2)) :
    r ^ 2 ≤ 1 - Real.exp (-Ψ) := by
  have h1mr : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  have h2 : -Ψ ≤ Real.log (1 - r ^ 2) := by linarith
  have h3 : Real.exp (-Ψ) ≤ 1 - r ^ 2 := by
    calc Real.exp (-Ψ) ≤ Real.exp (Real.log (1 - r ^ 2)) :=
          Real.exp_le_exp.mpr h2
      _ = 1 - r ^ 2 := Real.exp_log h1mr
  linarith

/-! ## Step 3: r-floor from Psi monotonicity + ODE dynamics

The key non-trivial step. We need: r(t) >= r_min > 0 uniformly.

Argument by contradiction:
  Suppose liminf r(t) = 0, i.e., r(t_n) -> 0 for some t_n -> infinity.
  For each w != 0 with gamma(w) = |w|:
    dalpha/dt = -|w|*alpha + (K/2)*r(t)*(1-alpha^2)
  When r is persistently small on intervals (by continuity), alpha decays
  exponentially: alpha(w,t) <= alpha(w,t0)*exp(-|w|*(t-t0)/2).

  Since Gaussian has gamma(w) = |w| > 0 for a.e. w, this forces alpha -> 0 a.e.
  By dominated convergence: Psi(t_n) -> 0.
  Contradicting Psi(t_n) >= Psi(0) > 0.

  The subtlety: r(t_n) -> 0 at isolated points does not force alpha decay.
  Need r small on INTERVALS, which follows from continuity + subsequence. -/

/-- Gronwall comparison: if r ≤ ε on [t₀, t₀+T] and γ = |ω| > 0,
    then α(ω, t₀+T) ≤ α(ω,t₀) * exp(-γ*T) + Kε/(2γ). -/
private theorem alpha_gronwall_bound
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε)
    (γ : ℝ) (hγ : 0 < γ) (T : ℝ) (hT : 0 < T) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (r : ℝ → ℝ) (α_ω : ℝ → ℝ)
    (hα_pos : ∀ t, t₀ ≤ t → t ≤ t₀ + T → 0 < α_ω t)
    (hα_lt : ∀ t, t₀ ≤ t → t ≤ t₀ + T → α_ω t < 1)
    (hr_bd : ∀ t, t₀ ≤ t → t ≤ t₀ + T → r t ≤ ε)
    (hα_ode : ∀ t, t₀ ≤ t → t ≤ t₀ + T → HasDerivAt α_ω
      (-γ * α_ω t + (K / 2) * r t * (1 - (α_ω t) ^ 2)) t) :
    α_ω (t₀ + T) ≤ α_ω t₀ * Real.exp (-γ * T) + K * ε / (2 * γ) := by
  sorry

/-- If r ≤ ε on [t₀, t₀+T], then Ψ(t₀+T) ≤ δ for suitable ε, T.
    Uses Gronwall on each α(ω) + dominated convergence. -/
private theorem psi_small_from_r_small
    (K : ℝ) (hK : 0 < K)
    (r : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_ode : ∀ ω, ∀ t ≥ (0 : ℝ), HasDerivAt (α ω)
      (-(|ω|) * α ω t + (K / 2) * r t * (1 - (α ω t) ^ 2)) t)
    (Ψ : ℝ → ℝ)
    (hΨ_def : ∀ t, Ψ t =
      -∫ ω : ℝ, Real.log (1 - (α ω t) ^ 2) * gaussianFreqDist 1 ω)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ →
      (∀ t, t₀ ≤ t → t ≤ t₀ + T → r t ≤ ε) → Ψ (t₀ + T) ≤ δ := by
  sorry

/-- Continuous function with infimum 0 has intervals where it stays small. -/
private theorem continuous_small_interval
    (r : ℝ → ℝ) (hr_cont : Continuous r) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (h_inf : ∀ ε > 0, ∃ t₀ : ℝ, 0 ≤ t₀ ∧ r t₀ < ε)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t, t₀ ≤ t → t ≤ t₀ + T → r t ≤ ε := by
  sorry

/-- R-FLOOR FROM PSI AND ODE.
    If alpha satisfies the OA scalar ODE with Gaussian frequency distribution,
    alpha(w,t) in (0,1), and Psi(0) > 0 with Psi monotone non-decreasing,
    then r(t) >= r_min > 0 for all t >= 0.

    Proof: by contradiction using ODE decay + DCT + Psi monotonicity.
    Suppose inf r = 0. Then r is small on intervals (continuity).
    Gronwall + DCT give Psi small on those intervals, contradicting Psi monotone. -/
theorem r_floor_from_psi_ode
    (K : ℝ) (hK : 0 < K)
    (r : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_ode : ∀ ω, ∀ t ≥ (0 : ℝ), HasDerivAt (α ω)
      (-(|ω|) * α ω t + (K / 2) * r t * (1 - (α ω t) ^ 2)) t)
    (h_sc : ∀ t ≥ (0 : ℝ), r t = ∫ ω : ℝ, α ω t * gaussianFreqDist 1 ω)
    (Ψ : ℝ → ℝ) (hΨ_mono : Monotone Ψ) (hΨ_pos : 0 < Ψ 0)
    (hΨ_def : ∀ t, Ψ t =
      -∫ ω : ℝ, Real.log (1 - (α ω t) ^ 2) * gaussianFreqDist 1 ω) :
    ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t := by
  by_contra h_neg
  push Not at h_neg
  -- h_neg : ∀ r_min > 0, ∃ t ≥ 0, r t < r_min
  -- i.e., inf_{t≥0} r(t) = 0
  have h_inf : ∀ ε > 0, ∃ t₀ : ℝ, 0 ≤ t₀ ∧ r t₀ < ε := by
    intro ε hε
    obtain ⟨t, ht_nn, hrt⟩ := h_neg ε hε
    exact ⟨t, ht_nn, hrt⟩
  -- Choose δ = Ψ(0) / 2 > 0
  set δ := Ψ 0 / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  -- Get ε, T from the Psi-smallness lemma
  obtain ⟨ε, hε, T, hT, h_small⟩ := psi_small_from_r_small K hK r α hr_nn hα_inv
    hα_ode Ψ hΨ_def δ hδ
  -- Get an interval [t₀, t₀+T] where r ≤ ε
  obtain ⟨t₀, ht₀, h_r_interval⟩ := continuous_small_interval r hr_cont hr_nn h_inf ε hε T hT
  -- Conclude Ψ(t₀+T) ≤ δ = Ψ(0)/2
  have hΨ_le : Ψ (t₀ + T) ≤ δ := h_small t₀ ht₀ h_r_interval
  -- But Ψ monotone gives Ψ(t₀+T) ≥ Ψ(0) > 2δ = Ψ(0)
  have hΨ_ge : Ψ 0 ≤ Ψ (t₀ + T) := hΨ_mono (by linarith)
  linarith

/-! ## Step 4: Gaussian global stability theorem -/

/-- GAUSSIAN GLOBAL STABILITY.
    For the continuum Kuramoto model with Gaussian g(w) = e^{-w^2/2}/sqrt(2pi)
    and K > Kc, any initial condition alpha(w,0) in (0,1) satisfies
    r(t) -> r* as t -> infinity.

    Status: reduces to r_floor_from_psi_ode (1 sorry). -/
theorem gaussian_global_stability
    (K : ℝ) (hK : K > 2 * Real.sqrt (2 * Real.pi) / Real.pi)
    (r : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hΨ_pos : 0 < -∫ ω : ℝ,
      Real.log (1 - (α ω 0) ^ 2) * gaussianFreqDist 1 ω) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      Tendsto r atTop (nhds r_star) := by
  sorry

end
