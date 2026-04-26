/-
  Kuramoto Stability Project — Global Monotone Functional
  =========================================================

  The functional Ψ[α] = -∫ g(ω) log(1 - |α(ω)|²) dω satisfies
    d/dt Ψ = K|r|² ≥ 0
  along the OA flow. This is GLOBAL (any g, any initial data).

  Key identity: d/dt |α|² = K · Re(r̄α) · (1-|α|²)
  (rotation -iωα drops out from d/dt |α|²).

  We prove the consequences that are checkable by nlinarith/linarith.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex

noncomputable section

/-- The rotation term drops out: Re(conj(α) · (-iωα)) = 0.
    This is because -iω|α|² is purely imaginary. -/
lemma rotation_drops_out_normSq (α : ℂ) (ω : ℝ) :
    (starRingEnd ℂ α * (-Complex.I * (ω : ℂ) * α)).re = 0 := by
  set a := α.re; set b := α.im
  simp only [Complex.ext_iff, starRingEnd_self_apply, Complex.conj_re,
    Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.re_add_im]
  ring

/-- d/dt Ψ = K|r|² ≥ 0 for K > 0. -/
lemma psi_dot_nonneg (K : ℝ) (r_re r_im : ℝ) (hK : 0 < K) :
    0 ≤ K * (r_re ^ 2 + r_im ^ 2) := by
  apply mul_nonneg (le_of_lt hK)
  nlinarith [sq_nonneg r_re, sq_nonneg r_im]

/-- d/dt Ψ = K|r|² = 0 iff r = 0. -/
lemma psi_dot_zero_iff (K : ℝ) (r_re r_im : ℝ) (hK : 0 < K) :
    K * (r_re ^ 2 + r_im ^ 2) = 0 ↔ r_re = 0 ∧ r_im = 0 := by
  constructor
  · intro h
    have h1 : r_re ^ 2 + r_im ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < r_re ^ 2 + r_im ^ 2 := by
        rcases (ne_iff_lt_or_gt.mp hne) with h | h
        · nlinarith [sq_nonneg r_re, sq_nonneg r_im]
        · exact h
      linarith [mul_pos hK hpos]
    constructor
    · nlinarith [sq_nonneg r_re, sq_nonneg r_im]
    · nlinarith [sq_nonneg r_re, sq_nonneg r_im]
  · rintro ⟨hr, hi⟩
    rw [hr, hi]
    simp

/-- Ψ is bounded below: Ψ ≥ 0 (since -log(1-x) ≥ 0 for x ∈ [0,1)). -/
lemma neg_log_one_sub_nonneg (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) := by
  rw [neg_nonneg]
  exact Real.log_nonpos (by linarith) (by linarith)

/-- Ψ = 0 iff α ≡ 0 (incoherence). Pointwise version. -/
lemma neg_log_one_sub_eq_zero (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) = 0 ↔ x = 0 := by
  rw [neg_eq_zero, Real.log_eq_zero]
  constructor
  · intro h
    rcases h with h | h | h
    · linarith
    · linarith
    · linarith
  · intro h
    rw [h]
    simp

/-! ## No periodic orbits -/

/-- KEY THEOREM: No nonconstant periodic orbits on the OA manifold.

    If α(·,t) has period T > 0, then Ψ(T) = Ψ(0).
    Since Ψ̇ = K|r|² ≥ 0, we get ∫₀ᵀ |r(t)|² dt = 0, hence r ≡ 0.
    With r ≡ 0: ∂_t α = -iωα ⟹ α(ω,t) = α(ω,0)e^{-iωt}.
    Periodicity ⟹ α(ω,0)(e^{-iωT}-1) = 0 for all ω.
    Since {ω : e^{-iωT} = 1} has measure zero and g > 0 a.e.,
    α(ω,0) = 0 a.e., giving the trivial orbit.

    Stated here as: periodicity + Ψ̇ ≥ 0 ⟹ ∫|r|² = 0.

    The core algebraic step: if Ψ̇ = K|r|² ≥ 0 and Ψ is periodic,
    then K|r(t)|² = 0 for all t, hence r(t) = 0.

    Stated simply: periodicity of a nondecreasing function implies constancy. -/
lemma nondecreasing_periodic_const (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hMono : ∀ t₁ t₂, t₁ ≤ t₂ → f t₁ ≤ f t₂)
    (hPeriodic : ∀ t, f (t + T) = f t) :
    ∀ t₁ t₂, t₁ ≤ t₂ → t₂ ≤ t₁ + T → f t₁ = f t₂ := by
  intro t₁ t₂ h12 h2T
  apply le_antisymm (hMono t₁ t₂ h12)
  have := hMono t₂ (t₁ + T) h2T
  rw [hPeriodic] at this
  exact this

-- The "no periodic orbits" theorem is the combination:
-- 1. nondecreasing_periodic_const: Ψ periodic + nondecreasing ⟹ Ψ constant
-- 2. Ψ̇ = K|r|², so Ψ constant ⟹ |r| = 0 pointwise
-- 3. |r| = 0 ⟹ α(ω,t) = α(ω,0)e^{-iωt} (free rotation)
-- 4. Periodicity + g > 0 a.e. ⟹ α ≡ 0
-- Steps 3-4 require ODE theory not in this file.

end
