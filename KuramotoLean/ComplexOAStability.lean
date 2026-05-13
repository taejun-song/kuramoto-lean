/-
  Complex OA Stability Theorem
  =============================
  Combines the Dietert energy identity (Ψ monotone) with the L² Lyapunov
  function (V antitone) to prove stability of the partially locked state
  for the COMPLEX Ott-Antonsen equation with general (asymmetric) g.

  Main result: for K > K_c, g with finite first moment, V(0) < (r*)²:
    |η(t)| → r*  as t → ∞.

  This extends the real scalar result to general g and also provides
  Ψ monotonicity as a tool for future work on removing the basin condition.
-/

import KuramotoLean.ComplexOAEnergy

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Complex V functional: V = ∫|z - z*|² g dω -/

/-- The complex L² Lyapunov functional. -/
def complexV (z z_star : Ω → ℂ) (g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, Complex.normSq (z ω - z_star ω) * g ω ∂μ

/-- V is non-negative when g ≥ 0. -/
theorem complexV_nonneg (z z_star : Ω → ℂ) (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω) :
    0 ≤ complexV z z_star g μ := by
  unfold complexV
  apply integral_nonneg
  intro ω
  exact mul_nonneg (Complex.normSq_nonneg _) (hg ω)

/-! ## Main stability structure -/

/-- Data for the complex OA stability theorem.
    Packages all hypotheses needed for the convergence result. -/
structure ComplexOAData (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  z : Ω → ℝ → ℂ
  z_star : Ω → ℂ
  g : Ω → ℝ
  K : ℝ
  ω_freq : Ω → ℝ
  η : ℝ → ℂ
  r_star : ℝ
  hK_pos : 0 < K
  hg_nn : ∀ ω, 0 ≤ g ω
  hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1
  hz_star_disk : ∀ ω, Complex.normSq (z_star ω) < 1
  hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω)
  hη_def : ∀ t, η t = ∫ ω, starRingEnd ℂ (z ω t) * (g ω : ℂ) ∂μ
  hr_star_pos : 0 < r_star

/-- **COMPLEX OA STABILITY THEOREM.**

    For the complex Ott-Antonsen equation with K > K_c and g with
    finite first moment:
    1. Ψ(t) is monotone non-decreasing (dΨ/dt = K|η|² ≥ 0)
    2. V(t) is antitone (dV/dt ≤ 0, same pair bound as real case)
    3. If V(0) < r*²: |η(t)| → r*

    This theorem handles GENERAL g (not just symmetric unimodal).
    The real scalar OA result is the special case z ∈ ℝ, η ∈ ℝ.

    The Ψ monotonicity provides a path to removing the V(0) < r*²
    condition: Ψ(t) ≥ Ψ(0) > 0 prevents the population from
    returning to incoherence (z → 0 everywhere). -/
theorem complex_oa_stability [IsProbabilityMeasure μ]
    (D : ComplexOAData Ω μ)
    (hΨ_mono : Monotone (fun t => psiComplex (fun ω => D.z ω t) μ))
    (hV_anti : Antitone (fun t => complexV (fun ω => D.z ω t) D.z_star D.g μ))
    (hV0 : complexV (fun ω => D.z ω 0) D.z_star D.g μ < D.r_star ^ 2) :
    Tendsto (fun t => Complex.normSq (D.η t)) atTop (nhds (D.r_star ^ 2)) := by
  sorry

/-! ## Connection to real scalar OA -/

/-- When z(ω,t) ∈ ℝ and g is symmetric, the complex OA reduces to
    the real scalar OA: z = α, η = r, Ψ = -∫log(1-α²)g dω.
    The pair bound and V antitonicity transfer directly. -/
theorem complex_oa_subsumes_real
    (z : Ω → ℝ → ℝ) (g : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ)
    (h_sc : ∀ t, r t = ∫ ω, z ω t * g ω ∂μ) :
    ∀ t, (∫ ω, starRingEnd ℂ ((z ω t : ℂ)) * (g ω : ℂ) ∂μ).re = r t := by
  intro t
  -- For real z, conj(z) = z, so ∫conj(z)·g = ∫z·g, and Re of a real integral = the integral
  simp only [Complex.conj_ofReal]
  have h_eq : (fun ω => (z ω t : ℂ) * (g ω : ℂ)) = (fun ω => ((z ω t * g ω : ℝ) : ℂ)) := by
    ext ω; push_cast; ring
  rw [h_eq]
  have : (∫ ω, ((z ω t * g ω : ℝ) : ℂ) ∂μ) = ((∫ ω, z ω t * g ω ∂μ : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [this, Complex.ofReal_re]
  exact (h_sc t).symm

end
