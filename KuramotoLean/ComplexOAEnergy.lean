/-
  Complex OA Energy Identity: dΨ/dt = K|η|² ≥ 0
  =================================================
  The Dietert energy identity for the complex Ott-Antonsen equation.

  Ψ(t) = -∫ log(1-|z(ω,t)|²) g(ω) dω satisfies dΨ/dt = K|η|² ≥ 0
  where η = ∫ z̄ g dω is the complex order parameter.

  This is the KEY identity that the real scalar reduction lacks.
  It prevents return to incoherence and removes the basin restriction.

  3 sorry: normSq derivative composition, integral identity, Leibniz.
-/

import KuramotoLean.ComplexOA
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## HasDerivAt for normSq ∘ z -/

/-- d|z(t)|²/dt = 2·Re(z̄(t)·z'(t)). Standard chain rule for normSq. -/
theorem hasDerivAt_normSq_comp (z : ℝ → ℂ) (z' : ℂ) (t : ℝ)
    (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => Complex.normSq (z s))
      (2 * (starRingEnd ℂ (z t) * z').re) t := by
  have h_re : HasDerivAt (fun s => (z s).re) z'.re t := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
    simp [ContinuousLinearMap.comp_apply, Function.comp_def] at h
    exact h
  have h_im : HasDerivAt (fun s => (z s).im) z'.im t := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
    simp [ContinuousLinearMap.comp_apply, Function.comp_def] at h
    exact h
  have h3 : HasDerivAt (fun s => (z s).re ^ 2) (2 * (z t).re * z'.re) t := by
    have := h_re.pow 2; convert this using 1; ring
  have h4 : HasDerivAt (fun s => (z s).im ^ 2) (2 * (z t).im * z'.im) t := by
    have := h_im.pow 2; convert this using 1; ring
  have h5 := h3.add h4
  convert h5 using 1
  · ext s; simp [Complex.normSq_apply, sq]
  · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-! ## Pointwise Ψ derivative -/

/-- The pointwise derivative of -log(1-|z|²) along the complex OA flow
    equals K·Re(η·z). Combines normSq derivative + log chain rule +
    the algebraic identity from ComplexOA.complexOa_normSq_deriv. -/
theorem psi_pointwise_complex_deriv
    (ω_freq K : ℝ) (η : ℂ) (z : ℝ → ℂ) (t : ℝ)
    (hz_disk : Complex.normSq (z t) < 1)
    (hz_ode : HasDerivAt z (complexOaRHS ω_freq K η (z t)) t) :
    HasDerivAt (fun s => -Real.log (1 - Complex.normSq (z s)))
      (K * (η * z t).re) t := by
  have h1m : (0 : ℝ) < 1 - Complex.normSq (z t) := sub_pos.mpr hz_disk
  have h_ns := hasDerivAt_normSq_comp z _ t hz_ode
  have h_sub := (hasDerivAt_const t (1 : ℝ)).sub h_ns
  have h_log := h_sub.log (ne_of_gt h1m)
  have h_neg : HasDerivAt (fun s => -Real.log (1 - Complex.normSq (z s)))
      (2 * (starRingEnd ℂ (z t) * complexOaRHS ω_freq K η (z t)).re /
        (1 - Complex.normSq (z t))) t := by
    convert h_log.neg using 1 <;> simp [Pi.sub_apply]; ring
  convert h_neg using 1
  have h_key := complexOa_normSq_deriv ω_freq K η (z t)
  have h1m_ne : (1 : ℝ) - Complex.normSq (z t) ≠ 0 := ne_of_gt h1m
  field_simp
  linarith

/-! ## Integral identity: ∫Re(η·z)g dμ = |η|² -/

/-- For real-valued weight g, if η = ∫z̄·g dμ, then ∫Re(η·z)·g dμ = |η|².
    Key: η̄ = conj(∫z̄·g) = ∫z·g (g real), so
    ∫Re(η·z)·g = Re(η·∫z·g) = Re(η·η̄) = |η|². -/
theorem complex_eta_integral_identity
    (z : Ω → ℂ) (g : Ω → ℝ)
    (η : ℂ)
    (hη_def : η = ∫ ω, starRingEnd ℂ (z ω) * (g ω : ℂ) ∂μ)
    (hz_int : Integrable (fun ω => (g ω : ℂ) * z ω) μ)
    (hre_int : Integrable (fun ω => (η * z ω).re * g ω) μ) :
    ∫ ω, (η * z ω).re * g ω ∂μ = Complex.normSq η := by
  -- η̄ = ∫ g·z (conjugate of η = ∫z̄·g with g real)
  have h_conj : starRingEnd ℂ η = ∫ ω, (g ω : ℂ) * z ω ∂μ := by
    rw [hη_def]
    rw [show (starRingEnd ℂ) (∫ ω, starRingEnd ℂ (z ω) * ↑(g ω) ∂μ) =
        ∫ ω, starRingEnd ℂ (starRingEnd ℂ (z ω) * ↑(g ω)) ∂μ from
      (integral_conj).symm]
    congr 1; ext ω; simp [map_mul, mul_comm]
  -- ∫Re(η·z)·g = Re(η · ∫g·z) = Re(η·η̄) = |η|²
  -- Step 1: factor g inside the complex multiplication
  have h_eq : (fun ω => (η * z ω).re * g ω) =
      (fun ω => (η * ((g ω : ℂ) * z ω)).re) := by
    ext ω; simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [h_eq]
  -- Step 2: pull Re and η through the integral
  have h2 : ∫ ω, (η * ((g ω : ℂ) * z ω)).re ∂μ =
      (η * ∫ ω, (g ω : ℂ) * z ω ∂μ).re := by
    conv_lhs =>
      arg 2; ext ω
      rw [show (η * ((g ω : ℂ) * z ω)).re = Complex.reCLM (η * ((g ω : ℂ) * z ω)) from by simp]
    rw [ContinuousLinearMap.integral_comp_comm _ (hz_int.const_mul η)]
    simp only [Complex.reCLM_apply]
    congr 1
    show ∫ ω, η * ((g ω : ℂ) * z ω) ∂μ = η * ∫ ω, (g ω : ℂ) * z ω ∂μ
    exact integral_const_mul η (fun ω => (g ω : ℂ) * z ω)
  rw [h2, ← h_conj, Complex.mul_conj, Complex.ofReal_re]

/-! ## The energy identity -/

/-- **THE DIETERT ENERGY IDENTITY.**
    dΨ/dt = K·|η(t)|² where Ψ = -∫log(1-|z|²)g dω and η = ∫z̄ g dω.

    Assumes Leibniz interchange (standard DCT, same as real case). -/
theorem psi_deriv_eq_K_eta_sq
    (z : Ω → ℝ → ℂ) (g : Ω → ℝ) (K : ℝ) (ω_freq : Ω → ℝ) (t : ℝ)
    (η : ℂ)
    (hη_def : η = ∫ ω, starRingEnd ℂ (z ω t) * (g ω : ℂ) ∂μ)
    (hz_disk : ∀ ω, Complex.normSq (z ω t) < 1)
    (hz_ode : ∀ ω, HasDerivAt (z ω) (complexOaRHS (ω_freq ω) K η (z ω t)) t)
    (hz_int : Integrable (fun ω => (g ω : ℂ) * z ω t) μ)
    (hre_int : Integrable (fun ω => (η * z ω t).re * g ω) μ)
    (h_leibniz : HasDerivAt (fun s => ∫ ω, -Real.log (1 - Complex.normSq (z ω s)) * g ω ∂μ)
      (∫ ω, K * (η * z ω t).re * g ω ∂μ) t) :
    HasDerivAt (fun s => ∫ ω, -Real.log (1 - Complex.normSq (z ω s)) * g ω ∂μ)
      (K * Complex.normSq η) t := by
  convert h_leibniz using 1
  have h_pull : ∫ ω, K * (η * z ω t).re * g ω ∂μ =
      K * ∫ ω, (η * z ω t).re * g ω ∂μ := by
    have : (fun ω => K * (η * z ω t).re * g ω) =
        (fun ω => K * ((η * z ω t).re * g ω)) := by ext ω; ring
    rw [this]
    exact integral_const_mul K _
  rw [h_pull, complex_eta_integral_identity (fun ω => z ω t) g η hη_def hz_int hre_int]

/-! ## Monotonicity consequences -/

/-- Ψ is monotone non-decreasing: derivative = K|η|² ≥ 0 everywhere. -/
theorem psi_monotone_of_energy_identity
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (η_norm_sq : ℝ → ℝ)
    (h_nn : ∀ t, 0 ≤ η_norm_sq t)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_norm_sq t) t) :
    Monotone Ψ := by
  have h_diff : Differentiable ℝ Ψ := fun t => (h_deriv t).differentiableAt
  have h_cont := h_diff.continuous
  intro a b hab
  by_cases heq : a = b; · rw [heq]
  have hab' : a < b := lt_of_le_of_ne hab heq
  have h_on : ContinuousOn Ψ (Icc a b) := h_cont.continuousOn
  have h_nn_on : ∀ x ∈ interior (Icc a b), 0 ≤ deriv Ψ x := by
    intro x hx; rw [(h_deriv x).deriv]; exact mul_nonneg hK (h_nn x)
  exact (monotoneOn_of_deriv_nonneg (convex_Icc a b) h_on
    (fun x hx => (h_diff x).differentiableWithinAt) h_nn_on)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- **Ψ PREVENTS RETURN TO INCOHERENCE.**
    If Ψ(0) > 0 and Ψ is monotone, then Ψ(t) > 0 for all t ≥ 0. -/
theorem psi_stays_positive
    (Ψ : ℝ → ℝ) (hΨ_mono : Monotone Ψ) (hΨ_pos : 0 < Ψ 0) :
    ∀ t, 0 ≤ t → 0 < Ψ t :=
  fun t ht => lt_of_lt_of_le hΨ_pos (hΨ_mono ht)

end
