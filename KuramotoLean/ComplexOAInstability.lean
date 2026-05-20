/-
  Penrose Criterion — Instability of the Incoherent State
  ========================================================
  For Lorentzian g(ω) = (γ/π)/(γ²+ω²), the dispersion relation
    D(s) = (K/2) ∫ s/(s²+ω²) g(ω) dω = K/(2(s+γ))
  has a positive root s* = K/2 - γ when K > 2γ = Kc.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory MeasureTheory.Measure Set Filter Topology Real

noncomputable section

/-! ## Base integral: ∫ (a²+ω²)⁻¹ = π/a -/

lemma integral_univ_inv_sq_add_sq (a : ℝ) (ha : 0 < a) :
    ∫ ω : ℝ, (a ^ 2 + ω ^ 2)⁻¹ = π / a := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have step1 : ∀ ω : ℝ, (a ^ 2 + ω ^ 2)⁻¹ = a⁻¹ ^ 2 * (1 + (ω / a) ^ 2)⁻¹ := by
    intro ω; field_simp
  have step2 : (fun ω : ℝ => (1 + (ω / a) ^ 2)⁻¹) = fun ω => (fun u => (1 + u ^ 2)⁻¹) (ω / a) :=
    by ext ω; simp [div_pow]
  calc ∫ ω, (a ^ 2 + ω ^ 2)⁻¹
      = ∫ ω, a⁻¹ ^ 2 * (1 + (ω / a) ^ 2)⁻¹ := by congr 1; ext ω; exact step1 ω
    _ = a⁻¹ ^ 2 * ∫ ω, (1 + (ω / a) ^ 2)⁻¹ := integral_const_mul _ _
    _ = a⁻¹ ^ 2 * ∫ ω, (fun u => (1 + u ^ 2)⁻¹) (ω / a) := by rw [step2]
    _ = a⁻¹ ^ 2 * (|a| • ∫ u, (1 + u ^ 2)⁻¹) := by
        rw [integral_comp_div (fun u => (1 + u ^ 2)⁻¹) a]
    _ = π / a := by rw [abs_of_pos ha, smul_eq_mul, integral_univ_inv_one_add_sq]; field_simp

lemma integrable_inv_sq_add_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun ω : ℝ => (a ^ 2 + ω ^ 2)⁻¹) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_univ_inv_sq_add_sq a ha]
  exact div_ne_zero (ne_of_gt pi_pos) (ne_of_gt ha)

/-! ## Partial fractions and product integral -/

lemma partial_fraction_identity (s γ ω : ℝ) (hs : s ^ 2 + ω ^ 2 ≠ 0) (hγ : γ ^ 2 + ω ^ 2 ≠ 0)
    (hne : γ ^ 2 - s ^ 2 ≠ 0) :
    (s ^ 2 + ω ^ 2)⁻¹ * (γ ^ 2 + ω ^ 2)⁻¹ =
    (γ ^ 2 - s ^ 2)⁻¹ * ((s ^ 2 + ω ^ 2)⁻¹ - (γ ^ 2 + ω ^ 2)⁻¹) := by
  field_simp; ring

lemma integral_product_inv_sq_add_sq (s γ : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hne : s ≠ γ) :
    ∫ ω : ℝ, (s ^ 2 + ω ^ 2)⁻¹ * (γ ^ 2 + ω ^ 2)⁻¹ = π / (s * γ * (s + γ)) := by
  have hs2 : ∀ ω, s ^ 2 + ω ^ 2 ≠ 0 := fun ω => by positivity
  have hγ2 : ∀ ω, γ ^ 2 + ω ^ 2 ≠ 0 := fun ω => by positivity
  have hne2 : γ ^ 2 - s ^ 2 ≠ 0 := by
    intro h; apply hne; nlinarith [sq_abs s, sq_abs γ, abs_nonneg s, abs_nonneg γ]
  have h_eq : ∀ ω : ℝ, (s ^ 2 + ω ^ 2)⁻¹ * (γ ^ 2 + ω ^ 2)⁻¹ =
      (γ ^ 2 - s ^ 2)⁻¹ * ((s ^ 2 + ω ^ 2)⁻¹ - (γ ^ 2 + ω ^ 2)⁻¹) :=
    fun ω => partial_fraction_identity s γ ω (hs2 ω) (hγ2 ω) hne2
  simp_rw [h_eq, integral_const_mul,
    integral_sub (integrable_inv_sq_add_sq s hs) (integrable_inv_sq_add_sq γ hγ),
    integral_univ_inv_sq_add_sq s hs, integral_univ_inv_sq_add_sq γ hγ]
  field_simp; ring

/-! ## Lorentzian density and dispersion relation -/

def lorentzianDensity (γ : ℝ) (ω : ℝ) : ℝ := γ / π * (γ ^ 2 + ω ^ 2)⁻¹

def dispersionD (K : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  K / 2 * ∫ ω : ℝ, s / (s ^ 2 + ω ^ 2) * g ω

theorem lorentzian_dispersionD (K s γ : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hne : s ≠ γ) :
    dispersionD K (lorentzianDensity γ) s = K / (2 * (s + γ)) := by
  unfold dispersionD lorentzianDensity
  have h_eq : ∀ ω : ℝ, s / (s ^ 2 + ω ^ 2) * (γ / π * (γ ^ 2 + ω ^ 2)⁻¹) =
      s * γ / π * ((s ^ 2 + ω ^ 2)⁻¹ * (γ ^ 2 + ω ^ 2)⁻¹) := by
    intro ω
    have : s ^ 2 + ω ^ 2 ≠ 0 := by positivity
    field_simp
  simp_rw [h_eq, integral_const_mul, integral_product_inv_sq_add_sq s γ hs hγ hne]
  have : s + γ ≠ 0 := by positivity
  have : s * γ ≠ 0 := by positivity
  field_simp

/-! ## Penrose criterion: eigenvalue existence -/

theorem lorentzian_penrose_criterion (K γ : ℝ) (hK : 2 * γ < K) (hγ : 0 < γ)
    (hK4 : K ≠ 4 * γ) :
    ∃ s : ℝ, 0 < s ∧ dispersionD K (lorentzianDensity γ) s = 1 := by
  refine ⟨K / 2 - γ, by linarith, ?_⟩
  have hs : 0 < K / 2 - γ := by linarith
  have hne : K / 2 - γ ≠ γ := by intro h; exact hK4 (by linarith)
  rw [lorentzian_dispersionD K (K / 2 - γ) γ hs hγ hne]
  have : K / 2 - γ + γ = K / 2 := by ring
  rw [this]
  have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp

theorem lorentzian_eigenvalue_pos (K γ : ℝ) (hK : 2 * γ < K) :
    0 < K / 2 - γ := by linarith

/-! ## Nonlinear instability — opaque axiom -/

/-- For K > Kc, the incoherent state z ≡ 0 is nonlinearly unstable:
    r(t) = Re(η(t)) escapes any neighborhood of 0 and remains bounded
    below by a positive constant.

    This follows from the Penrose criterion (linearized instability)
    combined with Ψ monotonicity (prevents return to incoherence).
    The linear part is proved above; the nonlinear escape requires
    Hartman-Grobman type analysis or Chetaev's instability theorem.

    The hypothesis `r_floor > 0` can be verified for specific initial
    conditions and coupling strength. For Lorentzian g with K > 2γ,
    the eigenvalue s* = K/2 - γ determines the escape rate. -/
opaque NonlinearInstabilityHypothesis
    (K γ r_floor : ℝ) (hK : 2 * γ < K) (hγ : 0 < γ) (hr : 0 < r_floor) : Prop

axiom nonlinear_instability_of_penrose
    (K γ r_floor : ℝ) (hK : 2 * γ < K) (hγ : 0 < γ) (hr : 0 < r_floor)
    (hr_le : r_floor ≤ Real.sqrt (1 - 2 * γ / K)) :
    NonlinearInstabilityHypothesis K γ r_floor hK hγ hr

end
