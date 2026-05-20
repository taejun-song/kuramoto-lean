/-
  Penrose Criterion — Instability of the Incoherent State
  ========================================================
  For Lorentzian g(ω) = (γ/π)/(γ²+ω²), the dispersion relation
    D(s) = (K/2) ∫ s/(s²+ω²) g(ω) dω = K/(2(s+γ))
  has a positive root s* = K/2 - γ when K > 2γ = Kc.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

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

/-! ## Squared integral: ∫ (1+x²)⁻² = π/2 via antiderivative -/

private lemma hasDerivAt_antideriv (x : ℝ) :
    HasDerivAt (fun x => (x / (1 + x ^ 2) + arctan x) / 2)
      (((1 + x ^ 2) ^ 2)⁻¹) x := by
  have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hd : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  convert ((hasDerivAt_id x).div hd h1 |>.add (hasDerivAt_arctan' x)).div_const 2 using 1
  simp only [id]; field_simp; ring

private lemma integrable_inv_one_add_sq_sq :
    Integrable (fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹) := by
  apply integrable_inv_one_add_sq.mono
  · exact (((continuous_const.add (continuous_pow 2)).pow 2).inv₀ (fun x =>
      pow_ne_zero 2 (ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)))).aestronglyMeasurable
  · filter_upwards with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((1 + x ^ 2) ^ 2)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + x ^ 2)⁻¹)]
    exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)])

private lemma tendsto_div_one_add_sq_atTop :
    Tendsto (fun x : ℝ => x / (1 + x ^ 2)) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg hx (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxp : (0 : ℝ) < x := by linarith
    rw [show x⁻¹ = x / x ^ 2 from by field_simp]
    exact div_le_div_of_nonneg_left hxp.le (by positivity) (le_add_of_nonneg_left zero_le_one)

private lemma tendsto_antideriv_atTop :
    Tendsto (fun x : ℝ => (x / (1 + x ^ 2) + arctan x) / 2) atTop (nhds (π / 4)) := by
  have h1 := tendsto_div_one_add_sq_atTop
  have h2 : Tendsto arctan atTop (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  have h3 := (h1.add h2).div_const 2
  simp only [zero_add] at h3
  rwa [show (π / 2 : ℝ) / 2 = π / 4 from by ring] at h3

private lemma tendsto_antideriv_atBot :
    Tendsto (fun x : ℝ => (x / (1 + x ^ 2) + arctan x) / 2) atBot (nhds (-(π / 4))) := by
  have h1 : Tendsto (fun x : ℝ => x / (1 + x ^ 2)) atBot (nhds 0) := by
    have h := tendsto_div_one_add_sq_atTop.comp tendsto_neg_atBot_atTop
    simp only [Function.comp_def, neg_sq] at h
    simpa [neg_div] using h.neg
  have h2 : Tendsto arctan atBot (nhds (-(π / 2))) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot
  have h3 := (h1.add h2).div_const 2
  simp only [zero_add] at h3
  rwa [show (-(π / 2) : ℝ) / 2 = -(π / 4) from by ring] at h3

lemma integral_univ_inv_one_add_sq_sq :
    ∫ x : ℝ, ((1 + x ^ 2) ^ 2)⁻¹ = π / 2 := by
  have := integral_of_hasDerivAt_of_tendsto hasDerivAt_antideriv integrable_inv_one_add_sq_sq
    tendsto_antideriv_atBot tendsto_antideriv_atTop
  linarith

/-! ## Squared base integral: ∫ (a²+ω²)⁻² = π/(2a³) -/

lemma integral_univ_inv_sq_add_sq_sq (a : ℝ) (ha : 0 < a) :
    ∫ ω : ℝ, ((a ^ 2 + ω ^ 2) ^ 2)⁻¹ = π / (2 * a ^ 3) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have step1 : ∀ ω : ℝ, ((a ^ 2 + ω ^ 2) ^ 2)⁻¹ =
      a⁻¹ ^ 4 * ((1 + (ω / a) ^ 2) ^ 2)⁻¹ := by
    intro ω; field_simp
  have step2 : (fun ω : ℝ => ((1 + (ω / a) ^ 2) ^ 2)⁻¹) =
      fun ω => (fun u => ((1 + u ^ 2) ^ 2)⁻¹) (ω / a) := by ext ω; simp [div_pow]
  calc ∫ ω, ((a ^ 2 + ω ^ 2) ^ 2)⁻¹
      = ∫ ω, a⁻¹ ^ 4 * ((1 + (ω / a) ^ 2) ^ 2)⁻¹ := by congr 1; ext ω; exact step1 ω
    _ = a⁻¹ ^ 4 * ∫ ω, ((1 + (ω / a) ^ 2) ^ 2)⁻¹ := integral_const_mul _ _
    _ = a⁻¹ ^ 4 * ∫ ω, (fun u => ((1 + u ^ 2) ^ 2)⁻¹) (ω / a) := by rw [step2]
    _ = a⁻¹ ^ 4 * (|a| • ∫ u, ((1 + u ^ 2) ^ 2)⁻¹) := by
        rw [integral_comp_div (fun u => ((1 + u ^ 2) ^ 2)⁻¹) a]
    _ = π / (2 * a ^ 3) := by
        rw [abs_of_pos ha, smul_eq_mul, integral_univ_inv_one_add_sq_sq]; field_simp

lemma integrable_inv_sq_add_sq_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun ω : ℝ => ((a ^ 2 + ω ^ 2) ^ 2)⁻¹) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_univ_inv_sq_add_sq_sq a ha]
  exact div_ne_zero (ne_of_gt pi_pos) (mul_ne_zero two_ne_zero (ne_of_gt (by positivity)))

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

lemma integral_product_inv_sq_add_sq_self (a : ℝ) (ha : 0 < a) :
    ∫ ω : ℝ, (a ^ 2 + ω ^ 2)⁻¹ * (a ^ 2 + ω ^ 2)⁻¹ = π / (2 * a ^ 3) := by
  have h_eq : ∀ ω : ℝ, (a ^ 2 + ω ^ 2)⁻¹ * (a ^ 2 + ω ^ 2)⁻¹ =
      ((a ^ 2 + ω ^ 2) ^ 2)⁻¹ := by
    intro ω; rw [← mul_inv, ← sq]
  simp_rw [h_eq]
  exact integral_univ_inv_sq_add_sq_sq a ha

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

theorem lorentzian_dispersionD_self (K γ : ℝ) (hγ : 0 < γ) :
    dispersionD K (lorentzianDensity γ) γ = K / (4 * γ) := by
  unfold dispersionD lorentzianDensity
  have h_eq : ∀ ω : ℝ, γ / (γ ^ 2 + ω ^ 2) * (γ / π * (γ ^ 2 + ω ^ 2)⁻¹) =
      γ ^ 2 / π * ((γ ^ 2 + ω ^ 2)⁻¹ * (γ ^ 2 + ω ^ 2)⁻¹) := by
    intro ω
    have : γ ^ 2 + ω ^ 2 ≠ 0 := by positivity
    field_simp
  simp_rw [h_eq, integral_const_mul, integral_product_inv_sq_add_sq_self γ hγ]
  field_simp; ring

/-! ## Penrose criterion: eigenvalue existence -/

theorem lorentzian_penrose_criterion (K γ : ℝ) (hK : 2 * γ < K) (hγ : 0 < γ) :
    ∃ s : ℝ, 0 < s ∧ dispersionD K (lorentzianDensity γ) s = 1 := by
  by_cases hK4 : K = 4 * γ
  · refine ⟨γ, hγ, ?_⟩
    rw [lorentzian_dispersionD_self K γ hγ, hK4]
    field_simp
  · refine ⟨K / 2 - γ, by linarith, ?_⟩
    have hs : 0 < K / 2 - γ := by linarith
    have hne : K / 2 - γ ≠ γ := by intro h; exact hK4 (by linarith)
    rw [lorentzian_dispersionD K (K / 2 - γ) γ hs hγ hne]
    have : K / 2 - γ + γ = K / 2 := by ring
    rw [this]
    have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt (by linarith)
    field_simp

theorem lorentzian_eigenvalue_pos (K γ : ℝ) (hK : 2 * γ < K) :
    0 < K / 2 - γ := by linarith

end
