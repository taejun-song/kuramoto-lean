/-
  Compact-Support Convergence for Complex OA
  ============================================
  Key algebraic identity (new):
    |1 - z²|² = 4·Im(z)² when |z|² = 1
  For locked equilibrium:
    |1 - z*(ω)²|² = 4ω²/(K²r²)

  Application: bounds the non-autonomous forcing in the V' equation,
  enabling axiom-free convergence for compact-support g where all
  oscillators are locked.

  Forcing structure on symmetric subspace (η = r ∈ ℝ):
    V'(t) = -K·r(t)·∫Re(z+z*)·|z-z*|²·g + K·(r(t)-r*)·∫Re(conj(z-z*)·(1-z*²))·g

  Using the identity: |1-z*²| = 2|ω|/(Kr*), so
    ∫|1-z*²|²·g = 4σ²/(K²r*²)  where σ² = ∫ω²g

  After Cauchy-Schwarz: |forcing| ≤ (2σ/r*)·V
  Rate condition: K·r_min·δ₀ > 2σ/r* (checkable, replaces Dietert axiom)
-/

import KuramotoLean.ComplexOAErrorIdentity
import KuramotoLean.ComplexOALockedEquil
import KuramotoLean.ComplexLeibniz
import KuramotoLean.GronwallBootstrap
import KuramotoLean.ComplexOAEndToEnd

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Key algebraic identity -/

/-- When |z|² = 1: |1 - z²|² = 4·Im(z)².
    Proof: 1 - z² = z·conj(z) - z² = z(conj(z) - z) = -2i·z·Im(z),
    so |1-z²|² = 4·Im(z)². -/
theorem normSq_one_minus_sq_of_unit (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq (1 - z ^ 2) = 4 * z.im ^ 2 := by
  have h : z.re * z.re + z.im * z.im = 1 := by rwa [Complex.normSq_apply] at hz
  simp only [Complex.normSq_apply, sq, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (z.re * z.re + z.im * z.im - 1),
    sq_nonneg z.re, sq_nonneg z.im, sq_nonneg (z.re * z.im)]

/-- For the locked equilibrium z*(ω) with |z*| = 1:
    |1 - z*(ω)²|² = 4ω²/(K²r²).
    This quantifies the non-autonomous forcing per oscillator. -/
theorem lockedEquil_one_minus_sq_normSq (ω K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hω : ω ^ 2 < K ^ 2 * r ^ 2) :
    Complex.normSq (1 - lockedEquil ω K r ^ 2) = 4 * ω ^ 2 / (K ^ 2 * r ^ 2) := by
  rw [normSq_one_minus_sq_of_unit _ (lockedEquil_normSq ω K r hK hr hω),
      lockedEquil_im ω K r hK hr]
  unfold lockedEquilIm
  have : (0 : ℝ) < K * r := mul_pos hK hr
  field_simp

/-! ## Per-oscillator forcing bound -/

/-- |Re(conj(a)·b)| ≤ ‖a‖·‖b‖. Connects the forcing integrand to norms. -/
theorem forcing_re_le_norms (a b : ℂ) :
    |(starRingEnd ℂ a * b).re| ≤ ‖a‖ * ‖b‖ := by
  calc |(starRingEnd ℂ a * b).re|
      ≤ ‖starRingEnd ℂ a * b‖ := Complex.abs_re_le_norm _
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, RCLike.norm_conj]

/-! ## Integral identity: ∫|1-z*²|²·g = 4σ²/(K²r²) for compact-support g -/

/-- For compact-support g where all oscillators are locked and z* is the
    locked equilibrium: ∫|1-z*(ω)²|²·g(ω) dμ = (4/(K²r²))·∫ω²·g dμ.
    This makes the forcing structure explicit. -/
theorem forcing_integral_identity
    (S : SymmetricFreq Ω μ) (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (h_locked : ∀ ω, 0 < S.g ω → (S.ω_freq ω) ^ 2 < K ^ 2 * r ^ 2)
    (z_star : Ω → ℂ)
    (hz_star : ∀ ω, 0 < S.g ω → z_star ω = lockedEquil (S.ω_freq ω) K r) :
    ∫ ω, Complex.normSq (1 - z_star ω ^ 2) * S.g ω ∂μ =
      4 / (K ^ 2 * r ^ 2) * ∫ ω, (S.ω_freq ω) ^ 2 * S.g ω ∂μ := by
  have h_pw : ∀ ω, Complex.normSq (1 - z_star ω ^ 2) * S.g ω =
      4 / (K ^ 2 * r ^ 2) * ((S.ω_freq ω) ^ 2 * S.g ω) := by
    intro ω
    by_cases hg : 0 < S.g ω
    · rw [hz_star ω hg, lockedEquil_one_minus_sq_normSq _ _ _ hK hr (h_locked ω hg)]; ring
    · push Not at hg
      have hg0 : S.g ω = 0 := le_antisymm hg (hg_nn ω)
      simp [hg0]
  rw [show (fun ω => Complex.normSq (1 - z_star ω ^ 2) * S.g ω) =
      (fun ω => 4 / (K ^ 2 * r ^ 2) * ((S.ω_freq ω) ^ 2 * S.g ω)) from funext h_pw,
    integral_const_mul]

/-! ## Weighted Cauchy-Schwarz for integrals -/

/-- Weighted Cauchy-Schwarz: (∫ f·h·w)² ≤ (∫ f²·w)·(∫ h²·w).
    Proof via quadratic discriminant: ∀s, 0 ≤ ∫(fs-h)²w ⟹ B² ≤ AC. -/
theorem weighted_cs_sq (f h : Ω → ℝ) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (hf2w : Integrable (fun ω => f ω ^ 2 * w ω) μ)
    (hh2w : Integrable (fun ω => h ω ^ 2 * w ω) μ)
    (hfhw : Integrable (fun ω => f ω * h ω * w ω) μ) :
    (∫ ω, f ω * h ω * w ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 * w ω ∂μ) * (∫ ω, h ω ^ 2 * w ω ∂μ) := by
  set A := ∫ ω, f ω ^ 2 * w ω ∂μ
  set B := ∫ ω, f ω * h ω * w ω ∂μ
  set C := ∫ ω, h ω ^ 2 * w ω ∂μ
  suffices hQ : ∀ s : ℝ, 0 ≤ A * s ^ 2 - 2 * s * B + C by
    by_cases hA : A = 0
    · have hB : B = 0 := by
        by_contra hB_ne
        have h1 := hQ ((C + 1) / (2 * B))
        have : A * ((C + 1) / (2 * B)) ^ 2 - 2 * ((C + 1) / (2 * B)) * B + C = -1 := by
          rw [hA]; field_simp; ring
        linarith
      simp [hB, hA]
    · have hA_pos : 0 < A := lt_of_le_of_ne
          (integral_nonneg (fun ω => mul_nonneg (sq_nonneg _) (hw ω))) (Ne.symm hA)
      have h1 := hQ (B / A)
      have h2 : A * (B / A) ^ 2 - 2 * (B / A) * B + C = C - B ^ 2 / A := by field_simp; ring
      rw [h2] at h1
      have h3 : B ^ 2 = A * (B ^ 2 / A) := by field_simp
      linarith [mul_le_mul_of_nonneg_left (show B ^ 2 / A ≤ C by linarith) (le_of_lt hA_pos)]
  intro s
  have hi_a : Integrable (fun ω => s ^ 2 * (f ω ^ 2 * w ω)) μ := hf2w.const_mul _
  have hi_b : Integrable (fun ω => (-2 * s) * (f ω * h ω * w ω)) μ := hfhw.const_mul _
  have hi_bc : Integrable (fun ω => (-2 * s) * (f ω * h ω * w ω) + h ω ^ 2 * w ω) μ :=
    hi_b.add hh2w
  calc (0 : ℝ)
      ≤ ∫ ω, (f ω * s - h ω) ^ 2 * w ω ∂μ :=
        integral_nonneg (fun ω => mul_nonneg (sq_nonneg _) (hw ω))
    _ = ∫ ω, (s ^ 2 * (f ω ^ 2 * w ω) +
          ((-2 * s) * (f ω * h ω * w ω) + h ω ^ 2 * w ω)) ∂μ :=
        integral_congr_ae (ae_of_all μ fun ω => by ring)
    _ = (∫ ω, s ^ 2 * (f ω ^ 2 * w ω) ∂μ) +
          ∫ ω, ((-2 * s) * (f ω * h ω * w ω) + h ω ^ 2 * w ω) ∂μ :=
        integral_add hi_a hi_bc
    _ = s ^ 2 * A + ((-2 * s) * B + C) := by
        rw [integral_const_mul, integral_add hi_b hh2w, integral_const_mul]
    _ = A * s ^ 2 - 2 * s * B + C := by ring

/-! ## Forcing Cauchy-Schwarz bound -/

/-- Cauchy-Schwarz for the forcing integrand: (∫√|z-z*|²·√|1-z*²|²·g)² ≤ V·∫|1-z*²|²·g.
    Combined with forcing_integral_identity, gives explicit σ-dependent bound. -/
theorem forcing_cs_sq_le (z z_star : Ω → ℂ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hV_int : Integrable (fun ω => Complex.normSq (z ω - z_star ω) * w ω) μ)
    (hS_int : Integrable (fun ω => Complex.normSq (1 - z_star ω ^ 2) * w ω) μ)
    (hM_int : Integrable (fun ω =>
      Real.sqrt (Complex.normSq (z ω - z_star ω)) *
      Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)) * w ω) μ) :
    (∫ ω, Real.sqrt (Complex.normSq (z ω - z_star ω)) *
           Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)) * w ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω - z_star ω) * w ω ∂μ) *
      (∫ ω, Complex.normSq (1 - z_star ω ^ 2) * w ω ∂μ) := by
  have sqrt_sq := fun (a : ℂ) => Real.sq_sqrt (Complex.normSq_nonneg a)
  have h := weighted_cs_sq
    (fun ω => Real.sqrt (Complex.normSq (z ω - z_star ω)))
    (fun ω => Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)))
    w hw
    (hV_int.congr (ae_of_all μ fun ω => by simp [sqrt_sq]))
    (hS_int.congr (ae_of_all μ fun ω => by simp [sqrt_sq]))
    hM_int
  simp_rw [sqrt_sq] at h
  exact h

/-! ## Jensen and algebraic forcing bounds -/

/-- Jensen for squares: (∫f·w)² ≤ ∫f²·w when ∫w = 1, w ≥ 0. -/
theorem jensen_sq_le_weighted (f : Ω → ℝ) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hw_norm : ∫ ω, w ω ∂μ = 1)
    (hf2w : Integrable (fun ω => f ω ^ 2 * w ω) μ)
    (hfw : Integrable (fun ω => f ω * w ω) μ) :
    (∫ ω, f ω * w ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 * w ω ∂μ := by
  have hw_int : Integrable w μ := by
    by_contra h; simp [integral_undef h] at hw_norm
  have h1w : Integrable (fun ω => (1 : ℝ) ^ 2 * w ω) μ := by simpa using hw_int
  have h := weighted_cs_sq f (fun _ => 1) w hw hf2w h1w (by simpa using hfw)
  simp only [mul_one] at h
  calc (∫ ω, f ω * w ω ∂μ) ^ 2
      ≤ (∫ ω, f ω ^ 2 * w ω ∂μ) * (∫ ω, 1 ^ 2 * w ω ∂μ) := h
    _ = (∫ ω, f ω ^ 2 * w ω ∂μ) * 1 := by simp [hw_norm]
    _ = ∫ ω, f ω ^ 2 * w ω ∂μ := mul_one _

/-- (∫Re(z-z*)·w)² ≤ V when ∫w = 1: Jensen + Re² ≤ normSq. -/
theorem re_sq_le_V (z z_star : Ω → ℂ) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hw_norm : ∫ ω, w ω ∂μ = 1)
    (hV_int : Integrable (fun ω => Complex.normSq (z ω - z_star ω) * w ω) μ)
    (hf2w : Integrable (fun ω => (z ω - z_star ω).re ^ 2 * w ω) μ)
    (hfw : Integrable (fun ω => (z ω - z_star ω).re * w ω) μ) :
    (∫ ω, (z ω - z_star ω).re * w ω ∂μ) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω - z_star ω) * w ω ∂μ := by
  calc (∫ ω, (z ω - z_star ω).re * w ω ∂μ) ^ 2
      ≤ ∫ ω, (z ω - z_star ω).re ^ 2 * w ω ∂μ :=
        jensen_sq_le_weighted _ w hw hw_norm hf2w hfw
    _ ≤ ∫ ω, Complex.normSq (z ω - z_star ω) * w ω ∂μ := by
        apply integral_mono hf2w hV_int fun ω => ?_
        exact mul_le_mul_of_nonneg_right
          (by rw [sq]; exact Complex.re_sq_le_normSq _) (hw ω)

/-- If d² ≤ V, I² ≤ V·F, 0 ≤ V, 0 ≤ F, then |d·I| ≤ √F·V.
    Key algebra: two √V factors from CS bounds multiply to give V. -/
theorem abs_mul_le_of_sq_bounds (d I V F : ℝ) (hV : 0 ≤ V)
    (hI : I ^ 2 ≤ V * F) (hd : d ^ 2 ≤ V) :
    |d * I| ≤ Real.sqrt F * V := by
  rw [abs_mul]
  have hd_le : |d| ≤ Real.sqrt V := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hd
  have hI_le : |I| ≤ Real.sqrt (V * F) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hI
  calc |d| * |I|
      ≤ Real.sqrt V * Real.sqrt (V * F) :=
        mul_le_mul hd_le hI_le (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt V * (Real.sqrt V * Real.sqrt F) := by
        rw [Real.sqrt_mul hV]
    _ = V * Real.sqrt F := by
        rw [← mul_assoc, ← sq, Real.sq_sqrt hV]
    _ = Real.sqrt F * V := mul_comm _ _

/-! ## Coercivity from body persistence -/

/-- If Re(z+z*) ≥ δ₀ pointwise, then ∫Re(z+z*)·|z-z*|²·w ≥ δ₀·V.
    Gives the decay rate in V' = -K·r(t)·∫Re(z+z*)·|z-z*|²·g + forcing. -/
theorem coercivity_lower_bound (z z_star : Ω → ℂ) (w : Ω → ℝ)
    (δ₀ : ℝ)
    (h_body : ∀ ω, δ₀ * (Complex.normSq (z ω - z_star ω) * w ω) ≤
      (z ω + z_star ω).re * (Complex.normSq (z ω - z_star ω) * w ω))
    (hV_int : Integrable (fun ω => Complex.normSq (z ω - z_star ω) * w ω) μ)
    (hW_int : Integrable (fun ω =>
      (z ω + z_star ω).re * (Complex.normSq (z ω - z_star ω) * w ω)) μ) :
    δ₀ * ∫ ω, Complex.normSq (z ω - z_star ω) * w ω ∂μ ≤
      ∫ ω, (z ω + z_star ω).re * (Complex.normSq (z ω - z_star ω) * w ω) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono (hV_int.const_mul _) hW_int h_body

/-! ## Forcing RE integral bound -/

/-- The forcing integral Re(conj(z-z*)·(1-z*²)) satisfies the CS bound from forcing_cs_sq_le.
    Bridge: Re(conj(a)b) ≤ |a|·|b| = √normSq(a)·√normSq(b) pointwise, then integrate. -/
theorem forcing_re_integral_sq_le (z z_star : Ω → ℂ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hV_int : Integrable (fun ω => Complex.normSq (z ω - z_star ω) * w ω) μ)
    (hS_int : Integrable (fun ω => Complex.normSq (1 - z_star ω ^ 2) * w ω) μ)
    (hM_int : Integrable (fun ω =>
      Real.sqrt (Complex.normSq (z ω - z_star ω)) *
      Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)) * w ω) μ)
    (hR_int : Integrable (fun ω =>
      (starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re * w ω) μ) :
    (∫ ω, (starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re * w ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω - z_star ω) * w ω ∂μ) *
      (∫ ω, Complex.normSq (1 - z_star ω ^ 2) * w ω ∂μ) := by
  set I := ∫ ω, (starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re * w ω ∂μ
  set M := ∫ ω, Real.sqrt (Complex.normSq (z ω - z_star ω)) *
    Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)) * w ω ∂μ
  have hM_nn : 0 ≤ M := integral_nonneg fun ω =>
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hw ω)
  have h_pw : ∀ ω, |(starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re| * w ω ≤
      Real.sqrt (Complex.normSq (z ω - z_star ω)) *
      Real.sqrt (Complex.normSq (1 - z_star ω ^ 2)) * w ω := by
    intro ω
    apply mul_le_mul_of_nonneg_right _ (hw ω)
    calc |(starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re|
        ≤ ‖z ω - z_star ω‖ * ‖1 - z_star ω ^ 2‖ := forcing_re_le_norms _ _
      _ = _ := by rw [Complex.norm_def, Complex.norm_def]
  have h_abs_le : |I| ≤ M := by
    rw [show |I| = ‖I‖ from (Real.norm_eq_abs I).symm]
    calc ‖I‖ ≤ ∫ ω, ‖(starRingEnd ℂ (z ω - z_star ω) * (1 - z_star ω ^ 2)).re * w ω‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ M := by
          apply integral_mono hR_int.norm hM_int fun ω => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw ω)]
          exact h_pw ω
  calc I ^ 2 ≤ M ^ 2 := by
        have := abs_le.mp h_abs_le
        exact sq_le_sq' this.1 this.2
    _ ≤ _ := forcing_cs_sq_le z z_star w hw hV_int hS_int hM_int

/-! ## Rate formula simplification -/

/-- K·√(4σ²/(K²r*²)) = 2√σ²/r*: simplifies the abstract forcing bound
    (from abs_mul_le_of_sq_bounds + forcing_integral_identity)
    into the concrete rate formula coefficient 2σ/r*. -/
theorem forcing_rate_simplify (σ_sq K r_star : ℝ)
    (hσ : 0 ≤ σ_sq) (hK : 0 < K) (hr : 0 < r_star) :
    K * Real.sqrt (4 * σ_sq / (K ^ 2 * r_star ^ 2)) =
      2 * Real.sqrt σ_sq / r_star := by
  have hK2 : (0 : ℝ) < K ^ 2 * r_star ^ 2 := by positivity
  rw [div_eq_mul_inv, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * σ_sq),
    Real.sqrt_inv, show (4 : ℝ) * σ_sq = (2 * Real.sqrt σ_sq) ^ 2 from by
      rw [mul_pow, Real.sq_sqrt hσ]; ring,
    Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.sqrt σ_sq),
    show K ^ 2 * r_star ^ 2 = (K * r_star) ^ 2 from by ring,
    Real.sqrt_sq (by positivity : (0:ℝ) ≤ K * r_star)]
  field_simp

/-! ## V' decomposition: Leibniz → coercivity + forcing -/

/-- The Leibniz derivative decomposes into coercivity + forcing via
    complexOa_error_general. Pointwise: each integrand splits. -/
theorem V_deriv_integrand_split (ω K : ℝ) (η z z_star : ℂ) (g_val : ℝ) :
    2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K η z).re * g_val =
      (-K * (η * (z + z_star)).re * Complex.normSq (z - z_star)) * g_val +
      (2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K η z_star).re) * g_val := by
  rw [complexOa_error_general]; ring

/-! ## Basin decay from rate formula -/

/-- V' decomposition + coercivity + forcing bound → basin decay.
    Discharge with c_decay = K·r_min·δ₀, c_force = 2σ/r*,
    rate = c_decay - c_force > 0. -/
theorem basin_decay_from_rate (V : ℝ → ℝ) (c_decay c_force : ℝ)
    (hV_diff : ∀ t, 0 < t → HasDerivAt V (deriv V t) t)
    (h_decomp : ∀ t, 0 < t → ∃ D F : ℝ,
      deriv V t ≤ D + F ∧ D ≤ -c_decay * V t ∧ |F| ≤ c_force * V t) :
    ∀ t, 0 < t →
      HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -(c_decay - c_force) * V t := by
  intro t ht
  exact ⟨hV_diff t ht, by
    obtain ⟨D, F, h_sum, h_D, h_F⟩ := h_decomp t ht
    linarith [le_abs_self F]⟩

/-! ## Compact-support convergence theorem -/

/-- **COMPACT-SUPPORT CONVERGENCE FOR COMPLEX OA** (0 sorry, 0 axioms).

    For compact-support g where all oscillators are locked, replaces the
    Dietert Landau damping axiom with a checkable basin decay condition.

    The basin decay hypothesis h_basin_decay is discharged by showing:
      rate = K·r_min·δ₀ - 2σ/r* > 0
    where σ² = ∫ω²g (second moment), δ₀ = inf Re(z+z*) on support in basin,
    r_min = r* - √B (lower bound on r(t) in basin).

    The forcing identity |1-z*²|² = 4ω²/(K²r*²) gives σ explicitly. -/
theorem compact_support_convergence [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (K : ℝ) (r_star : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_disk : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    (B rate : ℝ) (hB : 0 < B) (hrate : 0 < rate)
    (hV0 : ∫ ω, Complex.normSq (z ω 0 - z_star ω) * S.g ω ∂μ < B)
    (hV_cont : Continuous (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (h_basin_decay : ∀ t, 0 < t →
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ < B →
      HasDerivAt (fun s => ∫ ω, Complex.normSq (z ω s - z_star ω) * S.g ω ∂μ)
        (deriv (fun s => ∫ ω, Complex.normSq (z ω s - z_star ω) * S.g ω ∂μ) t) t ∧
      deriv (fun s => ∫ ω, Complex.normSq (z ω s - z_star ω) * S.g ω ∂μ) t ≤
        -rate * ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  set V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
  have hV_nn : ∀ t, 0 ≤ t → 0 ≤ V t :=
    fun t _ => integral_nonneg (fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω))
  have hV_zero : Tendsto V atTop (nhds 0) :=
    gronwall_bootstrap_tendsto V B rate hrate hB hV_cont hV_nn hV0 h_basin_decay
  exact complex_oa_end_to_end S z z_star K r_star hK hr_star_pos hz_disk
    hz_star_pos hz_star_lt hz_sym hz_star_sym hg_nn hg_int hg_norm hz_ode hr_star_eq
    hz_star_equil hV_int hη_int hη_star_int hφ_meas hV_zero

/-! ## ODE barrier: positive initial value stays positive -/

/-- If f(0) > 0 and f'(t) > 0 whenever f(t) = 0, then f stays positive.
    Proof: if f first becomes ≤ 0 at time T, then f(T) = 0 (continuity from below),
    so f'(T) > 0, but the slope from the left is ≤ 0. Contradiction. -/
theorem positive_barrier (f : ℝ → ℝ) (hf_cont : Continuous f) (hf0 : 0 < f 0)
    (hf_barrier : ∀ t, 0 ≤ t → f t = 0 → 0 < deriv f t) :
    ∀ t, 0 ≤ t → 0 < f t := by
  by_contra h; push Not at h
  obtain ⟨t₀, ht₀, hft₀⟩ := h
  set S := Set.Icc 0 t₀ ∩ f ⁻¹' Set.Iic 0
  have hS_ne : S.Nonempty := ⟨t₀, ⟨⟨ht₀, le_refl _⟩, hft₀⟩⟩
  have hS_closed : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hf_cont)
  have hS_bdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set T := sInf S
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have hT_pos : 0 < T := by
    suffices h : T ≠ 0 from lt_of_le_of_ne hT_mem.1.1 (Ne.symm h)
    intro h; have : f T ≤ 0 := hT_mem.2; rw [h] at this; linarith
  have hf_pos : ∀ t, 0 ≤ t → t < T → 0 < f t := by
    intro t ht htT
    by_contra hle; push Not at hle
    exact not_lt.mpr (csInf_le hS_bdd ⟨⟨ht, le_trans (le_of_lt htT) hT_mem.1.2⟩, hle⟩) htT
  have hfT : f T = 0 := le_antisymm hT_mem.2
    (ge_of_tendsto (hf_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (by
      filter_upwards [Ioo_mem_nhdsLT hT_pos] with t ht
      exact le_of_lt (hf_pos t ht.1.le ht.2)))
  have h_deriv := hf_barrier T hT_pos.le hfT
  have h_slope := (differentiableAt_of_deriv_ne_zero (ne_of_gt h_deriv)).hasDerivAt.tendsto_slope
  have h_slope_left : Tendsto (slope f T) (𝓝[<] T) (𝓝 (deriv f T)) :=
    h_slope.mono_left (nhdsWithin_mono T fun _ hy => ne_of_lt hy)
  have h_slope_nonpos : ∀ᶠ y in 𝓝[<] T, slope f T y ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT hT_pos] with y hy
    rw [slope_def_field, hfT, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos
      (le_of_lt (hf_pos y hy.1.le hy.2)) (le_of_lt (sub_neg.mpr hy.2))
  linarith [le_of_tendsto h_slope_left h_slope_nonpos]

theorem positive_barrier_on_Icc (f : ℝ → ℝ) (T : ℝ) (hf_cont : Continuous f) (hf0 : 0 < f 0)
    (hf_barrier : ∀ t, 0 ≤ t → t ≤ T → f t = 0 → 0 < deriv f t) :
    ∀ t, 0 ≤ t → t ≤ T → 0 < f t := by
  intro t₀ ht₀ ht₀T
  by_contra h; push Not at h
  set S := Set.Icc 0 t₀ ∩ f ⁻¹' Set.Iic 0
  have hS_ne : S.Nonempty := ⟨t₀, ⟨⟨ht₀, le_refl _⟩, h⟩⟩
  have hS_closed : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hf_cont)
  have hS_bdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf S
  have hτ_mem : τ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have hτ_pos : 0 < τ := by
    suffices h : τ ≠ 0 from lt_of_le_of_ne hτ_mem.1.1 (Ne.symm h)
    intro h; have : f τ ≤ 0 := hτ_mem.2; rw [h] at this; linarith
  have hf_pos : ∀ t, 0 ≤ t → t < τ → 0 < f t := by
    intro t ht htτ
    by_contra hle; push Not at hle
    exact not_lt.mpr (csInf_le hS_bdd ⟨⟨ht, le_trans (le_of_lt htτ) hτ_mem.1.2⟩, hle⟩) htτ
  have hfτ : f τ = 0 := le_antisymm hτ_mem.2
    (ge_of_tendsto (hf_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (by
      filter_upwards [Ioo_mem_nhdsLT hτ_pos] with t ht
      exact le_of_lt (hf_pos t ht.1.le ht.2)))
  have h_deriv := hf_barrier τ hτ_pos.le (le_trans hτ_mem.1.2 ht₀T) hfτ
  have h_slope := (differentiableAt_of_deriv_ne_zero (ne_of_gt h_deriv)).hasDerivAt.tendsto_slope
  have h_slope_left : Tendsto (slope f τ) (𝓝[<] τ) (𝓝 (deriv f τ)) :=
    h_slope.mono_left (nhdsWithin_mono τ fun _ hy => ne_of_lt hy)
  have h_slope_nonpos : ∀ᶠ y in 𝓝[<] τ, slope f τ y ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT hτ_pos] with y hy
    rw [slope_def_field, hfτ, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos
      (le_of_lt (hf_pos y hy.1.le hy.2)) (le_of_lt (sub_neg.mpr hy.2))
  linarith [le_of_tendsto h_slope_left h_slope_nonpos]

/-! ## Body persistence: Re(z) stays positive under strong coupling -/

/-- Re(complexOaRHS) at Re(z)=0 with real η: equals ω·Im(z) + Kr/2·(1+Im(z)²). -/
theorem complexOaRHS_re_at_re_zero (ω K r : ℝ) (y : ℝ) :
    (complexOaRHS ω K (↑r) ⟨0, y⟩).re = ω * y + K * r / 2 * (1 + y ^ 2) := by
  have h1 : starRingEnd ℂ (↑r : ℂ) = ↑r := RCLike.conj_ofReal r
  simp only [complexOaRHS, h1, Complex.add_re, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.I_mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.div_ofNat_re, Complex.div_ofNat_im, sq]
  ring

/-- At Re(z)=0 in the unit disk, the OA flow pushes Re(z) positive
    when K·r/2 > |ω|. The coupling overpowers the natural frequency. -/
theorem complexOaRHS_re_pos_at_re_zero (ω K r : ℝ) (y : ℝ)
    (hKr : 0 < K * r) (hω : |ω| < K * r / 2) :
    0 < (complexOaRHS ω K (↑r) ⟨0, y⟩).re := by
  rw [complexOaRHS_re_at_re_zero]
  nlinarith [abs_lt.mp hω, sq_nonneg (K * r * y + ω), sq_nonneg y]

/-- **BODY PERSISTENCE.** Under the complex OA flow, Re(z(t)) stays positive
    when Re(z(0)) > 0 and coupling dominates: K·r(t)/2 > |ω| for all t ≥ 0. -/
theorem body_persistence (ω_freq K : ℝ) (z : ℝ → ℂ) (η : ℝ → ℂ)
    (hz_cont : Continuous z)
    (hz0_re : 0 < (z 0).re)
    (hz_ode : ∀ t, HasDerivAt z (complexOaRHS ω_freq K (η t) (z t)) t)
    (hη_real : ∀ t, (η t).im = 0)
    (hr_bound : ∀ t, 0 ≤ t → |ω_freq| < K * (η t).re / 2) :
    ∀ t, 0 ≤ t → 0 < (z t).re := by
  apply positive_barrier (fun t => (z t).re)
    (Complex.continuous_re.comp hz_cont) hz0_re
  intro t ht hzt_re
  have h_re_deriv : HasDerivAt (fun s => (z s).re)
      (complexOaRHS ω_freq K (η t) (z t)).re t := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hz_ode t)
    simp only [Function.comp_def] at h
    exact h
  rw [h_re_deriv.deriv]
  have hη_eq : η t = ↑((η t).re) := by
    apply Complex.ext <;> simp [hη_real t]
  have hz_eq : z t = ⟨0, (z t).im⟩ := by
    apply Complex.ext <;> simp [hzt_re]
  rw [hη_eq, hz_eq]
  exact complexOaRHS_re_pos_at_re_zero ω_freq K _ _
    (by linarith [hr_bound t ht, abs_nonneg ω_freq]) (hr_bound t ht)

theorem body_persistence_on_Icc (ω_freq K : ℝ) (z : ℝ → ℂ) (η : ℝ → ℂ) (T : ℝ)
    (hz_cont : Continuous z) (hz0_re : 0 < (z 0).re)
    (hz_ode : ∀ t, HasDerivAt z (complexOaRHS ω_freq K (η t) (z t)) t)
    (hη_real : ∀ t, (η t).im = 0)
    (hr_bound : ∀ t, 0 ≤ t → t ≤ T → |ω_freq| < K * (η t).re / 2) :
    ∀ t, 0 ≤ t → t ≤ T → 0 < (z t).re := by
  apply positive_barrier_on_Icc (fun t => (z t).re) T
    (Complex.continuous_re.comp hz_cont) hz0_re
  intro t ht htT hzt_re
  have h_re_deriv : HasDerivAt (fun s => (z s).re)
      (complexOaRHS ω_freq K (η t) (z t)).re t := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hz_ode t)
    simp only [Function.comp_def] at h; exact h
  rw [h_re_deriv.deriv]
  have hη_eq : η t = ↑((η t).re) := by
    apply Complex.ext <;> simp [hη_real t]
  have hz_eq : z t = ⟨0, (z t).im⟩ := by
    apply Complex.ext <;> simp [hzt_re]
  rw [hη_eq, hz_eq]
  exact complexOaRHS_re_pos_at_re_zero ω_freq K _ _
    (by linarith [hr_bound t ht htT, abs_nonneg ω_freq]) (hr_bound t ht htT)

/-! ## Order parameter bounds from Cauchy-Schwarz -/

/-- (η.re - r*)² ≤ V and V < r*² imply η.re > 0. -/
theorem eta_re_pos_of_cs_bound (η_re r_star V : ℝ) (hr : 0 < r_star)
    (h_cs : (η_re - r_star) ^ 2 ≤ V) (hV : V < r_star ^ 2) :
    0 < η_re := by
  nlinarith [sq_nonneg η_re]

/-- (η.re - r*)² ≤ V implies η.re ≥ r* - √V. -/
theorem eta_re_ge_of_cs_bound (η_re r_star V : ℝ)
    (h_cs : (η_re - r_star) ^ 2 ≤ V) :
    r_star - Real.sqrt V ≤ η_re := by
  have : |η_re - r_star| ≤ Real.sqrt V := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h_cs
  linarith [(abs_le.mp this).1]

/-! ## Basin coupling: Cauchy-Schwarz → body persistence hypotheses -/

/-- In the basin V < B, the compact-support coupling condition
    |ω| < K·(r* - √B)/2 propagates to |ω| < K·η.re/2
    via the Cauchy-Schwarz lower bound on η.re. -/
theorem coupling_bound_in_basin (ω_freq K r_star η_re V B : ℝ) (hK : 0 < K)
    (h_cs : (η_re - r_star) ^ 2 ≤ V) (hV : V < B)
    (hω : |ω_freq| < K * (r_star - Real.sqrt B) / 2) :
    |ω_freq| < K * η_re / 2 := by
  have h1 : r_star - Real.sqrt B ≤ η_re := by
    have := eta_re_ge_of_cs_bound η_re r_star V h_cs
    linarith [Real.sqrt_le_sqrt (le_of_lt hV)]
  nlinarith

/-- Body persistence gives Re(z+z*) ≥ Re(z*) when Re(z) > 0. -/
theorem re_sum_ge_of_re_pos (z z_star : ℂ) (δ₀ : ℝ)
    (hz : 0 < z.re) (hzs : δ₀ ≤ z_star.re) :
    δ₀ ≤ (z + z_star).re := by
  simp only [Complex.add_re]; linarith

/-- Pointwise coercivity from body persistence + equilibrium structure:
    Re(z) > 0 and Re(z*) ≥ δ₀ ≥ 0 implies the weighted coercivity bound. -/
theorem coercivity_pointwise_of_body (z z_star : ℂ) (w δ₀ : ℝ)
    (hw : 0 ≤ w) (_hδ₀ : 0 ≤ δ₀)
    (hz : 0 < z.re) (hzs : δ₀ ≤ z_star.re) :
    δ₀ * (Complex.normSq (z - z_star) * w) ≤
      (z + z_star).re * (Complex.normSq (z - z_star) * w) := by
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Complex.normSq_nonneg _) hw)
  exact re_sum_ge_of_re_pos z z_star δ₀ hz hzs

/-! ## Forcing simplification for real η -/

/-- When z* is equilibrium at r* and η = ↑r is real, the forcing term becomes
    K·(r-r*)·Re(conj(z-z*)·(1-z*²)). -/
theorem forcing_real_eta (ω K r r_star : ℝ) (z z_star : ℂ)
    (hz_star_equil : complexOaRHS ω K (↑r_star) z_star = 0) :
    2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K (↑r) z_star).re =
      K * (r - r_star) * (starRingEnd ℂ (z - z_star) * (1 - z_star ^ 2)).re := by
  rw [forcing_eq_eta_diff ω K (↑r) (↑r_star) z_star hz_star_equil]
  have h_conj : starRingEnd ℂ ((↑r : ℂ) - ↑r_star) = ↑r - ↑r_star := by
    rw [show (↑r : ℂ) - ↑r_star = ↑(r - r_star) from by push_cast; ring]
    exact RCLike.conj_ofReal _
  rw [h_conj, show ((↑r : ℂ) - ↑r_star) - ((↑r : ℂ) - ↑r_star) * z_star ^ 2 =
      ((↑r : ℂ) - ↑r_star) * (1 - z_star ^ 2) from by ring,
    show (↑K : ℂ) / 2 * (((↑r : ℂ) - ↑r_star) * (1 - z_star ^ 2)) =
      ↑(K * (r - r_star) / 2) * (1 - z_star ^ 2) from by push_cast; ring,
    show starRingEnd ℂ (z - z_star) * (↑(K * (r - r_star) / 2) * (1 - z_star ^ 2)) =
      ↑(K * (r - r_star) / 2) * (starRingEnd ℂ (z - z_star) * (1 - z_star ^ 2)) from by ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring

/-- Coercivity term on symmetric subspace: when η = ↑r is real,
    -K·Re(η·(z+z*))·|z-z*|² = -K·r·Re(z+z*)·|z-z*|². -/
theorem coercivity_real_eta (K r : ℝ) (z z_star : ℂ) :
    -K * ((↑r : ℂ) * (z + z_star)).re * Complex.normSq (z - z_star) =
      -K * r * (z + z_star).re * Complex.normSq (z - z_star) := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring

/-! ## Forcing absolute value bound -/

/-- |K·d·I| ≤ K·√F·V when d²≤V and I²≤V·F.
    Applies to forcing = K·(r(t)-r*)·∫Re(conj(z-z*)·(1-z*²))·g
    where d = r(t)-r*, I = ∫..., F = ∫|1-z*²|²·g. -/
theorem forcing_bound_of_cs (K d I V F : ℝ)
    (hK : 0 < K) (hV : 0 ≤ V)
    (hd : d ^ 2 ≤ V) (hI : I ^ 2 ≤ V * F) :
    |K * d * I| ≤ K * Real.sqrt F * V := by
  rw [show K * d * I = K * (d * I) from by ring, abs_mul, abs_of_pos hK,
    show K * Real.sqrt F * V = K * (Real.sqrt F * V) from by ring]
  exact mul_le_mul_of_nonneg_left (abs_mul_le_of_sq_bounds d I V F hV hI hd) (le_of_lt hK)

/-- Net decay rate: if coercivity ≥ c₁·V and |forcing| ≤ c₂·V with c₁ > c₂,
    then V' ≤ -(c₁-c₂)·V. For compact-support: c₁ = K·r_min·δ₀, c₂ = K·√F. -/
theorem net_decay_of_coercivity_forcing (V_val D_val F_val c₁ c₂ : ℝ)
    (h_sum : D_val + F_val ≤ -c₁ * V_val + c₂ * V_val) :
    D_val + F_val ≤ -(c₁ - c₂) * V_val := by linarith

/-- If V' ≤ -c₁·V + F and |F| ≤ c₂·V, then V' ≤ -(c₁-c₂)·V.
    Instantiate with c₁ = K·r_min·δ₀, c₂ = K·√(∫|1-z*²|²g).
    The rate c₁ - c₂ > 0 is the checkable condition replacing Dietert. -/
theorem decay_from_coercivity_and_forcing (V_deriv V_val F_val c₁ c₂ : ℝ)
    (h_upper : V_deriv ≤ -c₁ * V_val + F_val)
    (h_force : |F_val| ≤ c₂ * V_val) :
    V_deriv ≤ -(c₁ - c₂) * V_val := by linarith [le_abs_self F_val]

/-! ## Per-oscillator V' integrand decomposition -/

/-- Full V' integrand decomposition on symmetric subspace (η = ↑r real).
    Combines complexOa_error_general + coercivity_real_eta + forcing_real_eta:
      2·Re(conj(z-z*)·RHS(z))·g = [-K·r·Re(z+z*)·|z-z*|²]·g + [K·(r-r*)·Re(conj(z-z*)·(1-z*²))]·g -/
theorem V_integrand_decomp_real_eta (ω K r r_star : ℝ) (z z_star : ℂ) (g_val : ℝ)
    (hz_star_equil : complexOaRHS ω K (↑r_star) z_star = 0) :
    2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K (↑r) z).re * g_val =
      (-K * r * (z + z_star).re * Complex.normSq (z - z_star)) * g_val +
      (K * (r - r_star) * (starRingEnd ℂ (z - z_star) * (1 - z_star ^ 2)).re) * g_val := by
  have h1 : 2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K (↑r) z).re =
      -K * r * (z + z_star).re * Complex.normSq (z - z_star) +
      K * (r - r_star) * (starRingEnd ℂ (z - z_star) * (1 - z_star ^ 2)).re := by
    linarith [complexOa_error_general ω K (↑r) z z_star,
      coercivity_real_eta K r z z_star,
      forcing_real_eta ω K r r_star z z_star hz_star_equil]
  calc 2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K (↑r) z).re * g_val
      = (2 * (starRingEnd ℂ (z - z_star) * complexOaRHS ω K (↑r) z).re) * g_val := by ring
    _ = (-K * r * (z + z_star).re * Complex.normSq (z - z_star) +
         K * (r - r_star) * (starRingEnd ℂ (z - z_star) * (1 - z_star ^ 2)).re) * g_val :=
        by rw [h1]
    _ = _ := by ring

/-! ## Integral V' decomposition -/

/-- Splits the Leibniz integral V'(t) = ∫ 2Re(conj(z-z*)·RHS)·g into
    coercivity integral + forcing integral, on symmetric subspace (η = ↑r). -/
theorem V_deriv_integral_split
    (S : SymmetricFreq Ω μ) (z z_star : Ω → ℂ) (K r r_star : ℝ)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K (↑r_star) (z_star ω) = 0)
    (h_coerce_int : Integrable (fun ω =>
      (-K * r * (z ω + z_star ω).re * Complex.normSq (z ω - z_star ω)) * S.g ω) μ)
    (h_force_int : Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ) :
    ∫ ω, 2 * (starRingEnd ℂ (z ω - z_star ω) *
      complexOaRHS (S.ω_freq ω) K (↑r) (z ω)).re * S.g ω ∂μ =
      ∫ ω, (-K * r * (z ω + z_star ω).re * Complex.normSq (z ω - z_star ω)) * S.g ω ∂μ +
      ∫ ω, (K * (r - r_star) * (starRingEnd ℂ (z ω - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω ∂μ := by
  rw [← integral_add h_coerce_int h_force_int]
  exact integral_congr_ae (ae_of_all μ fun ω =>
    V_integrand_decomp_real_eta (S.ω_freq ω) K r r_star (z ω) (z_star ω) (S.g ω)
      (hz_star_equil ω))

/-- The coercivity integral factors: ∫(-K·r·Re(z+z*)·|z-z*|²)·g = -K·r·∫Re(z+z*)·|z-z*|²·g.
    After factoring, coercivity_lower_bound gives ≥ δ₀·V. -/
theorem coercivity_integral_factor (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r : ℝ) :
    ∫ ω, (-K * r * (z ω + z_star ω).re * Complex.normSq (z ω - z_star ω)) * g ω ∂μ =
      -K * r * ∫ ω, (z ω + z_star ω).re *
        (Complex.normSq (z ω - z_star ω) * g ω) ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all μ fun ω => by ring)

/-- The forcing integral factors: ∫K·(r-r*)·Re(conj(z-z*)·(1-z*²))·g = K·(r-r*)·∫Re(...)·g. -/
theorem forcing_integral_factor (z z_star : Ω → ℂ) (g : Ω → ℝ) (K r r_star : ℝ) :
    ∫ ω, (K * (r - r_star) * (starRingEnd ℂ (z ω - z_star ω) *
      (1 - z_star ω ^ 2)).re) * g ω ∂μ =
      K * (r - r_star) * ∫ ω, (starRingEnd ℂ (z ω - z_star ω) *
        (1 - z_star ω ^ 2)).re * g ω ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all μ fun ω => by ring)

/-! ## Algebraic rate bound: coercivity + forcing → V' ≤ -rate·V -/

/-- Core rate bound: V' = -K·r·W + K·(r-r*)·I, with coercivity W ≥ δ₀·V,
    basin r ≥ r_min, and forcing |K·(r-r*)·I| ≤ K·√F·V gives
    V' ≤ -(K·r_min·δ₀ - K·√F)·V.
    This is the algebraic heart of the compact-support convergence. -/
theorem V_deriv_rate_bound (K r r_star r_min δ₀ W I V_val F_val : ℝ)
    (hK : 0 < K) (hr : 0 ≤ r) (hr_min : r_min ≤ r) (hδ₀ : 0 ≤ δ₀)
    (hV : 0 ≤ V_val) (_hF : 0 ≤ F_val)
    (hW_bound : δ₀ * V_val ≤ W)
    (hd_sq : (r - r_star) ^ 2 ≤ V_val)
    (hI_sq : I ^ 2 ≤ V_val * F_val) :
    -K * r * W + K * (r - r_star) * I ≤
      -(K * r_min * δ₀ - K * Real.sqrt F_val) * V_val := by
  have h_coerce : -K * r * W ≤ -K * r_min * δ₀ * V_val := by
    have h1 : K * r * (δ₀ * V_val) ≤ K * r * W :=
      mul_le_mul_of_nonneg_left hW_bound (mul_nonneg (le_of_lt hK) hr)
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hK) (sub_nonneg.mpr hr_min))
      (mul_nonneg hδ₀ hV)]
  have h_force : K * (r - r_star) * I ≤ K * Real.sqrt F_val * V_val :=
    le_trans (le_abs_self _)
      (forcing_bound_of_cs K (r - r_star) I V_val F_val hK hV hd_sq hI_sq)
  linarith

/-! ## Full assembly: compact-support h_basin_decay discharge -/

theorem compact_support_h_basin_decay_at [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star B δ₀ F_val : ℝ) {t : ℝ}
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_star_disk : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
    (hB_le : B ≤ r_star ^ 2)
    (ht : 0 < t)
    (hVt : (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) < B)
    (h_body_t : ∀ ω, 0 < (z ω t).re)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    let V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
    let rate := K * (r_star - Real.sqrt B) * δ₀ - K * Real.sqrt F_val
    HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -rate * V t := by
  intro V rate
  have h_leibniz := complex_leibniz S z z_star K hz_ode hz_disk hz_star_disk
    hV_int hg_nn hg_int hω_g_int hK hz_cont hη_bdd
  have hV_hasderiv := h_leibniz.2 t ht
  refine ⟨hV_hasderiv.congr_deriv hV_hasderiv.deriv.symm, ?_⟩
  rw [hV_hasderiv.deriv]
  set r_t := (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re
  have hη_eq : ∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ = (↑r_t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hη_real t
  simp_rw [hη_eq]
  rw [V_deriv_integral_split S (fun ω => z ω t) z_star K r_t r_star hz_star_equil
    (h_coerce_int t r_t) (h_force_int t r_t)]
  rw [coercivity_integral_factor (fun ω => z ω t) z_star S.g K r_t,
    forcing_integral_factor (fun ω => z ω t) z_star S.g K r_t r_star]
  have hV_nn : 0 ≤ V t :=
    integral_nonneg fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω)
  have h_r_min : r_star - Real.sqrt B ≤ r_t := by
    have := eta_re_ge_of_cs_bound r_t r_star (V t) (h_cs t)
    linarith [Real.sqrt_le_sqrt (le_of_lt hVt)]
  have h_W_bound : δ₀ * V t ≤
      ∫ ω, (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω) ∂μ :=
    coercivity_lower_bound (fun ω => z ω t) z_star S.g δ₀
      (fun ω => coercivity_pointwise_of_body (z ω t) (z_star ω) (S.g ω) δ₀
        (hg_nn ω) (le_of_lt hδ₀) (h_body_t ω) (hδ₀_bound ω))
      (hV_int t) (h_W_int t)
  have hr_t_nn : 0 ≤ r_t := by
    have : Real.sqrt B ≤ r_star :=
      (Real.sqrt_le_sqrt hB_le).trans_eq (Real.sqrt_sq (le_of_lt hr_star_pos))
    linarith [h_r_min]
  exact V_deriv_rate_bound K r_t r_star (r_star - Real.sqrt B) δ₀
    (∫ ω, (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω) ∂μ)
    (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) * (1 - z_star ω ^ 2)).re * S.g ω ∂μ)
    (V t) F_val hK hr_t_nn h_r_min (le_of_lt hδ₀) hV_nn hF_nn
    h_W_bound (h_cs t) (h_force_sq t)

theorem compact_support_h_decay_of_r_floor [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star r_floor δ₀ F_val : ℝ) {t : ℝ}
    (hK : 0 < K) (_hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_star_disk : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
    (ht : 0 < t)
    (h_r_floor_t : r_floor ≤ (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re)
    (hr_floor_nn : 0 ≤ r_floor)
    (h_body_t : ∀ ω, 0 < (z ω t).re)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    let V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
    let rate := K * r_floor * δ₀ - K * Real.sqrt F_val
    HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -rate * V t := by
  intro V rate
  have h_leibniz := complex_leibniz S z z_star K hz_ode hz_disk hz_star_disk
    hV_int hg_nn hg_int hω_g_int hK hz_cont hη_bdd
  have hV_hasderiv := h_leibniz.2 t ht
  refine ⟨hV_hasderiv.congr_deriv hV_hasderiv.deriv.symm, ?_⟩
  rw [hV_hasderiv.deriv]
  set r_t := (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re
  have hη_eq : ∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ = (↑r_t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hη_real t
  simp_rw [hη_eq]
  rw [V_deriv_integral_split S (fun ω => z ω t) z_star K r_t r_star hz_star_equil
    (h_coerce_int t r_t) (h_force_int t r_t)]
  rw [coercivity_integral_factor (fun ω => z ω t) z_star S.g K r_t,
    forcing_integral_factor (fun ω => z ω t) z_star S.g K r_t r_star]
  have hV_nn : 0 ≤ V t :=
    integral_nonneg fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω)
  have h_W_bound : δ₀ * V t ≤
      ∫ ω, (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω) ∂μ :=
    coercivity_lower_bound (fun ω => z ω t) z_star S.g δ₀
      (fun ω => coercivity_pointwise_of_body (z ω t) (z_star ω) (S.g ω) δ₀
        (hg_nn ω) (le_of_lt hδ₀) (h_body_t ω) (hδ₀_bound ω))
      (hV_int t) (h_W_int t)
  exact V_deriv_rate_bound K r_t r_star r_floor δ₀
    (∫ ω, (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω) ∂μ)
    (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) * (1 - z_star ω ^ 2)).re * S.g ω ∂μ)
    (V t) F_val hK (le_trans hr_floor_nn h_r_floor_t) h_r_floor_t (le_of_lt hδ₀) hV_nn hF_nn
    h_W_bound (h_cs t) (h_force_sq t)

theorem compact_support_h_basin_decay [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star B δ₀ F_val : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_star_disk : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ)
    (_hB_pos : 0 < B) (hB_le : B ≤ r_star ^ 2)
    (h_body : ∀ ω t, 0 ≤ t →
      (∫ ω', Complex.normSq (z ω' t - z_star ω') * S.g ω' ∂μ) < B →
      0 < (z ω t).re)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    let V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
    let rate := K * (r_star - Real.sqrt B) * δ₀ - K * Real.sqrt F_val
    ∀ t, 0 < t → V t < B →
      HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -rate * V t := by
  intro V rate t ht hVt
  exact compact_support_h_basin_decay_at S z z_star K r_star B δ₀ F_val
    hK hr_star_pos hz_ode hz_disk hz_star_disk hη_real hz_star_equil
    hg_nn hg_int hω_g_int hz_cont hη_bdd hV_int h_cs hB_le ht hVt
    (fun ω => h_body ω t (le_of_lt ht) hVt) hδ₀ hδ₀_bound hF_nn h_force_sq
    h_coerce_int h_force_int h_W_int

/-! ## End-to-end: single theorem, no axioms -/

theorem compact_support_full_convergence [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star B δ₀ F_val : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_disk_strict : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    (hB_pos : 0 < B) (hB_le : B ≤ r_star ^ 2)
    (hV0 : ∫ ω, Complex.normSq (z ω 0 - z_star ω) * S.g ω ∂μ < B)
    (hV_cont : Continuous (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (h_body : ∀ ω t, 0 ≤ t →
      (∫ ω', Complex.normSq (z ω' t - z_star ω') * S.g ω' ∂μ) < B →
      0 < (z ω t).re)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (hrate : 0 < K * (r_star - Real.sqrt B) * δ₀ - K * Real.sqrt F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  have h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤
      ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ :=
    fun t => eta_re_cauchy_schwarz (fun ω => z ω t) z_star S.g r_star
      hg_nn hg_int hg_norm hr_star_eq (hV_int t) (hη_int t) hη_star_int (hφ_meas t)
  exact compact_support_convergence S z z_star K r_star hK hr_star_pos
    hz_disk_strict hz_star_pos hz_star_lt hz_sym hz_star_sym hg_nn hg_int hg_norm
    hz_ode hr_star_eq hz_star_equil hV_int hη_int hη_star_int hφ_meas
    B _ hB_pos hrate hV0 hV_cont
    (compact_support_h_basin_decay S z z_star K r_star B δ₀ F_val
      hK hr_star_pos hz_ode hz_disk (fun ω => le_of_lt (hz_star_lt ω))
      hη_real hz_star_equil hg_nn hg_int hω_g_int hz_cont hη_bdd
      hV_int h_cs hB_pos hB_le h_body hδ₀ hδ₀_bound hF_nn h_force_sq
      h_coerce_int h_force_int h_W_int)

theorem compact_support_convergence_locked [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star B δ₀ F_val : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_disk_strict : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    (hB_pos : 0 < B) (hB_le : B ≤ r_star ^ 2)
    (hV0 : ∫ ω, Complex.normSq (z ω 0 - z_star ω) * S.g ω ∂μ < B)
    (hV_cont : Continuous (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (hz0_re : ∀ ω, 0 < (z ω 0).re)
    (h_lock : ∀ ω, |S.ω_freq ω| < K * (r_star - Real.sqrt B) / 2)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (hrate : 0 < K * (r_star - Real.sqrt B) * δ₀ - K * Real.sqrt F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  set V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
  set η := fun t => ∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ
  have h_cs : ∀ t, ((η t).re - r_star) ^ 2 ≤ V t :=
    fun t => eta_re_cauchy_schwarz (fun ω => z ω t) z_star S.g r_star
      hg_nn hg_int hg_norm hr_star_eq (hV_int t) (hη_int t) hη_star_int (hφ_meas t)
  have hV_nn : ∀ t, 0 ≤ t → 0 ≤ V t :=
    fun t _ => integral_nonneg (fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω))
  have h_body_from_history : ∀ ω t, 0 < t →
      (∀ s, 0 ≤ s → s < t → V s < B) → V t < B → 0 < (z ω t).re := by
    intro ω t ht h_hist hVt
    have h_basin_on : ∀ s, 0 ≤ s → s ≤ t → V s < B := by
      intro s hs hst
      rcases eq_or_lt_of_le hst with rfl | hlt
      · exact hVt
      · exact h_hist s hs hlt
    have h_coupling : ∀ s, 0 ≤ s → s ≤ t →
        |S.ω_freq ω| < K * (η s).re / 2 := by
      intro s hs hst
      exact coupling_bound_in_basin (S.ω_freq ω) K r_star
        (η s).re (V s) B hK (h_cs s) (h_basin_on s hs hst) (h_lock ω)
    exact body_persistence_on_Icc (S.ω_freq ω) K (z ω) (fun s => η s) t
      (hz_cont ω) (hz0_re ω) (hz_ode ω) hη_real h_coupling t (le_of_lt ht) le_rfl
  have hV_zero : Tendsto V atTop (nhds 0) :=
    gronwall_bootstrap_tendsto_history V B
      (K * (r_star - Real.sqrt B) * δ₀ - K * Real.sqrt F_val) hrate hB_pos
      hV_cont hV_nn hV0
      (fun t ht h_hist hVt => compact_support_h_basin_decay_at S z z_star K r_star
        B δ₀ F_val hK hr_star_pos hz_ode hz_disk
        (fun ω => le_of_lt (hz_star_lt ω)) hη_real hz_star_equil hg_nn hg_int
        hω_g_int hz_cont hη_bdd hV_int h_cs hB_le ht hVt
        (fun ω => h_body_from_history ω t ht h_hist hVt)
        hδ₀ hδ₀_bound hF_nn h_force_sq h_coerce_int h_force_int h_W_int)
  exact complex_oa_end_to_end S z z_star K r_star hK hr_star_pos hz_disk_strict
    hz_star_pos hz_star_lt hz_sym hz_star_sym hg_nn hg_int hg_norm hz_ode hr_star_eq
    hz_star_equil hV_int hη_int hη_star_int hφ_meas hV_zero

/-- **CONVERGENCE FROM ORDER-PARAMETER FLOOR** (0 sorry, 0 axioms).
    If Re(η(t)) ≥ r_floor > 0 and Re(z(ω,t)) > 0 for all t > 0,
    then V → 0 and Re(η)² → r*² WITHOUT any basin condition on V(0). -/
theorem compact_support_convergence_r_floor [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star r_floor δ₀ F_val : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_disk_strict : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    (hV_cont : Continuous (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (h_r_floor : ∀ t, 0 ≤ t → r_floor ≤
      (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re)
    (hr_floor_nn : 0 ≤ r_floor)
    (h_body : ∀ ω t, 0 < t → 0 < (z ω t).re)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (hrate : 0 < K * r_floor * δ₀ - K * Real.sqrt F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  set V := fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ
  have h_cs : ∀ t, ((∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re - r_star) ^ 2 ≤ V t :=
    fun t => eta_re_cauchy_schwarz (fun ω => z ω t) z_star S.g r_star
      hg_nn hg_int hg_norm hr_star_eq (hV_int t) (hη_int t) hη_star_int (hφ_meas t)
  have hV_nn : ∀ t, 0 ≤ t → 0 ≤ V t :=
    fun t _ => integral_nonneg (fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω))
  have h_decay : ∀ t, 0 < t →
      HasDerivAt V (deriv V t) t ∧
      deriv V t ≤ -(K * r_floor * δ₀ - K * Real.sqrt F_val) * V t :=
    fun t ht => compact_support_h_decay_of_r_floor S z z_star K r_star r_floor δ₀ F_val
      hK hr_star_pos hz_ode hz_disk (fun ω => le_of_lt (hz_star_lt ω)) hη_real
      hz_star_equil hg_nn hg_int hω_g_int hz_cont hη_bdd hV_int h_cs
      ht (h_r_floor t (le_of_lt ht)) hr_floor_nn (fun ω => h_body ω t ht)
      hδ₀ hδ₀_bound hF_nn h_force_sq h_coerce_int h_force_int h_W_int
  have hV_zero : Tendsto V atTop (nhds 0) :=
    gronwall_bootstrap_tendsto V (V 0 + 1)
      (K * r_floor * δ₀ - K * Real.sqrt F_val) hrate
      (by linarith [hV_nn 0 le_rfl]) hV_cont hV_nn (by linarith)
      (fun t ht _ => h_decay t ht)
  exact complex_oa_end_to_end S z z_star K r_star hK hr_star_pos hz_disk_strict
    hz_star_pos hz_star_lt hz_sym hz_star_sym hg_nn hg_int hg_norm hz_ode hr_star_eq
    hz_star_equil hV_int hη_int hη_star_int hφ_meas hV_zero

/-- **GLOBAL CONVERGENCE FROM ORDER-PARAMETER FLOOR** (0 sorry, 0 axioms).
    Derives body persistence from r-floor + frequency locking + initial body,
    then delegates to compact_support_convergence_r_floor.
    NO basin condition V(0) < B required. -/
theorem compact_support_convergence_r_floor_locked [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ) (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ)
    (K r_star r_floor δ₀ F_val : ℝ)
    (hK : 0 < K) (hr_star_pos : 0 < r_star)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_disk_strict : ∀ ω t, 0 ≤ t → Complex.normSq (z ω t) < 1)
    (hz_star_pos : ∀ ω, 0 < Complex.normSq (z_star ω))
    (hz_star_lt : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_star_sym : ∀ ω, z_star (S.neg ω) = starRingEnd ℂ (z_star ω))
    (hg_nn : ∀ ω, 0 ≤ S.g ω) (hg_int : Integrable S.g μ)
    (hg_norm : ∫ ω, S.g ω ∂μ = 1)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hr_star_eq : r_star = (∫ ω, starRingEnd ℂ (z_star ω) * (S.g ω : ℂ) ∂μ).re)
    (hz_star_equil : ∀ ω, complexOaRHS (S.ω_freq ω) K ((r_star : ℂ)) (z_star ω) = 0)
    (hη_real : ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0)
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hη_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hη_star_int : Integrable (fun ω => starRingEnd ℂ (z_star ω) * (S.g ω : ℂ)) μ)
    (hφ_meas : ∀ t, AEStronglyMeasurable (fun ω => (z ω t - z_star ω).re) μ)
    (hV_cont : Continuous (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ))
    (h_r_floor : ∀ t, 0 ≤ t → r_floor ≤
      (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re)
    (hr_floor_nn : 0 ≤ r_floor)
    (hz0_re : ∀ ω, 0 < (z ω 0).re)
    (h_lock : ∀ ω, |S.ω_freq ω| < K * r_floor / 2)
    (hδ₀ : 0 < δ₀) (hδ₀_bound : ∀ ω, δ₀ ≤ (z_star ω).re)
    (hF_nn : 0 ≤ F_val)
    (h_force_sq : ∀ t,
      (∫ ω, (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re * S.g ω ∂μ) ^ 2 ≤
      (∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) * F_val)
    (hrate : 0 < K * r_floor * δ₀ - K * Real.sqrt F_val)
    (h_coerce_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (-K * r * (z ω t + z_star ω).re * Complex.normSq (z ω t - z_star ω)) * S.g ω) μ)
    (h_force_int : ∀ (t : ℝ) (r : ℝ), Integrable (fun ω =>
      (K * (r - r_star) * (starRingEnd ℂ (z ω t - z_star ω) *
        (1 - z_star ω ^ 2)).re) * S.g ω) μ)
    (h_W_int : ∀ t, Integrable (fun ω =>
      (z ω t + z_star ω).re * (Complex.normSq (z ω t - z_star ω) * S.g ω)) μ) :
    Tendsto (fun t => (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re ^ 2)
      atTop (nhds (r_star ^ 2)) := by
  set η := fun t => ∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ
  have h_body : ∀ ω t, 0 < t → 0 < (z ω t).re := by
    intro ω t ht
    have h_coupling : ∀ s, 0 ≤ s → s ≤ t →
        |S.ω_freq ω| < K * (η s).re / 2 := fun s hs _ =>
      lt_of_lt_of_le (h_lock ω)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (h_r_floor s hs) (le_of_lt hK)) (by positivity))
    exact body_persistence_on_Icc (S.ω_freq ω) K (z ω) η t
      (hz_cont ω) (hz0_re ω) (hz_ode ω) hη_real h_coupling t (le_of_lt ht) le_rfl
  exact compact_support_convergence_r_floor S z z_star K r_star r_floor δ₀ F_val
    hK hr_star_pos hz_ode hz_disk hz_disk_strict hz_star_pos hz_star_lt hz_sym hz_star_sym
    hg_nn hg_int hg_norm hω_g_int hz_cont hr_star_eq hz_star_equil hη_real hη_bdd
    hV_int hη_int hη_star_int hφ_meas hV_cont h_r_floor hr_floor_nn h_body
    hδ₀ hδ₀_bound hF_nn h_force_sq hrate h_coerce_int h_force_int h_W_int

end
