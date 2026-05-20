/-
  Complex OA Body Integral Decay
  ================================
  From per-oscillator exponential decay to integrated V_body → 0.

  If each oscillator's error satisfies f(ω,t) ≤ C·exp(-rate·t),
  then V(t) = ∫ f(ω,t)·g(ω) ≤ C·exp(-rate·t)·∫g → 0.

  0 sorry.
-/

import KuramotoLean.ComplexOAPerOscillatorDecay

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem body_integral_tendsto_zero
    (f : Ω → ℝ → ℝ) (g : Ω → ℝ) (C rate : ℝ)
    (hrate : 0 < rate)
    (hg_nn : ∀ ω, 0 ≤ g ω)
    (hf_nn : ∀ ω t, 0 ≤ t → 0 ≤ f ω t)
    (hf_bound : ∀ ω t, 0 ≤ t → f ω t ≤ C * Real.exp (-rate * t))
    (hfg_int : ∀ t, 0 ≤ t → Integrable (fun ω => f ω t * g ω) μ)
    (hg_int : Integrable g μ) :
    Tendsto (fun t => ∫ ω, f ω t * g ω ∂μ) atTop (nhds 0) := by
  set G := ∫ ω, g ω ∂μ
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun t ht =>
      integral_nonneg fun ω => mul_nonneg (hf_nn ω t ht) (hg_nn ω)⟩
  · exact eventually_atTop.mpr ⟨0, fun t ht => by
      have h_pw : ∀ ω, f ω t * g ω ≤ C * Real.exp (-rate * t) * g ω :=
        fun ω => mul_le_mul_of_nonneg_right (hf_bound ω t ht) (hg_nn ω)
      calc ∫ ω, f ω t * g ω ∂μ
          ≤ ∫ ω, C * Real.exp (-rate * t) * g ω ∂μ :=
            integral_mono (hfg_int t ht) (hg_int.const_mul _) h_pw
        _ = C * Real.exp (-rate * t) * G := integral_const_mul _ _⟩
  · have h1 : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b / rate, fun s hs =>
        le_of_eq_of_le (by field_simp) (mul_le_mul_of_nonneg_left hs (le_of_lt hrate))⟩
    have h2 : Tendsto (fun t => Real.exp (-rate * t)) atTop (nhds 0) :=
      (tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun _ => by simp
    have h3 : Tendsto (fun t => C * Real.exp (-rate * t) * G) atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := C)).mul h2
      simpa [mul_zero] using this.mul (tendsto_const_nhds (x := G))
    exact h3

theorem complex_oa_body_decay
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (ω_freq : Ω → ℝ) (g : Ω → ℝ)
    (K r rate : ℝ) (_hK : 0 < K) (_hr : 0 < r) (hrate : 0 < rate)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (hz_star_eq : ∀ ω, complexOaRHS (ω_freq ω) K (↑r) (z_star ω) = 0)
    (hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω) (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hz_cont : ∀ ω, Continuous (fun t => Complex.normSq (z ω t - z_star ω)))
    (h_weight : ∀ ω z', Complex.normSq (z' - z_star ω) < 2 →
        rate ≤ K * r * (z' + z_star ω).re)
    (h_basin : ∀ ω, Complex.normSq (z ω 0 - z_star ω) < 2)
    (hfg_int : ∀ t, 0 ≤ t →
        Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * g ω) μ) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ)
      atTop (nhds 0) := by
  apply body_integral_tendsto_zero _ _ 2 rate hrate hg_nn
    (fun ω t _ => Complex.normSq_nonneg _) _ hfg_int hg_int
  intro ω t ht
  calc Complex.normSq (z ω t - z_star ω)
      ≤ Complex.normSq (z ω 0 - z_star ω) * Real.exp (-rate * t) :=
        perOscillator_exp_bound (z ω) (ω_freq ω) K r (z_star ω) 2 rate
          _hK _hr (by norm_num) hrate (hz_star_eq ω) (hz_cont ω)
          (hz_ode ω) (h_weight ω) (h_basin ω) t ht
    _ ≤ 2 * Real.exp (-rate * t) :=
        mul_le_mul_of_nonneg_right (le_of_lt (h_basin ω)) (le_of_lt (exp_pos _))

theorem complex_oa_body_decay_B
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (ω_freq : Ω → ℝ) (g : Ω → ℝ)
    (K r rate B : ℝ) (_hK : 0 < K) (_hr : 0 < r) (hrate : 0 < rate) (hB : 0 < B)
    (hg_nn : ∀ ω, 0 ≤ g ω) (hg_int : Integrable g μ)
    (hz_star_eq : ∀ ω, complexOaRHS (ω_freq ω) K (↑r) (z_star ω) = 0)
    (hz_ode : ∀ ω t, 0 ≤ t → HasDerivAt (z ω) (complexOaRHS (ω_freq ω) K (↑r) (z ω t)) t)
    (hz_cont : ∀ ω, Continuous (fun t => Complex.normSq (z ω t - z_star ω)))
    (h_weight : ∀ ω z', Complex.normSq (z' - z_star ω) < B →
        rate ≤ K * r * (z' + z_star ω).re)
    (h_basin : ∀ ω, Complex.normSq (z ω 0 - z_star ω) < B)
    (hfg_int : ∀ t, 0 ≤ t →
        Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * g ω) μ) :
    Tendsto (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * g ω ∂μ)
      atTop (nhds 0) := by
  apply body_integral_tendsto_zero _ _ B rate hrate hg_nn
    (fun ω t _ => Complex.normSq_nonneg _) _ hfg_int hg_int
  intro ω t ht
  calc Complex.normSq (z ω t - z_star ω)
      ≤ Complex.normSq (z ω 0 - z_star ω) * Real.exp (-rate * t) :=
        perOscillator_exp_bound (z ω) (ω_freq ω) K r (z_star ω) B rate
          _hK _hr hB hrate (hz_star_eq ω) (hz_cont ω)
          (hz_ode ω) (h_weight ω) (h_basin ω) t ht
    _ ≤ B * Real.exp (-rate * t) :=
        mul_le_mul_of_nonneg_right (le_of_lt (h_basin ω)) (le_of_lt (exp_pos _))

end
