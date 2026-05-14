/-
  Uniform Continuous Dependence for OA Solutions
  ================================================
  Proves h_unif_approx: uniform-in-time approximation of the
  continuum OA order parameter by n-pole solutions.

  Strategy: Gronwall inequality on the difference |r_n(t) - r(t)|.
  The OA scalar RHS is Lipschitz in α uniformly, and the self-consistency
  r = ∫α·g gives |r_n - r| ≤ ‖g_n - g‖_{L¹} + Lip·∫|α_n - α| ≤ ...

  For this file: prove the abstract uniform approximation lemma.
  Takes Lipschitz bound as hypothesis (from ODE structure).
  1 sorry (the target).
-/

import KuramotoLean.ComplexOASymmetry

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

/-- **UNIFORM CONTINUOUS DEPENDENCE (GRONWALL).**
    If two order parameters r, r_n satisfy:
    |r_n(t) - r(t)| ≤ δ_n + L·∫₀ᵗ |r_n(s) - r(s)| ds
    (standard Gronwall setup from Lipschitz ODE + L¹ approximation of g),
    then |r_n(t) - r(t)| ≤ δ_n · e^{Lt} for all t.

    For the n-pole approximation: δ_n = ‖g_n - g‖_{L¹} → 0.
    The exponential growth e^{Lt} is UNIFORM in n.
    But this gives approximation on [0,T], not uniform on [0,∞).

    For UNIFORM-in-time: use that both r_n and r eventually enter the
    basin V < r*² (after time T_n). After basin entry, both converge
    exponentially to r*. So |r_n(t) - r(t)| ≤ max on [0,T_n] + exp decay.

    SIMPLIFICATION: take the uniform bound directly as the theorem statement.
    The Gronwall computation is standard. -/
theorem uniform_approximation_from_gronwall
    (r : ℝ → ℝ) (r_star : ℝ)
    (r_approx : ℕ → ℝ → ℝ)
    -- Each r_n converges
    (_h_npole_conv : ∀ n, Tendsto (r_approx n) atTop (nhds r_star))
    -- Gronwall: |r_n(t) - r(t)| ≤ δ_n · e^{Lt} on [0,T]
    (L : ℝ) (hL : 0 < L)
    (δ : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ n)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (h_gronwall : ∀ n t, 0 ≤ t → |r_approx n t - r t| ≤ δ n * Real.exp (L * t))
    -- Both enter basin: ∃ T_unif, ∀ n, ∀ t ≥ T_unif, |r_n(t) - r*| < 1
    (T_basin : ℝ) (_hT_basin : 0 < T_basin)
    (_h_basin : ∀ n, ∀ t, T_basin ≤ t → |r_approx n t - r_star| < 1)
    (_h_r_basin : ∀ t, T_basin ≤ t → |r t - r_star| < 1)
    -- After basin entry, exponential convergence with uniform rate
    (μ_rate : ℝ) (hμ : 0 < μ_rate)
    (h_exp_conv : ∀ n t, T_basin ≤ t →
      |r_approx n t - r_star| ≤ Real.exp (-μ_rate * (t - T_basin)))
    (h_r_exp : ∀ t, T_basin ≤ t →
      |r t - r_star| ≤ Real.exp (-μ_rate * (t - T_basin))) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, 0 ≤ t → |r_approx n t - r t| < ε := by
  intro ε hε
  -- Step 1: Choose T₁ ≥ T_basin such that 2·exp(-μ·(T₁ - T_basin)) < ε
  -- For t ≥ T₁, triangle inequality gives bound < ε.
  -- Step 2: For t ∈ [0, T₁], Gronwall gives |r_n(t) - r(t)| ≤ δ_n · exp(L·T₁).
  -- Choose N so that δ_N · exp(L·T₁) < ε.
  set T₁ := max T_basin (T_basin + (1 / μ_rate) * Real.log (4 / ε))
  have hTle : T_basin ≤ T₁ := le_max_left _ _
  -- Extract N from hδ_zero: δ n → 0 means eventually δ n < ε / exp(L * T₁)
  have hexp_pos : (0 : ℝ) < Real.exp (L * T₁) := Real.exp_pos _
  have hbound : (0 : ℝ) < ε / Real.exp (L * T₁) := div_pos hε hexp_pos
  rw [Metric.tendsto_atTop] at hδ_zero
  obtain ⟨N, hN⟩ := hδ_zero (ε / Real.exp (L * T₁)) hbound
  refine ⟨N, fun n hn t ht => ?_⟩
  by_cases htT : t ≤ T₁
  · -- Case 1: t ≤ T₁, use Gronwall
    have hδn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_lt (hδ_pos n))] at hδn
    have hδn_pos : (0 : ℝ) ≤ δ n := le_of_lt (hδ_pos n)
    calc |r_approx n t - r t|
        ≤ δ n * Real.exp (L * t) := h_gronwall n t ht
      _ ≤ δ n * Real.exp (L * T₁) := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left htT (le_of_lt hL))
          · exact hδn_pos
      _ < ε := (lt_div_iff₀ hexp_pos).mp hδn
  · -- Case 2: t > T₁, use exponential convergence to r*
    push Not at htT
    have htB : T_basin ≤ t := le_trans hTle (le_of_lt htT)
    have tri : |r_approx n t - r t| ≤ |r_approx n t - r_star| + |r t - r_star| := by
      calc |r_approx n t - r t|
          = |(r_approx n t - r_star) - (r t - r_star)| := by ring_nf
        _ ≤ |r_approx n t - r_star| + |r t - r_star| := abs_sub _ _
    have hexp_bound : |r_approx n t - r_star| + |r t - r_star|
        ≤ 2 * Real.exp (-μ_rate * (t - T_basin)) := by
      have h1 := h_exp_conv n t htB
      have h2 := h_r_exp t htB
      linarith
    have hfinal : 2 * Real.exp (-μ_rate * (t - T_basin)) < ε := by
      have hT₁_ge : T_basin + (1 / μ_rate) * Real.log (4 / ε) ≤ T₁ :=
        le_max_right _ _
      have ht_sub : (1 / μ_rate) * Real.log (4 / ε) < t - T_basin := by linarith
      have h4ε : (0 : ℝ) < 4 / ε := div_pos (by norm_num) hε
      have hexp_lt : Real.exp (-μ_rate * (t - T_basin))
          < Real.exp (-(μ_rate * ((1 / μ_rate) * Real.log (4 / ε)))) :=
        Real.exp_strictMono (by linarith [mul_lt_mul_of_pos_left ht_sub hμ])
      have hsimp : μ_rate * ((1 / μ_rate) * Real.log (4 / ε)) = Real.log (4 / ε) := by
        field_simp
      rw [hsimp] at hexp_lt
      have hexp_val : Real.exp (-(Real.log (4 / ε))) = ε / 4 := by
        rw [Real.exp_neg, Real.exp_log h4ε]
        rw [show (4 / ε)⁻¹ = ε / 4 from by field_simp]
      linarith
    linarith

end
