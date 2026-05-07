/-
  LorentzianPointwiseConv.lean
  ============================
  Per-ω convergence to equilibrium from r(t) → r*.

  KEY IDEA: For each ω with γ(ω) > 0, the scalar ODE
    dα/dt = oaScalarRHS(γ, K, r, t, α) = -γα + (K/2)r(t)(1-α²)
  satisfies V(t) = (α-α*)² → 0 whenever r(t) → r*.

  PROOF:
    dV/dt = 2(α-α*)·oaScalarRHS ≤ -2γV + K|r-r*|  (Gronwall forcing)
    For any ε > 0: choose T with |r(t)-r*| < γε/K for t ≥ T.
    On [T,∞): dV/dt ≤ -2γV + γε.
    By gronwall_with_forcing: V(T+s) ≤ V(T)·exp(-2γs) + ε/2.
    V(T) ≤ 1, exp(-2γs) → 0 → V(t) → 0.

  Then dominated convergence (bound ≤ 4, integrable) gives V∞ → 0.

  Covers Lorentzian: μ absolutely continuous → γ(ω) = |ω| > 0 a.e.

  0 sorry.
-/

import KuramotoLean.ContinuumDerivedGronwall

open MeasureTheory Real Set Filter Topology

noncomputable section

/-! ## Key inequality: dV/dt ≤ -2γV + K|r - r*| -/

/-- The derivative 2(α-α*)·oaScalarRHS ≤ -2γ(α-α*)² + K|r - r_star|.
    Uses equilibrium γ·α* = (K/2)·r*·(1-α*²) and bounds for α,α* ∈ [0,1]. -/
private theorem oa_V_deriv_bound
    (γ K r_star α α_star r_val : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr_star : 0 < r_star)
    (hα_ge : 0 ≤ α) (hα_le : α ≤ 1)
    (hαs_ge : 0 ≤ α_star) (hαs_le : α_star ≤ 1)
    (hequil : γ * α_star = (K / 2) * r_star * (1 - α_star ^ 2)) :
    2 * (α - α_star) * (-γ * α + K / 2 * r_val * (1 - α ^ 2)) ≤
      -2 * γ * (α - α_star) ^ 2 + K * |r_val - r_star| := by
  -- Key: 2(α-α*)(-γα + (K/2)r(1-α²))
  --    = -2γ(α-α*)² - K*r**(α+α*)(α-α*)² + K*(α-α*)*(r-r*)*(1-α²)
  -- where first correction term ≤ 0, second ≤ K|r-r*| via |α-α*|≤1, 1-α²≤1
  -- Algebraic identity using equilibrium: LHS = -2γ(α-α*)² - Kr*(α+α*)(α-α*)² + K(r_val-r*)(α-α*)(1-α²)
  have hid : 2 * (α - α_star) * (-γ * α + K / 2 * r_val * (1 - α ^ 2)) =
      -2 * γ * (α - α_star) ^ 2
      - K * r_star * (α + α_star) * (α - α_star) ^ 2
      + K * (r_val - r_star) * ((α - α_star) * (1 - α ^ 2)) := by
    linear_combination -2 * (α - α_star) * hequil
  rw [hid]
  have hmid : 0 ≤ K * r_star * (α + α_star) * (α - α_star) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.le hr_star.le)
      (add_nonneg hα_ge hαs_ge)) (sq_nonneg _)
  have hlast : K * (r_val - r_star) * ((α - α_star) * (1 - α ^ 2)) ≤ K * |r_val - r_star| := by
    rcases le_or_gt r_star r_val with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hprod : (α - α_star) * (1 - α ^ 2) ≤ 1 := by
        nlinarith [sq_nonneg α, mul_nonneg hαs_ge (sub_nonneg.mpr hα_le)]
      nlinarith [mul_nonneg hK.le (sub_nonneg.mpr h)]
    · rw [abs_of_nonpos (sub_nonpos.mpr h.le)]
      have hprod : -1 ≤ (α - α_star) * (1 - α ^ 2) := by
        nlinarith [sq_nonneg α, mul_nonneg hαs_ge (sub_nonneg.mpr hα_le),
                   mul_nonneg hα_ge (sub_nonneg.mpr hα_le)]
      nlinarith [mul_nonneg hK.le (sub_nonneg.mpr h.le)]
  linarith

/-! ## Per-ω convergence: Gronwall + vanishing forcing -/

/-- **Per-ω convergence.** For γ > 0 and r(t) → r*, the scalar OA solution
    α(t) satisfying dα/dt = oaScalarRHS(γ, K, r, t, α) converges: α(t) → α*.

    Proof: ε-splitting on the Gronwall bound dV/dt ≤ -2γV + K|r-r*|. -/
theorem oa_scalar_pointwise_tendsto
    (γ K r_star : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr_star : 0 < r_star)
    (r : ℝ → ℝ)
    (hr_tendsto : Tendsto r atTop (nhds r_star))
    (hr_bdd_r : ∀ t, |r t| ≤ 1)
    (α : ℝ → ℝ)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (hα_bdd : ∀ t, 0 ≤ t → 0 ≤ α t ∧ α t ≤ 1)
    (α_star : ℝ)
    (hα_star_eq : γ * α_star = (K / 2) * r_star * (1 - α_star ^ 2))
    (hα_star_bdd : 0 ≤ α_star ∧ α_star ≤ 1) :
    Tendsto (fun t => (α t - α_star) ^ 2) atTop (nhds 0) := by
  -- V(t) = (α(t) - α_star)²
  let V := fun t => (α t - α_star) ^ 2
  -- V ≥ 0 and V(t) ≤ 1
  have hV_nn : ∀ t, 0 ≤ V t := fun t => sq_nonneg _
  have hV_bdd : ∀ t, 0 ≤ t → V t ≤ 1 := fun t ht => by
    show (α t - α_star) ^ 2 ≤ 1
    nlinarith [(hα_bdd t ht).1, (hα_bdd t ht).2, hα_star_bdd.1, hα_star_bdd.2]
  -- V is continuous on [0, ∞)
  have hV_cont : ContinuousOn V (Ici 0) :=
    (hα_cont.sub continuousOn_const).pow 2
  -- V has derivative 2(α-α*)·oaScalarRHS at t > 0
  have hV_deriv : ∀ t, 0 < t →
      HasDerivAt V (2 * (α t - α_star) * oaScalarRHS γ K r t (α t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => α s - α_star) (oaScalarRHS γ K r t (α t)) t :=
      (hα_ode t ht).sub_const α_star
    have h2 := h1.pow 2
    convert h2 using 1
    push_cast; ring
  -- V' bound: 2(α-α*)·oaScalarRHS ≤ -2γV + K|r - r*|
  have hV_ineq : ∀ t, 0 < t →
      2 * (α t - α_star) * oaScalarRHS γ K r t (α t) ≤
        -2 * γ * V t + K * |r t - r_star| := by
    intro t ht
    unfold oaScalarRHS
    exact oa_V_deriv_bound γ K r_star (α t) α_star (r t)
      hγ hK hr_star (hα_bdd t (le_of_lt ht)).1 (hα_bdd t (le_of_lt ht)).2
      hα_star_bdd.1 hα_star_bdd.2 hα_star_eq
  -- ε-N argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose δ = γε/K so that K·δ/(2γ) = ε/2
  have hδ_pos : 0 < γ * ε / K := by positivity
  -- Choose T so |r(t)-r*| < δ for t ≥ T
  rw [Metric.tendsto_atTop] at hr_tendsto
  obtain ⟨T₀, hT₀⟩ := hr_tendsto (γ * ε / K) hδ_pos
  -- T = max T₀ 0 ensures T ≥ 0
  let T := max T₀ 0
  have hT_ge : T₀ ≤ T := le_max_left T₀ 0
  have hT_nn : (0 : ℝ) ≤ T := le_max_right T₀ 0
  -- For t ≥ T: |r(t) - r*| < γε/K → K|r(t)-r*| ≤ γε
  have h_forcing : ∀ t, T ≤ t → K * |r t - r_star| ≤ γ * ε := by
    intro t ht
    have h := hT₀ t (le_trans hT_ge ht)
    rw [Real.dist_eq] at h
    have h2 : K * |r t - r_star| < K * (γ * ε / K) :=
      mul_lt_mul_of_pos_left h hK
    have h3 : K * (γ * ε / K) = γ * ε := by field_simp
    linarith
  -- Shifted V̂(s) = V(T + s) satisfies the same structure
  let V_shift := fun s => V (T + s)
  -- V_shift continuous on [0, ∞)
  have hVs_cont : ContinuousOn V_shift (Ici 0) :=
    hV_cont.comp ((continuous_const.add continuous_id).continuousOn)
      (fun s hs => mem_Ici.mpr (by simp only [mem_Ici] at hs; linarith))
  -- V_shift has derivative ≤ -2γ·V_shift + γε for s > 0
  have hVs_deriv : ∀ s, 0 < s →
      HasDerivAt V_shift (2 * (α (T + s) - α_star) *
        oaScalarRHS γ K r (T + s) (α (T + s))) s := by
    intro s hs
    have hinner : HasDerivAt (fun x => T + x) 1 s := by
      simpa using (hasDerivAt_id s).const_add T
    have hV := hV_deriv (T + s) (by linarith [hT_nn])
    exact hV.comp s hinner |>.congr_deriv (by ring)
  have hVs_bound : ∀ s, 0 < s →
      2 * (α (T + s) - α_star) * oaScalarRHS γ K r (T + s) (α (T + s)) ≤
        -(2 * γ) * V_shift s + γ * ε := by
    intro s hs
    have h1 := hV_ineq (T + s) (by linarith [hT_nn])
    have h2 := h_forcing (T + s) (by linarith)
    have h3 : -(2 * γ) * V_shift s = -2 * γ * V_shift s := by ring
    linarith
  -- Apply gronwall_with_forcing: V_shift(s) ≤ V_shift(0)·exp(-2γs) + ε/2
  have h_exp_pos : 0 < 2 * γ := by linarith
  have hVs_gronwall : ∀ s, 0 ≤ s →
      V_shift s ≤ V_shift 0 * rexp (-(2 * γ) * s) + γ * ε / (2 * γ) :=
    gronwall_with_forcing V_shift
      (fun s => 2 * (α (T + s) - α_star) * oaScalarRHS γ K r (T + s) (α (T + s)))
      (2 * γ) (γ * ε) (by linarith) (by positivity) hVs_cont
      (fun s hs => hVs_deriv s hs) (fun s hs => hVs_bound s hs)
  -- Simplify: γε/(2γ) = ε/2
  have h_simp : γ * ε / (2 * γ) = ε / 2 := by field_simp
  -- V_shift(0) = V(T) ≤ 1
  have hV_shift0_bdd : V_shift 0 ≤ 1 := by
    simp only [V_shift, add_zero]; exact hV_bdd T hT_nn
  -- exp(-2γs) → 0 as s → ∞; choose N with exp(-(2γ)N) < ε/2
  obtain ⟨N, hN⟩ : ∃ N : ℝ, 0 ≤ N ∧ rexp (-(2 * γ) * N) < ε / 2 := by
    have htend : Tendsto (fun s => rexp (-(2 * γ) * s)) atTop (nhds 0) := by
      simp_rw [show ∀ s : ℝ, -(2 * γ) * s = -(2 * γ * s) from fun s => by ring]
      exact tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_atTop_atTop.mpr fun b => ⟨b / (2 * γ), fun y hy => by
          nlinarith [(div_le_iff₀ h_exp_pos).mp hy]⟩)
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨M, hM⟩ := htend (ε / 2) (half_pos hε)
    exact ⟨max M 0, le_max_right M 0, by
      have := hM (max M 0) (le_max_left M 0)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (exp_nonneg _)] at this
      exact this⟩
  -- For t ≥ T + N: V(t) < ε
  refine ⟨T + N, fun t ht => ?_⟩
  have hs_nn : 0 ≤ t - T := by linarith
  have hs_geN : N ≤ t - T := by linarith [hN.1]
  have hVt_eq : V t = V_shift (t - T) := by simp [V_shift]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hV_nn t), hVt_eq]
  have hVs := hVs_gronwall (t - T) hs_nn
  rw [h_simp] at hVs
  calc V_shift (t - T)
      ≤ V_shift 0 * rexp (-(2 * γ) * (t - T)) + ε / 2 := hVs
    _ ≤ 1 * rexp (-(2 * γ) * (t - T)) + ε / 2 := by
        linarith [mul_le_mul_of_nonneg_right hV_shift0_bdd (exp_nonneg (-(2 * γ) * (t - T)))]
    _ = rexp (-(2 * γ) * (t - T)) + ε / 2 := by ring
    _ ≤ rexp (-(2 * γ) * N) + ε / 2 := by
        have hexp : rexp (-(2 * γ) * (t - T)) ≤ rexp (-(2 * γ) * N) :=
          Real.exp_le_exp.mpr (by nlinarith [h_exp_pos])
        linarith
    _ < ε / 2 + ε / 2 := by linarith [hN.2]
    _ = ε := by ring

/-! ## V∞ → 0 via dominated convergence -/

/-- **Continuum Lyapunov convergence from r(t) → r*.**
    If r(t) → r* and γ(ω) > 0 a.e., then V∞(t) = ∫(α-α*)² dμ → 0.

    Proof: pointwise convergence (oa_scalar_pointwise_tendsto) + DCT with bound 4. -/
theorem V_inf_tendsto_zero_from_r
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K)
    (hγ_ae_pos : ∀ᵐ ω ∂μ, 0 < γ ω)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ)
    (hr_tendsto : Tendsto r atTop (nhds r_star))
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (α : Ω → ℝ → ℝ)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_ode : ∀ ω t, 0 < t → HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_bdd : ∀ ω t, 0 ≤ t → 0 ≤ α ω t ∧ α ω t ≤ 1)
    (hα_sq_meas : ∀ t, AEStronglyMeasurable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) := by
  -- For a.e. ω, γ(ω) > 0, so the per-ω convergence applies
  have h_pw : ∀ᵐ ω ∂μ, Tendsto (fun t => (α ω t - α_star ω) ^ 2) atTop (nhds 0) := by
    filter_upwards [hγ_ae_pos] with ω hγ_pos
    exact oa_scalar_pointwise_tendsto (γ ω) K r_star hγ_pos hK hr_star_pos
      r hr_tendsto hr_bdd (α ω) (hα_cont ω) (hα_ode ω)
      (hα_bdd ω) (α_star ω) (hα_star_equil ω)
      ⟨le_of_lt (hα_star_pos ω), le_of_lt (hα_star_lt ω)⟩
  -- Apply dominated convergence: bound is 4 (constant), a.e. converging
  have h_bound : ∀ᶠ t in atTop, ∀ᵐ ω ∂μ, ‖(α ω t - α_star ω) ^ 2‖ ≤ (4 : ℝ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    apply Eventually.of_forall; intro ω
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hα_bdd ω t ht).1, (hα_bdd ω t ht).2,
               (hα_star_pos ω).le, (hα_star_lt ω).le,
               sq_nonneg (α ω t - α_star ω)]
  -- Convert: ∫(α-α*)² → ∫0 = 0
  have h_dct := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Ω => (4 : ℝ))
    (Eventually.of_forall fun t => hα_sq_meas t)
    h_bound (integrable_const 4)
    (by filter_upwards [h_pw] with ω h_ω; exact h_ω)
  simp only [integral_zero] at h_dct
  exact h_dct

end
