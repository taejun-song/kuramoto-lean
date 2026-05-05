/-
  Kuramoto Stability — Standard Continuum Convergence (Final)
  ============================================================
  End-to-end theorem for the STANDARD continuum Kuramoto model:
  - γ(ω) = |ω| UNBOUNDED on R, but INTEGRABLE: ∫γ dμ < ∞
  - Body persistence only (not uniform)
  - Arbitrary probability measure (no minimum atom)

  Key new ingredient: body pair coercive bound.
  ∫∫_all pair ≥ 2·δ·ds·μ(body)·V_body
  proved via:
    1. pair_ge_delta_sq on body×body (pointwise coercivity)
    2. pair(ω₁, ·) integrable (from Q, S integrability)
    3. Monotonicity chain: ∫∫_all ≥ ∫_{body}∫ ≥ ∫_{body}∫_{body} ≥ coercive

  Covers: Gaussian, Student-t ν>2, compact support. NOT Lorentzian.
  0 sorry. 0 axioms.
-/

import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.AntitoneConvergence
import KuramotoLean.ContinuumFiniteMoment

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Leibniz rule with integrable γ dominator -/

private theorem leibniz_integrable_gamma
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hγ_int : Integrable γ μ) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hK : 0 < K) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hαs_int : Integrable α_star μ)
    (hγ_meas : AEStronglyMeasurable γ μ) :
    ContinuousOn (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0) ∧
    (∀ t, 0 < t → HasDerivAt (fun s => ∫ ω, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ) t) := by
  have hα_inv_all : ∀ ω t, 0 < α ω t ∧ α ω t < 1 := by
    intro ω t; by_cases ht : 0 ≤ t
    · exact hα_inv ω t ht
    · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]; exact hα_inv ω 0 le_rfl
  have hα_cts : ∀ ω, Continuous (α ω) := by
    intro ω
    have h_eq : α ω = fun t => α ω (max t 0) := by
      ext t; by_cases ht : 0 ≤ t
      · simp [max_eq_left ht]
      · push_neg at ht; rw [hα_neg ω t (le_of_lt ht), max_eq_right (le_of_lt ht)]
    rw [h_eq]
    exact (hα_cont ω).comp_continuous (continuous_id.max continuous_const)
      (fun t => mem_Ici.mpr (le_max_right t 0))
  constructor
  · exact (MeasureTheory.continuous_of_dominated
      (F := fun t ω => (α ω t - α_star ω) ^ 2) (bound := fun _ => (1 : ℝ))
      (fun t => (hα_sq_int t).aestronglyMeasurable)
      (fun t => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hα_inv_all ω t).1, (hα_inv_all ω t).2,
          hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)])
      (integrable_const 1)
      (Eventually.of_forall fun ω => ((hα_cts ω).sub continuous_const).pow 2)).continuousOn
  · intro t ht
    exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s ω => (α ω s - α_star ω) ^ 2)
      (F' := fun s ω => 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s))
      (bound := fun ω => 2 * γ ω + K)
      (hs := Ioi_mem_nhds ht)
      (hF_meas := Eventually.of_forall fun s => (hα_sq_int s).aestronglyMeasurable)
      (hF_int := hα_sq_int t)
      (hF'_meas := by
        show AEStronglyMeasurable
          (fun ω => 2 * (α ω t - α_star ω) *
            (-(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2))) μ
        exact ((aestronglyMeasurable_const.mul
          ((hα_int t).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable)).mul
          ((hγ_meas.neg.mul (hα_int t).aestronglyMeasurable).add
            (aestronglyMeasurable_const.mul
              (aestronglyMeasurable_const.sub
                ((hα_int t).aestronglyMeasurable.pow 2))))))
      (h_bound := by
        apply Eventually.of_forall; intro ω s hs
        have hs_pos := mem_Ioi.mp hs
        have hp := (hα_inv ω s (le_of_lt hs_pos)).1
        have hl := (hα_inv ω s (le_of_lt hs_pos)).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        have h_diff : |α ω s - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have h_rhs : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ γ ω + K / 2 := by
          unfold oaScalarRHS
          have hr1 := hr_bdd s
          have h1 : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
          have h2 : 1 - (α ω s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω s)]
          have hγ_nn : 0 ≤ γ ω := hγ_nn ω
          have hα_nn : 0 ≤ α ω s := le_of_lt hp
          have hα_le : α ω s ≤ 1 := le_of_lt hl
          have hrs_lo : -1 ≤ r s := (abs_le.mp hr1).1
          have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
          rw [abs_le]; constructor <;> nlinarith [mul_nonneg hγ_nn hα_nn,
            mul_nonneg (by linarith : (0:ℝ) ≤ K/2) h1]
        calc ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖
            = 2 * |α ω s - α_star ω| * |oaScalarRHS (γ ω) K r s (α ω s)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
          _ ≤ 2 * 1 * (γ ω + K / 2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h_diff (by positivity))
                h_rhs (abs_nonneg _) (by positivity)
          _ = 2 * γ ω + K := by ring)
      (bound_integrable := (hγ_int.const_mul 2).add (integrable_const K))
      (h_diff := Eventually.of_forall fun ω s hs => by
        have h := (hα_ode ω s (le_of_lt (mem_Ioi.mp hs))).sub_const (α_star ω)
        convert h.pow 2 using 1; push_cast; ring) |>.2

/-! ## Helper: Q-integrand integrability -/

private theorem q_int_of_gamma_int [IsProbabilityMeasure μ]
    (α αs γ : Ω → ℝ) (K r_star : ℝ)
    (hK : 0 < K) (hr_star : 0 < r_star)
    (hα_pos : ∀ ω, 0 < α ω) (hα_lt : ∀ ω, α ω < 1)
    (hαs_pos : ∀ ω, 0 < αs ω) (hαs_lt : ∀ ω, αs ω < 1)
    (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hαs_equil : ∀ ω, γ ω * αs ω = (K / 2) * r_star * (1 - (αs ω) ^ 2))
    (hα_int : Integrable (fun ω => α ω) μ)
    (hαs_int : Integrable αs μ)
    (hα_sq_int : Integrable (fun ω => (α ω - αs ω) ^ 2) μ)
    (hγ_int : Integrable γ μ)
    (hγ_meas : AEStronglyMeasurable γ μ) :
    Integrable (fun ω => (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω)) μ := by
  have hKr : 0 < K * r_star := mul_pos hK hr_star
  have h_inv : ∀ ω, 1 / αs ω = αs ω + 2 * γ ω / (K * r_star) := by
    intro ω
    field_simp [ne_of_gt (hαs_pos ω), ne_of_gt hKr]
    nlinarith [hαs_equil ω, sq_nonneg (αs ω), hαs_pos ω, hαs_lt ω, hγ_nn ω]
  have h_eq : ∀ ω, (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω) =
      (α ω - αs ω) ^ 2 * (α ω + αs ω + 2 / (K * r_star) * γ ω) := by
    intro ω; congr 1; rw [h_inv]; ring
  simp_rw [h_eq]
  exact ((integrable_const 2).add (hγ_int.const_mul (2 / (K * r_star)))).mono'
    ((hα_sq_int.aestronglyMeasurable).mul
      ((hα_int.aestronglyMeasurable.add hαs_int.aestronglyMeasurable).add
        (hγ_meas.const_mul (2 / (K * r_star)))))
    (Eventually.of_forall fun ω => by
      have h_nn : (0 : ℝ) ≤ α ω + αs ω + 2 / (K * r_star) * γ ω := by
        have := hα_pos ω; have := hαs_pos ω; have := hγ_nn ω
        have := div_pos (by norm_num : (0:ℝ) < 2) hKr; linarith [mul_nonneg (le_of_lt this) (hγ_nn ω)]
      have h_sq_le : (α ω - αs ω) ^ 2 ≤ 1 := by
        nlinarith [hα_pos ω, hα_lt ω, hαs_pos ω, hαs_lt ω]
      have h_sum_le : α ω + αs ω + 2 / (K * r_star) * γ ω ≤
          2 + 2 / (K * r_star) * γ ω := by linarith [hα_lt ω, hαs_lt ω]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h_nn)]
      calc (α ω - αs ω) ^ 2 * (α ω + αs ω + 2 / (K * r_star) * γ ω)
          ≤ 1 * (2 + 2 / (K * r_star) * γ ω) :=
            mul_le_mul h_sq_le h_sum_le h_nn zero_le_one
        _ = 2 + 2 / (K * r_star) * γ ω := one_mul _)

private theorem s_int_bdd [IsProbabilityMeasure μ]
    (α αs : Ω → ℝ)
    (hα_pos : ∀ ω, 0 < α ω) (hα_lt : ∀ ω, α ω < 1)
    (hαs_pos : ∀ ω, 0 < αs ω) (hαs_lt : ∀ ω, αs ω < 1)
    (hα_int : Integrable (fun ω => α ω) μ)
    (hαs_int : Integrable αs μ) :
    Integrable (fun ω => (α ω - αs ω) * (1 - (α ω) ^ 2)) μ :=
  (integrable_const (1:ℝ)).mono'
    ((hα_int.aestronglyMeasurable.sub hαs_int.aestronglyMeasurable).mul
      (aestronglyMeasurable_const.sub (hα_int.aestronglyMeasurable.pow 2)))
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |α ω - αs ω| * |1 - (α ω) ^ 2|
          ≤ 1 * 1 := mul_le_mul
            (abs_le.mpr ⟨by linarith [hα_pos ω, hαs_lt ω], by linarith [hα_lt ω, hαs_pos ω]⟩)
            (by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (α ω), hα_lt ω, hα_pos ω])
            (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1)

/-! ## Pair inner integrability -/

private theorem pair_inner_integrable
    (α αs : Ω → ℝ) (ω₁ : Ω)
    (hq_int : Integrable (fun ω => (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω)) μ)
    (hs_int : Integrable (fun ω => (α ω - αs ω) * (1 - (α ω) ^ 2)) μ)
    (hαs_int : Integrable αs μ)
    (hp_int : Integrable (fun ω => α ω - αs ω) μ) :
    Integrable (fun ω₂ => pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂)) μ := by
  have h_rw : (fun ω₂ => pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂)) =
      fun ω₂ =>
        (αs ω₁ * ((α ω₂ - αs ω₂) ^ 2 * (α ω₂ + 1 / αs ω₂)) -
         (α ω₁ - αs ω₁) * ((α ω₂ - αs ω₂) * (1 - α ω₂ ^ 2))) +
        (αs ω₂ * ((α ω₁ - αs ω₁) ^ 2 * (α ω₁ + 1 / αs ω₁)) -
         (α ω₁ - αs ω₁) * (α ω₂ - αs ω₂) * (1 - α ω₁ ^ 2)) := by
    ext ω₂; unfold pairIntegrand; ring
  rw [h_rw]
  exact ((hq_int.const_mul _).sub (hs_int.const_mul _)).add
    ((hαs_int.mul_const _).sub ((hp_int.const_mul _).mul_const _))

/-! ## Body pair coercive bound

The key new lemma: ∫∫_all pair ≥ 2·δ·ds·μ(body)·V_body.

Chain:
  ∫∫_all pair
  ≥ ∫_{body} [∫_all pair(ω₁,·)]      (setIntegral_le_integral, outer nonneg)
  ≥ ∫_{body} [∫_{body} pair(ω₁,·)]   (setIntegral_mono_on, inner nonneg)
  ≥ ∫_{body} [δ·ds·(p₁²·m + V_b)]    (pair_ge_delta_sq on body)
  = 2·δ·ds·μ(body)·V_body             (computation)
-/

private theorem body_pair_coercive [IsProbabilityMeasure μ]
    (α αs : Ω → ℝ) (γ : Ω → ℝ) (K r_star : ℝ) (δ ds : ℝ)
    (body : Set Ω)
    (hα_pos : ∀ ω, 0 < α ω) (hα_lt : ∀ ω, α ω < 1)
    (hαs_pos : ∀ ω, 0 < αs ω) (hαs_lt : ∀ ω, αs ω < 1)
    (hδ_pos : 0 < δ) (hds_pos : 0 < ds)
    (hα_lb : ∀ ω, ω ∈ body → δ ≤ α ω)
    (hαs_lb : ∀ ω, ω ∈ body → ds ≤ αs ω)
    (hbody_meas : MeasurableSet body)
    (hq_int : Integrable (fun ω => (α ω - αs ω) ^ 2 * (α ω + 1 / αs ω)) μ)
    (hs_int : Integrable (fun ω => (α ω - αs ω) * (1 - (α ω) ^ 2)) μ)
    (hαs_int : Integrable αs μ)
    (hp_int : Integrable (fun ω => α ω - αs ω) μ)
    (hα_sq_int : Integrable (fun ω => (α ω - αs ω) ^ 2) μ)
    (h_outer_int : Integrable (fun ω₁ =>
      ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ) μ) :
    2 * (δ * ds) * (μ body).toReal * ∫ ω in body, (α ω - αs ω) ^ 2 ∂μ ≤
    ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ ∂μ := by
  set V_body := ∫ ω in body, (α ω - αs ω) ^ 2 ∂μ
  set m := (μ body).toReal
  set g_all := fun ω₁ => ∫ ω₂, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ
  set g_body := fun ω₁ => ∫ ω₂ in body, pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) ∂μ
  have h_pair_nn : ∀ ω₁ ω₂, 0 ≤ pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) :=
    fun ω₁ ω₂ => pair_bound (α ω₁) (α ω₂) (αs ω₁) (αs ω₂)
      (hα_pos ω₁) (hα_pos ω₂) (hα_lt ω₁) (hα_lt ω₂) (hαs_pos ω₁) (hαs_pos ω₂)
  have h_inner_int : ∀ ω₁, Integrable
      (fun ω₂ => pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂)) μ :=
    fun ω₁ => pair_inner_integrable α αs ω₁ hq_int hs_int hαs_int hp_int
  have hg_all_nn : ∀ ω₁, 0 ≤ g_all ω₁ :=
    fun ω₁ => integral_nonneg (h_pair_nn ω₁)
  have hg_body_nn : ∀ ω₁, 0 ≤ g_body ω₁ :=
    fun ω₁ => integral_nonneg (h_pair_nn ω₁)
  -- Step 1: ∫∫ pair ≥ ∫_{body} g_all (outer monotonicity)
  have h_step1 : ∫ ω₁ in body, g_all ω₁ ∂μ ≤ ∫ ω₁, g_all ω₁ ∂μ :=
    setIntegral_le_integral h_outer_int (ae_of_all μ hg_all_nn)
  -- Steps 2+3 combined: ∫_{body} g_all ≥ ∫_{body} [δ·ds·(p₁²·m + V_body)]
  -- For each ω₁ ∈ body: g_all(ω₁) ≥ g_body(ω₁) ≥ δ·ds·(p₁²·m + V_body)
  have h_combined : ∫ ω₁ in body, δ * ds * ((α ω₁ - αs ω₁) ^ 2 * m + V_body) ∂μ ≤
      ∫ ω₁ in body, g_all ω₁ ∂μ := by
    apply setIntegral_mono_on
    · exact ((hα_sq_int.integrableOn.mul_const _).add
        (integrable_const _).integrableOn).const_mul _
    · exact h_outer_int.integrableOn
    · exact hbody_meas
    · intro ω₁ hω₁
      -- g_all(ω₁) ≥ g_body(ω₁)
      have h_ge_body : g_body ω₁ ≤ g_all ω₁ :=
        setIntegral_le_integral (h_inner_int ω₁) (ae_of_all μ (h_pair_nn ω₁))
      -- g_body(ω₁) ≥ δ·ds·(p₁²·m + V_body)
      have h_pw : ∀ ω₂, ω₂ ∈ body →
          δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ≤
          pairIntegrand (α ω₁) (αs ω₁) (α ω₂) (αs ω₂) :=
        fun ω₂ hω₂ => pair_ge_delta_sq (hα_pos ω₁) (hα_pos ω₂) (hα_lt ω₁) (hα_lt ω₂)
          (hαs_pos ω₁) (hαs_pos ω₂) hδ_pos (hα_lb ω₁ hω₁) (hα_lb ω₂ hω₂)
          (hαs_lb ω₁ hω₁) (hαs_lb ω₂ hω₂)
      have h_lhs_eq : δ * ds * ((α ω₁ - αs ω₁) ^ 2 * m + V_body) =
          ∫ ω₂ in body, δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ∂μ := by
        have hrw : ∫ ω₂ in body, δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ∂μ =
            δ * ds * ∫ ω₂ in body, ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ∂μ :=
          integral_const_mul _ _
        rw [hrw, integral_add (integrable_const _).integrableOn hα_sq_int.integrableOn,
            setIntegral_const]
        simp only [m, V_body, Measure.real, smul_eq_mul]; ring
      have h_int_lb : IntegrableOn
          (fun ω₂ => δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2)) body μ :=
        ((integrable_const _).integrableOn.add hα_sq_int.integrableOn).const_mul _
      calc δ * ds * ((α ω₁ - αs ω₁) ^ 2 * m + V_body)
          = ∫ ω₂ in body, δ * ds * ((α ω₁ - αs ω₁) ^ 2 + (α ω₂ - αs ω₂) ^ 2) ∂μ := h_lhs_eq
        _ ≤ g_body ω₁ := setIntegral_mono_on h_int_lb
            (h_inner_int ω₁).integrableOn hbody_meas (fun ω₂ hω₂ => h_pw ω₂ hω₂)
        _ ≤ g_all ω₁ := h_ge_body
  -- Step 4: compute ∫_{body} δ·ds·(p₁²·m + V_body) = 2·δ·ds·m·V_body
  have h_step4 : 2 * (δ * ds) * m * V_body =
      ∫ ω₁ in body, δ * ds * ((α ω₁ - αs ω₁) ^ 2 * m + V_body) ∂μ := by
    rw [integral_const_mul, integral_add (hα_sq_int.integrableOn.mul_const _)
        (integrable_const _).integrableOn, integral_mul_const, setIntegral_const]
    simp only [m, V_body, Measure.real, smul_eq_mul]; ring
  linarith [h_step1, h_combined, h_step4]

/-! ## Main theorem -/

theorem kuramoto_standard_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_int_pos : 0 < ∫ ω, γ ω ∂μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (α_0 : Ω → ℝ) (_hα_0_pos : ∀ ω, 0 < α_0 ω) (_hα_0_lt : ∀ ω, α_0 ω < 1)
    (h_exists : ∃ (r : ℝ → ℝ) (α : Ω → ℝ → ℝ),
      Continuous r ∧ (∀ t, |r t| ≤ 1) ∧ (∀ t, 0 ≤ t → 0 ≤ r t) ∧
      (∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t) ∧
      (∀ ω, ContinuousOn (α ω) (Ici 0)) ∧
      (∀ ω, α ω 0 = α_0 ω) ∧
      (∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, t ≤ 0 → α ω t = α ω 0) ∧
      (∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) ∧
      (∀ M, 0 < M → ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) ∧
      (∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, hr_cont, hr_bdd, hr_nn, hα_ode, hα_cont, _hα_init, h_sc,
    hα_int, hα_sq_int, hα_neg, hα_inv, h_body_persist, hγ_level⟩ := h_exists
  refine ⟨r, hr_cont, ?_⟩
  haveI : SFinite μ := inferInstance
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  have hV_nn : ∀ t, 0 ≤ V t := fun t => integral_nonneg (fun _ => sq_nonneg _)
  -- Step 1: Leibniz with integrable γ
  have ⟨hV_cont_on, hV_has_deriv⟩ :=
    leibniz_integrable_gamma (μ := μ) γ K r α α_star hα_ode hα_inv hα_sq_int
      hγ_int hγ hK hr_bdd hα_star_pos hα_star_lt hα_cont hα_neg hα_int hαs_int hγ_meas
  -- r* > 0
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq]
    have h_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ :=
      integral_nonneg (fun ω => (hα_star_pos ω).le)
    rcases h_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨ω, hω⟩ := ((integral_eq_zero_iff_of_nonneg
        (fun ω => (hα_star_pos ω).le) hαs_int).mp h.symm).exists
      simp at hω; linarith [hα_star_pos ω]
  -- Step 2: dV/dt ≤ 0
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    have h_unfold : ∀ ω, oaScalarRHS (γ ω) K r t (α ω t) =
        -(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2) := fun _ => rfl
    simp_rw [h_unfold]
    have hq := q_int_of_gamma_int (fun ω => α ω t) α_star γ K r_star hK hr_star_pos
      (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hγ hα_star_equil (hα_int t) hαs_int (hα_sq_int t) hγ_int hγ_meas
    have hs := s_int_bdd (fun ω => α ω t) α_star
      (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt (hα_int t) hαs_int
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK hγ (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t) hq hs
  -- Step 3: V antitone
  have hV_anti : Antitone V :=
    lyapunov_antitone γ K r α α_star r_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  -- Step 4: V → 0
  have hV_zero : Tendsto V atTop (nhds 0) := by
    obtain ⟨L, hL_nn, hV_lim⟩ := antitone_bounded_converges V hV_anti hV_nn
    suffices hL0 : L = 0 by rwa [hL0] at hV_lim
    by_contra hL_ne
    have hL_pos : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL_ne)
    have hVt_ge_L : ∀ t, L ≤ V t :=
      fun t => le_of_tendsto hV_lim (eventually_atTop.mpr ⟨t, fun s hs => hV_anti hs⟩)
    have hL_le_one : L ≤ 1 := by
      have hV0_le : V 0 ≤ 1 := by
        have h1 : (∫ _, (1:ℝ) ∂μ) = 1 := by
          rw [integral_const]; simp [Measure.real, measure_univ]
        calc V 0 ≤ ∫ _, (1:ℝ) ∂μ :=
              integral_mono (hα_sq_int 0) (integrable_const 1) (fun ω => by
                simp only [Pi.one_apply]
                nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2,
                           hα_star_pos ω, hα_star_lt ω])
          _ = 1 := h1
      linarith [hVt_ge_L 0]
    -- Choose M for tail < L/4
    set C_γ := ∫ ω, γ ω ∂μ
    have hCγ_nn : 0 ≤ C_γ := integral_nonneg (fun ω => hγ ω)
    have hCγ_pos : 0 < C_γ := hγ_int_pos
    set M := max (4 * C_γ / L) 1 with hM_def
    have hM_pos : (0:ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    set body := {ω | γ ω ≤ M}
    have hbody_meas : MeasurableSet body := hγ_level M
    -- Tail measure < L/4
    have h_tail_small : (μ {ω | M < γ ω}).toReal ≤ L / 4 := by
      have h_markov : (μ {ω | M < γ ω}).toReal * M ≤ C_γ := by
        have h_meas : MeasurableSet {ω | M < γ ω} := by
          rw [show {ω | M < γ ω} = bodyᶜ from by ext ω; simp [body, not_le]]
          exact hbody_meas.compl
        calc (μ {ω | M < γ ω}).toReal * M = ∫ _ in {ω | M < γ ω}, M ∂μ := by
              rw [setIntegral_const]; simp [Measure.real, smul_eq_mul, mul_comm]
          _ ≤ ∫ ω in {ω | M < γ ω}, γ ω ∂μ :=
              setIntegral_mono_on (integrable_const M).integrableOn
                hγ_int.integrableOn h_meas (fun ω hω => le_of_lt hω)
          _ ≤ C_γ := setIntegral_le_integral hγ_int
              (ae_of_all μ fun ω => hγ ω)
      calc (μ {ω | M < γ ω}).toReal ≤ C_γ / M := (le_div_iff₀ hM_pos).mpr h_markov
        _ ≤ C_γ / (4 * C_γ / L) := div_le_div_of_nonneg_left hCγ_nn
              (div_pos (by positivity) hL_pos) (le_max_left _ _)
        _ = L / 4 := by
            have hL' : L ≠ 0 := ne_of_gt hL_pos
            have hCγ' : C_γ ≠ 0 := ne_of_gt hCγ_pos
            field_simp
    -- Body persistence
    obtain ⟨δ_M, hδ_M_pos, hα_lb_body⟩ := h_body_persist M hM_pos
    set ds_M := K * r_star / (2 * M + K * r_star)
    have h_denom_pos : 0 < 2 * M + K * r_star := by positivity
    have hds_M_pos : 0 < ds_M := div_pos (mul_pos hK hr_star_pos) h_denom_pos
    have hds_lb_body : ∀ ω, γ ω ≤ M → ds_M ≤ α_star ω := by
      intro ω hγω
      rw [div_le_iff₀ h_denom_pos]
      nlinarith [hα_star_equil ω, sq_nonneg (α_star ω), hα_star_pos ω, hα_star_lt ω]
    -- V_body ≥ 3L/4
    set V_body := fun t => ∫ ω in body, (α ω t - α_star ω) ^ 2 ∂μ
    have hVb_ge : ∀ t, 3 * L / 4 ≤ V_body t := by
      intro t
      have h_tail_le : ∫ ω in bodyᶜ, (α ω t - α_star ω) ^ 2 ∂μ ≤ L / 4 := by
        calc ∫ ω in bodyᶜ, (α ω t - α_star ω) ^ 2 ∂μ
            ≤ ∫ _ in bodyᶜ, (1:ℝ) ∂μ := by
              apply setIntegral_mono_on (hα_sq_int t).integrableOn
                (integrable_const 1).integrableOn hbody_meas.compl fun ω _ => by
                by_cases ht : 0 ≤ t
                · nlinarith [(hα_inv ω t ht).1, (hα_inv ω t ht).2, hα_star_pos ω, hα_star_lt ω]
                · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]
                  nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2, hα_star_pos ω, hα_star_lt ω]
          _ = (μ bodyᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real, smul_eq_mul]
          _ = (μ {ω | M < γ ω}).toReal := by
              have hset : bodyᶜ = {ω | M < γ ω} := by ext ω; simp [body, not_le]
              rw [hset]
          _ ≤ L / 4 := h_tail_small
      have hVb_nn : 0 ≤ V_body t := integral_nonneg (fun _ => sq_nonneg _)
      linarith [hVt_ge_L t, (integral_add_compl hbody_meas (hα_sq_int t)).symm]
    -- μ(body) > 0
    have hbody_pos : μ body ≠ 0 := by
      intro heq
      have hmass : μ univ = μ body + μ bodyᶜ := (measure_add_measure_compl hbody_meas).symm
      rw [measure_univ, heq, zero_add] at hmass
      have hbc1 : (μ bodyᶜ).toReal = 1 := by
        have h := congr_arg ENNReal.toReal hmass
        simp only [ENNReal.toReal_one] at h; exact h.symm
      have hbc2 : (μ bodyᶜ).toReal = (μ {ω | M < γ ω}).toReal := by
        have hset : bodyᶜ = {ω | M < γ ω} := by ext ω; simp [body, not_le]
        rw [hset]
      have htail_one : (μ {ω | M < γ ω}).toReal = 1 := by rw [← hbc2, hbc1]
      linarith [h_tail_small, hL_le_one]
    have hbody_toReal_pos : 0 < (μ body).toReal :=
      ENNReal.toReal_pos hbody_pos (measure_ne_top μ body)
    -- dV/dt ≤ -c₀ for all t > 0
    set c₀ := K / 2 * (2 * δ_M * ds_M * (μ body).toReal * (3 * L / 4))
    have hc₀_pos : 0 < c₀ := by positivity
    have hV'_le : ∀ s, 0 < s →
        ∫ ω, 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s) ∂μ ≤ -c₀ := by
      intro s hs
      have h_unfold : ∀ ω, oaScalarRHS (γ ω) K r s (α ω s) =
          -(γ ω) * α ω s + K / 2 * r s * (1 - (α ω s) ^ 2) := fun _ => rfl
      simp_rw [h_unfold]
      -- Q and S integrability
      have hq_int := q_int_of_gamma_int (fun ω => α ω s) α_star γ K r_star hK hr_star_pos
        (fun ω => (hα_inv ω s (le_of_lt hs)).1) (fun ω => (hα_inv ω s (le_of_lt hs)).2)
        hα_star_pos hα_star_lt hγ hα_star_equil (hα_int s) hαs_int (hα_sq_int s) hγ_int hγ_meas
      have hs_int := s_int_bdd (fun ω => α ω s) α_star
        (fun ω => (hα_inv ω s (le_of_lt hs)).1) (fun ω => (hα_inv ω s (le_of_lt hs)).2)
        hα_star_pos hα_star_lt (hα_int s) hαs_int
      have hp_int : Integrable (fun ω => α ω s - α_star ω) μ := (hα_int s).sub hαs_int
      -- Per-ω identity → integral formula
      have h_pw : ∀ ω, 2 * (α ω s - α_star ω) *
          (-(γ ω) * α ω s + K / 2 * r s * (1 - (α ω s) ^ 2)) =
          (-K * r_star) * ((α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω)) +
          (K * (r s - r_star)) * ((α ω s - α_star ω) * (1 - (α ω s) ^ 2)) := by
        intro ω
        have hγω : γ ω = K / 2 * r_star * (1 - (α_star ω) ^ 2) / α_star ω := by
          field_simp [ne_of_gt (hα_star_pos ω)] at hα_star_equil ⊢; linarith [hα_star_equil ω]
        rw [hγω]; field_simp [ne_of_gt (hα_star_pos ω)]; ring
      simp_rw [h_pw]
      rw [integral_add (hq_int.const_mul _) (hs_int.const_mul _)]
      simp_rw [integral_const_mul]
      set Q := ∫ ω, (α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω) ∂μ
      set S := ∫ ω, (α ω s - α_star ω) * (1 - (α ω s) ^ 2) ∂μ
      set D := r s - r_star
      have h_D_eq : ∫ ω, (α ω s - α_star ω) ∂μ = D := by
        simp [D]; rw [integral_sub (hα_int s) hαs_int, h_sc s (le_of_lt hs), hr_star_eq]
      -- Pair Fubini identity: 2(r*·Q - D·S) = ∫∫ pair
      have h_out12 : Integrable (fun ω₁ =>
          α_star ω₁ * Q - (α ω₁ s - α_star ω₁) * S) μ :=
        (hαs_int.mul_const _).sub (hp_int.mul_const _)
      have h_out21 : Integrable (fun ω₁ =>
          (α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁) * (∫ ω, α_star ω ∂μ) -
          (α ω₁ s - α_star ω₁) * (1 - (α ω₁ s) ^ 2) * (∫ ω, (α ω s - α_star ω) ∂μ)) μ :=
        (hq_int.mul_const _).sub (hs_int.mul_const _)
      have h_fub := pair_fubini_identity (μ := μ) (fun ω => α ω s) α_star
        hq_int hs_int hαs_int hp_int h_out12 h_out21
      rw [hr_star_eq.symm, h_D_eq] at h_fub
      -- Outer integrability for body_pair_coercive
      have h_outer_int : Integrable (fun ω₁ =>
          ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ) μ := by
        have h_eq : ∀ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ =
            (α_star ω₁ * Q - (α ω₁ s - α_star ω₁) * S) +
            ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁) * (∫ ω, α_star ω ∂μ) -
             (α ω₁ s - α_star ω₁) * (1 - (α ω₁ s) ^ 2) * (∫ ω, (α ω s - α_star ω) ∂μ)) := by
          intro ω₁
          have hi12 : Integrable (fun ω₂ =>
              α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) μ :=
            (hq_int.const_mul _).sub (hs_int.const_mul _)
          have hi21 : Integrable (fun ω₂ =>
              α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
              (α ω₁ s - α_star ω₁) * (α ω₂ s - α_star ω₂) * (1 - α ω₁ s ^ 2)) μ :=
            (hαs_int.mul_const _).sub ((hp_int.const_mul _).mul_const _)
          have h_rw : ∀ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) =
              (α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
               (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
              (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
               (α ω₁ s - α_star ω₁) * (α ω₂ s - α_star ω₂) * (1 - α ω₁ s ^ 2)) := by
            intro ω₂; unfold pairIntegrand; ring
          simp_rw [h_rw]; rw [integral_add hi12 hi21]
          congr 1
          · rw [integral_sub (hq_int.const_mul _) (hs_int.const_mul _),
                integral_const_mul, integral_const_mul]
          · have h_diff : Integrable (fun ω₂ => α ω₂ s - α_star ω₂) μ := hp_int
            simp_rw [show ∀ ω₂, α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
                (α ω₁ s - α_star ω₁) * (α ω₂ s - α_star ω₂) * (1 - α ω₁ s ^ 2) =
                ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) * α_star ω₂ +
                (-(((α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2)))) * (α ω₂ s - α_star ω₂) from fun _ => by ring]
            rw [integral_add (hαs_int.const_mul _) (h_diff.const_mul _),
                integral_const_mul, integral_const_mul]; ring
        exact (h_out12.add h_out21).congr (ae_of_all μ fun ω₁ => (h_eq ω₁).symm)
      -- Body pair coercive bound
      have h_bpc := body_pair_coercive (fun ω => α ω s) α_star γ K r_star δ_M ds_M body
        (fun ω => (hα_inv ω s (le_of_lt hs)).1) (fun ω => (hα_inv ω s (le_of_lt hs)).2)
        hα_star_pos hα_star_lt hδ_M_pos hds_M_pos
        (fun ω hω => hα_lb_body ω hω s (le_of_lt hs))
        (fun ω hω => hds_lb_body ω hω)
        hbody_meas hq_int hs_int hαs_int hp_int (hα_sq_int s) h_outer_int
      -- Connect pair bound to the integral
      have h_pair_eq : ∫ ω₁, ∫ ω₂,
          pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ ∂μ =
          ∫ ω₁, ∫ ω₂,
            ((α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
             (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
              (α ω₁ s - α_star ω₁) * (α ω₂ s - α_star ω₂) * (1 - α ω₁ s ^ 2))) ∂μ ∂μ := by
        congr 1; ext ω₁; congr 1; ext ω₂; unfold pairIntegrand; ring
      rw [h_pair_eq] at h_bpc
      have h_combined2 : 2 * (δ_M * ds_M) * (μ body).toReal * V_body s ≤
          2 * (r_star * Q - D * S) := h_fub ▸ h_bpc
      have hVbs := hVb_ge s
      have hm_pos := hbody_toReal_pos
      have h_lb : K * (δ_M * ds_M) * (μ body).toReal * (3 * L / 4) ≤
          K * (r_star * Q - D * S) := by
        have h1 : (δ_M * ds_M) * (μ body).toReal * (3 * L / 4) ≤
            (δ_M * ds_M) * (μ body).toReal * V_body s :=
          mul_le_mul_of_nonneg_left hVbs (mul_nonneg (mul_nonneg hδ_M_pos.le hds_M_pos.le) hm_pos.le)
        have h2 : (δ_M * ds_M) * (μ body).toReal * V_body s ≤ r_star * Q - D * S := by linarith
        nlinarith [mul_pos hK (mul_pos hδ_M_pos (mul_pos hds_M_pos hm_pos))]
      have hc₀_unfold : c₀ = K * (δ_M * ds_M) * (μ body).toReal * (3 * L / 4) := by ring
      linarith
    -- Linear decrease → V < 0 contradiction
    have hW_le : ∀ n : ℕ, V (1 + ↑n) ≤ V 1 - c₀ * n := by
      intro n; induction n with
      | zero => simp
      | succ k ih =>
        have hsk : (0 : ℝ) < 1 + ↑k := by positivity
        set W : ℝ → ℝ := fun t => V t + c₀ * t
        have hW_anti : AntitoneOn W (Icc (1 + ↑k) (1 + ↑(k + 1))) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          · exact (hV_cont_on.mono (fun t ht => mem_Ici.mpr (le_trans (le_of_lt hsk) ht.1))).add
              (continuousOn_const.mul continuousOn_id)
          · intro t ht; rw [interior_Icc] at ht
            exact ((hV_has_deriv t (lt_trans hsk ht.1)).add
              ((hasDerivAt_id t).const_mul c₀)).differentiableAt.differentiableWithinAt
          · intro t ht; rw [interior_Icc] at ht
            have hWd : HasDerivAt W
                (∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ + c₀ * 1) t :=
              (hV_has_deriv t (lt_trans hsk ht.1)).add ((hasDerivAt_id t).const_mul c₀)
            rw [hWd.deriv]; simp only [mul_one]
            linarith [hV'_le t (lt_trans hsk ht.1)]
        have := hW_anti (left_mem_Icc.mpr (by push_cast; linarith))
          (right_mem_Icc.mpr (by push_cast; linarith)) (by push_cast; linarith)
        simp [W] at this; push_cast at this ih ⊢; linarith
    have : V (1 + ↑(Nat.ceil (V 1 / c₀) + 1)) < 0 := by
      have hn : V 1 - c₀ * ↑(Nat.ceil (V 1 / c₀) + 1) < 0 := by
        have hVc0 : V 1 / c₀ < ↑(Nat.ceil (V 1 / c₀) + 1) := by
          have h1 := Nat.le_ceil (V 1 / c₀)
          have h2 := Nat.lt_succ_self (Nat.ceil (V 1 / c₀))
          exact_mod_cast lt_of_le_of_lt h1 (by exact_mod_cast h2)
        linarith [(div_lt_iff₀ hc₀_pos).mp hVc0]
      linarith [hW_le (Nat.ceil (V 1 / c₀) + 1)]
    linarith [hV_nn (1 + ↑(Nat.ceil (V 1 / c₀) + 1))]
  -- Step 5: V → 0 implies r → r*
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hV_zero
  obtain ⟨N, hN⟩ := hV_zero (ε ^ 2) (by positivity)
  refine ⟨max N 0, fun t ht => ?_⟩
  have ht_ge : N ≤ t := le_trans (le_max_left _ _) ht
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have hV_t := hN t ht_ge
  simp only [Real.dist_eq, sub_zero] at hV_t
  rw [abs_of_nonneg (hV_nn t)] at hV_t
  have hCS : (r t - r_star) ^ 2 ≤ V t := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, integral_sub (hα_int t) hαs_int]
    rw [hrsc]; exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hCS hV_t) (le_of_lt hε)

end
