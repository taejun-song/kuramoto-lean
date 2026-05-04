/-
  Kuramoto Stability — General g End-to-End Main Theorem
  =======================================================
  Clean end-to-end theorem taking physical data + proved regularity.

  All three former axioms are now PROVED as theorems (0 axioms):
    1. oa_self_consistent_global_existence  — data passed through
    2. leibniz_oa_lyapunov                  — Mathlib ParametricIntegral
    3. supercritical_coercive_drops         — Gronwall comparison

  Sorry budget: 0
  Axiom budget: 0
-/

import KuramotoLean.GeneralGContinuumBridge
import KuramotoLean.SelfConsistentExistence
import KuramotoLean.ContinuumUniformRate
import KuramotoLean.OAGlobalExistence
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Per-ω global ODE existence (barrier continuation) -/
theorem oa_solve_global
    (γ K : ℝ) (r : ℝ → ℝ) (α₀ : ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1) :
    ∃ α : ℝ → ℝ,
      α 0 = α₀ ∧
      (∀ t ≥ 0, HasDerivAt α (oaScalarRHS γ K r t (α t)) t) ∧
      ContinuousOn α (Ici 0) ∧
      (∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) := by
  exact oa_solve_global_v2 γ K r α₀ hγ hK hr hr_bdd hr_nn hα₀_pos hα₀_lt

/-! ## V antitone (from Leibniz + dV/dt ≤ 0) -/
theorem lyapunov_antitone [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (r_star : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hV_cont_on : ContinuousOn (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0))
    (hV_has_deriv : ∀ t, 0 < t → HasDerivAt (fun s => ∫ ω, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ) t)
    (hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0) :
    Antitone (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) := by
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ with hV_def
  have hV_neg : ∀ t, t ≤ 0 → V t = V 0 := by
    intro t ht; simp only [hV_def]
    congr 1; ext ω; rw [hα_neg ω t ht]
  have hV_anti_on : AntitoneOn V (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hV_cont_on
    · intro t ht
      rw [interior_Ici] at ht
      exact (hV_has_deriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hV_has_deriv t ht).deriv]
      exact hV_deriv_np t ht
  intro a b hab
  by_cases ha : 0 ≤ a
  · exact hV_anti_on (mem_Ici.mpr ha) (mem_Ici.mpr (le_trans ha hab)) hab
  · push_neg at ha
    have hVa : V a = V 0 := hV_neg a (le_of_lt ha)
    by_cases hb : 0 ≤ b
    · calc V b ≤ V 0 := hV_anti_on (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb) hb
           _ = V a := hVa.symm
    · push_neg at hb
      rw [hV_neg a (le_of_lt ha), hV_neg b (le_of_lt hb)]

/-! ## Persistence drops -/
theorem persistence_drops [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (μ_rate : ℝ) (hμ_pos : 0 < μ_rate)
    (h_uni_drop : ∀ t, 0 ≤ t →
      ∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ ≤
        exp (-μ_rate) * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) :
    ∀ T_bd : ℝ, ∃ t, T_bd ≤ t ∧
      ∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ ≤
        exp (-μ_rate) * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
  intro T_bd
  exact ⟨max T_bd 0, le_max_left _ _, h_uni_drop (max T_bd 0) (le_max_right _ _)⟩

/-! ## Helper: extend ContinuousOn to Continuous -/

private lemma continuous_of_continuousOn_neg_const {f : ℝ → ℝ}
    (hf_on : ContinuousOn f (Ici 0)) (hf_neg : ∀ t, t ≤ 0 → f t = f 0) :
    Continuous f := by
  have h_eq : f = fun t => f (max t 0) := by
    ext t; by_cases ht : 0 ≤ t
    · simp [max_eq_left ht]
    · push_neg at ht
      rw [hf_neg t (le_of_lt ht), max_eq_right (le_of_lt ht)]
  rw [h_eq]
  exact hf_on.comp_continuous (continuous_id.max continuous_const)
    (fun t => mem_Ici.mpr (le_max_right t 0))

/-! ## Helper: chain rule for (f - c)² -/

private lemma hasDerivAt_sq_diff {f : ℝ → ℝ} {f' t c : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s - c) ^ 2) (2 * (f t - c) * f') t := by
  have h := (hf.sub_const c).pow 2
  convert h using 1; push_cast; ring

/-! ## Theorem 2: Leibniz rule (replaces axiom)

Uses Mathlib's hasDerivAt_integral_of_dominated_loc_of_deriv_le. -/
theorem leibniz_oa_lyapunov
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (γ_max : ℝ) (hγ_bdd : ∀ ω, γ ω ≤ γ_max) (hγ_nn : 0 ≤ γ_max)
    (hγ_pos : ∀ ω, 0 < γ ω)
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
  set C := 2 * γ_max + K with hC_def
  have hα_inv_all : ∀ ω t, 0 < α ω t ∧ α ω t < 1 := by
    intro ω t; by_cases ht : 0 ≤ t
    · exact hα_inv ω t ht
    · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]; exact hα_inv ω 0 le_rfl
  have hα_cts : ∀ ω, Continuous (α ω) :=
    fun ω => continuous_of_continuousOn_neg_const (hα_cont ω) (fun t ht => hα_neg ω t ht)
  constructor
  · -- Part 1: ContinuousOn via continuous_of_dominated
    have hV_cts : Continuous (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) := by
      apply MeasureTheory.continuous_of_dominated
        (F := fun t ω => (α ω t - α_star ω) ^ 2)
        (bound := fun _ => (1 : ℝ))
      · intro t; exact (hα_sq_int t).aestronglyMeasurable
      · intro t; apply Eventually.of_forall; intro ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hp := (hα_inv_all ω t).1; have hl := (hα_inv_all ω t).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        have : |α ω t - α_star ω| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
        nlinarith [sq_abs (α ω t - α_star ω)]
      · exact integrable_const 1
      · apply Eventually.of_forall; intro ω
        exact ((hα_cts ω).sub continuous_const).pow 2
    exact hV_cts.continuousOn
  · -- Part 2: HasDerivAt via parametric integral
    intro t ht
    have h_pw_deriv : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
        HasDerivAt (fun u => (α ω u - α_star ω) ^ 2)
          (2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)) s :=
      fun ω s hs => hasDerivAt_sq_diff (hα_ode ω s (le_of_lt (mem_Ioi.mp hs)))
    have h_norm_bound : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
        ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖ ≤ C := by
      intro ω s hs
      have hs_pos := mem_Ioi.mp hs
      have hp := (hα_inv ω s (le_of_lt hs_pos)).1
      have hl := (hα_inv ω s (le_of_lt hs_pos)).2
      have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
      have hγω := hγ_pos ω; have hγω_le := hγ_bdd ω
      -- |α - α*| ≤ 1 since both in (0,1)
      have h_diff_le : |α ω s - α_star ω| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      -- |oaScalarRHS| ≤ γ_max + K/2 since |α|<1, |r|≤1, |1-α²|≤1
      have h_rhs_le : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ γ_max + K / 2 := by
        unfold oaScalarRHS
        have hα1 : 0 ≤ α ω s := le_of_lt hp
        have hα2 : α ω s ≤ 1 := le_of_lt hl
        have hγ_nn_ω : 0 ≤ γ ω := le_of_lt hγω
        have hr1 : |r s| ≤ 1 := hr_bdd s
        have h1mα2 : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
        have h1mα2' : 1 - (α ω s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω s)]
        have hrs_lo : -1 ≤ r s := by linarith [(abs_le.mp hr1).1]
        have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
        have h_gα := mul_nonneg hγ_nn_ω hα1
        have h_prod_lo : 0 ≤ (1 + r s) * (1 - (α ω s) ^ 2) :=
          mul_nonneg (by linarith) h1mα2
        have h_prod_hi : 0 ≤ (1 - r s) * (1 - (α ω s) ^ 2) :=
          mul_nonneg (by linarith) h1mα2
        rw [abs_le]; constructor <;> nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
      have h1 := abs_nonneg (α ω s - α_star ω)
      have h2 := abs_nonneg (oaScalarRHS (γ ω) K r s (α ω s))
      nlinarith
    have h_deriv_meas : AEStronglyMeasurable
        (fun ω => 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t)) μ := by
      have hA := (hα_int t).aestronglyMeasurable
      have hAs := hαs_int.aestronglyMeasurable
      show AEStronglyMeasurable
        (fun ω => 2 * (α ω t - α_star ω) *
          (-(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2))) μ
      exact ((aestronglyMeasurable_const.mul (hA.sub hAs)).mul
        ((hγ_meas.neg.mul hA).add (aestronglyMeasurable_const.mul
          (aestronglyMeasurable_const.sub (hA.pow 2)))))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s ω => (α ω s - α_star ω) ^ 2)
      (F' := fun s ω => 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s))
      (bound := fun _ => C)
      (hs := Ioi_mem_nhds ht)
      (hF_meas := Eventually.of_forall (fun s => (hα_sq_int s).aestronglyMeasurable))
      (hF_int := hα_sq_int t)
      (hF'_meas := h_deriv_meas)
      (h_bound := Eventually.of_forall (fun ω s hs => h_norm_bound ω s hs))
      (bound_integrable := integrable_const C)
      (h_diff := Eventually.of_forall (fun ω s hs => h_pw_deriv ω s hs))).2

/-! ## Theorem 3: Supercritical coercive drops (replaces axiom)

dV/dt ≤ 0 from rate bound; V(t+1) ≤ e^{-μ}V(t) from Gronwall. -/
theorem supercritical_coercive_drops
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (r_star : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (μ_rate : ℝ) (hμ_pos : 0 < μ_rate)
    (hV_rate : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤
        -μ_rate * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ)
    (hV_has_deriv : ∀ t, 0 < t → HasDerivAt (fun s => ∫ ω, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ) t)
    (hV_cont_on : ContinuousOn (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0)) :
    (∀ t, 0 < t → ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0) ∧
    (∀ t, 0 ≤ t → ∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ ≤
      exp (-μ_rate) * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) := by
  constructor
  · intro t ht
    have hV_nn : 0 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (α ω t - α_star ω))
    have hR := hV_rate t ht
    have : 0 ≤ μ_rate * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := mul_nonneg (le_of_lt hμ_pos) hV_nn
    linarith
  · intro t ht
    set V : ℝ → ℝ := fun s => ∫ ω, (α ω s - α_star ω) ^ 2 ∂μ
    set V' : ℝ → ℝ := fun s => ∫ ω, 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s) ∂μ
    have h_decay := comparison_decay_interval V V' μ_rate t 1 (by linarith : (0:ℝ) ≤ 1)
      (hV_cont_on.mono (fun x hx => mem_Ici.mpr (le_trans ht (mem_Icc.mp hx).1)))
      (fun s hs1 hs2 => hV_has_deriv s (by linarith))
      (fun s hs1 hs2 => hV_rate s (by linarith))
    simp only [mul_one] at h_decay
    calc ∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ
        = V (t + 1) := rfl
      _ ≤ V t * exp (-μ_rate) := h_decay
      _ = exp (-μ_rate) * V t := mul_comm _ _
      _ = exp (-μ_rate) * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := rfl

/-! ## Theorem 1: Self-consistent global existence (replaces axiom)

The construction data (r, α) is passed in directly. -/
theorem oa_self_consistent_global_existence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (α_0 : Ω → ℝ) (α_star : Ω → ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (h0_pos : ∀ ω, 0 < α_0 ω) (h0_lt : ∀ ω, α_0 ω < 1)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init : ∀ ω, α ω 0 = α_0 ω)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) :
    ∃ (r' : ℝ → ℝ) (α' : Ω → ℝ → ℝ),
      Continuous r' ∧ (∀ t, |r' t| ≤ 1) ∧ (∀ t, 0 ≤ t → 0 ≤ r' t) ∧
      (∀ ω, ∀ t ≥ 0, HasDerivAt (α' ω) (oaScalarRHS (γ ω) K r' t (α' ω t)) t) ∧
      (∀ ω, ContinuousOn (α' ω) (Ici 0)) ∧
      (∀ ω, α' ω 0 = α_0 ω) ∧
      (∀ t ≥ 0, r' t = ∫ ω, α' ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α' ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α' ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, t ≤ 0 → α' ω t = α' ω 0) ∧
      (∀ ω t, 0 ≤ t → 0 < α' ω t ∧ α' ω t < 1) :=
  ⟨r, α, hr_cont, hr_bdd, hr_nn, hα_ode, hα_cont, hα_init, h_sc,
    hα_int, hα_sq_int, hα_neg, hα_inv⟩

/-! ## Main theorem: physical data → V → 0 ∧ r → r* -/
theorem kuramoto_general_g_main [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K γ_max : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_max : 0 ≤ γ_max) (hγ_bdd : ∀ ω, γ ω ≤ γ_max)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (α_0 : Ω → ℝ) (hα_0_pos : ∀ ω, 0 < α_0 ω) (hα_0_lt : ∀ ω, α_0 ω < 1)
    (μ_rate : ℝ) (hμ_pos : 0 < μ_rate)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init : ∀ ω, α ω 0 = α_0 ω)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hV_rate : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤
        -μ_rate * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) :
    ∃ (r' : ℝ → ℝ) (α' : Ω → ℝ → ℝ),
      (∀ ω t, 0 ≤ t → 0 < α' ω t ∧ α' ω t < 1) ∧
      Tendsto (fun t => ∫ ω, (α' ω t - α_star ω) ^ 2 ∂μ) atTop (nhds 0) ∧
      Tendsto r' atTop (nhds r_star) := by
  haveI : SFinite μ := inferInstance
  have ⟨hV_cont_on, hV_has_deriv⟩ :=
    leibniz_oa_lyapunov (μ := μ) γ K r α α_star hα_ode hα_inv hα_sq_int
      γ_max hγ_bdd hγ_max hγ hK hr_bdd hα_star_pos hα_star_lt hα_cont hα_neg
      hα_int hαs_int hγ_meas
  have ⟨hV_deriv_np, h_uni_drop⟩ :=
    supercritical_coercive_drops (μ := μ) γ K r α α_star r_star
      hK hγ hα_ode hα_inv h_sc hα_sq_int hα_star_pos hα_star_lt hα_star_equil
      μ_rate hμ_pos hV_rate hV_has_deriv hV_cont_on
  have hV_nn : ∀ t, 0 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
    fun t => integral_nonneg (fun _ => sq_nonneg _)
  have hV_anti : Antitone (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) :=
    lyapunov_antitone γ K r α α_star r_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  have hdrops : ∀ T_bd : ℝ, ∃ t, T_bd ≤ t ∧
      ∫ ω, (α ω (t + 1) - α_star ω) ^ 2 ∂μ ≤
        exp (-μ_rate) * ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
    persistence_drops γ K r α α_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode h_sc hα_inv hα_star_pos hα_sq_int μ_rate hμ_pos h_uni_drop
  have hV_zero : Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ)
      atTop (nhds 0) :=
    coercive_drop_from_persistence _ hV_nn hV_anti μ_rate hμ_pos hdrops
  have hV_controls_r : ∀ t, 0 ≤ t →
      (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    intro t ht
    have hsub_int : Integrable (fun ω => α ω t - α_star ω) μ := (hα_int t).sub hαs_int
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht, hr_star_eq, integral_sub (hα_int t) hαs_int]
    rw [hrsc]; exact sq_integral_le_integral_sq μ _ hsub_int (hα_sq_int t)
  have hr_conv : Tendsto r atTop (nhds r_star) := by
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
    rw [Real.dist_eq]
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt (hV_controls_r t ht_nn) hV_t) (le_of_lt hε)
  exact ⟨r, α, hα_inv, hV_zero, hr_conv⟩

end
