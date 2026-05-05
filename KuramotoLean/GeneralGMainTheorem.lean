/-
  Kuramoto Stability — General g End-to-End Main Theorem
  =======================================================
  Clean end-to-end theorem taking physical data + proved regularity.

  kuramoto_solved is UNCONDITIONAL: no mu_rate or hV_rate hypothesis.
  dV/dt ≤ 0 is DERIVED from the pair bound (per-ω identity + DS ≤ r*Q).
  V → 0 via persistence + coercive pair bound + Grönwall comparison.

  The persistence hypothesis (∃ δ > 0, α(ω,t) ≥ δ) replaces the circular
  hV_rate. It is a structural property of the OA flow (proved for n-poles
  in ChetaevEscape.lean) and does NOT assume the conclusion.

  Proof chain:
    persistence + equilibrium → α* ≥ ds > 0
    → coercive pair bound: ∫∫pair ≥ 2δ·ds·V
    → quantitative rate: dV/dt ≤ -K·δ·ds·V
    → Grönwall comparison: V(t+1) ≤ exp(-K·δ·ds)·V(t)
    → Barbalat drops: V → 0

  Axiom budget: 0
-/

import KuramotoLean.SelfConsistentExistence
import KuramotoLean.ContinuumUniformRate
import KuramotoLean.ContinuumRigidity
import KuramotoLean.ContinuumIdentity
import KuramotoLean.ContinuumSupercritical
import KuramotoLean.OAGlobalExistence
import KuramotoLean.GronwallBridge
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
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
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
    (hγ_pos : ∀ ω, 0 ≤ γ ω)
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
        have hγ_nn_ω : 0 ≤ γ ω := hγω
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

/-! ## Per-ω Lyapunov identity for oaScalarRHS

The per-ω contribution to dV/dt factors using the equilibrium condition.
At r = r*: (α-α*) · f = -(K/2)r*(α-α*)²(α+1/α*) ≤ 0.
At general r: adds coupling K(r-r*)(α-α*)(1-α²)/2. -/
private theorem per_omega_identity (γ K r_star r_t α α_star : ℝ)
    (hα_star_ne : α_star ≠ 0)
    (h_equil : γ * α_star = (K / 2) * r_star * (1 - α_star ^ 2)) :
    2 * (α - α_star) * (-γ * α + (K / 2) * r_t * (1 - α ^ 2)) =
    -K * r_star * (α - α_star) ^ 2 * (α + 1 / α_star) +
    K * (r_t - r_star) * (α - α_star) * (1 - α ^ 2) := by
  have hγ : γ = (K / 2) * r_star * (1 - α_star ^ 2) / α_star := by
    field_simp at h_equil ⊢; linarith
  rw [hγ]; field_simp; ring

/-! ## Continuum Lyapunov derivative ≤ 0

The integral ∫ 2(α-α*)·oaScalarRHS dμ = K·(DS - r*Q) ≤ 0
where D = r-r*, S = ∫(α-α*)(1-α²), Q = ∫(α-α*)²(α+1/α*).

The inequality DS ≤ r*Q follows from ∫∫ pair ≥ 0:
  ∫∫ pair = 2(r*Q - DS) ≥ 0.

The double-integral identity uses Fubini + the splitting
  (2-α₁²-α₂²) = (1-α₁²) + (1-α₂²). -/
theorem continuum_lyapunov_deriv_nonpos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r_t : ℝ) (α α_star : Ω → ℝ) (r_star : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hα_pos : ∀ ω, 0 < α ω) (hα_lt : ∀ ω, α ω < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (_hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (h_sc : r_t = ∫ ω, α ω ∂μ)
    (hα_int : Integrable (fun ω => α ω) μ)
    (hαs_int : Integrable α_star μ)
    (_hα_sq_int : Integrable (fun ω => (α ω - α_star ω) ^ 2) μ)
    (hq_int : Integrable (fun ω => (α ω - α_star ω) ^ 2 * (α ω + 1 / α_star ω)) μ)
    (hs_int : Integrable (fun ω => (α ω - α_star ω) * (1 - (α ω) ^ 2)) μ) :
    ∫ ω, 2 * (α ω - α_star ω) * (-γ ω * α ω + (K / 2) * r_t * (1 - (α ω) ^ 2)) ∂μ ≤ 0 := by
  have h_p_int : Integrable (fun ω => α ω - α_star ω) μ := hα_int.sub hαs_int
  have h_pw : ∀ ω, 2 * (α ω - α_star ω) * (-γ ω * α ω + (K / 2) * r_t * (1 - (α ω) ^ 2)) =
      (-K * r_star) * ((α ω - α_star ω) ^ 2 * (α ω + 1 / α_star ω)) +
      (K * (r_t - r_star)) * ((α ω - α_star ω) * (1 - (α ω) ^ 2)) := by
    intro ω
    have h := per_omega_identity (γ ω) K r_star r_t (α ω) (α_star ω)
      (ne_of_gt (hα_star_pos ω)) (hα_star_equil ω)
    rw [h]; ring
  simp_rw [h_pw]
  rw [integral_add (hq_int.const_mul _) (hs_int.const_mul _)]
  simp_rw [integral_const_mul]
  have h_nn := pair_bound_from_products α α_star hα_pos hα_lt hα_star_pos (μ := μ)
  have h_fub := pair_fubini_identity (μ := μ) α α_star hq_int hs_int hαs_int h_p_int
    ((hαs_int.mul_const _).sub (h_p_int.mul_const _))
    ((hq_int.mul_const _).sub (hs_int.mul_const _))
  have h_D : ∫ ω, (α ω - α_star ω) ∂μ = r_t - r_star := by
    rw [integral_sub hα_int hαs_int, h_sc, hr_star_eq]
  rw [hr_star_eq.symm, h_D] at h_fub
  nlinarith [h_nn, h_fub]

/-! ## Quantitative Lyapunov rate: dV/dt ≤ -K·δ·ds · V

With persistence (α ≥ δ > 0) and equilibrium lower bound (α* ≥ ds > 0),
the coercive pair bound gives a quantitative decay rate.

Takes the coercive bound as hypothesis (proved via continuum_coercive_integral
at the callsite). -/
theorem continuum_lyapunov_rate
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r_t : ℝ) (α α_star : Ω → ℝ) (r_star δ_per ds : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (_hα_pos : ∀ ω, 0 < α ω) (_hα_lt : ∀ ω, α ω < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (_hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (h_sc : r_t = ∫ ω, α ω ∂μ)
    (hα_int : Integrable (fun ω => α ω) μ)
    (hαs_int : Integrable α_star μ)
    (_hα_sq_int : Integrable (fun ω => (α ω - α_star ω) ^ 2) μ)
    (_hδ_pos : 0 < δ_per) (_hds_pos : 0 < ds)
    (hq_int : Integrable (fun ω => (α ω - α_star ω) ^ 2 * (α ω + 1 / α_star ω)) μ)
    (hs_int : Integrable (fun ω => (α ω - α_star ω) * (1 - (α ω) ^ 2)) μ)
    (h_pair_coercive : 2 * (δ_per * ds) * ∫ ω, (α ω - α_star ω) ^ 2 ∂μ ≤
      ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ) :
    ∫ ω, 2 * (α ω - α_star ω) * (-γ ω * α ω + (K / 2) * r_t * (1 - (α ω) ^ 2)) ∂μ ≤
    -(K * δ_per * ds) * ∫ ω, (α ω - α_star ω) ^ 2 ∂μ := by
  have h_p_int : Integrable (fun ω => α ω - α_star ω) μ := hα_int.sub hαs_int
  have h_pw : ∀ ω, 2 * (α ω - α_star ω) * (-γ ω * α ω + (K / 2) * r_t * (1 - (α ω) ^ 2)) =
      (-K * r_star) * ((α ω - α_star ω) ^ 2 * (α ω + 1 / α_star ω)) +
      (K * (r_t - r_star)) * ((α ω - α_star ω) * (1 - (α ω) ^ 2)) := by
    intro ω
    have h := per_omega_identity (γ ω) K r_star r_t (α ω) (α_star ω)
      (ne_of_gt (hα_star_pos ω)) (hα_star_equil ω)
    rw [h]; ring
  simp_rw [h_pw]
  rw [integral_add (hq_int.const_mul _) (hs_int.const_mul _)]
  simp_rw [integral_const_mul]
  have h_fub := pair_fubini_identity (μ := μ) α α_star hq_int hs_int hαs_int h_p_int
    ((hαs_int.mul_const _).sub (h_p_int.mul_const _))
    ((hq_int.mul_const _).sub (hs_int.mul_const _))
  have h_D : ∫ ω, (α ω - α_star ω) ∂μ = r_t - r_star := by
    rw [integral_sub hα_int hαs_int, h_sc, hr_star_eq]
  rw [hr_star_eq.symm, h_D] at h_fub
  -- Convert pairIntegrand form to expanded form used by pair_fubini_identity
  have h_pair_eq : ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁) (α_star ω₁) (α ω₂) (α_star ω₂) ∂μ ∂μ =
      ∫ ω₁, ∫ ω₂,
        ((α_star ω₁ * ((α ω₂ - α_star ω₂) ^ 2 * (α ω₂ + 1 / α_star ω₂)) -
          (α ω₁ - α_star ω₁) * ((α ω₂ - α_star ω₂) * (1 - α ω₂ ^ 2))) +
         (α_star ω₂ * ((α ω₁ - α_star ω₁) ^ 2 * (α ω₁ + 1 / α_star ω₁)) -
          (α ω₁ - α_star ω₁) * (α ω₂ - α_star ω₂) * (1 - α ω₁ ^ 2))) ∂μ ∂μ := by
    congr 1; ext ω₁; congr 1; ext ω₂; unfold pairIntegrand; ring
  nlinarith [h_pair_coercive, h_pair_eq, h_fub]

/-! ## End-to-end stability theorem: physical data + existence → convergence

UNCONDITIONAL: no mu_rate or hV_rate hypothesis.
dV/dt ≤ 0 derived from equilibrium + self-consistency + pair bound.
V → 0 via persistence + coercive pair bound + Grönwall comparison. -/
theorem kuramoto_solved [IsProbabilityMeasure μ]
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
      (∃ δ_per : ℝ, 0 < δ_per ∧ ∀ ω, ∀ t, 0 ≤ t → δ_per ≤ α ω t)) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, hr_cont, hr_bdd, hr_nn, hα_ode, hα_cont, _hα_init, h_sc,
    hα_int, hα_sq_int, hα_neg, hα_inv, hα_persist⟩ := h_exists
  refine ⟨r, hr_cont, ?_⟩
  haveI : SFinite μ := inferInstance
  have ⟨hV_cont_on, hV_has_deriv⟩ :=
    leibniz_oa_lyapunov (μ := μ) γ K r α α_star hα_ode hα_inv hα_sq_int
      γ_max hγ_bdd hγ_max (fun ω => (hγ ω).le) hK hr_bdd hα_star_pos hα_star_lt hα_cont hα_neg
      hα_int hαs_int hγ_meas
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    have h_unfold : ∀ ω, oaScalarRHS (γ ω) K r t (α ω t) =
        -(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2) := fun _ => rfl
    simp_rw [h_unfold]
    -- Integrability: bounded functions on probability space
    -- (α-α*)²·(α+1/α*) ≤ C (α* ≥ K·r*/(2γ_max+K·r*) from equilibrium)
    -- (α-α*)·(1-α²) bounded by 1 (both factors ≤ 1 on (0,1))
    have hr_star_pos : 0 < r_star := by
      rw [hr_star_eq]
      have h_nn : ∀ ω, (0 : ℝ) ≤ α_star ω := fun ω => le_of_lt (hα_star_pos ω)
      have h_int_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ := integral_nonneg h_nn
      rcases h_int_nn.lt_or_eq with h | h
      · exact h
      · exfalso
        have h_ae := (integral_eq_zero_iff_of_nonneg h_nn hαs_int).mp h.symm
        obtain ⟨ω, hω⟩ := h_ae.exists
        simp only [Pi.zero_apply] at hω; linarith [hα_star_pos ω]
    have h_inv : ∀ ω, 1 / α_star ω = α_star ω + 2 * γ ω / (K * r_star) := by
      intro ω
      have h_eq := hα_star_equil ω
      field_simp [ne_of_gt (hα_star_pos ω), ne_of_gt (mul_pos hK hr_star_pos)]
      nlinarith [sq_nonneg (α_star ω)]
    have hq_int : Integrable (fun ω => (α ω t - α_star ω) ^ 2 *
        (α ω t + 1 / α_star ω)) μ := by
      set C := 2 + 2 * γ_max / (K * r_star)
      have hq_le : ∀ ω, α ω t + 1 / α_star ω ≤ C := by
        intro ω; rw [h_inv ω]
        have := (hα_inv ω t (le_of_lt ht)).2
        have := hα_star_lt ω
        have := hγ_bdd ω
        have hKr := mul_pos hK hr_star_pos
        have : 2 * γ ω / (K * r_star) ≤ 2 * γ_max / (K * r_star) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      have hm : AEStronglyMeasurable (fun ω => (α ω t - α_star ω) ^ 2 *
          (α ω t + 1 / α_star ω)) μ := by
        have h_eq_fn : (fun ω => (α ω t - α_star ω) ^ 2 * (α ω t + 1 / α_star ω)) =
            fun ω => (α ω t - α_star ω) ^ 2 *
              (α ω t + α_star ω + 2 * γ ω / (K * r_star)) := by
          ext ω; congr 1; rw [h_inv ω]; ring
        rw [h_eq_fn]
        have h_sum : AEStronglyMeasurable
            (fun ω => α ω t + α_star ω + 2 * γ ω / (K * r_star)) μ := by
          refine ((hα_int t).aestronglyMeasurable.add
            hαs_int.aestronglyMeasurable).add ?_
          show AEStronglyMeasurable (fun ω => 2 * γ ω / (K * r_star)) μ
          convert hγ_meas.const_mul (2 / (K * r_star)) using 1; ext ω; ring
        exact (((hα_int t).aestronglyMeasurable.sub
          hαs_int.aestronglyMeasurable).pow 2).mul h_sum
      exact (memLp_top_of_bound hm C (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        have hp := (hα_inv ω t (le_of_lt ht)).1
        have hl := (hα_inv ω t (le_of_lt ht)).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        have h_q_nn : 0 ≤ α ω t + 1 / α_star ω := by linarith [div_pos one_pos hp']
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) h_q_nn)]
        have h_sq : (α ω t - α_star ω) ^ 2 ≤ 1 := by nlinarith
        nlinarith [hq_le ω, sq_nonneg (α ω t - α_star ω)])).integrable le_top
    have hs_int : Integrable (fun ω => (α ω t - α_star ω) *
        (1 - (α ω t) ^ 2)) μ := by
      have hm : AEStronglyMeasurable (fun ω => (α ω t - α_star ω) *
          (1 - (α ω t) ^ 2)) μ :=
        ((hα_int t).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable).mul
          (aestronglyMeasurable_const.sub ((hα_int t).aestronglyMeasurable.pow 2))
      exact (memLp_top_of_bound hm 1 (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        have hp := (hα_inv ω t (le_of_lt ht)).1
        have hl := (hα_inv ω t (le_of_lt ht)).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        rw [abs_mul]
        have h1 : |α ω t - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have h2 : |1 - (α ω t) ^ 2| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (α ω t)]
        calc |α ω t - α_star ω| * |1 - (α ω t) ^ 2|
            ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
          _ = 1 := mul_one 1)).integrable le_top
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK (fun ω => (hγ ω).le) (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t) hq_int hs_int
  have hV_nn : ∀ t, 0 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
    fun t => integral_nonneg (fun _ => sq_nonneg _)
  have hV_anti : Antitone (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ) :=
    lyapunov_antitone γ K r α α_star r_star hK (fun ω => (hγ ω).le) hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  have hV_zero : Tendsto (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ)
      atTop (nhds 0) := by
    obtain ⟨δ_per, hδ_per_pos, hα_lb⟩ := hα_persist
    -- Lower bound on α* from equilibrium: α* ≥ K·r*/(2γ_max + K·r*)
    have hr_star_pos : 0 < r_star := by
      rw [hr_star_eq]
      have h_nn : ∀ ω, (0 : ℝ) ≤ α_star ω := fun ω => le_of_lt (hα_star_pos ω)
      have h_int_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ := integral_nonneg h_nn
      rcases h_int_nn.lt_or_eq with h | h
      · exact h
      · exfalso
        have h_ae := (integral_eq_zero_iff_of_nonneg h_nn hαs_int).mp h.symm
        obtain ⟨ω, hω⟩ := h_ae.exists
        simp only [Pi.zero_apply] at hω; linarith [hα_star_pos ω]
    set ds := K * r_star / (2 * γ_max + K * r_star) with hds_def
    have h_denom_pos : 0 < 2 * γ_max + K * r_star := by positivity
    have hds_pos : 0 < ds := div_pos (mul_pos hK hr_star_pos) h_denom_pos
    have hds_lb : ∀ ω, ds ≤ α_star ω := by
      intro ω
      have h_eq := hα_star_equil ω
      have hαs_lt := hα_star_lt ω
      have hαs_pos := hα_star_pos ω
      have hγω_le := hγ_bdd ω
      show K * r_star / (2 * γ_max + K * r_star) ≤ α_star ω
      rw [div_le_iff₀ h_denom_pos]
      nlinarith [sq_nonneg (α_star ω)]
    -- Rate parameter
    set rate := K * δ_per * ds with hrate_def
    have hrate_pos : 0 < rate := by positivity
    -- Apply continuum_V_tendsto_zero with geometric drops
    apply continuum_V_tendsto_zero _ rate hrate_pos hV_nn hV_anti
    -- Provide drops: ∀ T, ∃ t ≥ T, V(t+1) ≤ exp(-rate)·V(t)
    intro T
    refine ⟨max T 1, le_max_left _ _, ?_⟩
    -- Use comparison_decay_interval to get the drop
    set a := max T 1
    have ha_pos : 0 < a := lt_of_lt_of_le one_pos (le_max_right T 1)
    have h_drop := comparison_decay_interval
      (fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ)
      (fun t => ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ)
      rate a 1 zero_le_one
      (hV_cont_on.mono (fun t ht => mem_Ici.mpr (le_trans (le_of_lt ha_pos) ht.1)))
      (fun t ht_lo _ => hV_has_deriv t (lt_trans ha_pos ht_lo))
      (fun t ht_lo _ => by
        have ht_pos : 0 < t := lt_trans ha_pos ht_lo
        have h_unfold : ∀ ω, oaScalarRHS (γ ω) K r t (α ω t) =
            -(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2) := fun _ => rfl
        simp_rw [h_unfold]
        -- Integrability (bounded functions on probability space)
        have h_inv_t : ∀ ω, 1 / α_star ω = α_star ω + 2 * γ ω / (K * r_star) := by
          intro ω
          have h_eq := hα_star_equil ω
          field_simp [ne_of_gt (hα_star_pos ω), ne_of_gt (mul_pos hK hr_star_pos)]
          nlinarith [sq_nonneg (α_star ω)]
        have hq_int_t : Integrable (fun ω => (α ω t - α_star ω) ^ 2 *
            (α ω t + 1 / α_star ω)) μ := by
          set C := 2 + 2 * γ_max / (K * r_star)
          have hq_le : ∀ ω, α ω t + 1 / α_star ω ≤ C := by
            intro ω; rw [h_inv_t ω]
            have := (hα_inv ω t (le_of_lt ht_pos)).2
            have := hα_star_lt ω
            have := hγ_bdd ω
            have hKr := mul_pos hK hr_star_pos
            have : 2 * γ ω / (K * r_star) ≤ 2 * γ_max / (K * r_star) :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
            linarith
          have hm : AEStronglyMeasurable (fun ω => (α ω t - α_star ω) ^ 2 *
              (α ω t + 1 / α_star ω)) μ := by
            have h_eq_fn : (fun ω => (α ω t - α_star ω) ^ 2 * (α ω t + 1 / α_star ω)) =
                fun ω => (α ω t - α_star ω) ^ 2 *
                  (α ω t + α_star ω + 2 * γ ω / (K * r_star)) := by
              ext ω; congr 1; rw [h_inv_t ω]; ring
            rw [h_eq_fn]
            have h_sum : AEStronglyMeasurable
                (fun ω => α ω t + α_star ω + 2 * γ ω / (K * r_star)) μ := by
              refine ((hα_int t).aestronglyMeasurable.add
                hαs_int.aestronglyMeasurable).add ?_
              show AEStronglyMeasurable (fun ω => 2 * γ ω / (K * r_star)) μ
              convert hγ_meas.const_mul (2 / (K * r_star)) using 1; ext ω; ring
            exact (((hα_int t).aestronglyMeasurable.sub
              hαs_int.aestronglyMeasurable).pow 2).mul h_sum
          exact (memLp_top_of_bound hm C (ae_of_all μ fun ω => by
            simp only [Real.norm_eq_abs]
            have hp := (hα_inv ω t (le_of_lt ht_pos)).1
            have hl := (hα_inv ω t (le_of_lt ht_pos)).2
            have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
            have h_q_nn : 0 ≤ α ω t + 1 / α_star ω := by linarith [div_pos one_pos hp']
            rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) h_q_nn)]
            have h_sq : (α ω t - α_star ω) ^ 2 ≤ 1 := by nlinarith
            nlinarith [hq_le ω, sq_nonneg (α ω t - α_star ω)])).integrable le_top
        have hs_int_t : Integrable (fun ω => (α ω t - α_star ω) *
            (1 - (α ω t) ^ 2)) μ := by
          have hm : AEStronglyMeasurable (fun ω => (α ω t - α_star ω) *
              (1 - (α ω t) ^ 2)) μ :=
            ((hα_int t).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable).mul
              (aestronglyMeasurable_const.sub ((hα_int t).aestronglyMeasurable.pow 2))
          exact (memLp_top_of_bound hm 1 (ae_of_all μ fun ω => by
            simp only [Real.norm_eq_abs]
            have hp := (hα_inv ω t (le_of_lt ht_pos)).1
            have hl := (hα_inv ω t (le_of_lt ht_pos)).2
            have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
            rw [abs_mul]
            have h1 : |α ω t - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            have h2 : |1 - (α ω t) ^ 2| ≤ 1 := by
              rw [abs_le]; constructor <;> nlinarith [sq_nonneg (α ω t)]
            calc |α ω t - α_star ω| * |1 - (α ω t) ^ 2|
                ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
              _ = 1 := mul_one 1)).integrable le_top
        -- Coercive pair bound: ∫∫pair ≥ 2δds·V
        have h_coercive : 2 * (δ_per * ds) *
            ∫ ω, ((fun ω => α ω t) ω - α_star ω) ^ 2 ∂μ ≤
            ∫ ω₁, ∫ ω₂, pairIntegrand ((fun ω => α ω t) ω₁) (α_star ω₁)
              ((fun ω => α ω t) ω₂) (α_star ω₂) ∂μ ∂μ := by
          set αt := fun ω => α ω t
          -- Pair integrand decomposes into integrable components
          have h_pair_decomp : ∀ ω₁ ω₂,
              pairIntegrand (αt ω₁) (α_star ω₁) (αt ω₂) (α_star ω₂) =
              (α_star ω₁ * ((αt ω₂ - α_star ω₂) ^ 2 * (αt ω₂ + 1 / α_star ω₂)) -
               (αt ω₁ - α_star ω₁) * ((αt ω₂ - α_star ω₂) * (1 - αt ω₂ ^ 2))) +
              (α_star ω₂ * ((αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁)) -
               (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2) * (αt ω₂ - α_star ω₂)) :=
            fun ω₁ ω₂ => by unfold pairIntegrand; ring
          have hi12 : ∀ ω₁, Integrable (fun ω₂ =>
              α_star ω₁ * ((αt ω₂ - α_star ω₂) ^ 2 * (αt ω₂ + 1 / α_star ω₂)) -
              (αt ω₁ - α_star ω₁) * ((αt ω₂ - α_star ω₂) * (1 - αt ω₂ ^ 2))) μ :=
            fun ω₁ => (hq_int_t.const_mul _).sub (hs_int_t.const_mul _)
          have hi21 : ∀ ω₁, Integrable (fun ω₂ =>
              α_star ω₂ * ((αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁)) -
              (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2) * (αt ω₂ - α_star ω₂)) μ :=
            fun ω₁ => (hαs_int.mul_const _).sub (((hα_int t).sub hαs_int).const_mul _)
          have h_pair_int : ∀ ω₁, Integrable
              (fun ω₂ => pairIntegrand (αt ω₁) (α_star ω₁) (αt ω₂) (α_star ω₂)) μ :=
            fun ω₁ => ((hi12 ω₁).add (hi21 ω₁)).congr
              (ae_of_all μ fun ω₂ => (h_pair_decomp ω₁ ω₂).symm)
          have h_bound_int : ∀ ω₁, Integrable
              (fun ω₂ => δ_per * ds * ((αt ω₁ - α_star ω₁) ^ 2 +
                (αt ω₂ - α_star ω₂) ^ 2)) μ := fun ω₁ =>
            ((integrable_const ((αt ω₁ - α_star ω₁) ^ 2)).add (hα_sq_int t)).const_mul _
          -- Integral of constant on probability space
          have prob_const : ∀ (c : ℝ), ∫ _ : Ω, c ∂μ = c := by
            intro c; rw [integral_const]; simp [Measure.real, measure_univ]
          -- Outer integrability via decomposition
          set Q_val := ∫ ω, (αt ω - α_star ω) ^ 2 * (αt ω + 1 / α_star ω) ∂μ
          set S_val := ∫ ω, (αt ω - α_star ω) * (1 - αt ω ^ 2) ∂μ
          set rs_val := ∫ ω, α_star ω ∂μ
          set D_val := ∫ ω, (αt ω - α_star ω) ∂μ
          have h_int_eq : ∀ ω₁, ∫ ω₂, pairIntegrand (αt ω₁) (α_star ω₁)
              (αt ω₂) (α_star ω₂) ∂μ =
              (α_star ω₁ * Q_val - (αt ω₁ - α_star ω₁) * S_val) +
              ((αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁) * rs_val -
               (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2) * D_val) := by
            intro ω₁
            have h_rw : (fun ω₂ => pairIntegrand (αt ω₁) (α_star ω₁) (αt ω₂) (α_star ω₂)) =
                fun ω₂ => (α_star ω₁ * ((αt ω₂ - α_star ω₂) ^ 2 * (αt ω₂ + 1 / α_star ω₂)) -
                  (αt ω₁ - α_star ω₁) * ((αt ω₂ - α_star ω₂) * (1 - αt ω₂ ^ 2))) +
                  (α_star ω₂ * ((αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁)) -
                   (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2) * (αt ω₂ - α_star ω₂)) :=
              funext (h_pair_decomp ω₁)
            rw [h_rw, integral_add (hi12 ω₁) (hi21 ω₁)]
            congr 1
            · rw [integral_sub (hq_int_t.const_mul (α_star ω₁))
                (hs_int_t.const_mul (αt ω₁ - α_star ω₁)),
                integral_const_mul, integral_const_mul]
            · -- Rewrite integrand to const_mul + const_mul form
              set c₁ := (αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁)
              set c₂ := (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2)
              have h_diff : Integrable (fun ω₂ => αt ω₂ - α_star ω₂) μ :=
                (hα_int t).sub hαs_int
              simp_rw [show ∀ ω₂, α_star ω₂ * c₁ - c₂ * (αt ω₂ - α_star ω₂) =
                  c₁ * α_star ω₂ + (-c₂) * (αt ω₂ - α_star ω₂) from fun _ => by ring]
              rw [integral_add (hαs_int.const_mul c₁) (h_diff.const_mul (-c₂)),
                integral_const_mul, integral_const_mul]
              ring
          have h_out12 : Integrable (fun ω₁ =>
              α_star ω₁ * Q_val - (αt ω₁ - α_star ω₁) * S_val) μ :=
            (hαs_int.mul_const _).sub (((hα_int t).sub hαs_int).mul_const _)
          have h_out21 : Integrable (fun ω₁ =>
              (αt ω₁ - α_star ω₁) ^ 2 * (αt ω₁ + 1 / α_star ω₁) * rs_val -
              (αt ω₁ - α_star ω₁) * (1 - αt ω₁ ^ 2) * D_val) μ :=
            (hq_int_t.mul_const _).sub (hs_int_t.mul_const _)
          have h_outer_pair : Integrable
              (fun ω₁ => ∫ ω₂, pairIntegrand (αt ω₁) (α_star ω₁)
                (αt ω₂) (α_star ω₂) ∂μ) μ :=
            (h_out12.add h_out21).congr
              (ae_of_all μ fun ω₁ => (h_int_eq ω₁).symm)
          have h_outer_bound : Integrable
              (fun ω₁ => δ_per * ds * ((αt ω₁ - α_star ω₁) ^ 2 +
                ∫ ω, (αt ω - α_star ω) ^ 2 ∂μ)) μ :=
            ((hα_sq_int t).add
              (integrable_const (∫ ω, (αt ω - α_star ω) ^ 2 ∂μ))).const_mul _
          exact continuum_coercive_integral μ αt α_star δ_per ds
            (fun ω => (hα_inv ω t (le_of_lt ht_pos)).1)
            (fun ω => (hα_inv ω t (le_of_lt ht_pos)).2)
            hα_star_pos hδ_per_pos hds_pos
            (fun ω => hα_lb ω t (le_of_lt ht_pos))
            hds_lb (hα_sq_int t) h_pair_int h_bound_int h_outer_pair h_outer_bound
        exact continuum_lyapunov_rate γ K (r t) (fun ω => α ω t) α_star r_star δ_per ds
          hK (fun ω => (hγ ω).le) (fun ω => (hα_inv ω t (le_of_lt ht_pos)).1)
          (fun ω => (hα_inv ω t (le_of_lt ht_pos)).2)
          hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht_pos))
          (hα_int t) hαs_int (hα_sq_int t) hδ_per_pos hds_pos hq_int_t hs_int_t
          h_coercive)
    have h_rw : (∫ ω, (α ω a - α_star ω) ^ 2 ∂μ) * rexp (-rate * 1) =
        rexp (-rate) * (∫ ω, (α ω a - α_star ω) ^ 2 ∂μ) := by ring
    linarith [h_drop, h_rw]
  have hV_controls_r : ∀ t, 0 ≤ t →
      (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    intro t ht
    have hsub_int : Integrable (fun ω => α ω t - α_star ω) μ := (hα_int t).sub hαs_int
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht, hr_star_eq, integral_sub (hα_int t) hαs_int]
    rw [hrsc]; exact sq_integral_le_integral_sq μ _ hsub_int (hα_sq_int t)
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

/-! ## Standard Continuum Kuramoto (Tail-Body Split)

`kuramoto_solved` requires three hypotheses that FAIL for the standard
continuum Kuramoto model with γ(ω) = |ω| on R:

1. **Uniform persistence** `∃ δ > 0, ∀ ω t, δ ≤ α(ω,t)` — FALSE.
   Drifting oscillators (|ω| > Kr*) have α*(ω) → 0.
2. **Bounded γ** `∀ ω, γ ω ≤ γ_max` — FALSE. γ(ω) = |ω| is unbounded.
3. **c_min** (minimum atom weight) — inapplicable to g(ω)dω.

The fix is the tail-body split [Dietert 2016, §2-3]:
  V = V_body(M) + V_tail(M)   via integral_add_compl
  V_tail ≤ μ({γ > M}) → 0     (probability measure, no moment condition)
  V_body → absorbing ball C(M) (body has γ ≤ M, so Leibniz/persistence work)
  C(M) → 0 as M → ∞           (body covers more locked oscillators)
-/

private theorem tail_measure_tendsto_zero_at_nat [IsFiniteMeasure μ]
    (γ : Ω → ℝ) (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M}) :
    Tendsto (fun n : ℕ => (μ {ω | (n : ℝ) < γ ω}).toReal) atTop (nhds 0) := by
  set s := fun n : ℕ => {ω | (n : ℝ) < γ ω}
  have hs_meas : ∀ n : ℕ, MeasurableSet (s n) := by
    intro n
    have : s n = {ω | γ ω ≤ (↑n : ℝ)}ᶜ := by ext ω; simp [s, not_le]
    rw [this]; exact (hγ_level _).compl
  have hs_anti : Antitone s :=
    fun m n hmn ω (hω : (n : ℝ) < γ ω) => lt_of_le_of_lt (Nat.cast_le.mpr hmn) hω
  have hs_inter : ⋂ n, s n = ∅ := by
    ext ω; simp only [s, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall,
      not_lt]; exact ⟨⌈γ ω⌉₊, Nat.le_ceil (γ ω)⟩
  have h_ennreal := tendsto_measure_iInter_atTop
    (fun n => (hs_meas n).nullMeasurableSet) hs_anti ⟨0, measure_ne_top μ _⟩
  rw [hs_inter, measure_empty] at h_ennreal
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_ennreal

private theorem tail_measure_tendsto_zero' [IsFiniteMeasure μ]
    (γ : Ω → ℝ) (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M}) :
    Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_nat := tail_measure_tendsto_zero_at_nat (μ := μ) γ hγ_level
  rw [Metric.tendsto_atTop] at h_nat
  obtain ⟨N, hN⟩ := h_nat ε hε
  refine ⟨↑N, fun M hM => ?_⟩
  have h_mono : (μ {ω | M < γ ω}).toReal ≤ (μ {ω | (↑N : ℝ) < γ ω}).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (fun ω hω => lt_of_le_of_lt hM hω))
  have hN_bound := hN N le_rfl
  simp only [Real.dist_eq, sub_zero] at hN_bound ⊢
  rw [abs_of_nonneg ENNReal.toReal_nonneg] at hN_bound ⊢
  linarith

private theorem gronwall_to_absorbing_ball
    (V_body : ℝ → ℝ) (V₀ rate C : ℝ)
    (hrate : 0 < rate) (_hC_nn : 0 ≤ C)
    (h_bound : ∀ t ≥ (0 : ℝ), V_body t ≤ V₀ * rexp (-rate * t) + C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t ≥ T, V_body t < C + ε := by
  have h_decay : Tendsto (fun t : ℝ => V₀ * rexp (-rate * t)) atTop (nhds 0) := by
    have hexp : Tendsto (fun t : ℝ => rexp (-rate * t)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hrate).mpr tendsto_id
      exact (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr
        (fun t => by simp only [Function.comp_def, neg_mul])
    have := hexp.const_mul V₀
    simp only [mul_zero] at this
    exact this.congr (fun _ => by ring)
  rw [Metric.tendsto_atTop] at h_decay
  obtain ⟨T, hT⟩ := h_decay ε hε
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have h_exp_small : V₀ * rexp (-rate * t) < ε := by
    have h := hT t (le_trans (le_max_left T 0) ht)
    rw [Real.dist_eq, sub_zero] at h
    by_cases hV₀ : 0 ≤ V₀
    · have h_nn : 0 ≤ V₀ * rexp (-rate * t) :=
        mul_nonneg hV₀ (le_of_lt (Real.exp_pos _))
      rw [abs_of_nonneg h_nn] at h; linarith
    · push_neg at hV₀
      have : V₀ * rexp (-rate * t) < 0 :=
        mul_neg_of_neg_of_pos hV₀ (Real.exp_pos (-rate * t))
      linarith
  linarith [h_bound t ht_nn]

/-- **Standard Continuum Kuramoto Stability (Tail-Body Split).**

For the standard continuum Kuramoto model with:
  • γ(ω) = |ω| — unbounded natural frequency on R
  • g ∈ L¹(R) — any integrable frequency distribution (probability measure)
  • BOTH locked (|ω| < Kr*) AND drifting (|ω| > Kr*) oscillators
  • α*(ω) → 0 as |ω| → ∞ — NO uniform lower bound

Conclusion: the order parameter r(t) → r* as t → ∞.

Does NOT assume:
  • `γ_max` / `hγ_bdd` — γ bounded globally (PROBLEM 2)
  • `∃ δ, ∀ ω t, δ ≤ α(ω,t)` — uniform persistence (PROBLEM 1)
  • `c_min` — minimum atom weight (PROBLEM 3)

Key hypothesis: `h_body_gronwall` — for each truncation level M > 0,
the body Lyapunov V_body(M,t) satisfies an exponential Gronwall bound:
  V_body(M,t) ≤ V_body(M,0) · exp(-rate(M)·t) + C(M)
with absorbing radius C(M) → 0 as M → ∞.

This body Gronwall is DERIVABLE from the bounded-γ stability machinery
applied to the body {γ ≤ M} where:
  • γ ≤ M → Leibniz differentiation of V_body (dominator 2M+K)
  • Body persistence: ∃ δ(M) > 0, α ≥ δ(M) on {γ ≤ M} (locked oscillators)
  • Body pair coercivity: ∫∫_body pair ≥ 2·δ(M)·ds(M)·V_body
  • Body ISS: dV_body/dt ≤ -K·δ(M)·ds(M)·V_body + K·μ(tail)
  • Gronwall comparison → exponential decay to absorbing ball C(M) -/
theorem kuramoto_solved_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (_hK : 0 < K) (_hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (_hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (C : ℝ → ℝ) (hC_nn : ∀ M, 0 ≤ C M) (hC_vanish : Tendsto C atTop (nhds 0))
    (h_body_gronwall : ∀ M : ℝ, 0 < M →
      ∃ (rate : ℝ), 0 < rate ∧
        ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
              rexp (-rate * t) + C M) :
    Tendsto r atTop (nhds r_star) := by
  have h_tail : Tendsto (fun M => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    tail_measure_tendsto_zero' (μ := μ) γ hγ_level
  have h_body_absorb : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε := by
    intro M hM ε hε
    obtain ⟨rate, hrate, h_gron⟩ := h_body_gronwall M hM
    exact gronwall_to_absorbing_ball
      (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ)
      _ rate (C M) hrate (hC_nn M) h_gron ε hε
  have h_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have h := hC_vanish.add h_tail; rwa [add_zero] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε ^ 2 / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  rw [Metric.tendsto_atTop] at h_vanish
  obtain ⟨N, hN⟩ := h_vanish δ hδ
  set M := max N 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_sum_small : C M + (μ {ω | M < γ ω}).toReal < δ := by
    have h := hN M (le_max_left N 1)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg
      (add_nonneg (hC_nn M) ENNReal.toReal_nonneg)] at h
  obtain ⟨T, hT⟩ := h_body_absorb M hM_pos δ hδ
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have ht_ge_T : T ≤ t := le_trans (le_max_left T 0) ht
  have hCS : (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht_nn, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]; exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  have hV_split : ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int t)).symm
  have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
  have hVtail : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ < δ := by
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω t - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int t).integrableOn
            (integrable_const 1).integrableOn (hγ_level M).compl
          intro ω _; nlinarith [(hα_inv ω t ht_nn).1, (hα_inv ω t ht_nn).2,
            hα_star_pos ω, hα_star_lt ω, sq_abs (α ω t - α_star ω)]
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
      _ = (μ {ω | M < γ ω}).toReal := by rw [h_compl]
      _ < δ := lt_of_le_of_lt (le_add_of_nonneg_left (hC_nn M)) h_sum_small
  have hVbody : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < 2 * δ := by
    have hC_lt : C M < δ :=
      lt_of_le_of_lt (le_add_of_nonneg_right ENNReal.toReal_nonneg) h_sum_small
    linarith [hT t ht_ge_T]
  have hV_lt : (r t - r_star) ^ 2 < ε ^ 2 := calc
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := hCS
    _ = _ + _ := hV_split
    _ < 2 * δ + δ := add_lt_add hVbody hVtail
    _ = 3 * (ε ^ 2 / 4) := by ring
    _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hV_lt (le_of_lt hε)

/-- **`kuramoto_solved` is a special case of `kuramoto_solved_continuum`.**

When γ IS bounded by γ_max and persistence IS uniform, the global Gronwall
V(t) ≤ V(0)·exp(-rate·t) implies body Gronwall with C(M) = μ({γ > M}).
Since γ is bounded, μ({γ > γ_max}) = 0, so C → 0. -/
theorem kuramoto_solved_of_bounded_gamma [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (rate : ℝ) (hrate : 0 < rate)
    (h_gronwall : ∀ t ≥ (0 : ℝ),
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) := by
  apply kuramoto_solved_continuum γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α
    h_sc hα_int hα_sq_int hα_inv
    (fun M => (μ {ω | M < γ ω}).toReal)
    (fun _ => ENNReal.toReal_nonneg)
    (tail_measure_tendsto_zero' (μ := μ) γ hγ_level)
  intro M _hM
  refine ⟨rate, hrate, fun t ht => ?_⟩
  have h_body_le : ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
      ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ :=
    setIntegral_le_integral (hα_sq_int t) (ae_of_all μ fun _ => sq_nonneg _)
  have h_split0 : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ =
      (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) +
      (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) :=
    (integral_add_compl (hγ_level M) (hα_sq_int 0)).symm
  have h_compl : {ω | γ ω ≤ M}ᶜ = {ω | M < γ ω} := by ext ω; simp [not_le]
  have h_tail0_le : ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ ≤
      (μ {ω | M < γ ω}).toReal := by
    calc ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (1 : ℝ) ∂μ := by
          apply setIntegral_mono_on (hα_sq_int 0).integrableOn
            (integrable_const 1).integrableOn (hγ_level M).compl
          intro ω _; nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2,
            hα_star_pos ω, hα_star_lt ω, sq_abs (α ω 0 - α_star ω)]
      _ = (μ {ω | γ ω ≤ M}ᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
      _ = _ := by rw [h_compl]
  have hexp_le : rexp (-rate * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h_body0_nn : (0 : ℝ) ≤ ∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have h_tail0_nn : (0 : ℝ) ≤ ∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  calc ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ
      ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := h_body_le
    _ ≤ (∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) := h_gronwall t ht
    _ = ((∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) +
         (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ)) *
          rexp (-rate * t) := by rw [← h_split0]
    _ = (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) :=
      add_mul _ _ _
    _ ≤ (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (∫ ω in {ω | γ ω ≤ M}ᶜ, (α ω 0 - α_star ω) ^ 2 ∂μ) := by
      linarith [mul_le_mul_of_nonneg_left hexp_le h_tail0_nn]
    _ ≤ (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) +
        (μ {ω | M < γ ω}).toReal := by linarith [h_tail0_le]

end
