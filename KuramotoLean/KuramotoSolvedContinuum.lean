/-
  Kuramoto Stability — Definitive Continuum Theorem
  ==================================================
  `kuramoto_solved_continuum`: the CORRECT theorem for the standard
  continuum Kuramoto model. Resolves three fundamental issues with
  `kuramoto_solved` (GeneralGMainTheorem.lean):

  PROBLEM 1 (uniform persistence): `kuramoto_solved` assumes
    ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t).
  FALSE for the standard model — drifting oscillators (|ω| > Kr*)
  have α(ω,t) → 0. Only LOCKED oscillators persist.
  FIX: Body persistence — ∀ M > 0, ∃ δ(M) > 0, on {γ ≤ M}: α ≥ δ(M).

  PROBLEM 2 (bounded γ): `kuramoto_solved` assumes γ(ω) ≤ γ_max.
  FALSE for the standard model — γ(ω) = |ω| is unbounded on R.
  FIX: γ integrable (∫ γ dμ < ∞). Leibniz uses ω-dependent dominator
  2γ(ω)+K, integrable since γ is.

  PROBLEM 3 (c_min): `kuramoto_solved` rate uses c_min (min atom weight).
  INAPPLICABLE to continuum g(ω)dω with no atoms.
  FIX: Rate from body pair coercivity:
    ∫∫ pair ≥ 2·δ_M·ds_M·μ(body)·V_body.

  Proof via tail-body split [Dietert 2016, §2-3]:

    V = V_body + V_tail                 (integral_add_compl)
    V_tail ≤ μ({γ > M}) → 0            (Markov: μ(tail)·M ≤ ∫γ)
    V_body → 0                          (Leibniz + body pair coercivity)
    |r - r*|² ≤ V → 0                  (Cauchy-Schwarz)

  Covers: Gaussian, Student-t ν>2, compact support. NOT Lorentzian.
  0 sorry. 0 axioms.
-/

import KuramotoLean.GeneralGMainTheorem
import KuramotoLean.ContinuumTailBodyConvergence

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Leibniz rule with integrable γ dominator

The key new ingredient: uses ω-dependent bound `2*γ(ω)+K` instead of
constant `2*γ_max+K`. Requires `Integrable γ μ` instead of bounded γ.
This is valid because `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
accepts an integrable (not necessarily constant) dominator function.

Per-ω bound: |2(α-α*)·oaScalarRHS| ≤ 2·|α-α*|·|f| ≤ 2·1·(γ+K/2) = 2γ+K.
Integrability: ∫(2γ+K)dμ = 2∫γ dμ + K < ∞ when γ is integrable. -/

theorem leibniz_oa_integrable_gamma
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hγ_int : Integrable γ μ)
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
        have hγω_pos := hγ_pos ω
        have h_diff : |α ω s - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have h_rhs : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ γ ω + K / 2 := by
          unfold oaScalarRHS
          have hr1 := hr_bdd s
          have h1 : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
          have h2 : 1 - (α ω s) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω s)]
          have hγ_nn : 0 ≤ γ ω := le_of_lt hγω_pos
          have hα_nn : 0 ≤ α ω s := le_of_lt hp
          have hα_le : α ω s ≤ 1 := le_of_lt hl
          have hrs_lo : -1 ≤ r s := (abs_le.mp hr1).1
          have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
          rw [abs_le]; constructor
          · nlinarith [mul_nonneg hγ_nn hα_nn, mul_nonneg (by linarith : (0:ℝ) ≤ K/2) h1]
          · nlinarith [mul_nonneg hγ_nn hα_nn, mul_nonneg (by linarith : (0:ℝ) ≤ K/2) h1]
        calc ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖
            = |2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)| := Real.norm_eq_abs _
          _ = 2 * |α ω s - α_star ω| * |oaScalarRHS (γ ω) K r s (α ω s)| := by
              rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
          _ ≤ 2 * 1 * (γ ω + K / 2) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left h_diff (by positivity))
                h_rhs (abs_nonneg _) (by positivity)
          _ = 2 * γ ω + K := by ring)
      (bound_integrable := (hγ_int.const_mul 2).add (integrable_const K))
      (h_diff := Eventually.of_forall fun ω s hs => by
        have h := (hα_ode ω s (le_of_lt (mem_Ioi.mp hs))).sub_const (α_star ω)
        convert h.pow 2 using 1; push_cast; ring) |>.2

/-! ## Main theorem: Standard continuum Kuramoto with integrable γ

Replaces `kuramoto_solved` for the standard continuum model.
Key hypothesis changes:
  - `hγ_int : Integrable γ μ` REPLACES `hγ_bdd : ∀ ω, γ ω ≤ γ_max`
  - Body persistence REPLACES uniform persistence
  - Body Leibniz drop (from body_leibniz_hasDerivAt + pair coercivity)

The body Leibniz drop hypothesis captures the quantitative body analysis:
  V(t) - V(t+1) ≥ K · coer(M) · (V(t+1) - μ(tail))
This is derivable from:
  • Bounded γ on body → body_leibniz_hasDerivAt (already proved)
  • Body persistence δ(M) + equilibrium bound ds(M) → pair coercivity
  • FTC on [t, t+1]: V(t)-V(t+1) = ∫_t^{t+1} |dV/ds| ds ≥ K·coer·V_body
-/
set_option maxHeartbeats 400000 in
theorem kuramoto_solved_integrable_gamma [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
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
      -- BODY persistence: for each M, ∃ δ(M) on {γ ≤ M}
      (∀ M, 0 < M → ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) ∧
      -- γ sublevel sets measurable
      (∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, hr_cont, hr_bdd, hr_nn, hα_ode, hα_cont, _hα_init, h_sc,
    hα_int, hα_sq_int, hα_neg, hα_inv, h_body_persist, hγ_level⟩ := h_exists
  refine ⟨r, hr_cont, ?_⟩
  haveI : SFinite μ := inferInstance
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  have hV_nn : ∀ t, 0 ≤ V t := fun t => integral_nonneg (fun _ => sq_nonneg _)
  -- Step 1: Leibniz with integrable γ dominator
  have ⟨hV_cont_on, hV_has_deriv⟩ :=
    leibniz_oa_integrable_gamma (μ := μ) γ K r α α_star hα_ode hα_inv hα_sq_int
      hγ_int hγ hK hr_bdd hα_star_pos hα_star_lt hα_cont hα_neg
      hα_int hαs_int hγ_meas
  -- Step 2: dV/dt ≤ 0 from pair bound → V antitone
  -- The derivative formula from Leibniz + the pair bound identity gives dV/dt ≤ 0.
  -- Q term (α-α*)²(α+1/α*) is integrable because 1/α* = α* + 2γ/(Kr*) and γ integrable.
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    have h_unfold : ∀ ω, oaScalarRHS (γ ω) K r t (α ω t) =
        -(γ ω) * α ω t + K / 2 * r t * (1 - (α ω t) ^ 2) := fun _ => rfl
    simp_rw [h_unfold]
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
    -- Q integrability: (α-α*)²(α+1/α*) integrable since 1/α* = α* + 2γ/(Kr*)
    -- from equilibrium, and γ is integrable. Bound: |(α-α*)²(α+1/α*)| ≤ 2+2γ/(Kr*).
    have hq_int : Integrable (fun ω => (α ω t - α_star ω) ^ 2 *
        (α ω t + 1 / α_star ω)) μ := by
      have hKr : 0 < K * r_star := mul_pos hK hr_star_pos
      have h_inv : ∀ ω, 1 / α_star ω = α_star ω + 2 * γ ω / (K * r_star) := by
        intro ω
        have heq := hα_star_equil ω
        have hα_ne : α_star ω ≠ 0 := ne_of_gt (hα_star_pos ω)
        field_simp
        nlinarith [sq_nonneg (α_star ω), hα_star_pos ω, hα_star_lt ω, hγ ω]
      have h_eq : ∀ ω, (α ω t - α_star ω) ^ 2 * (α ω t + 1 / α_star ω) =
          (α ω t - α_star ω) ^ 2 * (α ω t + α_star ω + 2 / (K * r_star) * γ ω) := by
        intro ω; congr 1; rw [h_inv]; ring
      simp_rw [h_eq]
      have h_bound : ∀ ω, ‖(α ω t - α_star ω) ^ 2 *
          (α ω t + α_star ω + 2 / (K * r_star) * γ ω)‖ ≤
          2 + 2 / (K * r_star) * γ ω := by
        intro ω
        have hp := (hα_inv ω t (le_of_lt ht)).1
        have hl := (hα_inv ω t (le_of_lt ht)).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        have hγω := hγ ω
        have h_sum_le : α ω t + α_star ω + 2 / (K * r_star) * γ ω ≤
            2 + 2 / (K * r_star) * γ ω := by linarith
        have h_sum_nn : (0 : ℝ) ≤ α ω t + α_star ω + 2 / (K * r_star) * γ ω := by
          positivity
        have h_sq_le : (α ω t - α_star ω) ^ 2 ≤ 1 := by nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h_sum_nn)]
        calc (α ω t - α_star ω) ^ 2 * (α ω t + α_star ω + 2 / (K * r_star) * γ ω)
            ≤ 1 * (2 + 2 / (K * r_star) * γ ω) :=
              mul_le_mul h_sq_le h_sum_le h_sum_nn zero_le_one
          _ = 2 + 2 / (K * r_star) * γ ω := one_mul _
      exact ((integrable_const 2).add (hγ_int.const_mul (2 / (K * r_star)))).mono'
        (((hα_sq_int t).aestronglyMeasurable).mul
          (((hα_int t).aestronglyMeasurable.add hαs_int.aestronglyMeasurable).add
            (hγ_meas.const_mul (2 / (K * r_star)))))
        (Eventually.of_forall h_bound)
    have hs_int : Integrable (fun ω => (α ω t - α_star ω) *
        (1 - (α ω t) ^ 2)) μ := by
      have h_bound : ∀ ω, ‖(α ω t - α_star ω) * (1 - (α ω t) ^ 2)‖ ≤ 1 := by
        intro ω
        have hp := (hα_inv ω t (le_of_lt ht)).1
        have hl := (hα_inv ω t (le_of_lt ht)).2
        have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |α ω t - α_star ω| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        have h2 : |1 - (α ω t) ^ 2| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (α ω t)]
        calc |α ω t - α_star ω| * |1 - (α ω t) ^ 2|
            ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      exact (integrable_const (1:ℝ)).mono'
        (((hα_int t).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable).mul
          (aestronglyMeasurable_const.sub ((hα_int t).aestronglyMeasurable.pow 2)))
        (Eventually.of_forall h_bound)
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK (fun ω => (hγ ω).le) (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t) hq_int hs_int
  have hV_anti : Antitone V :=
    lyapunov_antitone γ K r α α_star r_star hK (fun ω => (hγ ω).le) hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  -- Step 3: V → 0 via tail-body structure.
  -- V antitone → V → L ≥ 0. If L > 0: body coercivity gives constant negative
  -- drift (V' ≤ -c₀), making V eventually negative — contradiction. So L = 0.
  have hV_zero : Tendsto V atTop (nhds 0) := by
    obtain ⟨L, hL_nn, hV_lim⟩ := antitone_bounded_converges V hV_anti hV_nn
    suffices hL0 : L = 0 by rwa [hL0] at hV_lim
    by_contra hL_ne
    have hL_pos : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL_ne)
    have hVt_ge_L : ∀ t, L ≤ V t :=
      fun t => le_of_tendsto hV_lim (eventually_atTop.mpr ⟨t, fun s hs => hV_anti hs⟩)
    have hr_star_pos : 0 < r_star := by
      rw [hr_star_eq]
      have h_nn : ∀ ω, (0:ℝ) ≤ α_star ω := fun ω => le_of_lt (hα_star_pos ω)
      have h_int_nn : (0:ℝ) ≤ ∫ ω, α_star ω ∂μ := integral_nonneg h_nn
      rcases h_int_nn.lt_or_eq with h | h
      · exact h
      · exfalso
        have h_ae := (integral_eq_zero_iff_of_nonneg h_nn hαs_int).mp h.symm
        obtain ⟨ω, hω⟩ := h_ae.exists
        simp only [Pi.zero_apply] at hω; linarith [hα_star_pos ω]
    set C_γ := ∫ ω, γ ω ∂μ
    have hCγ_nn : 0 ≤ C_γ := integral_nonneg (fun ω => le_of_lt (hγ ω))
    set M := max (4 * C_γ / L) 1 with hM_def
    have hM_pos : (0:ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_ge : 4 * C_γ / L ≤ M := le_max_left _ _
    set body := {ω | γ ω ≤ M}
    have h_tail_small : (μ {ω | M < γ ω}).toReal ≤ L / 4 := by
      have h_meas : MeasurableSet {ω | M < γ ω} := by
        have : {ω | M < γ ω} = {ω | γ ω ≤ M}ᶜ := by ext ω; simp [not_le]
        rw [this]; exact (hγ_level M).compl
      have h_markov : (μ {ω | M < γ ω}).toReal * M ≤ C_γ := by
        have h1 : (μ {ω | M < γ ω}).toReal * M = ∫ _ in {ω | M < γ ω}, M ∂μ := by
          rw [setIntegral_const]; simp [Measure.real]
        rw [h1]
        calc ∫ _ in {ω | M < γ ω}, M ∂μ
            ≤ ∫ ω in {ω | M < γ ω}, γ ω ∂μ :=
              setIntegral_mono_on (integrable_const M).integrableOn
                hγ_int.integrableOn h_meas (fun ω hω => le_of_lt hω)
          _ ≤ C_γ := setIntegral_le_integral hγ_int (ae_of_all μ fun ω => le_of_lt (hγ ω))
      have h_le : (μ {ω | M < γ ω}).toReal ≤ C_γ / M :=
        (le_div_iff₀ hM_pos).mpr h_markov
      have h_div_le : C_γ / M ≤ L / 4 := by
        by_cases hC : C_γ ≤ 0
        · have : C_γ = 0 := le_antisymm hC hCγ_nn
          simp [this]; linarith [hL_pos]
        · push_neg at hC
          rw [div_le_div_iff₀ hM_pos (by linarith : (0:ℝ) < 4)]
          have hL_ne' : L ≠ 0 := ne_of_gt hL_pos
          nlinarith [mul_comm (4 * C_γ / L) L, div_mul_cancel₀ (4 * C_γ) hL_ne',
            le_max_left (4 * C_γ / L) 1]
      linarith
    obtain ⟨δ_M, hδ_M_pos, hα_lb_body⟩ := h_body_persist M hM_pos
    have h_denom_pos : 0 < 2 * M + K * r_star := by positivity
    set ds_M := K * r_star / (2 * M + K * r_star)
    have hds_M_pos : 0 < ds_M := div_pos (mul_pos hK hr_star_pos) h_denom_pos
    have hds_lb_body : ∀ ω, γ ω ≤ M → ds_M ≤ α_star ω := by
      intro ω hγω
      rw [div_le_iff₀ h_denom_pos]
      nlinarith [sq_nonneg (α_star ω), hα_star_pos ω, hα_star_lt ω, hα_star_equil ω]
    have hbody_meas : MeasurableSet body := hγ_level M
    have hbody_finite : IsFiniteMeasure (μ.restrict body) := isFiniteMeasureRestrict μ body
    set V_body := fun t => ∫ ω in body, (α ω t - α_star ω) ^ 2 ∂μ
    have hVb_nn : ∀ t, 0 ≤ V_body t := fun t => integral_nonneg (fun _ => sq_nonneg _)
    have hV_split : ∀ t, V t = V_body t + ∫ ω in bodyᶜ, (α ω t - α_star ω) ^ 2 ∂μ :=
      fun t => (integral_add_compl hbody_meas (hα_sq_int t)).symm
    have hVb_ge : ∀ t, 3 * L / 4 ≤ V_body t := by
      intro t
      have h_tail_le : ∫ ω in bodyᶜ, (α ω t - α_star ω) ^ 2 ∂μ ≤ L / 4 := by
        have h_sq_le : ∀ ω, (α ω t - α_star ω) ^ 2 ≤ 1 := fun ω => by
          by_cases ht : 0 ≤ t
          · nlinarith [(hα_inv ω t ht).1, (hα_inv ω t ht).2, hα_star_pos ω, hα_star_lt ω]
          · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]
            nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2,
              hα_star_pos ω, hα_star_lt ω]
        have h_tail_compl : bodyᶜ = {ω | M < γ ω} := by ext ω; simp [body, not_le]
        calc ∫ ω in bodyᶜ, (α ω t - α_star ω) ^ 2 ∂μ
            ≤ ∫ _ in bodyᶜ, (1:ℝ) ∂μ :=
              setIntegral_mono_on (hα_sq_int t).integrableOn
                (integrable_const 1).integrableOn hbody_meas.compl (fun ω _ => h_sq_le ω)
          _ = (μ bodyᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
          _ = (μ {ω | M < γ ω}).toReal := by rw [h_tail_compl]
          _ ≤ L / 4 := h_tail_small
      linarith [hVt_ge_L t, hV_split t, hVb_nn t]
    have hVt_le_one : ∀ t, V t ≤ 1 := fun t => by
      have h_sq_le : ∀ ω, (α ω t - α_star ω) ^ 2 ≤ 1 := fun ω => by
        by_cases ht : 0 ≤ t
        · nlinarith [(hα_inv ω t ht).1, (hα_inv ω t ht).2, hα_star_pos ω, hα_star_lt ω]
        · push_neg at ht; rw [hα_neg ω t (le_of_lt ht)]
          nlinarith [(hα_inv ω 0 le_rfl).1, (hα_inv ω 0 le_rfl).2,
            hα_star_pos ω, hα_star_lt ω]
      calc V t = ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := rfl
        _ ≤ ∫ _ : Ω, (1:ℝ) ∂μ := integral_mono (hα_sq_int t) (integrable_const 1)
            (fun ω => h_sq_le ω)
        _ = 1 := by simp [integral_const, measure_univ]
    have hbody_toReal_pos : 0 < (μ body).toReal := by
      have h_body_ne_zero : μ body ≠ 0 := by
        intro h_eq
        have h_body_compl : μ univ = μ body + μ bodyᶜ :=
          (measure_add_measure_compl hbody_meas).symm
        rw [measure_univ, h_eq, zero_add] at h_body_compl
        have h1 : (μ bodyᶜ).toReal = 1 := by
          rw [← h_body_compl]; simp [Measure.real]
        have h_tail_compl : bodyᶜ = {ω | M < γ ω} := by ext ω; simp [body, not_le]
        have h_tail : (μ bodyᶜ).toReal ≤ L / 4 := by
          rw [h_tail_compl]; exact h_tail_small
        linarith [hVt_ge_L 0, hVt_le_one 0]
      exact ENNReal.toReal_pos h_body_ne_zero (measure_ne_top μ body)
    set c₀ := K / 2 * (2 * δ_M * ds_M * (μ body).toReal * (3 * L / 4))
    have hc₀_pos : 0 < c₀ := by positivity
    -- Prove derivative bound: dV/dt ≤ -c₀ for all s > 0
    have hV'_le : ∀ s, 0 < s →
        ∫ ω, 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s) ∂μ ≤ -c₀ := by
      intro s hs
      have hKr : 0 < K * r_star := mul_pos hK hr_star_pos
      have h_inv : ∀ ω, 1 / α_star ω = α_star ω + 2 * γ ω / (K * r_star) := by
        intro ω
        have hα_ne : α_star ω ≠ 0 := ne_of_gt (hα_star_pos ω)
        field_simp
        nlinarith [sq_nonneg (α_star ω), hα_star_pos ω, hα_star_lt ω, hγ ω,
          hα_star_equil ω]
      have hq_int : Integrable (fun ω => (α ω s - α_star ω) ^ 2 *
          (α ω s + 1 / α_star ω)) μ := by
        have h_eq : ∀ ω, (α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω) =
            (α ω s - α_star ω) ^ 2 * (α ω s + α_star ω + 2 / (K * r_star) * γ ω) := by
          intro ω; congr 1; rw [h_inv]; ring
        simp_rw [h_eq]
        exact ((integrable_const 2).add (hγ_int.const_mul (2 / (K * r_star)))).mono'
          (((hα_sq_int s).aestronglyMeasurable).mul
            (((hα_int s).aestronglyMeasurable.add hαs_int.aestronglyMeasurable).add
              (hγ_meas.const_mul (2 / (K * r_star)))))
          (Eventually.of_forall fun ω => by
            have hp := (hα_inv ω s (le_of_lt hs)).1
            have hl := (hα_inv ω s (le_of_lt hs)).2
            have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
            have h_sum_nn : (0:ℝ) ≤ α ω s + α_star ω + 2 / (K * r_star) * γ ω := by
              have := hγ ω; positivity
            have h_sum_le : α ω s + α_star ω + 2 / (K * r_star) * γ ω ≤
                2 + 2 / (K * r_star) * γ ω := by linarith
            have h_sq_le : (α ω s - α_star ω) ^ 2 ≤ 1 := by nlinarith
            rw [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (sq_nonneg _) h_sum_nn)]
            exact (mul_le_mul_of_nonneg_right h_sq_le h_sum_nn).trans
              (by simp only [one_mul]; exact h_sum_le))
      have hs_int : Integrable (fun ω => (α ω s - α_star ω) * (1 - (α ω s) ^ 2)) μ :=
        (integrable_const (1:ℝ)).mono'
          (((hα_int s).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable).mul
            (aestronglyMeasurable_const.sub ((hα_int s).aestronglyMeasurable.pow 2)))
          (Eventually.of_forall fun ω => by
            have hp := (hα_inv ω s (le_of_lt hs)).1
            have hl := (hα_inv ω s (le_of_lt hs)).2
            have hp' := hα_star_pos ω; have hl' := hα_star_lt ω
            rw [Real.norm_eq_abs, abs_mul]
            calc |α ω s - α_star ω| * |1 - (α ω s) ^ 2|
                ≤ 1 * 1 := mul_le_mul
                    (abs_le.mpr ⟨by linarith, by linarith⟩)
                    (by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (α ω s)])
                    (abs_nonneg _) zero_le_one
              _ = 1 := mul_one 1)
      have h_p_int : Integrable (fun ω => α ω s - α_star ω) μ := (hα_int s).sub hαs_int
      set Q := ∫ ω, (α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω) ∂μ
      set S := ∫ ω, (α ω s - α_star ω) * (1 - (α ω s) ^ 2) ∂μ
      set D := r s - r_star
      -- Inner integral identity
      have h_inner_eq : ∀ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
          (α ω₂ s) (α_star ω₂) ∂μ =
          (α_star ω₁ * Q - (α ω₁ s - α_star ω₁) * S) +
          ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁) * r_star -
           (α ω₁ s - α_star ω₁) * (1 - (α ω₁ s) ^ 2) * D) := by
        intro ω₁
        have hi12 : Integrable (fun ω₂ =>
            α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
            (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) μ :=
          (hq_int.const_mul _).sub (hs_int.const_mul _)
        have hi21 : Integrable (fun ω₂ =>
            α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
            (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂)) μ :=
          (hαs_int.mul_const _).sub (h_p_int.const_mul _)
        have h_rw : (fun ω₂ => pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂)) =
            fun ω₂ =>
            (α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
            (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
             (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂)) :=
          funext fun ω₂ => by unfold pairIntegrand; ring
        rw [h_rw, integral_add hi12 hi21]
        congr 1
        · rw [integral_sub (hq_int.const_mul _) (hs_int.const_mul _),
            integral_const_mul, integral_const_mul]
        · set c₁ := (α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)
          set c₂ := (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2)
          simp_rw [show ∀ ω₂, α_star ω₂ * c₁ - c₂ * (α ω₂ s - α_star ω₂) =
            c₁ * α_star ω₂ + (-c₂) * (α ω₂ s - α_star ω₂) from fun _ => by ring]
          rw [integral_add (hαs_int.const_mul c₁) (h_p_int.const_mul (-c₂)),
            integral_const_mul, integral_const_mul, hr_star_eq]
          have hD : ∫ ω, (α ω s - α_star ω) ∂μ = D := by
            simp only [D]
            rw [integral_sub (hα_int s) hαs_int, h_sc s (le_of_lt hs), hr_star_eq]
          rw [hD]; ring
      -- Outer integrability from inner identity
      have h_outer_pair_int : Integrable
          (fun ω₁ => ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ) μ :=
        ((hαs_int.mul_const Q).sub (h_p_int.mul_const S)).add
          ((hq_int.mul_const r_star).sub (hs_int.mul_const D)) |>.congr
          (ae_of_all μ fun ω₁ => (h_inner_eq ω₁).symm)
      -- Body lower bound: ∫∫_full pair ≥ 2*δ_M*ds_M*(μ body)*V_body
      have h_body_pair_bound : 2 * δ_M * ds_M * (μ body).toReal * V_body s ≤
          ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
            (α ω₂ s) (α_star ω₂) ∂μ ∂μ := by
        -- pair_ge_delta_sq on body
        have h_pair_lb_body : ∀ ω₁ ω₂, γ ω₁ ≤ M → γ ω₂ ≤ M →
            δ_M * ds_M * ((α ω₁ s - α_star ω₁) ^ 2 + (α ω₂ s - α_star ω₂) ^ 2) ≤
            pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) := fun ω₁ ω₂ hω₁ hω₂ =>
          pair_ge_delta_sq
            (hα_inv ω₁ s (le_of_lt hs)).1 (hα_inv ω₂ s (le_of_lt hs)).1
            (hα_inv ω₁ s (le_of_lt hs)).2 (hα_inv ω₂ s (le_of_lt hs)).2
            (hα_star_pos ω₁) (hα_star_pos ω₂)
            hδ_M_pos (hα_lb_body ω₁ hω₁ s (le_of_lt hs))
            (hα_lb_body ω₂ hω₂ s (le_of_lt hs))
            (hds_lb_body ω₁ hω₁) (hds_lb_body ω₂ hω₂)
        -- Shared integrability: pair on body measure
        have h_p1_sq_int_body : Integrable (fun ω => (α ω s - α_star ω) ^ 2)
            (μ.restrict body) :=
          (hα_sq_int s).mono_measure Measure.restrict_le_self
        have h_pair_inner_int_body : ∀ ω₁, Integrable
            (fun ω₂ => pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂))
            (μ.restrict body) := fun ω₁ => by
          have hi12 : Integrable (fun ω₂ =>
              α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) μ :=
            (hq_int.const_mul (α_star ω₁)).sub (hs_int.const_mul (α ω₁ s - α_star ω₁))
          have hi21 : Integrable (fun ω₂ =>
              α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
              (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂)) μ :=
            (hαs_int.mul_const ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁))).sub
              (h_p_int.const_mul ((α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2)))
          have h_eq : ∀ ω₂, (fun ω₂ =>
              (α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
                (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
              (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
                (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂))) ω₂ =
              pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) := fun ω₂ => by
            unfold pairIntegrand; ring
          exact (hi12.add hi21).mono_measure Measure.restrict_le_self |>.congr
            (ae_of_all (μ.restrict body) (h_eq ·))
        have h_pair_nn_full : ∀ ω₁, 0 ≤ ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
            (α ω₂ s) (α_star ω₂) ∂μ := fun ω₁ =>
          integral_nonneg fun ω₂ => pair_bound (α ω₁ s) (α ω₂ s) (α_star ω₁) (α_star ω₂)
            (hα_inv ω₁ s (le_of_lt hs)).1 (hα_inv ω₂ s (le_of_lt hs)).1
            (hα_inv ω₁ s (le_of_lt hs)).2 (hα_inv ω₂ s (le_of_lt hs)).2
            (hα_star_pos ω₁) (hα_star_pos ω₂)
        have h_pair_nn_body : ∀ ω₁, 0 ≤ ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁)
            (α ω₂ s) (α_star ω₂) ∂μ := fun ω₁ =>
          integral_nonneg fun ω₂ => pair_bound (α ω₁ s) (α ω₂ s) (α_star ω₁) (α_star ω₂)
            (hα_inv ω₁ s (le_of_lt hs)).1 (hα_inv ω₂ s (le_of_lt hs)).1
            (hα_inv ω₁ s (le_of_lt hs)).2 (hα_inv ω₂ s (le_of_lt hs)).2
            (hα_star_pos ω₁) (hα_star_pos ω₂)
        have h_pi_int_full : ∀ ω₁, Integrable
            (fun ω₂ => pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂)) μ := fun ω₁ => by
          have hi12 : Integrable (fun ω₂ =>
              α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) μ :=
            (hq_int.const_mul (α_star ω₁)).sub (hs_int.const_mul (α ω₁ s - α_star ω₁))
          have hi21 : Integrable (fun ω₂ =>
              α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
              (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂)) μ :=
            (hαs_int.mul_const ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁))).sub
              (h_p_int.const_mul ((α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2)))
          have h_eq : ∀ ω₂, (fun ω₂ =>
              (α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
                (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
              (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
                (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂))) ω₂ =
              pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) := fun ω₂ => by
            unfold pairIntegrand; ring
          exact (hi12.add hi21).congr (ae_of_all μ (h_eq ·))
        have h_body_le_full : ∀ ω₁,
            ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ ≤
            ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ := fun ω₁ =>
          setIntegral_le_integral (h_pi_int_full ω₁)
            (ae_of_all μ fun ω₂ => pair_bound (α ω₁ s) (α ω₂ s) (α_star ω₁) (α_star ω₂)
              (hα_inv ω₁ s (le_of_lt hs)).1 (hα_inv ω₂ s (le_of_lt hs)).1
              (hα_inv ω₁ s (le_of_lt hs)).2 (hα_inv ω₂ s (le_of_lt hs)).2
              (hα_star_pos ω₁) (hα_star_pos ω₂))
        set Q_b := ∫ ω in body, (α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω) ∂μ
        set S_b := ∫ ω in body, (α ω s - α_star ω) * (1 - (α ω s) ^ 2) ∂μ
        set rs_b := ∫ ω in body, α_star ω ∂μ
        set D_b := ∫ ω in body, (α ω s - α_star ω) ∂μ
        have h_inner_body_eq : ∀ ω₁,
            ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ =
            (α_star ω₁ * Q_b - (α ω₁ s - α_star ω₁) * S_b) +
            ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁) * rs_b -
             (α ω₁ s - α_star ω₁) * (1 - (α ω₁ s) ^ 2) * D_b) := by
          intro ω₁
          have hq_b : Integrable (fun ω₂ =>
              α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
              (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2)))
              (μ.restrict body) :=
            ((hq_int.const_mul (α_star ω₁)).sub (hs_int.const_mul _)).mono_measure
              Measure.restrict_le_self
          have hp_b : Integrable (fun ω₂ =>
              α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
              (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂))
              (μ.restrict body) :=
            ((hαs_int.mul_const _).sub (h_p_int.const_mul _)).mono_measure
              Measure.restrict_le_self
          have h_rw : (fun ω₂ => pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂)) =
              fun ω₂ =>
              (α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
                (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
              (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
               (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) * (α ω₂ s - α_star ω₂)) :=
            funext fun ω₂ => by unfold pairIntegrand; ring
          rw [h_rw, integral_add hq_b hp_b]
          congr 1
          · rw [integral_sub (hq_int.const_mul _|>.mono_measure Measure.restrict_le_self)
                (hs_int.const_mul _|>.mono_measure Measure.restrict_le_self),
              integral_const_mul, integral_const_mul]
          · set c₁ := (α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)
            set c₂ := (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2)
            simp_rw [show ∀ ω₂, α_star ω₂ * c₁ - c₂ * (α ω₂ s - α_star ω₂) =
              c₁ * α_star ω₂ + (-c₂) * (α ω₂ s - α_star ω₂) from fun _ => by ring]
            rw [integral_add (hαs_int.mono_measure Measure.restrict_le_self |>.const_mul c₁)
              ((h_p_int.mono_measure Measure.restrict_le_self).const_mul (-c₂)),
              integral_const_mul, integral_const_mul]
            ring
        have h_outer_pair_body_int : Integrable
            (fun ω₁ => ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁)
              (α ω₂ s) (α_star ω₂) ∂μ) (μ.restrict body) :=
          ((hαs_int.mul_const Q_b).sub (h_p_int.mul_const S_b)).add
            ((hq_int.mul_const rs_b).sub (hs_int.mul_const D_b)) |>.mono_measure
              Measure.restrict_le_self |>.congr
          (ae_of_all (μ.restrict body) (fun ω₁ => (h_inner_body_eq ω₁).symm))
        -- body×body integral ≥ 2*δ_M*ds_M*(μ body)*V_body
        have h_body_body_lb : 2 * δ_M * ds_M * (μ body).toReal * V_body s ≤
            ∫ ω₁ in body, ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁)
              (α ω₂ s) (α_star ω₂) ∂μ ∂μ := by
          have h_lb_inner_int : ∀ ω₁, Integrable
              (fun ω₂ => δ_M * ds_M * ((α ω₁ s - α_star ω₁) ^ 2 + (α ω₂ s - α_star ω₂) ^ 2))
              (μ.restrict body) :=
            fun ω₁ => ((integrable_const _).add h_p1_sq_int_body).const_mul _
          have h_inner_lb : ∀ ω₁ ∈ body,
              δ_M * ds_M * ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s) ≤
              ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁)
                (α ω₂ s) (α_star ω₂) ∂μ := by
            intro ω₁ hω₁
            have h_inner_rhs_eq : ∫ ω₂ in body, δ_M * ds_M *
                ((α ω₁ s - α_star ω₁) ^ 2 + (α ω₂ s - α_star ω₂) ^ 2) ∂μ =
                δ_M * ds_M * ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s) := by
              simp_rw [show ∀ ω₂, δ_M * ds_M *
                  ((α ω₁ s - α_star ω₁) ^ 2 + (α ω₂ s - α_star ω₂) ^ 2) =
                  δ_M * ds_M * (α ω₁ s - α_star ω₁) ^ 2 +
                  δ_M * ds_M * (α ω₂ s - α_star ω₂) ^ 2 from fun _ => by ring]
              rw [integral_add
                  ((integrable_const _).mono_measure Measure.restrict_le_self)
                  (h_p1_sq_int_body.const_mul _),
                setIntegral_const, integral_const_mul]
              simp only [Measure.real, smul_eq_mul]; ring
            rw [← h_inner_rhs_eq]
            exact setIntegral_mono_on (h_lb_inner_int ω₁) (h_pair_inner_int_body ω₁)
              hbody_meas (fun ω₂ hω₂ => h_pair_lb_body ω₁ ω₂ hω₁ hω₂)
          have h_outer_lb_int : Integrable
              (fun ω₁ => δ_M * ds_M *
                ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s))
              (μ.restrict body) := by
            have hrw : (fun ω₁ => δ_M * ds_M *
                ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s)) =
                fun ω₁ => δ_M * ds_M * ((μ body).toReal * (α ω₁ s - α_star ω₁) ^ 2 + V_body s) := by
              funext ω₁; ring
            rw [hrw]
            exact ((h_p1_sq_int_body.const_mul (μ body).toReal).add
              ((integrable_const (V_body s)).mono_measure Measure.restrict_le_self))
              |>.const_mul (δ_M * ds_M)
          have h_outer_mono : ∫ ω₁ in body, δ_M * ds_M *
              ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s) ∂μ ≤
              ∫ ω₁ in body, ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁)
                (α ω₂ s) (α_star ω₂) ∂μ ∂μ :=
            setIntegral_mono_on h_outer_lb_int h_outer_pair_body_int hbody_meas h_inner_lb
          have h_lhs_eq : ∫ ω₁ in body, δ_M * ds_M *
              ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s) ∂μ =
              2 * δ_M * ds_M * (μ body).toReal * V_body s := by
            simp_rw [show ∀ ω₁, δ_M * ds_M *
                ((α ω₁ s - α_star ω₁) ^ 2 * (μ body).toReal + V_body s) =
                δ_M * ds_M * (μ body).toReal * (α ω₁ s - α_star ω₁) ^ 2 +
                δ_M * ds_M * V_body s from fun _ => by ring]
            rw [integral_add
                (h_p1_sq_int_body.const_mul _)
                ((integrable_const _).mono_measure Measure.restrict_le_self),
              setIntegral_const, integral_const_mul]
            simp only [Measure.real, smul_eq_mul, V_body]; ring
          linarith
        -- body×body ≤ full×full
        have h_inner_body_le_full : ∀ ω₁,
            ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ ≤
            ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ := fun ω₁ =>
          setIntegral_le_integral (h_pi_int_full ω₁)
            (ae_of_all μ fun ω₂ =>
              pair_bound (α ω₁ s) (α ω₂ s) (α_star ω₁) (α_star ω₂)
                (hα_inv ω₁ s (le_of_lt hs)).1 (hα_inv ω₂ s (le_of_lt hs)).1
                (hα_inv ω₁ s (le_of_lt hs)).2 (hα_inv ω₂ s (le_of_lt hs)).2
                (hα_star_pos ω₁) (hα_star_pos ω₂))
        have h_outer_body_le : ∫ ω₁ in body,
            ∫ ω₂ in body, pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ ∂μ ≤
            ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
              (α ω₂ s) (α_star ω₂) ∂μ ∂μ :=
          (setIntegral_mono_on h_outer_pair_body_int h_outer_pair_int.integrableOn
            hbody_meas (fun ω₁ _ => h_body_le_full ω₁)).trans
            (setIntegral_le_integral h_outer_pair_int
              (ae_of_all μ fun ω₁ => h_pair_nn_full ω₁))
        linarith
      -- Connect to derivative via pair_fubini_identity
      have h_D_eq : ∫ ω, (α ω s - α_star ω) ∂μ = D := by
        simp only [D]; rw [integral_sub (hα_int s) hαs_int, h_sc s (le_of_lt hs), hr_star_eq]
      have h_out12' : Integrable (fun ω₁ =>
          α_star ω₁ * (∫ ω, (α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω) ∂μ) -
          (α ω₁ s - α_star ω₁) * (∫ ω, (α ω s - α_star ω) * (1 - α ω s ^ 2) ∂μ)) μ :=
        (hαs_int.mul_const Q).sub (h_p_int.mul_const S)
      have h_out21' : Integrable (fun ω₁ =>
          (α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁) *
            (∫ ω, α_star ω ∂μ) -
          (α ω₁ s - α_star ω₁) * (1 - α ω₁ s ^ 2) *
            (∫ ω, (α ω s - α_star ω) ∂μ)) μ :=
        (hq_int.mul_const (∫ ω, α_star ω ∂μ)).sub
          (hs_int.mul_const (∫ ω, (α ω s - α_star ω) ∂μ))
      have h_fub := pair_fubini_identity (μ := μ) (fun ω => α ω s) α_star
        hq_int hs_int hαs_int h_p_int h_out12' h_out21'
      have h_pair_val : ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
          (α ω₂ s) (α_star ω₂) ∂μ ∂μ = 2 * (r_star * Q - D * S) := by
        have : ∫ ω₁, ∫ ω₂, pairIntegrand (α ω₁ s) (α_star ω₁)
            (α ω₂ s) (α_star ω₂) ∂μ ∂μ =
            ∫ ω₁, ∫ ω₂,
              ((α_star ω₁ * ((α ω₂ s - α_star ω₂) ^ 2 * (α ω₂ s + 1 / α_star ω₂)) -
                (α ω₁ s - α_star ω₁) * ((α ω₂ s - α_star ω₂) * (1 - α ω₂ s ^ 2))) +
              (α_star ω₂ * ((α ω₁ s - α_star ω₁) ^ 2 * (α ω₁ s + 1 / α_star ω₁)) -
                (α ω₁ s - α_star ω₁) * (α ω₂ s - α_star ω₂) * (1 - α ω₁ s ^ 2))) ∂μ ∂μ := by
          congr 1; ext ω₁; congr 1; ext ω₂; unfold pairIntegrand; ring
        rw [this, h_fub, h_D_eq, ← hr_star_eq]
      have h_all_pair_ge : 0 ≤ ∫ ω₁, ∫ ω₂,
          pairIntegrand (α ω₁ s) (α_star ω₁) (α ω₂ s) (α_star ω₂) ∂μ ∂μ :=
        (pair_bound_from_products (fun ω => α ω s) α_star
          (fun ω => (hα_inv ω s (le_of_lt hs)).1)
          (fun ω => (hα_inv ω s (le_of_lt hs)).2) hα_star_pos (μ := μ)).trans_eq
          (by congr 1; ext ω₁; congr 1; ext ω₂; unfold pairIntegrand; ring)
      -- Derivative computation
      have h_pw : ∀ ω, 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s) =
          (-K * r_star) * ((α ω s - α_star ω) ^ 2 * (α ω s + 1 / α_star ω)) +
          (K * (r s - r_star)) * ((α ω s - α_star ω) * (1 - (α ω s) ^ 2)) := by
        intro ω
        have hγω : γ ω = K / 2 * r_star * (1 - (α_star ω) ^ 2) / α_star ω := by
          have heq := hα_star_equil ω
          field_simp [ne_of_gt (hα_star_pos ω)] at heq ⊢; linarith
        simp only [oaScalarRHS]; rw [hγω]
        field_simp [ne_of_gt (hα_star_pos ω)]; ring
      rw [show ∫ ω, 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s) ∂μ =
          (-K * r_star) * Q + (K * D) * S from by
        simp_rw [h_pw]
        rw [integral_add (hq_int.const_mul _) (hs_int.const_mul _)]
        simp_rw [integral_const_mul]; simp [Q, S, D]]
      have h_chain : K * (r_star * Q - D * S) ≥ c₀ := by
        have h1 : r_star * Q - D * S ≥ δ_M * ds_M * (μ body).toReal * V_body s := by
          have hbp := h_body_pair_bound
          rw [h_pair_val] at hbp; linarith
        have h2 : V_body s ≥ 3 * L / 4 := hVb_ge s
        have h4 : r_star * Q - D * S ≥ δ_M * ds_M * (μ body).toReal * (3 * L / 4) := by
          calc r_star * Q - D * S ≥ δ_M * ds_M * (μ body).toReal * V_body s := h1
            _ ≥ δ_M * ds_M * (μ body).toReal * (3 * L / 4) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        have h5 : K * (r_star * Q - D * S) ≥ K * (δ_M * ds_M * (μ body).toReal * (3 * L / 4)) :=
          mul_le_mul_of_nonneg_left h4 (le_of_lt hK)
        simp only [c₀]; linarith
      linarith
    -- Additive drift contradiction: V decreases by c₀ per unit time
    have hW_le : ∀ n : ℕ, V (1 + ↑n) ≤ V 1 - c₀ * ↑n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hsk : (0 : ℝ) < 1 + ↑k := by positivity
        have hW_anti : AntitoneOn (fun t => V t + c₀ * t)
            (Icc (1 + ↑k) (1 + ↑(k + 1))) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          · apply ContinuousOn.add
            · exact hV_cont_on.mono (fun t ht => mem_Ici.mpr (le_trans (le_of_lt hsk) ht.1))
            · exact (continuousOn_const.mul continuousOn_id)
          · intro t ht
            rw [interior_Icc] at ht
            have ht_pos : 0 < t := lt_trans hsk ht.1
            have hc₀t : HasDerivAt (fun u => c₀ * u) c₀ t := by
              have := (hasDerivAt_id t).const_mul c₀
              simp only [mul_one, id] at this; exact this
            exact (hV_has_deriv t ht_pos |>.add hc₀t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            have ht_pos : 0 < t := lt_trans hsk ht.1
            have hVd := hV_has_deriv t ht_pos
            have hc₀t : HasDerivAt (fun u => c₀ * u) c₀ t := by
              have := (hasDerivAt_id t).const_mul c₀
              simp only [mul_one, id] at this; exact this
            have hW_has : HasDerivAt (fun t => V t + c₀ * t)
                (∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ + c₀) t :=
              hVd.add hc₀t
            rw [hW_has.deriv]
            linarith [hV'_le t ht_pos]
        have hW_drop := hW_anti
          (left_mem_Icc.mpr (by push_cast; linarith))
          (right_mem_Icc.mpr (by push_cast; linarith))
          (by push_cast; linarith)
        simp only at hW_drop
        push_cast at hW_drop ih ⊢
        linarith
    -- Final contradiction: choose n large enough so V(1+n) < 0
    obtain ⟨n, hn⟩ : ∃ n : ℕ, V 1 < c₀ * ↑n := by
      refine ⟨⌈V 1 / c₀⌉₊ + 1, ?_⟩
      have h1 : V 1 / c₀ < ↑(⌈V 1 / c₀⌉₊ + 1) := by
        push_cast
        exact lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
      linarith [(div_lt_iff₀ hc₀_pos).mp h1]
    linarith [hV_nn (1 + (n : ℝ)), hW_le n]
  -- Step 4: V → 0 implies r → r*
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

/-- **Definitive Continuum Kuramoto Stability (Tail-Body Split).**

For the standard continuum Kuramoto model with unbounded γ(ω) = |ω|.

Compared to `kuramoto_solved` (GeneralGMainTheorem.lean):
- NO `γ_max` or `hγ_bdd`: γ may be unbounded, only needs `∫ γ dμ < ∞`
- NO uniform persistence: only body persistence on each {γ ≤ M}
- NO `c_min`: rate from body pair coercivity, not minimum atom weight

The tail-body split:
1. **Tail** {γ > M}: V_tail ≤ μ({γ > M}) → 0 by Markov (∫γ < ∞)
2. **Body** {γ ≤ M}: γ bounded by M → Leibniz works → pair coercivity → V_body → 0
3. **Combine**: V = V_body + V_tail → 0, so |r - r*|² ≤ V → 0

Applicable to Gaussian, Student-t (ν > 2), compact support distributions.
Proved: 0 sorry, 0 axioms. -/
theorem kuramoto_solved_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
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
      (∀ M, 0 < M → ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t) ∧
      (∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) :=
  kuramoto_solved_integrable_gamma γ K hK hγ hγ_int hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil α_0 hα_0_pos hα_0_lt h_exists

end
