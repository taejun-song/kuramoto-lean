/-
  KuramotoGammaMinFirstMomentConcrete.lean
  =========================================
  Concrete version of ContinuumGammaMinFirstMoment.lean (exp 294).

  REPLACES the abstract (C, h_body_rate, h_combined_vanish) triad with
  concrete physical hypotheses:
    • hr_star_pos: r* > 0 (equilibrium order parameter is positive)
    • α₀_lb: global lower bound α₀_lb ≤ α(ω,t) ∀ω, t ≥ 0
    • hV_body_cont: V_body(M,·) ∈ C([0,∞)) for each M > 0
    • hμ_body_pos: μ{γ ≤ M} > 0 for each M > 0

  DERIVES internally:
    • Equilibrium lower bound: α*(ω) ≥ K·r*/(2M+K·r*) for γ(ω) ≤ M
      (algebraic consequence of equilibrium equation + α*∈(0,1))
    • Body Gronwall absorbing radius C(M) = K·τ(M)/rate(M) via
      body_gronwall_from_persistence with δ=α₀_lb, ds=K·r*/(2M+K·r*)
    • Combined vanishing C(M)+τ(M) → 0 from:
        - M·τ(M) → 0 (first_moment_tail_vanish, ∫γ<∞)
        - τ(M) → 0 (tail_measure_tendsto_zero', probability measure)

  KEY ALGEBRAIC FACT: For α* ∈ (0,1) with γ·α* = (K/2)·r*(1-α*²):
    α* · (2γ+Kr*) = Kr*(1-α*²) + Kr*·α* = Kr*(1+α*(1-α*)) ≥ Kr*
  Hence Kr*/(2γ+Kr*) ≤ α*. Then Kr*/(2M+Kr*) ≤ Kr*/(2γ+Kr*) ≤ α* for γ≤M.

  COVERAGE: Same as kuramoto_gamma_min_first_moment (γ_min>0, first moment)
  with the explicit addition of global persistence α₀_lb ≤ α(ω,t).

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumGammaMinFirstMoment
import KuramotoLean.BodyGronwallBound
import KuramotoLean.FirstMomentTailVanish

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Equilibrium lower bound from algebraic constraint.**
    If α* ∈ (0,1) satisfies γ·α* = (K/2)·r·(1-α*²) and γ ≤ M, then
    α* ≥ K·r/(2·M + K·r).

    Proof: α*·(2γ+Kr) = Kr(1-α*²) + Kr·α* = Kr(1+α*(1-α*)) ≥ Kr
    (since α*(1-α*) ≥ 0 for α*∈(0,1)), so Kr ≤ α*·(2γ+Kr) ≤ α*·(2M+Kr). -/
private lemma equil_lb_from_constraint
    (γ_v α_v K r M : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hM : 0 < M)
    (hα_pos : 0 < α_v) (hα_lt : α_v < 1) (hγ_le : γ_v ≤ M)
    (hequil : γ_v * α_v = (K / 2) * r * (1 - α_v ^ 2)) :
    K * r / (2 * M + K * r) ≤ α_v := by
  have h_denom : 0 < 2 * M + K * r := by positivity
  rw [div_le_iff₀ h_denom]
  have h_expand : 2 * γ_v * α_v = K * r * (1 - α_v ^ 2) := by linarith
  have h_step : K * r ≤ α_v * (2 * γ_v + K * r) := by
    nlinarith [sq_nonneg α_v, mul_pos hα_pos (by linarith : (0 : ℝ) < 1 - α_v),
      mul_pos hK hr]
  calc K * r ≤ α_v * (2 * γ_v + K * r) := h_step
    _ ≤ α_v * (2 * M + K * r) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hα_pos)

/-- **Concrete first-moment convergence: γ_min > 0 + first moment + global persistence.**

    End-to-end theorem from ODE hypotheses + γ_min > 0 + first moment ∫γdμ<∞
    + global persistence α₀_lb ≤ α(ω,t) → r(t) → r*.

    REPLACES abstract (C, h_body_rate, h_combined_vanish) from
    `kuramoto_gamma_min_first_moment` with concrete derivable consequences.

    The body absorbing radius is:
      C(M) = K·τ(M) / (K·α₀_lb·(K·r*/(2M+K·r*))·μ{γ≤M})

    Combined vanishing C(M)+τ(M) → 0 follows from:
      C(M) ≤ [2/(α₀_lb·K·r*·μ₁)] · M·τ(M) + [1/(α₀_lb·μ₁)] · τ(M)
    where M·τ(M) → 0 (first moment) and τ(M) → 0 (probability measure). -/
theorem kuramoto_gamma_min_first_moment_concrete [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_int : Integrable γ μ)
    (γ_min : ℝ) (hγ_min : 0 < γ_min) (hγ_lb : ∀ ω, γ_min ≤ γ ω)
    (α₀_lb : ℝ) (hα₀_lb_pos : 0 < α₀_lb)
    (hα_lb : ∀ ω t, 0 ≤ t → α₀_lb ≤ α ω t)
    (hV_body_cont : ∀ M, 0 < M → ContinuousOn
        (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0))
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    Tendsto r atTop (nhds r_star) := by
  have hds_lb : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → K * r_star / (2 * M + K * r_star) ≤ α_star ω :=
    fun M hM ω hω => equil_lb_from_constraint (γ ω) (α_star ω) K r_star M hK hr_star_pos hM
      (hα_star_pos ω) (hα_star_lt ω) hω (hα_star_equil ω)
  have hds_pos : ∀ M, 0 < M → 0 < K * r_star / (2 * M + K * r_star) := fun M hM => by positivity
  let C : ℝ → ℝ := fun M =>
    K * (μ {ω | M < γ ω}).toReal /
      (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal)
  have hC_nn : ∀ M, 0 ≤ C M := by
    intro M
    show 0 ≤ K * (μ {ω | M < γ ω}).toReal /
        (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal)
    by_cases hM_nn : (0 : ℝ) ≤ M
    · apply div_nonneg (mul_nonneg hK.le ENNReal.toReal_nonneg)
      apply mul_nonneg
      · apply mul_nonneg (mul_nonneg hK.le hα₀_lb_pos.le)
        exact div_nonneg (mul_nonneg hK.le hr_star_pos.le) (by positivity)
      · exact ENNReal.toReal_nonneg
    · push_neg at hM_nn
      have h_empty : (μ {ω : Ω | γ ω ≤ M}).toReal = 0 := by
        have hset : {ω : Ω | γ ω ≤ M} = ∅ := by
          ext ω
          simp only [mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_trans hM_nn (lt_of_lt_of_le hγ_min (hγ_lb ω))
        simp [hset]
      simp [h_empty]
  have h_body_rate : ∀ M : ℝ, 0 < M → ∃ rate : ℝ, 0 < rate ∧ ∀ t ≥ (0 : ℝ),
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t) + C M := by
    intro M hM
    obtain ⟨hrate_pos, hbound⟩ := body_gronwall_from_persistence γ K hK hγ hγ_meas
      α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hr_bdd
      hα_ode hα_int hα_sq_int hα_inv h_sc M hM (hγ_level M) α₀_lb hα₀_lb_pos
      (K * r_star / (2 * M + K * r_star)) (hds_pos M hM)
      (fun ω _ t ht => hα_lb ω t ht) (hds_lb M hM) (hμ_body_pos M hM) (hV_body_cont M hM)
    exact ⟨K * α₀_lb * (K * r_star / (2 * M + K * r_star)) * (μ {ω | γ ω ≤ M}).toReal,
      hrate_pos, hbound⟩
  have h_combined_vanish : Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
    have h_Mτ := first_moment_tail_vanish γ hγ hγ_int hγ_level
    have h_τ : Tendsto (fun M : ℝ => (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
      tail_measure_tendsto_zero' γ hγ_level
    have hμ₁_pos : 0 < (μ {ω | γ ω ≤ 1}).toReal := hμ_body_pos 1 one_pos
    let A := 2 / (α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal)
    let B := 1 / (α₀_lb * (μ {ω | γ ω ≤ 1}).toReal) + 1
    have hA_pos : 0 < A := by positivity
    have hB_pos : 0 < B := by positivity
    have h_upper : Tendsto
        (fun M : ℝ => A * M * (μ {ω | M < γ ω}).toReal + B * (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun M : ℝ => A * (M * (μ {ω | M < γ ω}).toReal)) atTop (nhds 0) := by
        have h := h_Mτ.const_mul A
        simp only [mul_zero] at h
        exact h.congr (fun M => by ring)
      have h2 : Tendsto (fun M : ℝ => B * (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
        have h := h_τ.const_mul B
        simp only [mul_zero] at h
        exact h
      have h3 := h1.add h2
      simp only [add_zero] at h3
      exact h3.congr (fun M => by ring)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    · filter_upwards with M
      have := hC_nn M
      have : (0 : ℝ) ≤ (μ {ω | M < γ ω}).toReal := ENNReal.toReal_nonneg
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
      have hM_pos : 0 < M := by linarith
      have h_τ_nn : 0 ≤ (μ {ω | M < γ ω}).toReal := ENNReal.toReal_nonneg
      have h_μ_body_pos : 0 < (μ {ω | γ ω ≤ M}).toReal := hμ_body_pos M hM_pos
      have h_μ_mono : (μ {ω | γ ω ≤ 1}).toReal ≤ (μ {ω | γ ω ≤ M}).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _)
          (measure_mono (fun ω hω => le_trans hω hM))
      have h_C_eq : C M = (μ {ω | M < γ ω}).toReal * (2 * M + K * r_star) /
          (α₀_lb * K * r_star * (μ {ω | γ ω ≤ M}).toReal) := by
        show K * (μ {ω | M < γ ω}).toReal /
            (K * α₀_lb * (K * r_star / (2 * M + K * r_star)) *
              (μ {ω | γ ω ≤ M}).toReal) =
          (μ {ω | M < γ ω}).toReal * (2 * M + K * r_star) /
            (α₀_lb * K * r_star * (μ {ω | γ ω ≤ M}).toReal)
        have hd : (2 : ℝ) * M + K * r_star ≠ 0 := by positivity
        have hK_ne : K ≠ 0 := ne_of_gt hK
        have hr_ne : r_star ≠ 0 := ne_of_gt hr_star_pos
        have hα_ne : α₀_lb ≠ 0 := ne_of_gt hα₀_lb_pos
        have hμ_ne : (μ {ω | γ ω ≤ M}).toReal ≠ 0 := ne_of_gt h_μ_body_pos
        field_simp [hd, hK_ne, hr_ne, hα_ne, hμ_ne]
      have h_C_bound : C M ≤ (μ {ω | M < γ ω}).toReal * (2 * M + K * r_star) /
          (α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal) := by
        rw [h_C_eq]
        apply div_le_div_of_nonneg_left
          (mul_nonneg h_τ_nn (by positivity))
          (by positivity)
          (mul_le_mul_of_nonneg_left h_μ_mono (by positivity))
      have h_arith : (μ {ω | M < γ ω}).toReal * (2 * M + K * r_star) /
          (α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal) +
          (μ {ω | M < γ ω}).toReal =
          A * M * (μ {ω | M < γ ω}).toReal + B * (μ {ω | M < γ ω}).toReal := by
        have h_ne : α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal ≠ 0 := by positivity
        have h_ne2 : α₀_lb * (μ {ω | γ ω ≤ 1}).toReal ≠ 0 := by positivity
        show (μ {ω | M < γ ω}).toReal * (2 * M + K * r_star) /
            (α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal) +
            (μ {ω | M < γ ω}).toReal =
          2 / (α₀_lb * K * r_star * (μ {ω | γ ω ≤ 1}).toReal) * M *
            (μ {ω | M < γ ω}).toReal +
          (1 / (α₀_lb * (μ {ω | γ ω ≤ 1}).toReal) + 1) * (μ {ω | M < γ ω}).toReal
        field_simp [h_ne, h_ne2]
        ring
      linarith
  exact kuramoto_gamma_min_first_moment γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hr_cont hr_bdd hr_nn
    hα_ode hα_cont hα_neg h_sc hα_int hα_sq_int hα_inv hγ_int γ_min hγ_min hγ_lb
    C hC_nn h_body_rate h_combined_vanish

end
