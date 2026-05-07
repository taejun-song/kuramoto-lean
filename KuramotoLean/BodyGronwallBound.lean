/-
  BodyGronwallBound.lean
  ======================
  Proves the body Gronwall bound from body persistence δ and equilibrium
  lower bound ds on body {γ ≤ M}.

  Given body persistence δ > 0 and equilibrium lower bound ds > 0, there
  exists rate = K·δ·ds·μ(body) > 0 such that
    V_body(t) ≤ V_body(0)·exp(-rate·t) + K·μ(tail)/rate.

  Proof chain:
    body Leibniz (re-proved with hγ_nn, no hα_neg)
    → per-ω identity (from equilibrium equation)
    → body integral decomposition
    → body Fubini (pair_fubini_identity on μ.restrict body)
    → body pair coercivity (pair_ge_delta_sq + setIntegral_mono_on)
    → tail bounds
    → derivative bound ≤ -rate·V_body + K·μ(tail)
    → body_gronwall_from_deriv

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumDerivedGronwall
import KuramotoLean.ContinuumIdentity
import KuramotoLean.ContinuumUniformRate

set_option maxHeartbeats 400000

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Body Leibniz without hγ_pos / hα_neg -/

private theorem body_leibniz_at_nn [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hK : 0 < K) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hαs_int : Integrable α_star μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (M : ℝ) (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    HasDerivAt (fun s => ∫ ω in {ω | γ ω ≤ M}, (α ω s - α_star ω) ^ 2 ∂μ)
      (∫ ω in {ω | γ ω ≤ M}, 2 * (α ω t₀ - α_star ω) *
        oaScalarRHS (γ ω) K r t₀ (α ω t₀) ∂μ) t₀ := by
  set body := {ω | γ ω ≤ M}
  haveI : IsFiniteMeasure (μ.restrict body) := isFiniteMeasureRestrict μ body
  have h_pw_deriv : ∀ ω, ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (fun u => (α ω u - α_star ω) ^ 2)
        (2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)) s := fun ω s hs => by
    have h := (hα_ode ω s (le_of_lt (mem_Ioi.mp hs))).sub_const (α_star ω)
    convert h.pow 2 using 1; push_cast; ring
  have h_norm_bound : ∀ ω ∈ {ω | γ ω ≤ M}, ∀ s ∈ Ioi (0 : ℝ),
      ‖2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s)‖ ≤ 2 * M + K := by
    intro ω hω s hs
    have hs_pos := mem_Ioi.mp hs
    have hp := (hα_inv ω s (le_of_lt hs_pos)).1
    have hl := (hα_inv ω s (le_of_lt hs_pos)).2
    have h_rhs_le : |oaScalarRHS (γ ω) K r s (α ω s)| ≤ M + K / 2 := by
      unfold oaScalarRHS
      have hr1 := hr_bdd s
      have hrs_lo : -1 ≤ r s := by linarith [(abs_le.mp hr1).1]
      have hrs_hi : r s ≤ 1 := (abs_le.mp hr1).2
      have h1mα2_nn : 0 ≤ 1 - (α ω s) ^ 2 := by nlinarith [sq_nonneg (α ω s)]
      have hp_lo : -1 ≤ r s * (1 - (α ω s) ^ 2) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + r s) h1mα2_nn, sq_nonneg (α ω s)]
      have hp_hi : r s * (1 - (α ω s) ^ 2) ≤ 1 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - r s) h1mα2_nn, sq_nonneg (α ω s)]
      have hK2 : 0 < K / 2 := by linarith
      have h_term1_lo : -(γ ω) * α ω s ≥ -M := by
        have h1 : γ ω * α ω s ≤ γ ω := mul_le_of_le_one_right (hγ_nn ω) (le_of_lt hl)
        have h2 : -(γ ω) * α ω s = -(γ ω * α ω s) := by ring
        have hγM : γ ω ≤ M := hω
        linarith
      have h_term1_hi : -(γ ω) * α ω s ≤ 0 :=
        by linarith [mul_nonneg (hγ_nn ω) (le_of_lt hp)]
      have h_term2_lo : K / 2 * (r s * (1 - (α ω s) ^ 2)) ≥ -(K / 2) := by
        nlinarith [mul_nonneg (le_of_lt hK2) (by linarith : 0 ≤ r s * (1 - (α ω s) ^ 2) + 1)]
      have h_term2_hi : K / 2 * (r s * (1 - (α ω s) ^ 2)) ≤ K / 2 := by
        nlinarith [mul_nonneg (le_of_lt hK2) (by linarith : 0 ≤ 1 - r s * (1 - (α ω s) ^ 2))]
      have heq : K / 2 * r s * (1 - (α ω s) ^ 2) = K / 2 * (r s * (1 - (α ω s) ^ 2)) := by ring
      rw [abs_le, heq]
      constructor <;> linarith
    have h_abs_diff : |α ω s - α_star ω| ≤ 1 :=
      abs_le.mpr ⟨by linarith [le_of_lt hp, hα_star_lt ω], by linarith [le_of_lt hl, hα_star_pos ω]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg (α ω s - α_star ω), abs_nonneg (oaScalarRHS (γ ω) K r s (α ω s)),
      mul_le_mul h_abs_diff h_rhs_le (abs_nonneg (oaScalarRHS (γ ω) K r s (α ω s))) one_pos.le]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => (α ω s - α_star ω) ^ 2)
    (F' := fun s ω => 2 * (α ω s - α_star ω) * oaScalarRHS (γ ω) K r s (α ω s))
    (bound := fun _ => 2 * M + K) (x₀ := t₀) (μ := μ.restrict body)
    (hs := Ioi_mem_nhds ht₀)
    (hF_meas := Eventually.of_forall fun s =>
      ((hα_sq_int s).aestronglyMeasurable).mono_measure Measure.restrict_le_self)
    (hF_int := (hα_sq_int t₀).mono_measure Measure.restrict_le_self)
    (hF'_meas := by
      change AEStronglyMeasurable (fun ω => 2 * (α ω t₀ - α_star ω) *
          (-(γ ω) * α ω t₀ + K / 2 * r t₀ * (1 - (α ω t₀) ^ 2))) (μ.restrict body)
      exact ((aestronglyMeasurable_const.mul
        ((hα_int t₀).aestronglyMeasurable.sub hαs_int.aestronglyMeasurable)).mul
        ((hγ_meas.neg.mul (hα_int t₀).aestronglyMeasurable).add
          (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.sub
            ((hα_int t₀).aestronglyMeasurable.pow 2))))).mono_measure Measure.restrict_le_self)
    (h_bound := (ae_restrict_mem hγ_level).mono fun ω hω s hs => h_norm_bound ω hω s hs)
    (bound_integrable := integrable_const _)
    (h_diff := Eventually.of_forall fun ω s hs => h_pw_deriv ω s hs)).2

/-! ## Helper lemmas with small contexts -/

private lemma s_integrand_abs_le_one (a b : ℝ) (hp : 0 < a) (hl : a < 1)
    (hb : 0 < b) (hbl : b < 1) :
    -1 ≤ (a - b) * (1 - a ^ 2) ∧ (a - b) * (1 - a ^ 2) ≤ 1 := by
  have h1ma2 : 0 ≤ 1 - a ^ 2 := by nlinarith [sq_nonneg a]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + (a - b)) h1ma2]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b + 1) (sq_nonneg a)]

/-- K*D_t*S_b ≤ K*μ(tail) given bounds on D_t and S_b. -/
private lemma k_dt_sb_bound (K D_t S_b μ_tail μ_body : ℝ)
    (hK : 0 < K)
    (h_D_t_le : D_t ≤ μ_tail) (h_D_t_ge : -μ_tail ≤ D_t)
    (h_S_b_le : S_b ≤ μ_body) (h_S_b_ge : -μ_body ≤ S_b)
    (hμ_body_le1 : μ_body ≤ 1)
    (htail_nn : 0 ≤ μ_tail) :
    K * D_t * S_b ≤ K * μ_tail := by
  have h_assoc : K * D_t * S_b = K * (D_t * S_b) := by ring
  rcases le_or_gt 0 S_b with hSb_nn | hSb_neg
  · have h1 : D_t * S_b ≤ μ_tail * S_b := mul_le_mul_of_nonneg_right h_D_t_le hSb_nn
    have h2 : μ_tail * S_b ≤ μ_tail * 1 :=
      mul_le_mul_of_nonneg_left (h_S_b_le.trans hμ_body_le1) htail_nn
    have h4 : K * (D_t * S_b) ≤ K * μ_tail :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hK)
    linarith
  · have hSb_le0 : S_b ≤ 0 := le_of_lt hSb_neg
    rcases le_or_gt 0 D_t with hDt_nn | hDt_neg
    · have h1 : D_t * S_b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDt_nn hSb_le0
      have h2 : K * (D_t * S_b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hK) h1
      linarith [mul_nonneg (le_of_lt hK) htail_nn]
    · have hSb_pos : 0 ≤ -S_b := by linarith
      have hDt_abs : -D_t ≤ μ_tail := by linarith
      have hSb_abs : -S_b ≤ 1 := by linarith
      have h1 : (-D_t) * (-S_b) ≤ μ_tail * 1 :=
        (mul_le_mul_of_nonneg_right hDt_abs hSb_pos).trans
          (mul_le_mul_of_nonneg_left hSb_abs htail_nn)
      have h4 : K * (D_t * S_b) ≤ K * μ_tail :=
        mul_le_mul_of_nonneg_left (by nlinarith) (le_of_lt hK)
      linarith

/-! ## Main theorem -/

theorem body_gronwall_from_persistence [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (M : ℝ) (hM : 0 < M)
    (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (δ : ℝ) (hδ : 0 < δ)
    (ds : ℝ) (hds : 0 < ds)
    (hα_lb : ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t)
    (hds_lb : ∀ ω, γ ω ≤ M → ds ≤ α_star ω)
    (hμ_body_pos : 0 < (μ {ω | γ ω ≤ M}).toReal)
    (hV_body_cont : ContinuousOn
        (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0)) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ t ≥ (0 : ℝ),
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
          rexp (-rate * t) + K * (μ {ω | M < γ ω}).toReal / rate := by
  set body := {ω | γ ω ≤ M}
  set tail := {ω | M < γ ω}
  set V_body := fun t => ∫ ω in body, (α ω t - α_star ω) ^ 2 ∂μ
  set rate := K * δ * ds * (μ body).toReal
  have hrate_pos : 0 < rate := by
    simp only [rate]
    exact mul_pos (mul_pos (mul_pos hK hδ) hds) hμ_body_pos
  refine ⟨rate, hrate_pos, ?_⟩
  apply body_gronwall_from_deriv V_body
    (fun t => ∫ ω in body, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ)
    rate (K * (μ tail).toReal) hrate_pos (by positivity) hV_body_cont
  · intro t₀ ht₀
    exact body_leibniz_at_nn γ K r α α_star hα_ode hα_inv hα_sq_int hγ_nn hK hr_bdd
      hα_star_pos hα_star_lt hα_int hαs_int hγ_meas M hγ_level t₀ ht₀
  · intro t₀ ht₀
    -- Local setup
    haveI hbody_fin : IsFiniteMeasure (μ.restrict body) := isFiniteMeasureRestrict μ body
    have hbody_meas : MeasurableSet body := hγ_level
    have htail_meas : MeasurableSet tail := by
      have : tail = bodyᶜ := by ext ω; simp [body, tail]
      rw [this]; exact hbody_meas.compl
    -- Basic integrability at t₀
    have h_p_int : Integrable (fun ω => α ω t₀ - α_star ω) μ := (hα_int t₀).sub hαs_int
    have h_p_int_b : Integrable (fun ω => α ω t₀ - α_star ω) (μ.restrict body) :=
      h_p_int.mono_measure Measure.restrict_le_self
    have h_p1_sq_int_b : Integrable (fun ω => (α ω t₀ - α_star ω) ^ 2) (μ.restrict body) :=
      (hα_sq_int t₀).mono_measure Measure.restrict_le_self
    have hαs_int_b : Integrable α_star (μ.restrict body) :=
      hαs_int.mono_measure Measure.restrict_le_self
    -- Q_b integrability: (α-α*)²*(α+1/α*) bounded on body by 1*(1+1/ds)
    have hq_int_b : Integrable (fun ω => (α ω t₀ - α_star ω) ^ 2 *
        (α ω t₀ + 1 / α_star ω)) (μ.restrict body) := by
      apply Integrable.mono' (integrable_const (1 + 1 / ds) |>.mono_measure Measure.restrict_le_self)
      · have h_inv_meas : AEStronglyMeasurable (fun ω => (1 : ℝ) / α_star ω) (μ.restrict body) :=
          ((hαs_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self).aemeasurable.inv
            |>.aestronglyMeasurable).congr (ae_of_all _ fun ω => (one_div (α_star ω)).symm)
        exact (h_p1_sq_int_b.aestronglyMeasurable.mul
          ((hα_int t₀).mono_measure Measure.restrict_le_self |>.aestronglyMeasurable.add
            h_inv_meas))
      · apply (ae_restrict_mem hγ_level).mono; intro ω hω
        rw [Real.norm_eq_abs]
        have hp := (hα_inv ω t₀ (le_of_lt ht₀)).1
        have hl := (hα_inv ω t₀ (le_of_lt ht₀)).2
        have hαs_le1 : α_star ω ≤ 1 := le_of_lt (hα_star_lt ω)
        have hαs_lb : ds ≤ α_star ω := hds_lb ω hω
        have h_sq : (α ω t₀ - α_star ω) ^ 2 ≤ 1 := by nlinarith [hα_star_pos ω]
        have h_inv : 1 / α_star ω ≤ 1 / ds :=
          one_div_le_one_div_of_le hds hαs_lb
        have h_sum_nn : 0 ≤ α ω t₀ + 1 / α_star ω := by
          have : 0 < α_star ω := hα_star_pos ω
          positivity
        have h_sum_le : α ω t₀ + 1 / α_star ω ≤ 1 + 1 / ds := by linarith [le_of_lt hl, h_inv]
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) h_sum_nn)]
        nlinarith [mul_le_mul_of_nonneg_right h_sq h_sum_nn]
    -- S_b integrability: |(α-α*)*(1-α²)| ≤ 1
    have hs_int_b : Integrable (fun ω => (α ω t₀ - α_star ω) *
        (1 - (α ω t₀) ^ 2)) (μ.restrict body) := by
      apply Integrable.mono' (integrable_const 1 |>.mono_measure Measure.restrict_le_self)
      · exact (h_p_int_b.aestronglyMeasurable.mul
          (aestronglyMeasurable_const.sub
            ((hα_int t₀).aestronglyMeasurable.mono_measure Measure.restrict_le_self |>.pow 2)))
      · apply (ae_restrict_mem hγ_level).mono; intro ω _
        rw [Real.norm_eq_abs, abs_mul]
        have hp := (hα_inv ω t₀ (le_of_lt ht₀)).1
        have hl := (hα_inv ω t₀ (le_of_lt ht₀)).2
        have hαs_p := hα_star_pos ω; have hαs_l := hα_star_lt ω
        have h_diff_lo : -1 ≤ α ω t₀ - α_star ω := by linarith [le_of_lt hp, hαs_l]
        have h_diff_hi : α ω t₀ - α_star ω ≤ 1 := by linarith [le_of_lt hl, hαs_p]
        have h_1mα2_lo : -1 ≤ 1 - (α ω t₀) ^ 2 := by nlinarith [sq_nonneg (α ω t₀)]
        have h_1mα2_hi : 1 - (α ω t₀) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω t₀)]
        exact mul_le_one₀ (abs_le.mpr ⟨h_diff_lo, h_diff_hi⟩)
          (abs_nonneg _) (abs_le.mpr ⟨h_1mα2_lo, h_1mα2_hi⟩)
    -- Body integrals
    set Q_b := ∫ ω in body, (α ω t₀ - α_star ω) ^ 2 * (α ω t₀ + 1 / α_star ω) ∂μ
    set S_b := ∫ ω in body, (α ω t₀ - α_star ω) * (1 - (α ω t₀) ^ 2) ∂μ
    set rs_b := ∫ ω in body, α_star ω ∂μ
    set D_b := ∫ ω in body, (α ω t₀ - α_star ω) ∂μ
    set rs_t := ∫ ω in tail, α_star ω ∂μ
    set D_t := ∫ ω in tail, (α ω t₀ - α_star ω) ∂μ
    set D := r t₀ - r_star
    -- Per-ω identity
    have h_pw : ∀ ω, 2 * (α ω t₀ - α_star ω) * oaScalarRHS (γ ω) K r t₀ (α ω t₀) =
        (-K * r_star) * ((α ω t₀ - α_star ω) ^ 2 * (α ω t₀ + 1 / α_star ω)) +
        (K * D) * ((α ω t₀ - α_star ω) * (1 - (α ω t₀) ^ 2)) := fun ω => by
      have heq := hα_star_equil ω
      have hαs_ne : α_star ω ≠ 0 := ne_of_gt (hα_star_pos ω)
      simp only [oaScalarRHS, D]
      have hαs_pos := hα_star_pos ω
      field_simp [hαs_ne]
      linear_combination -2 * (α ω t₀ - α_star ω) * α ω t₀ * heq
    -- Body integral of derivative
    have h_body_eq : ∫ ω in body, 2 * (α ω t₀ - α_star ω) *
        oaScalarRHS (γ ω) K r t₀ (α ω t₀) ∂μ =
        (-K * r_star) * Q_b + (K * D) * S_b := by
      simp_rw [h_pw]
      rw [integral_add (hq_int_b.const_mul _) (hs_int_b.const_mul _),
        integral_const_mul, integral_const_mul]
    -- Inner integral identity for body×body pair
    have h_inner_eq : ∀ ω₁,
        ∫ ω₂ in body, pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂) ∂μ =
        (α_star ω₁ * Q_b - (α ω₁ t₀ - α_star ω₁) * S_b) +
        ((α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁) * rs_b -
         (α ω₁ t₀ - α_star ω₁) * (1 - α ω₁ t₀ ^ 2) * D_b) := fun ω₁ => by
      have h1 : Integrable (fun ω₂ =>
          α_star ω₁ * ((α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂)) -
          (α ω₁ t₀ - α_star ω₁) * ((α ω₂ t₀ - α_star ω₂) * (1 - α ω₂ t₀ ^ 2)))
          (μ.restrict body) := (hq_int_b.const_mul _).sub (hs_int_b.const_mul _)
      have h2 : Integrable (fun ω₂ =>
          α_star ω₂ * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁)) -
          (α ω₁ t₀ - α_star ω₁) * (1 - α ω₁ t₀ ^ 2) * (α ω₂ t₀ - α_star ω₂))
          (μ.restrict body) := (hαs_int_b.mul_const _).sub (h_p_int_b.const_mul _)
      rw [show (fun ω₂ => pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂)) =
          fun ω₂ => (α_star ω₁ * ((α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂)) -
            (α ω₁ t₀ - α_star ω₁) * ((α ω₂ t₀ - α_star ω₂) * (1 - α ω₂ t₀ ^ 2))) +
          (α_star ω₂ * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁)) -
           (α ω₁ t₀ - α_star ω₁) * (1 - α ω₁ t₀ ^ 2) * (α ω₂ t₀ - α_star ω₂)) from
        funext fun ω₂ => by unfold pairIntegrand; ring]
      rw [integral_add h1 h2]
      congr 1
      · rw [integral_sub (hq_int_b.const_mul _) (hs_int_b.const_mul _),
          integral_const_mul, integral_const_mul]
      · set c₁ := (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁)
        set c₂ := (α ω₁ t₀ - α_star ω₁) * (1 - α ω₁ t₀ ^ 2)
        simp_rw [show ∀ ω₂, α_star ω₂ * c₁ - c₂ * (α ω₂ t₀ - α_star ω₂) =
          c₁ * α_star ω₂ + (-c₂) * (α ω₂ t₀ - α_star ω₂) from fun _ => by ring]
        rw [integral_add (hαs_int_b.mul_const c₁ |>.congr (ae_of_all _ fun _ => by ring))
          (h_p_int_b.const_mul _), integral_const_mul, integral_const_mul]
        ring
    -- Outer integrability for body×body
    have h_outer_pair_b : Integrable
        (fun ω₁ => ∫ ω₂ in body, pairIntegrand (α ω₁ t₀) (α_star ω₁)
          (α ω₂ t₀) (α_star ω₂) ∂μ) (μ.restrict body) :=
      ((hαs_int_b.mul_const Q_b).sub (h_p_int_b.mul_const S_b)).add
        ((hq_int_b.mul_const rs_b).sub (hs_int_b.mul_const D_b)) |>.congr
        (ae_of_all _ fun ω₁ => (h_inner_eq ω₁).symm)
    -- Inner integrand integrability: pair on body
    have h_pair_inner_b : ∀ ω₁ ∈ body, Integrable
        (fun ω₂ => pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂))
        (μ.restrict body) := fun ω₁ hω₁ => by
      -- pairIntegrand = sum - difference, bounded by 4 + 2/ds on body
      apply Integrable.mono' (integrable_const (4 + 2/ds) |>.mono_measure Measure.restrict_le_self)
      · -- AEStronglyMeasurable: pairIntegrand is a combination of integrable functions
        have h_inv_meas : AEStronglyMeasurable (fun ω₂ => (1 : ℝ) / α_star ω₂)
            (μ.restrict body) :=
          ((hαs_int.aestronglyMeasurable.mono_measure (Measure.restrict_le_self (s := body))).aemeasurable.inv
            |>.aestronglyMeasurable).congr (ae_of_all _ fun ω => (one_div (α_star ω)).symm)
        have hα_meas : AEStronglyMeasurable (fun ω₂ => α ω₂ t₀) (μ.restrict body) :=
          (hα_int t₀).mono_measure (Measure.restrict_le_self (s := body)) |>.aestronglyMeasurable
        have hαs_meas : AEStronglyMeasurable (fun ω₂ => α_star ω₂) (μ.restrict body) :=
          hαs_int_b.aestronglyMeasurable
        have hp_meas : AEStronglyMeasurable (fun ω₂ => α ω₂ t₀ - α_star ω₂) (μ.restrict body) :=
          h_p_int_b.aestronglyMeasurable
        have hq_meas : AEStronglyMeasurable (fun ω₂ => (α ω₂ t₀ - α_star ω₂) ^ 2) (μ.restrict body) :=
          h_p1_sq_int_b.aestronglyMeasurable
        have hmeas1 : AEStronglyMeasurable
            (fun ω₂ => α_star ω₁ * (α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂))
            (μ.restrict body) :=
          (aestronglyMeasurable_const.mul hq_meas).mul (hα_meas.add h_inv_meas)
        have hmeas2 : AEStronglyMeasurable
            (fun ω₂ => α_star ω₂ * (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁))
            (μ.restrict body) :=
          (hαs_meas.mul aestronglyMeasurable_const).mul aestronglyMeasurable_const
        have hmeas3 : AEStronglyMeasurable
            (fun ω₂ => (α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂) * (2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2))
            (μ.restrict body) :=
          (aestronglyMeasurable_const.mul hp_meas).mul
            (aestronglyMeasurable_const.sub (hα_meas.pow 2))
        simp only [pairIntegrand]
        exact (hmeas1.add hmeas2).sub hmeas3
      · -- Norm bound: |pairIntegrand| ≤ 4 + 2/ds on body
        apply (ae_restrict_mem hγ_level).mono; intro ω₂ hω₂
        rw [Real.norm_eq_abs]
        have hp₂ := (hα_inv ω₂ t₀ (le_of_lt ht₀)).1
        have hl₂ := (hα_inv ω₂ t₀ (le_of_lt ht₀)).2
        have hp₁ := (hα_inv ω₁ t₀ (le_of_lt ht₀)).1
        have hl₁ := (hα_inv ω₁ t₀ (le_of_lt ht₀)).2
        have hαs₂_lb : ds ≤ α_star ω₂ := hds_lb ω₂ hω₂
        have hαs₁_lb : ds ≤ α_star ω₁ := hds_lb ω₁ hω₁
        have hαs₂_pos := hα_star_pos ω₂
        have hαs₁_pos := hα_star_pos ω₁
        have h_inv₂ : 1 / α_star ω₂ ≤ 1 / ds := one_div_le_one_div_of_le hds hαs₂_lb
        have h_inv₁ : 1 / α_star ω₁ ≤ 1 / ds := one_div_le_one_div_of_le hds hαs₁_lb
        have hα_star_lt₁ : α_star ω₁ < 1 := hα_star_lt ω₁
        have hα_star_lt₂ : α_star ω₂ < 1 := hα_star_lt ω₂
        have h_sq₁ : (α ω₁ t₀ - α_star ω₁) ^ 2 ≤ 1 := by nlinarith
        have h_sq₂ : (α ω₂ t₀ - α_star ω₂) ^ 2 ≤ 1 := by nlinarith
        have h_sum₁_nn : 0 ≤ α ω₁ t₀ + 1 / α_star ω₁ := by positivity
        have h_sum₂_nn : 0 ≤ α ω₂ t₀ + 1 / α_star ω₂ := by positivity
        have h_sum₁ : α ω₁ t₀ + 1 / α_star ω₁ ≤ 1 + 1 / ds := by linarith [le_of_lt hl₁]
        have h_sum₂ : α ω₂ t₀ + 1 / α_star ω₂ ≤ 1 + 1 / ds := by linarith [le_of_lt hl₂]
        -- Bound each term of pairIntegrand
        have h_sq₂_nn : 0 ≤ (α ω₂ t₀ - α_star ω₂) ^ 2 := sq_nonneg _
        have h_sq₁_nn : 0 ≤ (α ω₁ t₀ - α_star ω₁) ^ 2 := sq_nonneg _
        have hterm1_nn : 0 ≤ α_star ω₁ * (α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂) :=
          mul_nonneg (mul_nonneg (le_of_lt hαs₁_pos) h_sq₂_nn) h_sum₂_nn
        have hterm1_hi : α_star ω₁ * (α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂) ≤ 1 + 1 / ds := by
          nlinarith [mul_nonneg h_sq₂_nn h_sum₂_nn]
        have hterm2_nn : 0 ≤ α_star ω₂ * (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁) :=
          mul_nonneg (mul_nonneg (le_of_lt hαs₂_pos) h_sq₁_nn) h_sum₁_nn
        have hterm2_hi : α_star ω₂ * (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁) ≤ 1 + 1 / ds := by
          nlinarith [mul_nonneg h_sq₁_nn h_sum₁_nn]
        have hterm3_abs : |(α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂) * (2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2)| ≤ 2 := by
          have h3 : |α ω₁ t₀ - α_star ω₁| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          have h4 : |α ω₂ t₀ - α_star ω₂| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          have hα₁_sq_le1 : α ω₁ t₀ ^ 2 ≤ 1 :=
            pow_le_one₀ (le_of_lt hp₁) (le_of_lt hl₁)
          have hα₂_sq_le1 : α ω₂ t₀ ^ 2 ≤ 1 :=
            pow_le_one₀ (le_of_lt hp₂) (le_of_lt hl₂)
          have h5hi : 2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2 ≤ 2 := by linarith [sq_nonneg (α ω₁ t₀), sq_nonneg (α ω₂ t₀)]
          have h5lo : -2 ≤ 2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2 := by linarith
          have h5 : |2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2| ≤ 2 := abs_le.mpr ⟨h5lo, h5hi⟩
          calc |(α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂) * (2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2)|
              ≤ |(α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂)| * 2 := by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
            _ ≤ (1 * 1) * 2 := by
                apply mul_le_mul_of_nonneg_right _ (by norm_num)
                rw [abs_mul]; linarith [mul_le_one₀ h3 (abs_nonneg _) h4]
            _ = 2 := by ring
        have hterm3_lo := (abs_le.mp hterm3_abs).1
        have hterm3_hi := (abs_le.mp hterm3_abs).2
        have h1ds_pos : 0 < 1 / ds := div_pos one_pos hds
        have h2ds_eq : 2 / ds = 1 / ds + 1 / ds := by ring
        have hgoal : |pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂)| ≤ 4 + 2 / ds := by
          have hval : pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂) =
              α_star ω₁ * (α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂) +
              α_star ω₂ * (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁) -
              (α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂) * (2 - α ω₁ t₀ ^ 2 - α ω₂ t₀ ^ 2) :=
            rfl
          rw [hval, abs_le]
          constructor
          · linarith [hterm1_nn, hterm2_nn, hterm3_hi, h1ds_pos]
          · linarith [hterm1_hi, hterm2_hi, hterm3_lo, h2ds_eq]
        linarith [hgoal]
    -- Lower bound integrability
    have h_lb_inner_b : ∀ ω₁, Integrable
        (fun ω₂ => δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 + (α ω₂ t₀ - α_star ω₂) ^ 2))
        (μ.restrict body) := fun ω₁ =>
      ((integrable_const _).add h_p1_sq_int_b).const_mul _
    -- For each ω₁ ∈ body: inner integral ≥ δ*ds*(p₁²*μ(body) + V_body)
    have h_inner_lb : ∀ ω₁ ∈ body,
        δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀) ≤
        ∫ ω₂ in body, pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂) ∂μ := by
      intro ω₁ hω₁
      have h_rhs : ∫ ω₂ in body,
          δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 + (α ω₂ t₀ - α_star ω₂) ^ 2) ∂μ =
          δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀) := by
        simp_rw [show ∀ ω₂, δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 + (α ω₂ t₀ - α_star ω₂) ^ 2) =
            δ * ds * (α ω₁ t₀ - α_star ω₁) ^ 2 + δ * ds * (α ω₂ t₀ - α_star ω₂) ^ 2
          from fun _ => by ring]
        rw [integral_add ((integrable_const _).mono_measure Measure.restrict_le_self)
          (h_p1_sq_int_b.const_mul _), setIntegral_const, integral_const_mul]
        simp only [Measure.real, smul_eq_mul, V_body]; ring
      rw [← h_rhs]
      exact setIntegral_mono_on (h_lb_inner_b ω₁) (h_pair_inner_b ω₁ hω₁) hbody_meas
        (fun ω₂ hω₂ => pair_ge_delta_sq
          (hα_inv ω₁ t₀ (le_of_lt ht₀)).1 (hα_inv ω₂ t₀ (le_of_lt ht₀)).1
          (hα_inv ω₁ t₀ (le_of_lt ht₀)).2 (hα_inv ω₂ t₀ (le_of_lt ht₀)).2
          (hα_star_pos ω₁) (hα_star_pos ω₂) hδ
          (hα_lb ω₁ hω₁ t₀ (le_of_lt ht₀)) (hα_lb ω₂ hω₂ t₀ (le_of_lt ht₀))
          (hds_lb ω₁ hω₁) (hds_lb ω₂ hω₂))
    -- Outer lower bound integrability
    have h_outer_lb_b : Integrable
        (fun ω₁ => δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀))
        (μ.restrict body) := by
      have : (fun ω₁ => δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀)) =
          fun ω₁ => δ * ds * ((μ body).toReal * (α ω₁ t₀ - α_star ω₁) ^ 2 + V_body t₀) :=
        funext fun _ => by ring
      rw [this]
      exact ((h_p1_sq_int_b.const_mul _).add ((integrable_const _).mono_measure
        Measure.restrict_le_self)).const_mul _
    -- Body×body pair ≥ 2*δ*ds*μ(body)*V_body
    have h_body_body_lb :
        2 * δ * ds * (μ body).toReal * V_body t₀ ≤
        ∫ ω₁ in body, ∫ ω₂ in body, pairIntegrand (α ω₁ t₀) (α_star ω₁)
          (α ω₂ t₀) (α_star ω₂) ∂μ ∂μ := by
      have h_outer_mono :=
        setIntegral_mono_on h_outer_lb_b h_outer_pair_b hbody_meas h_inner_lb
      have h_lhs_eq :
          ∫ ω₁ in body, δ * ds *
            ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀) ∂μ =
          2 * δ * ds * (μ body).toReal * V_body t₀ := by
        simp_rw [show ∀ ω₁, δ * ds * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (μ body).toReal + V_body t₀) =
            δ * ds * (μ body).toReal * (α ω₁ t₀ - α_star ω₁) ^ 2 + δ * ds * V_body t₀
          from fun _ => by ring]
        rw [integral_add (h_p1_sq_int_b.const_mul _)
          ((integrable_const _).mono_measure Measure.restrict_le_self), setIntegral_const,
          integral_const_mul]
        simp only [Measure.real, smul_eq_mul, V_body]; ring
      linarith
    -- Body Fubini: ∫∫_body pair = 2*(rs_b*Q_b - D_b*S_b)
    -- pair_fubini_identity applied to μ.restrict body
    have h_out12_b : Integrable (fun ω₁ =>
        α_star ω₁ * Q_b - (α ω₁ t₀ - α_star ω₁) * S_b) (μ.restrict body) :=
      (hαs_int_b.mul_const Q_b).sub (h_p_int_b.mul_const S_b)
    have h_out21_b : Integrable (fun ω₁ =>
        (α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁) * rs_b -
        (α ω₁ t₀ - α_star ω₁) * (1 - α ω₁ t₀ ^ 2) * D_b) (μ.restrict body) :=
      (hq_int_b.mul_const rs_b).sub (hs_int_b.mul_const D_b)
    have h_fub := @pair_fubini_identity Ω _ (μ.restrict body)
      (fun ω => α ω t₀) α_star hq_int_b hs_int_b hαs_int_b h_p_int_b h_out12_b h_out21_b
    -- Convert h_fub to body double integral
    have h_pair_body_val :
        ∫ ω₁ in body, ∫ ω₂ in body, pairIntegrand (α ω₁ t₀) (α_star ω₁)
          (α ω₂ t₀) (α_star ω₂) ∂μ ∂μ =
        2 * (rs_b * Q_b - D_b * S_b) := by
      -- pairIntegrand = (sum of two asymmetric terms)
      simp_rw [show ∀ ω₁ ω₂, pairIntegrand (α ω₁ t₀) (α_star ω₁) (α ω₂ t₀) (α_star ω₂) =
          (α_star ω₁ * ((α ω₂ t₀ - α_star ω₂) ^ 2 * (α ω₂ t₀ + 1 / α_star ω₂)) -
            (α ω₁ t₀ - α_star ω₁) * ((α ω₂ t₀ - α_star ω₂) * (1 - α ω₂ t₀ ^ 2))) +
          (α_star ω₂ * ((α ω₁ t₀ - α_star ω₁) ^ 2 * (α ω₁ t₀ + 1 / α_star ω₁)) -
            (α ω₁ t₀ - α_star ω₁) * (α ω₂ t₀ - α_star ω₂) * (1 - α ω₁ t₀ ^ 2))
        from fun ω₁ ω₂ => by unfold pairIntegrand; ring]
      -- ∫ in body = ∫ ∂(μ.restrict body) by definition
      exact h_fub.trans (by simp only [Q_b, S_b, rs_b, D_b])
    -- Coercivity: rs_b*Q_b - D_b*S_b ≥ δ*ds*μ(body)*V_body
    have h_coer : δ * ds * (μ body).toReal * V_body t₀ ≤ rs_b * Q_b - D_b * S_b := by
      have h := h_body_body_lb
      rw [h_pair_body_val] at h; linarith
    -- Decompose r* = rs_b + rs_t
    have h_rs_split : r_star = rs_b + rs_t := by
      simp only [rs_b, rs_t]
      have : tail = bodyᶜ := by ext ω; simp [body, tail]
      rw [hr_star_eq, ← integral_add_compl hbody_meas hαs_int, this]
    -- Decompose D = D_b + D_t
    have h_D_split : D = D_b + D_t := by
      simp only [D, D_b, D_t]
      have htail_eq : tail = bodyᶜ := by ext ω; simp [body, tail]
      rw [show r t₀ - r_star = ∫ ω, (α ω t₀ - α_star ω) ∂μ by
        rw [h_sc t₀ (le_of_lt ht₀), hr_star_eq, ← integral_sub (hα_int t₀) hαs_int]]
      rw [← integral_add_compl hbody_meas h_p_int, htail_eq]
    -- Tail bound: rs_t ≥ 0
    have hrs_t_nn : 0 ≤ rs_t :=
      integral_nonneg fun ω => le_of_lt (hα_star_pos ω)
    -- Q_b ≥ 0
    have hQ_b_nn : 0 ≤ Q_b :=
      integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (by
        have := (hα_inv ω t₀ (le_of_lt ht₀)).1; have := hα_star_pos ω; positivity)
    -- |D_t| ≤ μ(tail).toReal
    have h_D_t_le : D_t ≤ (μ tail).toReal := by
      simp only [D_t]
      have htail_eq : tail = bodyᶜ := by ext ω; simp [body, tail]
      rw [htail_eq]
      calc ∫ ω in bodyᶜ, (α ω t₀ - α_star ω) ∂μ
          ≤ ∫ _ in bodyᶜ, (1 : ℝ) ∂μ :=
            setIntegral_mono_on h_p_int.integrableOn (integrable_const 1).integrableOn
              hbody_meas.compl (fun ω _ => by
                have := (hα_inv ω t₀ (le_of_lt ht₀)).1
                have := (hα_inv ω t₀ (le_of_lt ht₀)).2
                have := hα_star_pos ω
                linarith)
        _ = (μ bodyᶜ).toReal := by rw [setIntegral_const]; simp [Measure.real]
    have h_D_t_ge : -((μ tail).toReal) ≤ D_t := by
      simp only [D_t]
      have htail_eq : tail = bodyᶜ := by ext ω; simp [body, tail]
      rw [htail_eq]
      calc -(μ bodyᶜ).toReal = ∫ _ in bodyᶜ, (-1 : ℝ) ∂μ := by
              rw [setIntegral_const]; simp [Measure.real]
        _ ≤ ∫ ω in bodyᶜ, (α ω t₀ - α_star ω) ∂μ :=
            setIntegral_mono_on (integrable_const _).integrableOn
              h_p_int.integrableOn hbody_meas.compl (fun ω _ => by
                have := (hα_inv ω t₀ (le_of_lt ht₀)).1
                have := (hα_inv ω t₀ (le_of_lt ht₀)).2
                have := hα_star_lt ω
                linarith)
    -- |S_b| ≤ (μ body).toReal ≤ 1
    have hμ_body_le1 : (μ body).toReal ≤ 1 := by
      have : (μ body).toReal ≤ (μ univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))
      simpa [measure_univ] using this
    have h_S_pw : ∀ ω, -1 ≤ (α ω t₀ - α_star ω) * (1 - (α ω t₀) ^ 2) ∧
        (α ω t₀ - α_star ω) * (1 - (α ω t₀) ^ 2) ≤ 1 := fun ω =>
      s_integrand_abs_le_one (α ω t₀) (α_star ω)
        (hα_inv ω t₀ (le_of_lt ht₀)).1 (hα_inv ω t₀ (le_of_lt ht₀)).2
        (hα_star_pos ω) (hα_star_lt ω)
    have h_S_b_le : S_b ≤ (μ body).toReal := by
      calc S_b ≤ ∫ _ in body, (1 : ℝ) ∂μ :=
            setIntegral_mono_on hs_int_b (integrable_const 1).integrableOn hbody_meas
              (fun ω _ => (h_S_pw ω).2)
        _ = (μ body).toReal := by rw [setIntegral_const]; simp [Measure.real]
    have h_S_b_ge : -((μ body).toReal) ≤ S_b := by
      calc -((μ body).toReal) = ∫ _ in body, (-1 : ℝ) ∂μ := by
              rw [setIntegral_const]; simp [Measure.real]
        _ ≤ S_b :=
            setIntegral_mono_on (integrable_const _).integrableOn hs_int_b hbody_meas
              (fun ω _ => (h_S_pw ω).1)
    -- K*D_t*S_b ≤ K*μ(tail)
    have h_Dt_Sb : K * D_t * S_b ≤ K * (μ tail).toReal :=
      k_dt_sb_bound K D_t S_b (μ tail).toReal (μ body).toReal hK
        h_D_t_le h_D_t_ge h_S_b_le h_S_b_ge hμ_body_le1 ENNReal.toReal_nonneg
    -- Final bound: d/dt V_body ≤ -rate*V_body + K*μ(tail)
    have h_coer2 : δ * ds * (μ body).toReal * V_body t₀ ≤ rs_b * Q_b - D_b * S_b := by
      have h := h_body_body_lb
      rw [h_pair_body_val] at h; linarith
    rw [h_body_eq]
    calc (-K * r_star) * Q_b + K * D * S_b
        = -K * (rs_b * Q_b - D_b * S_b) + (-K * rs_t * Q_b + K * D_t * S_b) := by
          rw [h_rs_split, h_D_split]; ring
      _ ≤ -K * (δ * ds * (μ body).toReal * V_body t₀) +
            (0 + K * (μ tail).toReal) := by
          have h_rs_t_Q : -K * rs_t * Q_b ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hK)) hrs_t_nn) hQ_b_nn
          linarith [mul_le_mul_of_nonneg_left h_coer2 (le_of_lt hK)]
      _ = -(K * δ * ds * (μ body).toReal) * V_body t₀ + K * (μ tail).toReal := by ring
      _ = -rate * V_body t₀ + K * (μ tail).toReal := by simp only [rate]

end
