/-
  OA Scalar ODE — Global Existence via Clamped ODE
  =================================================
  Strategy: solve the clamped ODE (RHS evaluated at max(0,min(α,1))),
  which has globally bounded RHS; then barrier arguments show α ∈ (0,1),
  so clamped = original.
-/
import KuramotoLean.ContinuumODEExistence
import KuramotoLean.GeneralGODEInstance
import Mathlib.Analysis.ODE.Gronwall

open MeasureTheory Real Set Filter Topology Metric

noncomputable section

private def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

private lemma clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left 0 _
private lemma clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 :=
  max_le (by norm_num) (min_le_right x 1)
private lemma clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_left h1, max_eq_right h0]
private lemma clamp01_continuous : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

private lemma clamp01_abs_sub_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ |x - y| :=
  calc |max 0 (min x 1) - max 0 (min y 1)|
      ≤ |min x 1 - min y 1| := by
        rw [max_comm 0 (min x 1), max_comm 0 (min y 1)]
        exact abs_max_sub_max_le_abs _ _ 0
    _ ≤ max |x - y| |(1 : ℝ) - 1| := abs_min_sub_min_le_max x 1 y 1
    _ = |x - y| := by simp

private def oaRHS_c (γ K : ℝ) (r : ℝ → ℝ) (t x : ℝ) : ℝ :=
  oaScalarRHS γ K r t (clamp01 x)

private lemma oaRHS_c_eq_of_mem {γ K : ℝ} {r : ℝ → ℝ} {t x : ℝ}
    (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    oaRHS_c γ K r t x = oaScalarRHS γ K r t x := by
  unfold oaRHS_c; rw [clamp01_of_mem h0 h1]

/-! ## Upper barrier for clamped ODE -/

/-- At α = 1, clamped RHS = oaScalarRHS(t, 1) = -γ < 0. -/
theorem clamped_upper_barrier
    (γ K : ℝ) (r α : ℝ → ℝ) (hγ : 0 < γ) (hr_cont : Continuous r)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaRHS_c γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_init_lt : α 0 < 1) (t : ℝ) (ht : 0 ≤ t) : α t < 1 := by
  -- Follows scalar_oa_upper_barrier exactly, with oaRHS_c replacing oaScalarRHS.
  by_contra h_neg; push_neg at h_neg
  let S : Set ℝ := Ici (0 : ℝ) ∩ {s | 1 ≤ α s}
  have hS_ne : S.Nonempty := ⟨t, mem_Ici.mpr ht, h_neg⟩
  have hS_closed : IsClosed S :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Ici
      (isClosed_le continuous_const continuous_id)
  have hS_bdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  let t₀ : ℝ := sInf S
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_nn : 0 ≤ t₀ := ht₀_mem.1
  have hα_t₀_ge : 1 ≤ α t₀ := ht₀_mem.2
  have ht₀_pos : 0 < t₀ := by
    rcases ht₀_nn.lt_or_eq with h | h; · exact h
    · exfalso; rw [← h] at hα_t₀_ge; linarith
  have h_before : ∀ s, 0 ≤ s → s < t₀ → α s < 1 := fun s hs hst =>
    lt_of_not_ge fun hge => not_lt.mpr (csInf_le hS_bdd ⟨mem_Ici.mpr hs, hge⟩) hst
  have hα_t₀_eq : α t₀ = 1 := by
    apply le_antisymm _ hα_t₀_ge
    by_contra h_gt; push_neg at h_gt
    have hIVT : (1 : ℝ) ∈ α '' Icc 0 t₀ :=
      intermediate_value_Icc ht₀_nn (hα_cont.mono Icc_subset_Ici_self)
        ⟨le_of_lt hα_init_lt, le_of_lt h_gt⟩
    obtain ⟨s, hs_icc, hαs⟩ := hIVT
    have hs_lt : s < t₀ := by
      rcases hs_icc.2.lt_or_eq with h | h; · exact h
      · rw [h] at hαs; linarith
    linarith [h_before s hs_icc.1 hs_lt]
  -- At t₀: clamped RHS = -γ < 0
  have hode_neg : oaRHS_c γ K r t₀ (α t₀) < 0 := by
    rw [hα_t₀_eq]; unfold oaRHS_c; rw [clamp01_of_mem (by norm_num) le_rfl]
    unfold oaScalarRHS; nlinarith
  have hα_at : ContinuousAt α t₀ := hα_cont.continuousAt (Ici_mem_nhds ht₀_pos)
  have hode_cont : ContinuousAt (fun s => oaRHS_c γ K r s (α s)) t₀ := by
    have hc_at : ContinuousAt (fun s => clamp01 (α s)) t₀ :=
      clamp01_continuous.continuousAt.comp hα_at
    show ContinuousAt (fun s => oaScalarRHS γ K r s (clamp01 (α s))) t₀
    have heq : (fun s => oaScalarRHS γ K r s (clamp01 (α s))) =
        fun s => -γ * clamp01 (α s) + K / 2 * r s * (1 - clamp01 (α s) ^ 2) :=
      funext fun s => by unfold oaScalarRHS; ring
    simp only [heq]
    have hr_at : ContinuousAt r t₀ := hr_cont.continuousAt
    fun_prop
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp
    (hode_cont.eventually_lt continuousAt_const hode_neg)
  set a := max 0 (t₀ - δ / 2)
  have ha_nn : 0 ≤ a := le_max_left _ _
  have ha_lt : a < t₀ := max_lt ht₀_pos (by linarith)
  have ha_dist : ∀ s, a ≤ s → s ≤ t₀ → dist s t₀ < δ := by
    intro s hs1 hs2; rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith [le_max_right (0 : ℝ) (t₀ - δ / 2)]
  have h_anti : AntitoneOn α (Icc a t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a t₀)
      (hα_cont.mono (fun x hx => mem_Ici.mpr (le_trans ha_nn hx.1)))
    · rw [interior_Icc]; intro s hs
      exact (hα_ode s (lt_of_le_of_lt ha_nn hs.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s ⟨hs_lo, hs_hi⟩
      rw [(hα_ode s (lt_of_le_of_lt ha_nn hs_lo)).deriv]
      exact le_of_lt (hδ_ball (ha_dist s (le_of_lt hs_lo) (le_of_lt hs_hi)))
  have : α t₀ ≤ α a :=
    h_anti (left_mem_Icc.mpr ha_lt.le) (right_mem_Icc.mpr ha_lt.le) ha_lt.le
  linarith [h_before a ha_nn ha_lt]

/-! ## Lower barrier for clamped ODE -/

theorem clamped_lower_barrier
    (γ K : ℝ) (r α : ℝ → ℝ) (hγ : 0 < γ) (hK : 0 < K)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaRHS_c γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_init_pos : 0 < α 0) (hα_upper : ∀ t, 0 ≤ t → α t < 1)
    (t : ℝ) (ht : 0 ≤ t) : 0 < α t := by
  -- Follows scalar_oa_lower_barrier. On [0,tm] where tm = first zero,
  -- α ∈ [0,1) so clamped = original and Grönwall multiplier works.
  by_contra h_le; push_neg at h_le
  let S : Set ℝ := Ici (0 : ℝ) ∩ {s | α s ≤ 0}
  have hS_ne : S.Nonempty := ⟨t, mem_Ici.mpr ht, h_le⟩
  have hS_closed : IsClosed S :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Ici
      (isClosed_le continuous_id continuous_const)
  have hS_bdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  set tm := sInf S
  have htm_mem : tm ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have htm_nn : 0 ≤ tm := htm_mem.1
  have hα_tm_le : α tm ≤ 0 := htm_mem.2
  have htm_pos : 0 < tm := by
    rcases eq_or_lt_of_le htm_nn with h | h
    · exfalso; rw [← h] at hα_tm_le; linarith
    · exact h
  have h_pos_before : ∀ s, 0 ≤ s → s < tm → 0 < α s := by
    intro s hs hst
    by_contra hsj; push_neg at hsj
    exact absurd (csInf_le hS_bdd ⟨mem_Ici.mpr hs, hsj⟩) (not_le.mpr hst)
  have hα_tm_eq : α tm = 0 := by
    rcases eq_or_lt_of_le hα_tm_le with h | h
    · exact le_antisymm hα_tm_le (le_of_eq h.symm)
    · exfalso
      have hcont := hα_cont.mono (Icc_subset_Ici_self : Icc 0 tm ⊆ Ici 0)
      have h_img : (0 : ℝ) ∈ α '' Icc 0 tm :=
        intermediate_value_Icc' htm_nn hcont ⟨le_of_lt h, le_of_lt hα_init_pos⟩
      obtain ⟨s, hs, hαs⟩ := h_img
      have hs_icc := mem_Icc.mp hs
      have hs_lt : s < tm := by
        rcases eq_or_lt_of_le hs_icc.2 with heq | hlt
        · exfalso; rw [heq] at hαs; linarith
        · exact hlt
      exact absurd (h_pos_before s hs_icc.1 hs_lt) (not_lt.mpr (le_of_eq hαs))
  have h_nn : ∀ s, 0 ≤ s → s ≤ tm → 0 ≤ α s := by
    intro s hs hst
    rcases lt_or_eq_of_le hst with hlt | heq
    · exact le_of_lt (h_pos_before s hs hlt)
    · rw [heq]; linarith [hα_tm_eq]
  -- On (0, tm): α ∈ (0, 1), so clamped = original.
  -- HasDerivAt α (oaScalarRHS ...) for s ∈ (0, tm).
  have hα_orig : ∀ s, 0 < s → s < tm →
      HasDerivAt α (oaScalarRHS γ K r s (α s)) s := by
    intro s hs hst
    have h0 : 0 ≤ α s := h_nn s (le_of_lt hs) (le_of_lt hst)
    have h1 : α s < 1 := hα_upper s (le_of_lt hs)
    rw [← oaRHS_c_eq_of_mem h0 (le_of_lt h1)]
    exact hα_ode s hs
  -- Grönwall multiplier F(s) = α(s) · exp(γs)
  set F : ℝ → ℝ := fun s => α s * exp (γ * s) with hF_def
  have hF_cont : ContinuousOn F (Icc 0 tm) :=
    ((hα_cont.mono Icc_subset_Ici_self).mul
      (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  have hF_deriv : ∀ s, 0 < s → s < tm →
      HasDerivAt F ((K / 2) * r s * (1 - α s ^ 2) * exp (γ * s)) s := by
    intro s hs hst
    have hexp : HasDerivAt (fun u => exp (γ * u)) (γ * exp (γ * s)) s := by
      have := ((hasDerivAt_id s).const_mul γ).exp
      simp only [mul_one, Function.comp, id] at this
      convert this using 1; ring
    have h := (hα_orig s hs hst).mul hexp
    have heq : oaScalarRHS γ K r s (α s) * exp (γ * s) + α s * (γ * exp (γ * s)) =
        (K / 2) * r s * (1 - α s ^ 2) * exp (γ * s) := by
      unfold oaScalarRHS; ring
    rw [heq] at h; exact h
  have hF_mono : MonotoneOn F (Icc 0 tm) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 tm) hF_cont
    · rw [interior_Icc]; intro s hs
      exact (hF_deriv s hs.1 hs.2).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s ⟨hs_lo, hs_hi⟩
      rw [(hF_deriv s hs_lo hs_hi).deriv]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by linarith : (0 : ℝ) ≤ K / 2) (hr_nn s (le_of_lt hs_lo)))
          (by nlinarith [hα_upper s (le_of_lt hs_lo),
                          h_nn s (le_of_lt hs_lo) (le_of_lt hs_hi), sq_abs (α s)]))
        (exp_nonneg _)
  have hF0 : F 0 = α 0 := by simp [hF_def, mul_zero, exp_zero, mul_one]
  have hFtm : F tm = 0 := by simp [hF_def, hα_tm_eq, zero_mul]
  linarith [hF_mono (left_mem_Icc.mpr htm_nn) (right_mem_Icc.mpr htm_nn) htm_nn,
            hα_init_pos]

private lemma oaRHS_c_lipschitzOnWith (γ K : ℝ) (r : ℝ → ℝ) (t : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr_bdd : ∀ t, |r t| ≤ 1) :
    LipschitzOnWith ⟨γ + K, by positivity⟩ (oaRHS_c γ K r t) Set.univ := by
  rw [lipschitzOnWith_iff_dist_le_mul]; intro x _ y _
  simp only [Real.dist_eq]; unfold oaRHS_c; rw [oaScalar_diff, abs_mul]
  have h_lip := clamp01_abs_sub_le x y
  have hc₁ := clamp01_nonneg x; have hc₂ := clamp01_nonneg y
  have hc₁' := clamp01_le_one x; have hc₂' := clamp01_le_one y
  have hrt := hr_bdd t
  have hrt_hi := le_of_abs_le hrt; have hrt_lo := neg_le_of_abs_le hrt
  have hp1 : 0 ≤ K / 2 * ((1 - r t) * (clamp01 x + clamp01 y)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hp2 : 0 ≤ K / 2 * ((1 + r t) * (clamp01 x + clamp01 y)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hp3 : 0 ≤ K / 2 * (2 - (clamp01 x + clamp01 y)) :=
    mul_nonneg (by linarith) (by linarith)
  have hcoeff : |-γ - K / 2 * r t * (clamp01 x + clamp01 y)| ≤ γ + K := by
    rw [abs_le]; constructor <;> nlinarith
  calc |clamp01 x - clamp01 y| * |-γ - K / 2 * r t * (clamp01 x + clamp01 y)|
      ≤ |x - y| * (γ + K) := mul_le_mul h_lip hcoeff (abs_nonneg _) (abs_nonneg _)
    _ = (γ + K) * |x - y| := mul_comm _ _

private lemma clamp01_sq_le (x : ℝ) : clamp01 x ^ 2 ≤ 1 := by
  have h := clamp01_le_one x; have h' := clamp01_nonneg x; nlinarith [sq_nonneg (1 - clamp01 x)]

/-! ## Clamped PL: local existence on any interval -/

private lemma clamped_picard (γ K : ℝ) (r : ℝ → ℝ) (α₀ : ℝ) (N : ℕ)
    (hγ : 0 < γ) (hK : 0 < K) (hr : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1) :
    ∃ α : ℝ → ℝ, α 0 = α₀ ∧
      ∀ t ∈ Icc (-(↑N + 1 : ℝ)) (↑N + 1 : ℝ),
        HasDerivWithinAt α (oaRHS_c γ K r t (α t))
          (Icc (-(↑N + 1 : ℝ)) (↑N + 1 : ℝ)) t := by
  -- The clamped ODE has bounded and Lipschitz RHS → Picard-Lindelöf on any interval.
  set T := (↑N + 1 : ℝ)
  have hT : 0 < T := by positivity
  set L_c : NNReal := ⟨γ + K / 2, by positivity⟩
  set K_c : NNReal := ⟨γ + K, by positivity⟩
  set ball_r : NNReal := ⟨(γ + K / 2) * T + |α₀| + 1, by positivity⟩
  have ht_mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
  have hpl : IsPicardLindelof (oaRHS_c γ K r) ⟨0, ht_mem⟩ α₀ ball_r 0 L_c K_c := by
    constructor
    · -- lipschitzOnWith: clamped RHS is (γ+K)-Lipschitz on any ball
      intro t _; rw [lipschitzOnWith_iff_dist_le_mul]; intro x _ y _
      simp only [Real.dist_eq]; unfold oaRHS_c; rw [oaScalar_diff, abs_mul]
      have hc₁ := clamp01_nonneg x; have hc₂ := clamp01_nonneg y
      have hc₁' := clamp01_le_one x; have hc₂' := clamp01_le_one y
      have hrt := hr_bdd t
      have h_lip := clamp01_abs_sub_le x y
      have hrt_hi := le_of_abs_le hrt; have hrt_lo := neg_le_of_abs_le hrt
      have hp1 : 0 ≤ K / 2 * ((1 - r t) * (clamp01 x + clamp01 y)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
      have hp2 : 0 ≤ K / 2 * ((1 + r t) * (clamp01 x + clamp01 y)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
      have hp3 : 0 ≤ K / 2 * (2 - (clamp01 x + clamp01 y)) :=
        mul_nonneg (by linarith) (by linarith)
      have hcoeff : |-γ - K / 2 * r t * (clamp01 x + clamp01 y)| ≤ γ + K := by
        rw [abs_le]; constructor <;> nlinarith
      calc |clamp01 x - clamp01 y| * |-γ - K / 2 * r t * (clamp01 x + clamp01 y)|
          ≤ |x - y| * (γ + K) := mul_le_mul h_lip hcoeff (abs_nonneg _) (abs_nonneg _)
        _ = (γ + K) * |x - y| := mul_comm _ _
    · -- continuousOn: continuous in t for fixed x
      intro x _; unfold oaRHS_c oaScalarRHS; fun_prop
    · -- norm_le: |RHS| ≤ γ+K/2 (bounded since clamp ∈ [0,1])
      intro t _ x _; rw [Real.norm_eq_abs]; unfold oaRHS_c oaScalarRHS
      change |-γ * clamp01 x + K / 2 * r t * (1 - clamp01 x ^ 2)| ≤ γ + K / 2
      have hc := clamp01_nonneg x; have hc' := clamp01_le_one x
      have hcs := clamp01_sq_le x
      have hrt_hi := le_of_abs_le (hr_bdd t); have hrt_lo := neg_le_of_abs_le (hr_bdd t)
      have hp1 : 0 ≤ K / 2 * ((1 + r t) * (1 - clamp01 x ^ 2)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by nlinarith))
      have hp2 : 0 ≤ K / 2 * ((1 - r t) * (1 - clamp01 x ^ 2)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by nlinarith))
      have hp3 : 0 ≤ γ * (1 - clamp01 x) := mul_nonneg (by linarith) (by linarith)
      have hp4 : 0 ≤ γ * clamp01 x := mul_nonneg (by linarith) hc
      rw [abs_le]; constructor <;> nlinarith
    · -- mul_max_le: ball large enough for time interval
      change (γ + K / 2) * max (T - 0) (0 - -T) ≤
        ((γ + K / 2) * T + |α₀| + 1) - 0
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      linarith [abs_nonneg α₀]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-! ## Main: oa_solve_global from clamped ODE -/

/-- Global existence for the OA scalar ODE with invariant region (0,1). -/
theorem oa_solve_global_v2
    (γ K : ℝ) (r : ℝ → ℝ) (α₀ : ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1) :
    ∃ α : ℝ → ℝ,
      α 0 = α₀ ∧
      (∀ t ≥ 0, HasDerivAt α (oaScalarRHS γ K r t (α t)) t) ∧
      ContinuousOn α (Ici 0) ∧
      (∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) := by
  -- Step 1: Global clamped solution
  have ⟨α, hα_init, hα_ode_c, hα_ode_c_zero, hα_cont⟩ :
      ∃ α : ℝ → ℝ, α 0 = α₀ ∧
        (∀ t, 0 < t → HasDerivAt α (oaRHS_c γ K r t (α t)) t) ∧
        HasDerivAt α (oaRHS_c γ K r 0 (α 0)) 0 ∧
        ContinuousOn α (Ici 0) := by
    -- Use clamped_picard for each N, show solutions agree, define global solution
    choose αN hαN_init hαN_deriv using
      fun N => clamped_picard γ K r α₀ N hγ hK hr hr_bdd
    -- All solutions agree on [-(N+1), N+1] by ODE uniqueness (Gronwall)
    have hagree : ∀ N M : ℕ, N ≤ M →
        EqOn (αN N) (αN M) (Icc (-(↑N + 1 : ℝ)) (↑N + 1)) := by
      intro N M hNM
      have hNM' : (↑N : ℝ) ≤ ↑M := Nat.cast_le.mpr hNM
      have hT_N : (0:ℝ) < ↑N + 1 := by positivity
      have hcN : ContinuousOn (αN N) (Icc (-(↑N + 1 : ℝ)) (↑N + 1)) :=
        fun t ht => (hαN_deriv N t ht).continuousWithinAt
      have hcM : ContinuousOn (αN M) (Icc (-(↑N + 1 : ℝ)) (↑N + 1)) := by
        intro t ht
        exact ((hαN_deriv M t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousWithinAt).mono
          (Icc_subset_Icc (by linarith) (by linarith))
      have hdN : ∀ t ∈ Ioo (-(↑N + 1 : ℝ)) (↑N + 1),
          HasDerivAt (αN N) (oaRHS_c γ K r t (αN N t)) t :=
        fun t ht => (hαN_deriv N t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      have hdM : ∀ t ∈ Ioo (-(↑N + 1 : ℝ)) (↑N + 1),
          HasDerivAt (αN M) (oaRHS_c γ K r t (αN M t)) t := by
        intro t ht
        exact (hαN_deriv M t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
          (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
      exact ODE_solution_unique_of_mem_Icc
        (v := fun t x => oaRHS_c γ K r t x) (s := fun _ => Set.univ)
        (fun t _ => oaRHS_c_lipschitzOnWith γ K r t hγ hK hr_bdd)
        ⟨by linarith, hT_N⟩ hcN hdN (fun _ _ => trivial)
        hcM hdM (fun _ _ => trivial) ((hαN_init N).trans (hαN_init M).symm)
    -- α agrees with αN N when -1 ≤ t ≤ N+1
    have hα_eq : ∀ (N : ℕ) (t : ℝ), -1 ≤ t → t ≤ ↑N + 1 →
        (fun t => αN (Nat.ceil (max t 0)) t) t = αN N t := by
      intro N t ht_lo ht_hi
      set M := Nat.ceil (max t 0) with hM_def
      have hM_ge : max t 0 ≤ ↑M := Nat.le_ceil _
      have hM_nn : (0:ℝ) ≤ ↑M := Nat.cast_nonneg M
      have ht_M_lo : -(↑M + 1 : ℝ) ≤ t := by
        rcases le_or_gt 0 t with h | h
        · linarith
        · have : max t 0 = 0 := max_eq_right h.le
          have : M = 0 := by rw [hM_def, this]; simp
          simp [this]; linarith
      have ht_M_hi : t ≤ ↑M + 1 := le_trans (le_max_left t 0) (le_trans hM_ge (by linarith))
      rcases le_total M N with hMN | hNM
      · exact hagree M N hMN ⟨ht_M_lo, ht_M_hi⟩
      · have hN_nn : (-(↑N + 1 : ℝ)) ≤ t := by
          have : (0:ℝ) ≤ ↑N := Nat.cast_nonneg N; linarith
        exact (hagree N M hNM ⟨hN_nn, ht_hi⟩).symm
    set α : ℝ → ℝ := fun t => αN (Nat.ceil (max t 0)) t
    -- Helper: derive HasDerivAt from PL + local agreement
    have hα_deriv_at : ∀ (N : ℕ) (t : ℝ),
        t ∈ Ioo (-(1 : ℝ)) (↑N + 1) →
        HasDerivAt α (oaRHS_c γ K r t (α t)) t := by
      intro N t ht
      have hN_nn : (0:ℝ) ≤ ↑N := Nat.cast_nonneg N
      have ht_mem : t ∈ Icc (-(↑N + 1 : ℝ)) (↑N + 1) :=
        ⟨by linarith [ht.1], le_of_lt ht.2⟩
      have ht_int : t ∈ Ioo (-(↑N + 1 : ℝ)) (↑N + 1) :=
        ⟨by linarith [ht.1], ht.2⟩
      have hder : HasDerivAt (αN N) (oaRHS_c γ K r t (αN N t)) t :=
        (hαN_deriv N t ht_mem).hasDerivAt (Icc_mem_nhds ht_int.1 ht_int.2)
      have hα_local : α =ᶠ[nhds t] αN N := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        exact ⟨Ioo (-1 : ℝ) (↑N + 1), Ioo_mem_nhds ht.1 ht.2,
          fun t' ht' => hα_eq N t' (by linarith [ht'.1]) (le_of_lt ht'.2)⟩
      have hα_t : α t = αN N t := hα_eq N t (by linarith [ht.1]) (le_of_lt ht.2)
      rw [hα_t]; exact hder.congr_of_eventuallyEq hα_local
    refine ⟨α, ?_, ?_, ?_, ?_⟩
    · -- α 0 = α₀
      show αN (Nat.ceil (max (0:ℝ) 0)) 0 = α₀
      simp [hαN_init]
    · -- HasDerivAt at t > 0
      intro t ht
      let N := Nat.ceil t + 1
      have hN_bound : t < ↑N + 1 := by
        change t < ↑(Nat.ceil t + 1) + 1; push_cast; linarith [Nat.le_ceil t]
      exact hα_deriv_at N t ⟨by linarith, hN_bound⟩
    · -- HasDerivAt at 0
      exact hα_deriv_at 0 0 ⟨by norm_num, by norm_num⟩
    · -- ContinuousOn
      intro t ht; rw [mem_Ici] at ht
      rcases eq_or_lt_of_le ht with rfl | ht'
      · exact (hα_deriv_at 0 0 ⟨by norm_num, by norm_num⟩).continuousAt.continuousWithinAt
      · let N := Nat.ceil t + 1
        have hN_bound : t < ↑N + 1 := by
          change t < ↑(Nat.ceil t + 1) + 1; push_cast; linarith [Nat.le_ceil t]
        exact (hα_deriv_at N t ⟨by linarith, hN_bound⟩).continuousAt.continuousWithinAt
  -- Step 2: α ∈ (0, 1) via clamped barriers
  have hα_lt_one : ∀ t, 0 ≤ t → α t < 1 :=
    clamped_upper_barrier γ K r α hγ hr hα_ode_c hα_cont (by rw [hα_init]; exact hα₀_lt)
  have hα_pos : ∀ t, 0 ≤ t → 0 < α t :=
    clamped_lower_barrier γ K r α hγ hK hr_nn hα_ode_c hα_cont
      (by rw [hα_init]; exact hα₀_pos) hα_lt_one
  -- Step 3: Clamped = Original on [0,∞) since α ∈ (0,1) ⊂ [0,1]
  have hα_ode_orig : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t := by
    intro t ht
    rw [← oaRHS_c_eq_of_mem (le_of_lt (hα_pos t (le_of_lt ht)))
        (le_of_lt (hα_lt_one t (le_of_lt ht)))]
    exact hα_ode_c t ht
  have hα_ode_zero : HasDerivAt α (oaScalarRHS γ K r 0 (α 0)) 0 := by
    rw [← oaRHS_c_eq_of_mem (by rw [hα_init]; linarith) (by rw [hα_init]; linarith)]
    exact hα_ode_c_zero
  exact ⟨α, hα_init,
    fun t ht => by rcases eq_or_lt_of_le ht with h | h
                   · rw [← h]; exact hα_ode_zero
                   · exact hα_ode_orig t h,
    hα_cont, fun t ht => ⟨hα_pos t ht, hα_lt_one t ht⟩⟩

end
