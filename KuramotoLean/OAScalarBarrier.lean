/-
  OAScalarBarrier.lean
  ====================
  The interval (0,1) is positively invariant for the per-ω OA scalar ODE:

      dα/dt = oaScalarRHS γ K r t α = -γ·α + (K/2)·r(t)·(1-α²)

  with r(t) ∈ [0,1] and γ,K > 0.

  UPPER BARRIER: α(t) < 1 for all t ≥ 0 if α(0) < 1.
    At α=1: RHS = -γ < 0. sInf argument: first crossing time t₀ gives α'(t₀) < 0
    near t₀, making α strictly decreasing into [a, t₀], contradicting α(a) < 1 < α(t₀).

  LOWER BARRIER: α(t) > 0 for all t ≥ 0 if α(0) > 0.
    Let gm(t) = α(t)·exp(γt). Then
      gm'(t) = (K/2)·r(t)·(1-α(t)²)·exp(γt) ≥ 0 on [0, t_m)
    where t_m = first zero and α ∈ (0,1) there (from upper_barrier).
    gm(0) > 0 and monotone → gm(t_m) ≥ gm(0) > 0 → α(t_m) > 0 → contradiction.

  Adapts InvariantBox.lean (n-pole case) to the scalar per-ω ODE.

  0 sorry.
-/

import KuramotoLean.ContinuumODEExistence

open MeasureTheory Real Set Filter Topology

noncomputable section

/-! ## Upper barrier: α(t) < 1 -/

/-- **Upper barrier**: if α(0) < 1 and r(t) ≤ 1 for t ≥ 0, then α(t) < 1 for all t ≥ 0.
    The ODE satisfies oaScalarRHS γ K r t 1 = -γ < 0 (the vector field points inward at α=1).
    At the first crossing time t₀ > 0 (from sInf), α is strictly decreasing into t₀ on some
    interval (a, t₀), contradicting α(a) < 1 = α(t₀). -/
theorem oaScalar_upper_barrier
    (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ)
    (hγ : 0 < γ)
    (hr_cont : ContinuousOn r (Ici 0))
    (hr_le : ∀ t, 0 ≤ t → r t ≤ 1)
    (hα₀_lt : α 0 < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    α t < 1 := by
  by_contra h_neg
  push_neg at h_neg
  -- S = {s ≥ 0 : α(s) ≥ 1}
  let S : Set ℝ := Ici (0 : ℝ) ∩ {s | 1 ≤ α s}
  have hS_ne : S.Nonempty := ⟨t, mem_Ici.mpr ht, h_neg⟩
  have hS_closed : IsClosed S :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_le continuous_const continuous_id)
  have hS_bdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  let t₀ := sInf S
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_nn : 0 ≤ t₀ := ht₀_mem.1
  have hα_ge : 1 ≤ α t₀ := ht₀_mem.2
  -- t₀ > 0 since α(0) < 1
  have ht₀_pos : 0 < t₀ := by
    rcases ht₀_nn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hα_ge; linarith
  -- α(s) < 1 strictly for s ∈ [0, t₀)
  have h_before : ∀ s, 0 ≤ s → s < t₀ → α s < 1 := fun s hs hst =>
    lt_of_not_ge fun hge =>
      not_lt.mpr (csInf_le hS_bdd ⟨mem_Ici.mpr hs, hge⟩) hst
  -- α(t₀) = 1 exactly (IVT: value 1 is hit on [0, t₀])
  have hα_eq : α t₀ = 1 := by
    apply le_antisymm _ hα_ge
    by_contra h_gt; push_neg at h_gt
    obtain ⟨s, hs_icc, hαs⟩ := intermediate_value_Icc ht₀_nn (hα_cont.mono Icc_subset_Ici_self)
      ⟨le_of_lt hα₀_lt, le_of_lt h_gt⟩
    exact absurd (h_before s hs_icc.1 (hs_icc.2.lt_of_ne (fun h => by rw [h] at hαs; linarith)))
      (not_lt.mpr hαs.symm.le)
  -- ODE derivative at t₀: oaScalarRHS γ K r t₀ 1 = -γ < 0
  have hode_neg : oaScalarRHS γ K r t₀ (α t₀) < 0 := by
    unfold oaScalarRHS; rw [hα_eq]; nlinarith [hr_le t₀ ht₀_nn]
  -- Continuity of the ODE composition at t₀
  have hode_cont : ContinuousAt (fun s => oaScalarRHS γ K r s (α s)) t₀ := by
    have hα_at : ContinuousAt α t₀ := hα_cont.continuousAt (Ici_mem_nhds ht₀_pos)
    have hr_at : ContinuousAt r t₀ := hr_cont.continuousAt (Ici_mem_nhds ht₀_pos)
    simp only [oaScalarRHS]
    fun_prop
  -- By continuity: ∃ δ > 0 with ODE < 0 on ball t₀ δ
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp
    (hode_cont.eventually_lt continuousAt_const hode_neg)
  -- On (a, t₀) ⊆ ball t₀ δ, the derivative is negative
  set a := max 0 (t₀ - δ / 2) with ha_def
  have ha_nn : 0 ≤ a := le_max_left _ _
  have ha_lt : a < t₀ := max_lt ht₀_pos (by linarith)
  have hderiv_neg : ∀ s ∈ interior (Icc a t₀), deriv α s < 0 := by
    rw [interior_Icc]
    intro s ⟨hs_lo, hs_hi⟩
    rw [(hα_ode s (lt_of_le_of_lt ha_nn hs_lo)).deriv]
    apply hδ_ball
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [le_max_right 0 (t₀ - δ/2), ha_def ▸ hs_lo], by linarith⟩
  -- α is strictly decreasing on [a, t₀]
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc a t₀)
    (hα_cont.mono fun s hs => mem_Ici.mpr (le_trans ha_nn hs.1))
    hderiv_neg
  -- α(a) > α(t₀) = 1 but α(a) < 1 — contradiction
  linarith [hanti (left_mem_Icc.mpr (le_of_lt ha_lt)) (right_mem_Icc.mpr (le_of_lt ha_lt)) ha_lt,
            h_before a ha_nn ha_lt, hα_eq]

/-! ## Lower barrier: α(t) > 0 -/

private def gm (γ : ℝ) (α : ℝ → ℝ) (t : ℝ) : ℝ := α t * Real.exp (γ * t)

private theorem gm_cont (γ : ℝ) (α : ℝ → ℝ) (hα_cont : ContinuousOn α (Ici 0)) :
    ContinuousOn (gm γ α) (Ici 0) :=
  hα_cont.mul (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

private theorem gm_hasDerivAt (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (gm γ α) ((K / 2) * r t * (1 - α t ^ 2) * Real.exp (γ * t)) t := by
  have hexp : HasDerivAt (fun u => Real.exp (γ * u)) (γ * Real.exp (γ * t)) t := by
    have h := ((hasDerivAt_id t).const_mul γ).exp
    simp only [mul_one] at h; rwa [mul_comm] at h
  have hderiv := (hα_ode t ht).mul hexp
  have hgm : gm γ α = fun u => α u * Real.exp (γ * u) := rfl
  rw [hgm]; convert hderiv using 1
  unfold oaScalarRHS; ring

/-- **Lower barrier**: if α(0) > 0, r(t) ∈ [0,1] for t ≥ 0, and α satisfies the OA scalar ODE,
    and α(t) < 1 for all t ≥ 0 (from upper_barrier), then α(t) > 0 for all t ≥ 0.
    Proof: Grönwall multiplier gm(t) = α(t)·exp(γt) has gm' = (K/2)·r·(1-α²)·exp(γt) ≥ 0
    on [0, t_m) (the first zero of α), so gm is monotone ≥ gm(0) > 0, contradicting gm(t_m) = 0. -/
theorem oaScalar_lower_barrier
    (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα₀_pos : 0 < α 0)
    (hα_lt : ∀ t, 0 ≤ t → α t < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < α t := by
  by_contra h_neg
  push_neg at h_neg
  -- S₀ = {s ≥ 0 : α(s) ≤ 0}
  let S₀ : Set ℝ := Ici (0 : ℝ) ∩ {s | α s ≤ 0}
  have hS₀_ne : S₀.Nonempty := ⟨t, mem_Ici.mpr ht, h_neg⟩
  have hS₀_closed : IsClosed S₀ :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_le continuous_id continuous_const)
  have hS₀_bdd : BddBelow S₀ := ⟨0, fun s hs => hs.1⟩
  let tm := sInf S₀
  have htm_mem : tm ∈ S₀ := hS₀_closed.csInf_mem hS₀_ne hS₀_bdd
  have htm_nn : 0 ≤ tm := htm_mem.1
  have hα_le : α tm ≤ 0 := htm_mem.2
  -- tm > 0 since α(0) > 0
  have htm_pos : 0 < tm := by
    rcases htm_nn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hα_le; linarith
  -- α(s) > 0 strictly for s ∈ [0, tm)
  have h_pos_before : ∀ s, 0 ≤ s → s < tm → 0 < α s := fun s hs hst =>
    lt_of_not_ge fun hge =>
      not_lt.mpr (csInf_le hS₀_bdd ⟨mem_Ici.mpr hs, hge⟩) hst
  -- α(tm) = 0 exactly (IVT: value 0 is hit on [0, tm])
  have hα_zero : α tm = 0 := by
    apply le_antisymm hα_le
    by_contra h_neg'; push_neg at h_neg'
    obtain ⟨s, hs_icc, hαs⟩ := intermediate_value_Icc' htm_nn (hα_cont.mono Icc_subset_Ici_self)
      ⟨le_of_lt h_neg', le_of_lt hα₀_pos⟩
    exact absurd (h_pos_before s hs_icc.1 (hs_icc.2.lt_of_ne (fun h => by rw [h] at hαs; linarith)))
      (not_lt.mpr (le_of_eq hαs))
  -- gm(t) = α(t)·exp(γt) is monotone nondecreasing on [0, tm]
  -- because gm'(t) = (K/2)·r(t)·(1-α(t)²)·exp(γt) ≥ 0
  -- (r ≥ 0, 1-α² ≥ 0 since α ∈ (0,1) on (0,tm), exp > 0)
  have hgm_mono : MonotoneOn (gm γ α) (Icc 0 tm) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 tm)
      ((gm_cont γ α hα_cont).mono Icc_subset_Ici_self)
    · rw [interior_Icc]; intro s hs
      exact (gm_hasDerivAt γ K r α hα_ode s hs.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s ⟨hs_lo, hs_hi⟩
      rw [(gm_hasDerivAt γ K r α hα_ode s hs_lo).deriv]
      have hαs_pos : 0 < α s := h_pos_before s (le_of_lt hs_lo) hs_hi
      have hαs_lt : α s < 1 := hα_lt s (le_of_lt hs_lo)
      have hr_s : 0 ≤ r s := hr_nn s (le_of_lt hs_lo)
      have h1 : 0 ≤ 1 - α s ^ 2 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - α s) (by linarith : 0 ≤ 1 + α s)]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hr_s) h1) (Real.exp_nonneg _)
  -- gm(0) = α(0) > 0 but gm(tm) = α(tm)·exp(γ·tm) = 0 contradicts monotonicity
  have hgm_0 : gm γ α 0 = α 0 := by simp [gm]
  have hgm_tm : gm γ α tm = 0 := by simp [gm, hα_zero]
  linarith [hgm_mono (left_mem_Icc.mpr htm_nn) (right_mem_Icc.mpr htm_nn) htm_nn,
            hα₀_pos, hgm_0, hgm_tm]

/-! ## Combined invariant box -/

/-- **Invariant box**: if α(0) ∈ (0,1), r(t) ∈ [0,1], γ,K > 0, and α satisfies the OA scalar ODE,
    then α(t) ∈ (0,1) for all t ≥ 0. -/
theorem oaScalar_invariant_box
    (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr_cont : ContinuousOn r (Ici 0))
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hr_le : ∀ t, 0 ≤ t → r t ≤ 1)
    (hα₀_pos : 0 < α 0) (hα₀_lt : α 0 < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < α t ∧ α t < 1 := by
  have h_upper : ∀ s, 0 ≤ s → α s < 1 :=
    fun s hs => oaScalar_upper_barrier γ K r α hγ hr_cont hr_le hα₀_lt hα_cont hα_ode s hs
  exact ⟨oaScalar_lower_barrier γ K r α hγ hK hr_nn hα₀_pos h_upper hα_cont hα_ode t ht,
         h_upper t ht⟩

end
