/-
  Kuramoto Stability - Invariant Box (0,1)^n
  ============================================
  Proves the positive invariance of (0,1)^n for the n-pole OA ODE.
  Eliminates hα_nn and hα_le from NPoleBarrierData.

  Upper barrier (α < 1): at α_k = 1, ODE = -γ_k < 0 independently of r.
  Lower barrier (α > 0): Grönwall multiplier on [0, t₀) bootstrap.

  Status: upper barrier proved, lower barrier in progress.
-/

import KuramotoLean.GlobalStabilitySupercritical
import KuramotoLean.CriticalConvergence
import Mathlib.Topology.Order.IntermediateValue

open Real Set Finset Filter Topology

noncomputable section

variable {n : ℕ}

structure NPoleODEData (n : ℕ) where
  γ : Fin n → ℝ
  c : Fin n → ℝ
  K : ℝ
  α : ℝ → Fin n → ℝ
  hK : 0 < K
  hγ : ∀ k, 0 < γ k
  hc : ∀ k, 0 < c k
  hα_ode : ∀ t, 0 < t → ∀ k,
    HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t
  hα_cont : ∀ k, ContinuousOn (fun t => α t k) (Ici 0)
  hα_init_pos : ∀ k, 0 < α 0 k
  hα_init_lt : ∀ k, α 0 k < 1

theorem upper_barrier (D : NPoleODEData n) (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    D.α t k < 1 := by
  by_contra h_neg
  push_neg at h_neg
  let S : Set ℝ := Ici (0 : ℝ) ∩ {s | 1 ≤ D.α s k}
  have hS_nonempty : S.Nonempty := ⟨t, mem_Ici.mpr ht, h_neg⟩
  have hS_closed : IsClosed S := by
    apply ContinuousOn.preimage_isClosed_of_isClosed (D.hα_cont k) isClosed_Ici
    exact isClosed_le continuous_const continuous_id
  have hS_bdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  let t₀ : ℝ := sInf S
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd
  have ht₀_nn : 0 ≤ t₀ := ht₀_mem.1
  have hα_t₀_ge : 1 ≤ D.α t₀ k := ht₀_mem.2
  have ht₀_pos : 0 < t₀ := by
    rcases ht₀_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : t₀ = 0 := h.symm
      have : (1 : ℝ) ≤ D.α 0 k := h0 ▸ hα_t₀_ge
      linarith [D.hα_init_lt k]
  have h_before : ∀ s, 0 ≤ s → s < t₀ → D.α s k < 1 := fun s hs hst =>
    lt_of_not_ge fun hge =>
      not_lt.mpr (csInf_le hS_bdd ⟨mem_Ici.mpr hs, hge⟩) hst
  have hα_t₀_eq : D.α t₀ k = 1 := by
    apply le_antisymm _ hα_t₀_ge
    by_contra h_gt
    push_neg at h_gt
    have hIVT : (1 : ℝ) ∈ (fun s => D.α s k) '' Icc 0 t₀ :=
      intermediate_value_Icc ht₀_nn ((D.hα_cont k).mono Icc_subset_Ici_self)
        ⟨le_of_lt (D.hα_init_lt k), le_of_lt h_gt⟩
    obtain ⟨s, hs_icc, hαs⟩ := hIVT
    have hs_lt : s < t₀ := by
      rcases hs_icc.2.lt_or_eq with h | h
      · exact h
      · rw [h] at hαs; linarith
    linarith [h_before s hs_icc.1 hs_lt]
  have hode_neg : nPoleODE D.γ D.c D.K (D.α t₀) k < 0 := by
    unfold nPoleODE; rw [hα_t₀_eq]; nlinarith [D.hγ k]
  have hode_cont : ContinuousAt (fun s => nPoleODE D.γ D.c D.K (D.α s) k) t₀ := by
    have hcont_k_at : ContinuousAt (fun s => D.α s k) t₀ :=
      (D.hα_cont k).continuousAt (Ici_mem_nhds ht₀_pos)
    have hcont_sum_at : ContinuousAt (fun s => ∑ j, D.c j * D.α s j) t₀ :=
      (continuousOn_finset_sum _ fun j _ => continuousOn_const.mul (D.hα_cont j)).continuousAt
        (Ici_mem_nhds ht₀_pos)
    have h1 : ContinuousAt (fun s => -(D.γ k) * D.α s k) t₀ :=
      continuousAt_const.mul hcont_k_at
    have h2 : ContinuousAt (fun s => D.K / 2 * (∑ j, D.c j * D.α s j) * (1 - D.α s k ^ 2)) t₀ :=
      (continuousAt_const.mul hcont_sum_at).mul (continuousAt_const.sub (hcont_k_at.pow 2))
    have h3 : (fun s => nPoleODE D.γ D.c D.K (D.α s) k) =
        (fun s => -(D.γ k) * D.α s k + D.K / 2 * (∑ j, D.c j * D.α s j) * (1 - D.α s k ^ 2)) :=
      funext fun s => by unfold nPoleODE; ring
    rw [h3]; exact h1.add h2
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp
    (hode_cont.eventually_lt continuousAt_const hode_neg)
  set a := max 0 (t₀ - δ / 2) with ha_def
  have ha_nn : 0 ≤ a := le_max_left _ _
  have ha_lt : a < t₀ := max_lt ht₀_pos (by linarith)
  have hderiv_neg : ∀ s ∈ interior (Icc a t₀), deriv (fun s => D.α s k) s < 0 := by
    rw [interior_Icc]
    intro s ⟨hs_lo, hs_hi⟩
    rw [(D.hα_ode s (lt_of_le_of_lt ha_nn hs_lo) k).deriv]
    apply hδ_ball
    rw [Real.dist_eq, abs_lt]
    constructor
    · have := max_le_iff.mp (le_of_lt hs_lo)
      linarith [this.2]
    · linarith
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc a t₀)
    ((D.hα_cont k).mono fun s hs => mem_Ici.mpr (le_trans ha_nn hs.1))
    hderiv_neg
  linarith [hanti (left_mem_Icc.mpr (le_of_lt ha_lt)) (right_mem_Icc.mpr (le_of_lt ha_lt)) ha_lt,
    h_before a ha_nn ha_lt, hα_t₀_eq]

private def gm (D : NPoleODEData n) (j : Fin n) (t : ℝ) : ℝ :=
  D.α t j * exp (D.γ j * t)

private theorem gm_cont (D : NPoleODEData n) (j : Fin n) :
    ContinuousOn (gm D j) (Ici 0) :=
  (D.hα_cont j).mul (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

private theorem gm_deriv_eq (D : NPoleODEData n) (j : Fin n) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (gm D j)
      ((D.K / 2) * (∑ i, D.c i * D.α s i) * (1 - D.α s j ^ 2) * exp (D.γ j * s)) s := by
  have hexp : HasDerivAt (fun u => exp (D.γ j * u)) (D.γ j * exp (D.γ j * s)) s := by
    have := ((hasDerivAt_id s).const_mul (D.γ j)).exp
    simp only [mul_one, Function.comp, id] at this
    convert this using 1; ring
  convert (D.hα_ode s hs j).mul hexp using 1
  unfold nPoleODE; ring

theorem lower_barrier (D : NPoleODEData n) (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    0 < D.α t k := by
  by_contra h_le
  push_neg at h_le
  set S := ⋃ j : Fin n, Ici (0 : ℝ) ∩ (fun s => D.α s j) ⁻¹' Iic 0
  have hS_ne : S.Nonempty := ⟨t, Set.mem_iUnion.mpr ⟨k, mem_Ici.mpr ht, h_le⟩⟩
  have hS_closed : IsClosed S := isClosed_iUnion_of_finite fun j =>
    (D.hα_cont j).preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  have hS_bdd : BddBelow S := ⟨0, fun s hs => (Set.mem_iUnion.mp hs).choose_spec.1⟩
  set tm := sInf S
  have htm_mem : tm ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  obtain ⟨j₀, hj₀_nn, hj₀_pre⟩ := Set.mem_iUnion.mp htm_mem
  have htm_nn : 0 ≤ tm := hj₀_nn
  have hj₀_le : D.α tm j₀ ≤ 0 := hj₀_pre
  have htm_pos : 0 < tm := by
    rcases eq_or_lt_of_le htm_nn with h | h
    · exfalso; rw [← h] at hj₀_le; linarith [D.hα_init_pos j₀]
    · exact h
  have h_pos_before : ∀ j s, 0 ≤ s → s < tm → 0 < D.α s j := by
    intro j s hs hst
    by_contra hsj; push_neg at hsj
    exact absurd (csInf_le hS_bdd (Set.mem_iUnion.mpr ⟨j, mem_Ici.mpr hs, hsj⟩)) (not_le.mpr hst)
  -- α_{j₀}(tm) = 0 by IVT
  have hα_j₀_eq : D.α tm j₀ = 0 := by
    rcases eq_or_lt_of_le hj₀_le with h | h
    · exact le_antisymm hj₀_le (le_of_eq h.symm)
    · exfalso
      have hcont := (D.hα_cont j₀).mono (Icc_subset_Ici_self : Icc 0 tm ⊆ Ici 0)
      have h_img : (0 : ℝ) ∈ (fun s => D.α s j₀) '' Icc 0 tm :=
        intermediate_value_Icc' htm_nn hcont ⟨le_of_lt h, le_of_lt (D.hα_init_pos j₀)⟩
      obtain ⟨s, hs, hαs⟩ := h_img
      have hs_icc := mem_Icc.mp hs
      have hαs' : D.α s j₀ = 0 := hαs
      have hs_lt : s < tm := by
        rcases eq_or_lt_of_le hs_icc.2 with heq | hlt
        · exfalso; rw [heq] at hαs'; linarith
        · exact hlt
      exact absurd (h_pos_before j₀ s hs_icc.1 hs_lt) (not_lt.mpr (le_of_eq hαs'))
  -- All components ≥ 0 on [0, tm]
  have h_nn : ∀ j s, 0 ≤ s → s ≤ tm → 0 ≤ D.α s j := by
    intro j s hs hst
    rcases lt_or_eq_of_le hst with hlt | heq
    · exact le_of_lt (h_pos_before j s hs hlt)
    · subst heq
      by_contra h_neg; push_neg at h_neg
      have h_mid := h_pos_before j (tm / 2) (by linarith) (by linarith)
      obtain ⟨u, hu, hαu⟩ := isPreconnected_Icc.intermediate_value₂
        (right_mem_Icc.mpr (by linarith : tm / 2 ≤ tm))
        (left_mem_Icc.mpr (by linarith : tm / 2 ≤ tm))
        ((D.hα_cont j).mono (fun x hx => mem_Ici.mpr (le_trans (by linarith) hx.1)))
        continuousOn_const h_neg.le (le_of_lt h_mid)
      have hu_icc := mem_Icc.mp hu
      have hu_nn : 0 ≤ u := le_trans (by linarith) hu_icc.1
      have hu_in_S : u ∈ S := Set.mem_iUnion.mpr ⟨j, mem_Ici.mpr hu_nn, le_of_eq hαu⟩
      have htm_le_u := csInf_le hS_bdd hu_in_S
      have hu_eq_tm : u = tm := le_antisymm hu_icc.2 htm_le_u
      rw [hu_eq_tm] at hαu
      linarith
  -- Grönwall multiplier monotone on [0, tm]
  have hgm_mono : MonotoneOn (gm D j₀) (Icc 0 tm) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 tm)
      ((gm_cont D j₀).mono Icc_subset_Ici_self)
    · rw [interior_Icc]; intro s hs
      exact (gm_deriv_eq D j₀ s hs.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s ⟨hs_lo, hs_hi⟩
      rw [(gm_deriv_eq D j₀ s hs_lo).deriv]
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (by linarith [D.hK])
          exact Finset.sum_nonneg fun j _ =>
            mul_nonneg (le_of_lt (D.hc j)) (h_nn j s (le_of_lt hs_lo) (le_of_lt hs_hi))
        · nlinarith [upper_barrier D j₀ s (le_of_lt hs_lo),
                      h_nn j₀ s (le_of_lt hs_lo) (le_of_lt hs_hi),
                      sq_abs (D.α s j₀)]
      · exact exp_nonneg _
  -- F(0) > 0 but F(tm) = 0 → contradiction
  have hF0 : gm D j₀ 0 = D.α 0 j₀ := by simp [gm]
  have hFtm : gm D j₀ tm = 0 := by simp [gm, hα_j₀_eq]
  linarith [hgm_mono (left_mem_Icc.mpr htm_nn) (right_mem_Icc.mpr htm_nn) htm_nn,
            D.hα_init_pos j₀]

theorem invariant_box (D : NPoleODEData n) (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    0 < D.α t k ∧ D.α t k < 1 :=
  ⟨lower_barrier D k t ht, upper_barrier D k t ht⟩

def NPoleODEData.toBarrierData (D : NPoleODEData n) : NPoleBarrierData n where
  γ := D.γ
  c := D.c
  K := D.K
  α := D.α
  hK := D.hK
  hγ := D.hγ
  hc := D.hc
  hα_nn := fun t ht k => le_of_lt (lower_barrier D k t ht)
  hα_le := fun t ht k => le_of_lt (upper_barrier D k t ht)
  hα_ode := D.hα_ode
  hα_cont := D.hα_cont

theorem parametric_convergence_from_ode (D : NPoleODEData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.toBarrierData.r t - r_star| < ε :=
  parametric_convergence D.toBarrierData hn hc_sum hK_super
    D.hα_init_pos D.hα_init_lt

theorem trifurcation_from_ode (D : NPoleODEData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1) :
    ∃ r_limit : ℝ, 0 ≤ r_limit ∧ r_limit ≤ 1 ∧
      Tendsto D.toBarrierData.r atTop (nhds r_limit) ∧
      (D.K ≤ npoleCriticalK D.γ D.c → r_limit = 0) ∧
      (npoleCriticalK D.γ D.c < D.K → 0 < r_limit ∧ r_limit < 1) := by
  rcases lt_trichotomy D.K (npoleCriticalK D.γ D.c) with hlt | heq | hgt
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_subcritical_convergence D.toBarrierData hn hlt,
      fun _ => rfl,
      fun h => absurd h (not_lt.mpr (le_of_lt hlt))⟩
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_critical_convergence D.toBarrierData hn heq,
      fun _ => rfl,
      fun h => absurd h (by linarith)⟩
  · obtain ⟨r_star, hr_pos, hr_lt, hr_conv⟩ :=
      parametric_convergence D.toBarrierData hn hc_sum hgt D.hα_init_pos D.hα_init_lt
    refine ⟨r_star, le_of_lt hr_pos, le_of_lt hr_lt, ?_, ?_, ?_⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨T, hT⟩ := hr_conv ε hε
      exact ⟨T, fun t ht => by rw [Real.dist_eq]; exact hT t ht⟩
    · intro h; linarith
    · intro _; exact ⟨hr_pos, hr_lt⟩

end
