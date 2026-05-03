/-
  Kuramoto Stability — General g ODE Instance (GAP 1)
  ====================================================
  Proves the invariant region (0,1) for the per-ω scalar OA ODE:
    dα/dt = -γα + (K/2)r(t)(1 - α²)

  Upper barrier: at α = 1, RHS = -γ < 0. First-touch + antitone argument.
  Lower barrier: Grönwall multiplier F(t) = α(t)exp(γt), dF/dt ≥ 0 when r ≥ 0.

  Then constructs ContinuumODEData from general g by filling hα_pos and hα_lt
  fields from the invariant region.

  0 sorry.
-/

import KuramotoLean.ContinuumODEExistence
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Real Set Filter Topology Metric

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Upper barrier: α(t) < 1

At α = 1, oaScalarRHS = -γ·1 + (K/2)·r(t)·0 = -γ < 0.
By continuity, the ODE value is negative near the first time α reaches 1.
Antitone on that interval contradicts the infimum being the first time. -/

theorem scalar_oa_upper_barrier
    (γ K : ℝ) (r α : ℝ → ℝ)
    (hγ : 0 < γ) (hr_cont : Continuous r)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_init_lt : α 0 < 1)
    (t : ℝ) (ht : 0 ≤ t) : α t < 1 := by
  by_contra h_neg
  push_neg at h_neg
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
    rcases ht₀_nn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hα_t₀_ge; linarith
  have h_before : ∀ s, 0 ≤ s → s < t₀ → α s < 1 := fun s hs hst =>
    lt_of_not_ge fun hge =>
      not_lt.mpr (csInf_le hS_bdd ⟨mem_Ici.mpr hs, hge⟩) hst
  have hα_t₀_eq : α t₀ = 1 := by
    apply le_antisymm _ hα_t₀_ge
    by_contra h_gt; push_neg at h_gt
    have hIVT : (1 : ℝ) ∈ α '' Icc 0 t₀ :=
      intermediate_value_Icc ht₀_nn (hα_cont.mono Icc_subset_Ici_self)
        ⟨le_of_lt hα_init_lt, le_of_lt h_gt⟩
    obtain ⟨s, hs_icc, hαs⟩ := hIVT
    have hs_lt : s < t₀ := by
      rcases hs_icc.2.lt_or_eq with h | h
      · exact h
      · rw [h] at hαs; linarith
    linarith [h_before s hs_icc.1 hs_lt]
  have hode_neg : oaScalarRHS γ K r t₀ (α t₀) < 0 := by
    rw [hα_t₀_eq]; unfold oaScalarRHS; nlinarith
  have hα_at : ContinuousAt α t₀ :=
    hα_cont.continuousAt (Ici_mem_nhds ht₀_pos)
  have hode_cont : ContinuousAt (fun s => oaScalarRHS γ K r s (α s)) t₀ := by
    have heq : (fun s => oaScalarRHS γ K r s (α s)) =
        fun s => -γ * α s + K / 2 * r s * (1 - α s ^ 2) :=
      funext fun s => by unfold oaScalarRHS; ring
    rw [heq]
    exact (continuousAt_const.mul hα_at).add
      ((continuousAt_const.mul hr_cont.continuousAt).mul
        (continuousAt_const.sub (hα_at.pow 2)))
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp
    (hode_cont.eventually_lt continuousAt_const hode_neg)
  set a := max 0 (t₀ - δ / 2)
  have ha_nn : 0 ≤ a := le_max_left _ _
  have ha_lt : a < t₀ := max_lt ht₀_pos (by linarith)
  have ha_dist : ∀ s, a ≤ s → s ≤ t₀ → dist s t₀ < δ := by
    intro s hs1 hs2
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
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

/-! ## Lower barrier: α(t) > 0

Grönwall multiplier F(t) = α(t)·exp(γt). Then:
  dF/dt = (K/2)·r(t)·(1 - α(t)²)·exp(γt) ≥ 0
when r ≥ 0 and α ∈ [0,1]. So F is monotone on [0, t_first_zero].
F(0) = α(0) > 0 but F(t_first_zero) = 0 — contradiction. -/

theorem scalar_oa_lower_barrier
    (γ K : ℝ) (r α : ℝ → ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_init_pos : 0 < α 0)
    (hα_upper : ∀ t, 0 ≤ t → α t < 1)
    (t : ℝ) (ht : 0 ≤ t) : 0 < α t := by
  by_contra h_le
  push_neg at h_le
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
  -- Grönwall multiplier F(s) = α(s) · exp(γs), inline
  set F : ℝ → ℝ := fun s => α s * exp (γ * s) with hF_def
  have hF_cont : ContinuousOn F (Icc 0 tm) :=
    ((hα_cont.mono Icc_subset_Ici_self).mul
      (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  have hF_deriv : ∀ s, 0 < s → s < tm →
      HasDerivAt F ((K / 2) * r s * (1 - α s ^ 2) * exp (γ * s)) s := by
    intro s hs _
    have hexp : HasDerivAt (fun u => exp (γ * u)) (γ * exp (γ * s)) s := by
      have := ((hasDerivAt_id s).const_mul γ).exp
      simp only [mul_one, Function.comp, id] at this
      convert this using 1; ring
    have h := (hα_ode s hs).mul hexp
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

/-! ## ContinuumODEData constructor from general g

Takes per-ω ODE solutions with initial conditions in (0,1) and r ≥ 0.
Derives invariant region (0,1) from upper + lower barriers.
Fills all ContinuumODEData fields. -/

def generalG_ContinuumODEData
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_ode : ∀ ω t, 0 < t → HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_ode_zero : ∀ ω, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r 0 (α ω 0)) 0)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init_pos : ∀ ω, 0 < α ω 0)
    (hα_init_lt : ∀ ω, α ω 0 < 1) :
    ContinuumODEData μ where
  γ := γ
  K := K
  hK := hK
  hγ := hγ
  r := r
  hr_cont := hr_cont
  hr_bdd := hr_bdd
  α := α
  α_star := α_star
  hα_star := hα_star_pos
  hα_star_lt := hα_star_lt
  hα_ode := fun ω t ht => by
    by_cases h : t = 0
    · rw [h]; exact hα_ode_zero ω
    · exact hα_ode ω t (lt_of_le_of_ne ht (Ne.symm h))
  hα_pos := fun ω t ht =>
    scalar_oa_lower_barrier (γ ω) K r (α ω) (hγ ω) hK hr_nn
      (hα_ode ω) (hα_cont ω) (hα_init_pos ω)
      (fun s hs => scalar_oa_upper_barrier (γ ω) K r (α ω) (hγ ω) hr_cont
        (hα_ode ω) (hα_cont ω) (hα_init_lt ω) s hs)
      t ht
  hα_lt := fun ω t ht =>
    scalar_oa_upper_barrier (γ ω) K r (α ω) (hγ ω) hr_cont
      (hα_ode ω) (hα_cont ω) (hα_init_lt ω) t ht

end
