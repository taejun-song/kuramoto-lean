/-
  Body Persistence from ODE Comparison
  =====================================
  Proves: if the scalar OA ODE has r(t) ≥ r_min > 0,
  then on body {γ ≤ M}, α(ω,t) is bounded below.

  The equilibrium β* of the comparison ODE dβ/dt = -Mβ + (K/2)r_min(1-β²)
  serves as a lower barrier: below β*, the solution is increasing.

  Key steps:
  1. β* = (-M + √(M²+K²r²))/(Kr) ∈ (0,1) — comparison equilibrium
  2. oaScalarRHS(γ,K,r,α) ≥ 0 when γ ≤ M, r ≥ r_min, α ≤ β*
  3. monotoneOn_of_deriv_nonneg: α non-decreasing while below β*
  4. Lower barrier: α(t) ≥ min(α(0), β*) for all t ≥ 0

  0 sorry.
-/

import KuramotoLean.ContinuumODEExistence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Real Set Filter Topology

noncomputable section

/-! ## Comparison equilibrium -/

def bodyEquilibrium (M K r_min : ℝ) : ℝ :=
  (-M + Real.sqrt (M ^ 2 + (K * r_min) ^ 2)) / (K * r_min)

theorem bodyEquilibrium_pos (M K r_min : ℝ) (hM : 0 ≤ M) (hK : 0 < K) (hr : 0 < r_min) :
    0 < bodyEquilibrium M K r_min := by
  unfold bodyEquilibrium
  have hKr : 0 < K * r_min := mul_pos hK hr
  rw [div_pos_iff_of_pos_right hKr]
  have hKr_sq : 0 < (K * r_min) ^ 2 := sq_pos_of_pos hKr
  have h_disc : M ^ 2 < M ^ 2 + (K * r_min) ^ 2 := by linarith
  have h_sqrt_gt : Real.sqrt (M ^ 2) < Real.sqrt (M ^ 2 + (K * r_min) ^ 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg M) h_disc
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hM] at h_sqrt_gt
  linarith

theorem bodyEquilibrium_lt_one (M K r_min : ℝ) (hM : 0 < M) (hK : 0 < K)
    (hr : 0 < r_min) (_hr_le : r_min ≤ 1) :
    bodyEquilibrium M K r_min < 1 := by
  unfold bodyEquilibrium
  have hKr : 0 < K * r_min := mul_pos hK hr
  rw [div_lt_one hKr]
  have h_sum_pos : 0 < M + K * r_min := by linarith
  have h_sq : M ^ 2 + (K * r_min) ^ 2 < (M + K * r_min) ^ 2 := by
    have : 0 < 2 * M * (K * r_min) := by positivity
    nlinarith
  have h_sqrt : Real.sqrt (M ^ 2 + (K * r_min) ^ 2) < M + K * r_min := by
    calc Real.sqrt (M ^ 2 + (K * r_min) ^ 2)
        < Real.sqrt ((M + K * r_min) ^ 2) :=
          Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg M, sq_nonneg (K * r_min)]) h_sq
      _ = M + K * r_min := by rw [Real.sqrt_sq (le_of_lt h_sum_pos)]
  linarith

theorem bodyEquilibrium_equil (M K r_min : ℝ) (hK : 0 < K) (hr : 0 < r_min) :
    M * bodyEquilibrium M K r_min =
      (K / 2) * r_min * (1 - (bodyEquilibrium M K r_min) ^ 2) := by
  unfold bodyEquilibrium
  have hKr_pos : 0 < K * r_min := mul_pos hK hr
  have hKr_ne : (K * r_min) ≠ 0 := ne_of_gt hKr_pos
  have h_nn : (0:ℝ) ≤ M ^ 2 + (K * r_min) ^ 2 := by nlinarith [sq_nonneg M, sq_nonneg (K*r_min)]
  have hS_sq : Real.sqrt (M ^ 2 + (K * r_min) ^ 2) ^ 2 = M ^ 2 + (K * r_min) ^ 2 :=
    Real.sq_sqrt h_nn
  have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt hK
  have hr_ne : (r_min : ℝ) ≠ 0 := ne_of_gt hr
  have hKr_sq : (K * r_min) ^ 2 = K ^ 2 * r_min ^ 2 := by ring
  rw [hKr_sq] at hS_sq
  field_simp [hKr_ne, hK_ne, hr_ne]
  nlinarith [hS_sq]

/-! ## ODE RHS non-negative below equilibrium -/

theorem oaScalar_nonneg_below_equil (γ_ω M K r_t r_min : ℝ)
    (hγ_le : γ_ω ≤ M) (hK : 0 < K) (hM : 0 ≤ M)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_t : r_min ≤ r_t) (hr_bdd : |r_t| ≤ 1)
    (α_val : ℝ) (hα_pos : 0 < α_val) (hα_lt : α_val < 1)
    (hα_le_eq : α_val ≤ bodyEquilibrium M K r_min) :
    0 ≤ -γ_ω * α_val + (K / 2) * r_t * (1 - α_val ^ 2) := by
  set β := bodyEquilibrium M K r_min
  have hβ_pos := bodyEquilibrium_pos M K r_min hM hK hr_min
  have h_equil := bodyEquilibrium_equil M K r_min hK hr_min
  have h1mα2 : 0 < 1 - α_val ^ 2 := by nlinarith [sq_nonneg α_val]
  -- Factor: -γ_ω·α + (K/2)·r_t·(1-α²) ≥ -M·α + (K/2)·r_min·(1-α²)
  --         = (β-α)·[M + (K/2)·r_min·(β+α)] ≥ 0
  suffices h : 0 ≤ -M * α_val + (K / 2) * r_min * (1 - α_val ^ 2) by
    have h1 : -M * α_val ≤ -γ_ω * α_val := by nlinarith [hα_pos]
    have h2 : (K / 2) * r_min * (1 - α_val ^ 2) ≤ (K / 2) * r_t * (1 - α_val ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt h1mα2)
      exact mul_le_mul_of_nonneg_left hr_t (by linarith)
    linarith
  have h_factor : -M * α_val + (K / 2) * r_min * (1 - α_val ^ 2) =
      (β - α_val) * (M + (K / 2) * r_min * (β + α_val)) := by
    nlinarith [h_equil]
  rw [h_factor]
  exact mul_nonneg (by linarith) (by positivity)

/-! ## Monotone below barrier: α non-decreasing while ≤ β*

The core lemma: on any interval [a,b] where α ≤ β*, α is non-decreasing.
Uses monotoneOn_of_deriv_nonneg with derivative = oaScalarRHS ≥ 0. -/

theorem alpha_monotone_below_barrier
    (γ_ω M K : ℝ) (r α : ℝ → ℝ) (r_min : ℝ)
    (hγ_pos : 0 < γ_ω) (hγ_le : γ_ω ≤ M) (hK : 0 < K)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t)
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (h_below : ∀ t, t ∈ Icc a b → α t ≤ bodyEquilibrium M K r_min) :
    MonotoneOn α (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (hα_cont.mono (fun x hx => mem_Ici.mpr (le_trans ha (mem_Icc.mp hx).1)))
  · rw [interior_Icc]
    intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt ha (mem_Ioo.mp ht).1
    exact (hα_ode t ht_pos).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt ha (mem_Ioo.mp ht).1
    rw [(hα_ode t ht_pos).deriv]
    have ht_nn : 0 ≤ t := le_of_lt ht_pos
    unfold oaScalarRHS
    exact oaScalar_nonneg_below_equil γ_ω M K (r t) r_min hγ_le hK
      (le_trans (le_of_lt hγ_pos) hγ_le) hr_min hr_le
      (hr_bound t ht_nn) (hr_bdd t) (α t) (hα_inv t ht_nn).1 (hα_inv t ht_nn).2
      (h_below t (mem_Icc.mpr ⟨le_of_lt (mem_Ioo.mp ht).1, le_of_lt (mem_Ioo.mp ht).2⟩))

/-! ## Body persistence: α cannot stay below β*

Main theorem: For t ≥ 0, α(t) ≥ min(α(0), β*).

Case 1 (α(0) ≤ β*): While α ≤ β*, it's non-decreasing, so α(t) ≥ α(0).
Case 2 (α(0) > β*): If α(t) < β*, then on [τ,t] (where τ is last exit from {α ≥ β*}),
  α is non-decreasing with α(τ) ≥ β*. Contradiction. -/

theorem body_persistence_lower_bound
    (γ_ω M K : ℝ) (r α : ℝ → ℝ) (r_min : ℝ)
    (hγ_pos : 0 < γ_ω) (hγ_le : γ_ω ≤ M) (hK : 0 < K)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t)
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (t : ℝ) (ht : 0 ≤ t) :
    min (α 0) (bodyEquilibrium M K r_min) ≤ α t := by
  set β := bodyEquilibrium M K r_min
  have hβ_pos := bodyEquilibrium_pos M K r_min
    (le_trans (le_of_lt hγ_pos) hγ_le) hK hr_min
  by_cases hα0_le : α 0 ≤ β
  · -- Case 1: α(0) ≤ β*. α is non-decreasing while below β*, so α(t) ≥ α(0).
    simp only [min_eq_left hα0_le]
    by_contra h_neg
    push_neg at h_neg
    -- α(t) < α(0) ≤ β*
    have hαt_lt_β : α t < β := lt_of_lt_of_le h_neg hα0_le
    -- Find the LAST time α is at or above α(0) before t
    -- Actually use: on any interval where α ≤ β*, α is monotone.
    -- If α ≤ β* on [0,t]: monotone gives α(t) ≥ α(0). Contradiction.
    -- If α > β* somewhere on [0,t]: let τ = sup {s ∈ [0,t] | α(s) > β*}.
    --   On [τ, t]: α ≤ β* (by definition of sup + continuity).
    --   Monotone on [τ,t]: α(t) ≥ α(τ). But α(τ) ≥ β* ≥ α(0). Contradiction.
    by_cases h_all_below : ∀ s ∈ Icc 0 t, α s ≤ β
    · -- All below β*: monotone on [0,t]
      have h_mono := alpha_monotone_below_barrier γ_ω M K r α r_min hγ_pos hγ_le
        hK hr_min hr_le hr_bound hr_bdd hα_ode hα_inv hα_cont 0 t le_rfl ht h_all_below
      linarith [h_mono (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht]
    · -- α exceeds β* at some point
      push_neg at h_all_below
      obtain ⟨s₀, hs₀_mem, hα_s₀⟩ := h_all_below
      have hs₀_nn : 0 ≤ s₀ := (mem_Icc.mp hs₀_mem).1
      have hs₀_le : s₀ ≤ t := (mem_Icc.mp hs₀_mem).2
      -- Since α(s₀) > β* and α(t) < β*, by IVT there exists τ ∈ [s₀, t] with α(τ) = β*.
      -- Take τ = sup of times in [s₀, t] where α ≥ β*.
      -- On [τ, t]: α ≤ β*. Monotone gives α(t) ≥ α(τ) ≥ β* > α(0). Contradiction.
      have h_ivt : ∃ τ ∈ Icc s₀ t, α τ = β ∧ ∀ s ∈ Icc τ t, α s ≤ β := by
        set S := Icc s₀ t ∩ α ⁻¹' (Ici β)
        have hα_cont_st : ContinuousOn α (Icc s₀ t) :=
          hα_cont.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hs₀_nn))
        have hS_ne : S.Nonempty := ⟨s₀, ⟨le_rfl, hs₀_le⟩, le_of_lt hα_s₀⟩
        have hS_closed : IsClosed S :=
          hα_cont_st.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
        have hS_bdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
        have hc_mem : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
        set τ := sSup S
        have hτ_lo : s₀ ≤ τ := hc_mem.1.1
        have hτ_hi : τ ≤ t := hc_mem.1.2
        have hατ_ge : β ≤ α τ := hc_mem.2
        have hτ_lt : τ < t := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
        have hατ_eq : α τ = β := by
          refine le_antisymm ?_ hατ_ge
          by_contra h_gt; push_neg at h_gt
          obtain ⟨δ', hδ', hball⟩ := Metric.continuousOn_iff.mp hα_cont_st τ
            (mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩) (α τ - β) (by linarith)
          set ε' := min (δ' / 2) ((t - τ) / 2)
          have hε'_pos : 0 < ε' := lt_min (by linarith) (by linarith)
          have hε'_lt_δ : ε' < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
          have hτε_in : τ + ε' ∈ Icc s₀ t := ⟨by linarith, by linarith [min_le_right (δ'/2) ((t-τ)/2)]⟩
          have hτε_dist : dist (τ + ε') τ < δ' := by
            rw [Real.dist_eq, show τ + ε' - τ = ε' from by ring, abs_of_pos hε'_pos]; exact hε'_lt_δ
          have h_close := hball (τ + ε') hτε_in hτε_dist
          have hα_ge : β ≤ α (τ + ε') := by
            rw [Real.dist_eq] at h_close; linarith [(abs_lt.mp h_close).1]
          exact absurd (le_csSup hS_bdd ⟨hτε_in, hα_ge⟩) (not_le.mpr (by linarith : τ < τ + ε'))
        have h_after : ∀ s ∈ Icc τ t, α s ≤ β := by
          intro s hs
          rcases eq_or_lt_of_le (mem_Icc.mp hs).1 with rfl | hlt
          · exact le_of_eq hατ_eq
          · by_contra hge; push_neg at hge
            exact absurd (le_csSup hS_bdd ⟨⟨by linarith [hτ_lo], (mem_Icc.mp hs).2⟩, le_of_lt hge⟩)
              (not_le.mpr hlt)
        exact ⟨τ, mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩, hατ_eq, h_after⟩
      obtain ⟨τ, hτ_mem, hατ_eq, h_after⟩ := h_ivt
      have hτ_nn : 0 ≤ τ := le_trans hs₀_nn (mem_Icc.mp hτ_mem).1
      have hτ_le : τ ≤ t := (mem_Icc.mp hτ_mem).2
      have h_mono := alpha_monotone_below_barrier γ_ω M K r α r_min hγ_pos hγ_le
        hK hr_min hr_le hr_bound hr_bdd hα_ode hα_inv hα_cont τ t hτ_nn hτ_le h_after
      have h_ge : α τ ≤ α t := h_mono (left_mem_Icc.mpr hτ_le) (right_mem_Icc.mpr hτ_le) hτ_le
      linarith [hατ_eq]
  · -- Case 2: α(0) > β*. Show α(t) ≥ β* (barrier from above).
    push_neg at hα0_le
    simp only [min_eq_right (le_of_lt hα0_le)]
    by_contra h_neg
    push_neg at h_neg
    -- α(t) < β* but α(0) > β*. Same argument: find last crossing, monotone after.
    have h_ivt : ∃ τ ∈ Icc 0 t, α τ = β ∧ ∀ s ∈ Icc τ t, α s ≤ β := by
      set S := Icc 0 t ∩ α ⁻¹' (Ici β)
      have hα_cont_0t : ContinuousOn α (Icc 0 t) :=
        hα_cont.mono (Icc_subset_Ici_self)
      have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, ht⟩, le_of_lt hα0_le⟩
      have hS_closed : IsClosed S :=
        hα_cont_0t.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hS_bdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
      have hc_mem : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
      set τ := sSup S
      have hτ_lo : 0 ≤ τ := hc_mem.1.1
      have hτ_hi : τ ≤ t := hc_mem.1.2
      have hατ_ge : β ≤ α τ := hc_mem.2
      have hτ_lt : τ < t := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
      have hατ_eq : α τ = β := by
        refine le_antisymm ?_ hατ_ge
        by_contra h_gt; push_neg at h_gt
        obtain ⟨δ', hδ', hball⟩ := Metric.continuousOn_iff.mp hα_cont_0t τ
          (mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩) (α τ - β) (by linarith)
        set ε' := min (δ' / 2) ((t - τ) / 2)
        have hε'_pos : 0 < ε' := lt_min (by linarith) (by linarith)
        have hε'_lt_δ : ε' < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hτε_in : τ + ε' ∈ Icc 0 t := ⟨by linarith, by linarith [min_le_right (δ'/2) ((t-τ)/2)]⟩
        have hτε_dist : dist (τ + ε') τ < δ' := by
          rw [Real.dist_eq, show τ + ε' - τ = ε' from by ring, abs_of_pos hε'_pos]; exact hε'_lt_δ
        have h_close := hball (τ + ε') hτε_in hτε_dist
        have hα_ge : β ≤ α (τ + ε') := by
          rw [Real.dist_eq] at h_close; linarith [(abs_lt.mp h_close).1]
        exact absurd (le_csSup hS_bdd ⟨hτε_in, hα_ge⟩) (not_le.mpr (by linarith : τ < τ + ε'))
      have h_after : ∀ s ∈ Icc τ t, α s ≤ β := by
        intro s hs
        rcases eq_or_lt_of_le (mem_Icc.mp hs).1 with rfl | hlt
        · exact le_of_eq hατ_eq
        · by_contra hge; push_neg at hge
          exact absurd (le_csSup hS_bdd ⟨⟨by linarith [hτ_lo], (mem_Icc.mp hs).2⟩, le_of_lt hge⟩)
            (not_le.mpr hlt)
      exact ⟨τ, mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩, hατ_eq, h_after⟩
    obtain ⟨τ, hτ_mem, hατ_eq, h_after⟩ := h_ivt
    have hτ_nn : 0 ≤ τ := (mem_Icc.mp hτ_mem).1
    have hτ_le : τ ≤ t := (mem_Icc.mp hτ_mem).2
    have h_mono := alpha_monotone_below_barrier γ_ω M K r α r_min hγ_pos hγ_le
      hK hr_min hr_le hr_bound hr_bdd hα_ode hα_inv hα_cont τ t hτ_nn hτ_le h_after
    have h_ge : α τ ≤ α t := h_mono (left_mem_Icc.mpr hτ_le) (right_mem_Icc.mpr hτ_le) hτ_le
    linarith [hατ_eq]

/-! ## Application to the continuum model -/

/-- **Body persistence for the continuum OA model.**
    On body {γ ≤ M} with r(t) ≥ r_min > 0:
    α(ω,t) ≥ min(α(ω,0), β*(M,K,r_min)) uniformly. -/
theorem continuum_body_persistence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (r_min M : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1) (hM : 0 < M)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t, 0 < t → HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_0_pos : ∀ ω, γ ω ≤ M → 0 < α ω 0)
    (hα_0_min : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hα_0_min
  set β := bodyEquilibrium M K r_min
  have hβ_pos := bodyEquilibrium_pos M K r_min (le_of_lt hM) hK hr_min
  refine ⟨min δ₀ β, lt_min hδ₀_pos hβ_pos, fun ω hγ_le t ht => ?_⟩
  have h_lower := body_persistence_lower_bound (γ ω) M K r (α ω) r_min
    (hγ ω) hγ_le hK hr_min hr_le hr_bound hr_bdd
    (hα_ode ω) (hα_inv ω) (hα_cont ω) t ht
  calc min δ₀ β ≤ min (α ω 0) β := min_le_min_right β (hδ₀ ω hγ_le)
    _ ≤ α ω t := h_lower

end
