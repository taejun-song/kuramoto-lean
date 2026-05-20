/-
  Ψ Energy → η Summability Bridge
  =================================
  Connects the Dietert energy identity dΨ/dt = K|η|² to:
  1. Ψ growth lower bound on intervals where η² ≥ m
  2. Bounded Ψ → interval length constraint (η can't stay large forever)
  3. Basin entry: V → 0 → ∃ T₀, V(T₀) < B
  4. Antitone Lyapunov convergence
  5. Barbalat-type: η² drops below any threshold (bounded Ψ → η transient)
  6. Contrapositive: persistent η² ≥ m forces Ψ unbounded

  12 theorems, 0 sorry.
-/

import KuramotoLean.ComplexOAEnergy
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

/-! ## Monotone Ψ converges to a limit when bounded -/

/-- Bounded monotone Ψ converges to its supremum. -/
theorem psi_tendsto_of_monotone_bounded
    (Ψ : ℝ → ℝ) (hΨ_mono : Monotone Ψ)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M) :
    ∃ L, Tendsto Ψ atTop (nhds L) ∧ ∀ t, Ψ t ≤ L := by
  have hΨ_bdd : BddAbove (range Ψ) :=
    ⟨M, fun _ ⟨t, ht⟩ => ht ▸ hM t⟩
  exact ⟨sSup (range Ψ),
    tendsto_atTop_ciSup hΨ_mono hΨ_bdd,
    fun t => le_ciSup hΨ_bdd t⟩

/-! ## Ψ growth gives lower bound on cumulative |η|² -/

/-- On [a,b], Ψ grows by at least K·m·(b-a) when η² ≥ m on [a,b].
    Uses Convex.mul_sub_le_image_sub_of_le_deriv from MVT. -/
theorem psi_growth_lower
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (a b : ℝ) (hab : a ≤ b) (m : ℝ) (hm : ∀ t, a ≤ t → t ≤ b → m ≤ η_sq t) :
    K * m * (b - a) ≤ Ψ b - Ψ a := by
  have h_diff : Differentiable ℝ Ψ := fun t => (h_deriv t).differentiableAt
  by_cases heq : a = b
  · subst heq; simp
  have hab' : a < b := lt_of_le_of_ne hab heq
  have h_cont : ContinuousOn Ψ (Icc a b) := h_diff.continuous.continuousOn
  have h_diffon : DifferentiableOn ℝ Ψ (interior (Icc a b)) :=
    h_diff.differentiableOn.mono interior_subset
  have h_lb : ∀ x ∈ interior (Icc a b), K * m ≤ deriv Ψ x := by
    intro x hx
    rw [(h_deriv x).deriv]
    have hx_mem := interior_subset hx
    exact mul_le_mul_of_nonneg_left (hm x hx_mem.1 hx_mem.2) (le_of_lt hK)
  exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b) h_cont h_diffon
    h_lb a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab

/-! ## Antitone Lyapunov converges -/

/-- Non-negative antitone function converges to its infimum. -/
theorem lyapunov_tendsto_of_antitone
    (V : ℝ → ℝ) (hV_anti : Antitone V) (hV_nn : ∀ t, 0 ≤ V t) :
    ∃ L, 0 ≤ L ∧ Tendsto V atTop (nhds L) := by
  have hΨ_mono : Monotone (fun t => -V t) := fun a b hab => neg_le_neg (hV_anti hab)
  have hΨ_bdd : BddAbove (range (fun t => -V t)) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ neg_nonpos.mpr (hV_nn t)⟩
  have h_tends := tendsto_atTop_ciSup hΨ_mono hΨ_bdd
  set L := sSup (range (fun t => -V t))
  have hL_le : L ≤ 0 := ciSup_le (fun t => neg_nonpos.mpr (hV_nn t))
  refine ⟨-L, by linarith, ?_⟩
  have : Tendsto (fun t => -(-V t)) atTop (nhds (-L)) := h_tends.neg
  simp only [neg_neg] at this
  exact this

/-! ## Basin entry from V → 0 -/

/-- **Basin entry.** If V → 0 then ∃ T₀, V(T₀) < B for any B > 0. -/
theorem basin_entry_of_tendsto_zero
    (V : ℝ → ℝ) (B : ℝ) (hB : 0 < B)
    (hV : Tendsto V atTop (nhds 0)) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ V T₀ < B := by
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T, hT⟩ := hV B hB
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  have h := hT (max T 0) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- **Basin entry (non-negative version).** -/
theorem basin_entry_of_tendsto_zero_nn
    (V : ℝ → ℝ) (hV_nn : ∀ t, 0 ≤ V t)
    (B : ℝ) (hB : 0 < B)
    (hV : Tendsto V atTop (nhds 0)) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ V T₀ < B ∧ 0 ≤ V T₀ := by
  obtain ⟨T₀, hT₀, hV_lt⟩ := basin_entry_of_tendsto_zero V B hB hV
  exact ⟨T₀, hT₀, hV_lt, hV_nn T₀⟩

/-! ## Antitone limit properties -/

/-- If V is antitone and V → L, then V(t) ≥ L for all t. -/
theorem antitone_tendsto_ge
    (V : ℝ → ℝ) (L : ℝ)
    (hV_anti : Antitone V) (hV_lim : Tendsto V atTop (nhds L)) :
    ∀ t, L ≤ V t := by
  intro t
  by_contra h
  simp only [not_le] at h
  have hε : 0 < L - V t := by linarith
  rw [Metric.tendsto_atTop] at hV_lim
  obtain ⟨T, hT⟩ := hV_lim (L - V t) hε
  have hT' := hT (max T t) (le_max_left _ _)
  rw [Real.dist_eq] at hT'
  have hle : V (max T t) ≤ V t := hV_anti (le_max_right _ _)
  rw [abs_lt] at hT'
  linarith

/-! ## Ψ monotone + bounded → interval length constraint -/

/-- **Cumulative η² bound.** Ψ monotone and bounded above → growth bounded. -/
theorem psi_cumulative_eta_bound
    (Ψ : ℝ → ℝ) (_hΨ_mono : Monotone Ψ)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M) :
    ∀ T, Ψ T - Ψ 0 ≤ M - Ψ 0 :=
  fun T => sub_le_sub_right (hM T) _

/-- **Interval length constraint.** If Ψ bounded and η² ≥ m > 0 on [a,b],
    then b - a ≤ (M - Ψ(a))/(K·m). η can't stay large indefinitely. -/
theorem eta_large_interval_bounded
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (a b : ℝ) (hab : a ≤ b) (m : ℝ) (hm : 0 < m)
    (h_large : ∀ t, a ≤ t → t ≤ b → m ≤ η_sq t) :
    b - a ≤ (M - Ψ a) / (K * m) := by
  have hKm : 0 < K * m := mul_pos hK hm
  have h_growth := psi_growth_lower Ψ K hK η_sq h_deriv a b hab m h_large
  have : K * m * (b - a) ≤ M - Ψ a := by linarith [hM b]
  rwa [le_div_iff₀ hKm, mul_comm]

/-- **Ψ growth rate exclusion.** If Ψ bounded and η² ≥ m on all of [a, a+L],
    then L ≤ (M - Ψ(0))/(Km). Proof: Ψ grows by ≥ Km·L on [a,a+L],
    but Ψ(a) ≥ Ψ(0) and Ψ(a+L) ≤ M cap the total growth. -/
theorem psi_eta_interval_budget
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (hΨ_mono : Monotone Ψ)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (a L : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L) (m : ℝ) (_hm : 0 < m)
    (h_large : ∀ s, a ≤ s → s ≤ a + L → m ≤ η_sq s) :
    K * m * L ≤ M - Ψ 0 := by
  have h_growth := psi_growth_lower Ψ K hK η_sq h_deriv a (a + L)
    (by linarith) m h_large
  have : Ψ (a + L) ≤ M := hM (a + L)
  have : Ψ 0 ≤ Ψ a := hΨ_mono ha
  linarith

/-! ## Barbalat-type: η² can't stay above any threshold forever -/

/-- **η² drops below any threshold.** If Ψ is bounded above with dΨ/dt = K|η|²,
    then for any m > 0 and any starting time T, there exists s ≥ T with η²(s) < m.
    Proof: if η² ≥ m on [T, T + L], Ψ grows by ≥ KmL. For L large enough this
    exceeds the headroom M - Ψ(T), contradiction. -/
theorem eta_sq_drops_below
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (m : ℝ) (hm : 0 < m) (T : ℝ) :
    ∃ s, T ≤ s ∧ η_sq s < m := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hKm : 0 < K * m := mul_pos hK hm
  set L := (M - Ψ T) / (K * m) + 1
  have hMT : 0 ≤ M - Ψ T := by linarith [hM T]
  have hL_pos : 0 < L := by positivity
  have h_growth := psi_growth_lower Ψ K hK η_sq h_deriv T (T + L)
    (by linarith) m (fun t ht1 _ => h t ht1)
  have hL_def : L = (M - Ψ T) / (K * m) + 1 := rfl
  have : K * m * L = (M - Ψ T) + K * m := by
    rw [hL_def, mul_add, mul_div_cancel₀ _ (ne_of_gt hKm), mul_one]
  linarith [hM (T + L)]

/-- **η² infinitely often below threshold.** Corollary of `eta_sq_drops_below`:
    for any m > 0, the set {t : η²(t) < m} is unbounded. -/
theorem eta_sq_frequently_small
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (m : ℝ) (hm : 0 < m) :
    ∀ T, ∃ s, T ≤ s ∧ η_sq s < m :=
  fun T => eta_sq_drops_below Ψ K hK η_sq h_deriv M hM m hm T

/-- **Ψ bounded + Penrose contrapositive.** If dΨ/dt = K|η|² with Ψ bounded,
    then η can't stay above any positive threshold on a half-line.
    Contrapositive: if η is eventually bounded below (η² ≥ m > 0 for all t ≥ T),
    then Ψ is unbounded. This is the "energy divergence from persistent coherence." -/
theorem psi_unbounded_of_eta_persistent
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (m : ℝ) (hm : 0 < m) (T : ℝ)
    (h_persist : ∀ t, T ≤ t → m ≤ η_sq t) :
    ∀ C, ∃ t, C < Ψ t := by
  intro C
  have hKm : 0 < K * m := mul_pos hK hm
  set L := max ((C - Ψ T) / (K * m)) 0 + 1
  have hL_pos : 0 < L := by linarith [le_max_right ((C - Ψ T) / (K * m)) 0]
  have hab : T ≤ T + L := by linarith
  have h_growth := psi_growth_lower Ψ K hK η_sq h_deriv T (T + L) hab m
    (fun t ht1 _ => h_persist t ht1)
  refine ⟨T + L, ?_⟩
  have hmax : (C - Ψ T) / (K * m) ≤ L - 1 := le_max_left _ _ |>.trans (by linarith)
  have : C - Ψ T ≤ (L - 1) * (K * m) := (div_le_iff₀ hKm).mp hmax
  nlinarith

end
