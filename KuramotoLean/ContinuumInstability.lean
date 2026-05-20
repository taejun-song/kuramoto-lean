/-
  Supercritical Convergence: K > Kc → r(t) → r*
  ================================================
  For K > Kc, the Kuramoto OA order parameter converges to r*
  unconditionally (no basin-of-attraction assumption, no axioms).

  Chain: K > Kc → r ≥ r_min > 0 → body persistence → V → 0 → r → r*.

  Key theorems:
  1. r_stays_positive_supercritical: DCT bootstrap gives r ≥ r_min > 0
  2. hPsi_floor_of_r_liminf: r-floor → V eventually enters basin
  3. kuramoto_supercritical_convergence: the unconditional end-to-end result

  0 sorry.
-/

import KuramotoLean.KuramotoGlobal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Continuum dispersion function -/

/-- The continuum dispersion function: h(λ) = (K/2)·∫ 1/(λ + γ(ω)) dμ(ω).
    Generalizes npoleDispersion from Fin n sums to measure integrals. -/
def continuumDispersion (γ : Ω → ℝ) (K : ℝ) (μ : Measure Ω) (lam : ℝ) : ℝ :=
  (K / 2) * ∫ ω, (1 / (lam + γ ω)) ∂μ

/-- The critical coupling for the continuum: Kc = 2 / ∫(1/γ) dμ. -/
def continuumKc (γ : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  2 / (∫ ω, (1 / γ ω) ∂μ)

/-- At λ = 0, the dispersion function equals (K/2)·∫(1/γ) dμ. -/
theorem continuumDispersion_at_zero (γ : Ω → ℝ) (K : ℝ) :
    continuumDispersion γ K μ 0 = (K / 2) * ∫ ω, (1 / γ ω) ∂μ := by
  unfold continuumDispersion; simp [zero_add]

/-- For K > Kc (supercritical): h(0) > 1. -/
theorem continuumDispersion_supercritical (γ : Ω → ℝ) (K : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (h_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (hK : continuumKc γ μ < K) :
    1 < continuumDispersion γ K μ 0 := by
  rw [continuumDispersion_at_zero]
  unfold continuumKc at hK
  rw [div_lt_iff₀ h_pos] at hK
  linarith

/-! ## hΨ_floor from V convergence + positive r lim inf -/

/-- **MAIN BRIDGE THEOREM.**
    If V is antitone, V ≥ 0, and r has a positive lim inf,
    then ∃ T₀ with V(T₀) < r*².

    The positive lim inf on r is what instability of incoherence provides
    (any trajectory with r(0) > 0 is repelled from r = 0 for K > Kc).

    Once r ≥ r_min > 0 eventually, the existing body persistence +
    Barbalat machinery gives V → 0, hence V eventually < r*². -/
theorem hPsi_floor_of_r_liminf [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hr_star_lt : r_star < 1)
    (h_r_liminf : ∃ r_min : ℝ, 0 < r_min ∧ r_min ≤ 1 ∧
      ∀ t, 0 ≤ t → r_min ≤ r t) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      (∫ ω, (α ω T₀ - α_star ω) ^ 2 ∂μ) < r_star ^ 2 := by
  obtain ⟨r_min, hr_min_pos, hr_min_le, hr_bound⟩ := h_r_liminf
  have hV_zero := kuramoto_V_zero_of_r_floor γ K hK hγ_pos hγ_level hγ_int
    r α hr_cont hr_bdd hα_ode hα_cont hα_neg h_sc hα_int hα_inv
    α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int
    hr_star_eq hα_star_equil hα_sq_int h_init_body r_min hr_min_pos
    hr_min_le hr_bound
  rw [Metric.tendsto_atTop] at hV_zero
  obtain ⟨T, hT⟩ := hV_zero (r_star ^ 2) (by positivity)
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  have hTt : T ≤ max T 0 := le_max_left _ _
  have h := hT (max T 0) hTt
  simp only [Real.dist_eq, sub_zero] at h
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))] at h
  exact h

/-! ## Bootstrap: K > Kc implies r stays uniformly positive -/

/-- Lower bound on bodyEquilibrium: β*(M,K,ε) ≥ Kε/(2M+Kε). -/
theorem bodyEquilibrium_lower_bound (M K ε : ℝ) (hM : 0 ≤ M) (hK : 0 < K) (hε : 0 < ε) :
    K * ε / (2 * M + K * ε) ≤ bodyEquilibrium M K ε := by
  unfold bodyEquilibrium
  have hKε : 0 < K * ε := mul_pos hK hε
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * M + K * ε) hKε]
  have h_nn : (0:ℝ) ≤ M ^ 2 + (K * ε) ^ 2 := by positivity
  have hS := Real.sq_sqrt h_nn
  have h_ineq : (K * ε) ^ 2 ≤ (-M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) *
      (2 * M + K * ε) := by
    have h_diff : -M + Real.sqrt (M ^ 2 + (K * ε) ^ 2) =
        (M ^ 2 + (K * ε) ^ 2 - M ^ 2) / (M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) := by
      have h_denom_pos : (0:ℝ) < M + Real.sqrt (M ^ 2 + (K * ε) ^ 2) := by
        have := Real.sqrt_nonneg (M ^ 2 + (K * ε) ^ 2); positivity
      rw [eq_div_iff (ne_of_gt h_denom_pos)]
      have : (-M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) *
          (M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) =
          Real.sqrt (M ^ 2 + (K * ε) ^ 2) ^ 2 - M ^ 2 := by ring
      linarith [hS]
    rw [h_diff]
    simp only [add_sub_cancel_left]
    rw [div_mul_eq_mul_div]
    have h_denom_pos : 0 < M + Real.sqrt (M ^ 2 + (K * ε) ^ 2) := by
      have := Real.sqrt_nonneg (M ^ 2 + (K * ε) ^ 2); positivity
    rw [le_div_iff₀ h_denom_pos]
    nlinarith [Real.sqrt_le_sqrt (show M ^ 2 + (K * ε) ^ 2 ≤
      (M + K * ε) ^ 2 from by nlinarith [sq_nonneg M, sq_nonneg (K * ε)]),
      Real.sqrt_sq (show (0:ℝ) ≤ M + K * ε from by positivity)]
  linarith

/-- Upper bound on bodyEquilibrium: β*(M,K,ε) ≤ Kε/(2M). -/
theorem bodyEquilibrium_upper_bound (M K ε : ℝ) (hM : 0 < M) (hK : 0 < K) (hε : 0 < ε) :
    bodyEquilibrium M K ε ≤ K * ε / (2 * M) := by
  unfold bodyEquilibrium
  have hKε : 0 < K * ε := mul_pos hK hε
  have h_nn : (0:ℝ) ≤ M ^ 2 + (K * ε) ^ 2 := by positivity
  have h_sqrt_ge : M ≤ Real.sqrt (M ^ 2 + (K * ε) ^ 2) := by
    calc M = Real.sqrt (M ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hM]
      _ ≤ Real.sqrt (M ^ 2 + (K * ε) ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have h_denom_pos : (0:ℝ) < M + Real.sqrt (M ^ 2 + (K * ε) ^ 2) := by
    have := Real.sqrt_nonneg (M ^ 2 + (K * ε) ^ 2); positivity
  have h_eq : (-M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) / (K * ε) =
      (K * ε) / (M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) := by
    rw [div_eq_div_iff (ne_of_gt hKε) (ne_of_gt h_denom_pos)]
    have : (-M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) *
        (M + Real.sqrt (M ^ 2 + (K * ε) ^ 2)) =
        Real.sqrt (M ^ 2 + (K * ε) ^ 2) ^ 2 - M ^ 2 := by ring
    linarith [Real.sq_sqrt h_nn]
  rw [h_eq]
  exact div_le_div_of_nonneg_left (by positivity : (0:ℝ) < K * ε).le
    (by positivity) (by linarith)

/-- Local body persistence: if α(0) ≥ bodyEquil and r ≥ ε on [0, T], α stays above. -/
private theorem local_persist_above (γ_ω K : ℝ) (r α_f : ℝ → ℝ) (ε T : ℝ)
    (hγ_nn : 0 ≤ γ_ω) (hK : 0 < K) (hε : 0 < ε) (hε_le : ε ≤ 1) (hT_pos : 0 < T)
    (hr_bound : ∀ t, 0 ≤ t → t ≤ T → ε ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 ≤ t → t ≤ T → HasDerivAt α_f (oaScalarRHS γ_ω K r t (α_f t)) t)
    (hα_inv : ∀ t, 0 ≤ t → t ≤ T → 0 < α_f t ∧ α_f t < 1)
    (hα_cont : ContinuousOn α_f (Icc 0 T))
    (hα0 : bodyEquilibrium γ_ω K ε ≤ α_f 0) :
    bodyEquilibrium γ_ω K ε ≤ α_f T := by
  set β := bodyEquilibrium γ_ω K ε
  by_contra h_neg; push_neg at h_neg
  set S := Icc 0 T ∩ α_f ⁻¹' (Ici β)
  have hS_ne : S.Nonempty := ⟨0, ⟨⟨le_refl _, le_of_lt hT_pos⟩, hα0⟩⟩
  have hS_closed : IsClosed S :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_bdd : BddAbove S := ⟨T, fun s hs => hs.1.2⟩
  set τ := sSup S
  have hτ_mem : τ ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  have hτ_lo : 0 ≤ τ := hτ_mem.1.1
  have hτ_hi : τ ≤ T := hτ_mem.1.2
  have hατ_ge : β ≤ α_f τ := hτ_mem.2
  have hτ_lt : τ < T := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
  have h_mono : MonotoneOn α_f (Icc τ T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc τ T)
      (hα_cont.mono (Icc_subset_Icc hτ_lo le_rfl))
    · rw [interior_Icc]; intro t ht
      exact (hα_ode t (le_trans hτ_lo (le_of_lt (mem_Ioo.mp ht).1))
        (le_of_lt (mem_Ioo.mp ht).2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht_lo := le_trans hτ_lo (le_of_lt (mem_Ioo.mp ht).1)
      have ht_hi := le_of_lt (mem_Ioo.mp ht).2
      rw [(hα_ode t ht_lo ht_hi).deriv]
      have hαt_le : α_f t ≤ β := by
        by_contra hgt; push_neg at hgt
        exact absurd (le_csSup hS_bdd
          (show t ∈ S from ⟨⟨ht_lo, ht_hi⟩, le_of_lt hgt⟩))
          (not_le.mpr (mem_Ioo.mp ht).1)
      unfold oaScalarRHS
      exact oaScalar_nonneg_below_equil γ_ω γ_ω K (r t) ε le_rfl hK hγ_nn hε hε_le
        (hr_bound t ht_lo ht_hi) (hr_bdd t) (α_f t)
        (hα_inv t ht_lo ht_hi).1 (hα_inv t ht_lo ht_hi).2 hαt_le
  linarith [h_mono (left_mem_Icc.mpr (le_of_lt hτ_lt))
    (right_mem_Icc.mpr (le_of_lt hτ_lt)) (le_of_lt hτ_lt)]

/-- Below-equilibrium monotonicity: if α(0) ≤ bodyEquil, α(T) ≥ α(0). -/
private theorem alpha_nondecreasing_below_equil (γ_ω K : ℝ) (r α_f : ℝ → ℝ) (ε T : ℝ)
    (hγ_nn : 0 ≤ γ_ω) (hK : 0 < K) (hε : 0 < ε) (hε_le : ε ≤ 1) (hT_pos : 0 < T)
    (hr_bound : ∀ t, 0 ≤ t → t ≤ T → ε ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 ≤ t → t ≤ T → HasDerivAt α_f (oaScalarRHS γ_ω K r t (α_f t)) t)
    (hα_inv : ∀ t, 0 ≤ t → t ≤ T → 0 < α_f t ∧ α_f t < 1)
    (hα_cont : ContinuousOn α_f (Icc 0 T))
    (hα0_le : α_f 0 ≤ bodyEquilibrium γ_ω K ε) :
    α_f 0 ≤ α_f T := by
  by_contra h_neg; push_neg at h_neg
  set S := Icc 0 T ∩ α_f ⁻¹' (Ici (α_f 0))
  have hS_ne : S.Nonempty := ⟨0, Set.mem_inter ⟨le_refl _, le_of_lt hT_pos⟩
    (Set.mem_preimage.mpr (mem_Ici.mpr le_rfl))⟩
  have hS_closed : IsClosed S :=
    hα_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_bdd : BddAbove S := ⟨T, fun s hs => hs.1.2⟩
  set τ := sSup S
  have hτ_mem : τ ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  have hτ_lo : 0 ≤ τ := hτ_mem.1.1
  have hτ_hi : τ ≤ T := hτ_mem.1.2
  have hατ_ge : α_f 0 ≤ α_f τ := hτ_mem.2
  have hτ_lt : τ < T := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
  have h_mono : MonotoneOn α_f (Icc τ T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc τ T)
      (hα_cont.mono (Icc_subset_Icc hτ_lo le_rfl))
    · rw [interior_Icc]; intro t ht
      exact (hα_ode t (le_trans hτ_lo (le_of_lt (mem_Ioo.mp ht).1))
        (le_of_lt (mem_Ioo.mp ht).2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht_lo := le_trans hτ_lo (le_of_lt (mem_Ioo.mp ht).1)
      have ht_hi := le_of_lt (mem_Ioo.mp ht).2
      rw [(hα_ode t ht_lo ht_hi).deriv]
      have hαt_le : α_f t ≤ bodyEquilibrium γ_ω K ε := by
        have : α_f t < α_f 0 := by
          by_contra hgt; push_neg at hgt
          exact absurd (le_csSup hS_bdd (show t ∈ S from ⟨⟨ht_lo, ht_hi⟩, hgt⟩))
            (not_le.mpr (mem_Ioo.mp ht).1)
        linarith [hα0_le]
      unfold oaScalarRHS
      exact oaScalar_nonneg_below_equil γ_ω γ_ω K (r t) ε le_rfl hK hγ_nn hε hε_le
        (hr_bound t ht_lo ht_hi) (hr_bdd t) (α_f t)
        (hα_inv t ht_lo ht_hi).1 (hα_inv t ht_lo ht_hi).2 hαt_le
  linarith [h_mono (left_mem_Icc.mpr (le_of_lt hτ_lt))
    (right_mem_Icc.mpr (le_of_lt hτ_lt)) (le_of_lt hτ_lt)]

/-- **SUPERCRITICAL BOOTSTRAP.**
    For K > Kc, r(t) ≥ r_min > 0 for all t ≥ 0.

    Uses local body persistence + self-consistency contradiction. -/
theorem r_stays_positive_supercritical [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (h_init_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0) :
    ∃ r_min : ℝ, 0 < r_min ∧ r_min ≤ 1 ∧ ∀ t, 0 ≤ t → r_min ≤ r t := by
  have h_super_ineq : 1 < (K / 2) * ∫ ω, (1 / γ ω) ∂μ := by
    unfold continuumKc at h_super; linarith [div_lt_iff₀ h_inv_pos |>.mp h_super]
  have hr_pos : ∀ t, 0 ≤ t → 0 < r t := by
    intro t ht; rw [h_sc t ht]
    exact (integral_pos_iff_support_of_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
      (hα_int t)).mpr (by
      rw [show Function.support (fun ω => α ω t) = Set.univ from
        Set.eq_univ_iff_forall.mpr (fun ω => ne_of_gt (hα_inv ω t ht).1)]
      simp [measure_univ])
  have h_bootstrap : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ε₀ < r 0 ∧
      (∀ t, 0 < t → (∀ s, 0 ≤ s → s ≤ t → ε₀ ≤ r s) → ε₀ < ∫ ω, α ω t ∂μ) := by
    -- DCT: ∫ min(α(ω,0), Kε/(2γ+Kε)) → ∫ min(α(ω,0), ∞) = r(0) as ε → 0,
    -- and for small ε: this integral > ε (since (K/2)∫(1/γ) > 1).
    have h_dct_choice : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ε₀ < r 0 ∧
        Integrable (fun ω => min (α ω 0) (K * ε₀ / (2 * γ ω + K * ε₀))) μ ∧
        (ε₀ < ∫ ω, min (α ω 0) (K * ε₀ / (2 * γ ω + K * ε₀)) ∂μ) := by
      have hα0_pos : ∀ ω, 0 < α ω 0 := fun ω => (hα_inv ω 0 le_rfl).1
      have hr0_pos : 0 < r 0 := hr_pos 0 le_rfl
      have hα0_aem : AEMeasurable (fun ω => α ω 0) μ :=
        (hα_int 0).aestronglyMeasurable.aemeasurable
      have hγ_aem : AEMeasurable γ μ := hγ_int.aestronglyMeasurable.aemeasurable
      set bnd : Ω → ℝ := fun ω => K / (2 * γ ω)
      have h_bnd_int : Integrable bnd μ := by
        show Integrable (fun ω => K / (2 * γ ω)) μ
        have : (fun ω => K / (2 * γ ω)) = fun ω => (K / 2) * (1 / γ ω) := by
          ext ω; ring
        rw [this]; exact h_inv_int.const_mul _
      have h_bnd_gt : 1 < ∫ ω, bnd ω ∂μ := by
        show 1 < ∫ ω, K / (2 * γ ω) ∂μ
        have heq : ∫ ω, K / (2 * γ ω) ∂μ = (K / 2) * ∫ ω, (1 / γ ω) ∂μ := by
          conv_lhs => rw [show (fun ω => K / (2 * γ ω)) = fun ω => (K / 2) * (1 / γ ω) from
            by ext ω; ring]
          exact integral_const_mul _ _
        linarith [h_super_ineq]
      set G : ℕ → Ω → ℝ := fun n ω =>
        min ((↑n + 1 : ℝ) * α ω 0) (K / (2 * γ ω + K / (↑n + 1 : ℝ)))
      have hG_nn : ∀ n ω, 0 ≤ G n ω := fun n ω =>
        le_min (mul_nonneg (by positivity) (hα0_pos ω).le)
          (div_nonneg hK.le (by have := hγ_pos ω; positivity))
      have hG_le : ∀ n ω, G n ω ≤ bnd ω := by
        intro n ω; show G n ω ≤ K / (2 * γ ω)
        exact min_le_of_right_le (div_le_div_of_nonneg_left (by positivity)
          (by have := hγ_pos ω; positivity)
          (le_add_of_nonneg_right (by positivity : (0:ℝ) ≤ K / (↑n + 1))))
      have h_meas : ∀ n, AEStronglyMeasurable (G n) μ := by
        intro n
        have h2 : AEMeasurable (fun ω => K / (2 * γ ω + K / (↑n + 1 : ℝ))) μ :=
          (hγ_aem.const_mul 2 |>.add_const (K / (↑n + 1 : ℝ))).inv.const_mul K
        exact ((hα0_aem.const_mul (↑n + 1 : ℝ)).min h2).aestronglyMeasurable
      have h_n1_atTop : Tendsto (fun n : ℕ => (↑n + 1 : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 (bnd ω)) := by
        apply ae_of_all; intro ω
        show Tendsto (fun n => G n ω) atTop (𝓝 (K / (2 * γ ω)))
        have hγω := hγ_pos ω
        have hαω := hα0_pos ω
        have h_second : Tendsto (fun n : ℕ => K / (2 * γ ω + K / (↑n + 1 : ℝ))) atTop
            (𝓝 (K / (2 * γ ω))) := by
          have h_denom : Tendsto (fun n : ℕ => 2 * γ ω + K / (↑n + 1 : ℝ)) atTop
              (𝓝 (2 * γ ω + 0)) :=
            tendsto_const_nhds.add (tendsto_const_nhds.div_atTop h_n1_atTop)
          simp only [add_zero] at h_denom
          exact tendsto_const_nhds.div h_denom (ne_of_gt (by positivity))
        have h_ev_eq : ∀ᶠ n in atTop, G n ω = K / (2 * γ ω + K / (↑n + 1 : ℝ)) := by
          have h_nα := h_n1_atTop.atTop_mul_const hαω
          exact (h_nα.eventually (Filter.eventually_ge_atTop (K / (2 * γ ω)))).mono
            fun n hn => min_eq_right (le_trans (div_le_div_of_nonneg_left (by positivity)
              (by positivity) (le_add_of_nonneg_right (by positivity))) hn)
        exact (Filter.tendsto_congr' h_ev_eq).mpr h_second
      have h_dct := tendsto_integral_of_dominated_convergence bnd h_meas h_bnd_int
        (fun n => ae_of_all μ fun ω => by
          rw [Real.norm_of_nonneg (hG_nn n ω)]; exact hG_le n ω)
        h_lim
      have h_ev_int : ∀ᶠ n in atTop, (1 : ℝ) < ∫ ω, G n ω ∂μ :=
        h_dct (Ioi_mem_nhds h_bnd_gt)
      have h_tends_zero : Tendsto (fun n : ℕ => (1 : ℝ) / ((↑n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h_n1_atTop
      rw [Filter.eventually_atTop] at h_ev_int
      obtain ⟨N₁, hN₁⟩ := h_ev_int
      obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
        (h_tends_zero.eventually (Iio_mem_nhds hr0_pos))
      set N := max N₁ N₂
      have hN_int := hN₁ N (le_max_left _ _)
      have hN_small := hN₂ N (le_max_right _ _)
      have hN1_pos : (0 : ℝ) < ↑N + 1 := by positivity
      refine ⟨1 / (↑N + 1), by positivity,
        (div_le_one hN1_pos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) N]),
        hN_small, ?_, ?_⟩
      · have h_min_aem : AEMeasurable (fun ω =>
            min (α ω 0) (K * (1 / (↑N + 1 : ℝ)) / (2 * γ ω + K * (1 / (↑N + 1 : ℝ))))) μ :=
          hα0_aem.min ((hγ_aem.const_mul 2 |>.add_const
            (K * (1 / (↑N + 1 : ℝ)))).inv.const_mul (K * (1 / (↑N + 1 : ℝ))))
        exact (hα_int 0).mono h_min_aem.aestronglyMeasurable
          (ae_of_all μ fun ω => by
            rw [Real.norm_of_nonneg (le_min (hα0_pos ω).le
              (div_nonneg (by positivity) (by have := hγ_pos ω; positivity))),
              Real.norm_of_nonneg (hα0_pos ω).le]
            exact min_le_left _ _)
      · have h_factor : (fun ω => min (α ω 0)
            (K * (1 / (↑N + 1 : ℝ)) / (2 * γ ω + K * (1 / (↑N + 1 : ℝ))))) =
            fun ω => (1 / (↑N + 1 : ℝ)) * G N ω := by
          ext ω; simp only [G]
          rw [mul_min_of_nonneg _ _ (div_nonneg zero_le_one hN1_pos.le)]
          have hN1_ne : (↑N + 1 : ℝ) ≠ 0 := ne_of_gt hN1_pos
          have hd_ne : 2 * γ ω + K / (↑N + 1 : ℝ) ≠ 0 :=
            ne_of_gt (by have := hγ_pos ω; positivity)
          congr 1 <;> field_simp <;> ring
        rw [h_factor, integral_const_mul]
        exact lt_mul_of_one_lt_right (by positivity) hN_int
    obtain ⟨ε₀, hε₀_pos, hε₀_le, hε₀_lt_r0, h_min_int, h_int_gt⟩ := h_dct_choice
    refine ⟨ε₀, hε₀_pos, hε₀_le, hε₀_lt_r0, fun t ht_pos hr_bound => ?_⟩
    have h_min_bound : ∀ ω, min (α ω 0) (K * ε₀ / (2 * γ ω + K * ε₀)) ≤ α ω t := by
      intro ω
      by_cases h_above : bodyEquilibrium (γ ω) K ε₀ ≤ α ω 0
      · have h_persist := local_persist_above (γ ω) K r (α ω) ε₀ t
            (le_of_lt (hγ_pos ω)) hK hε₀_pos hε₀_le ht_pos hr_bound hr_bdd
            (fun s hs0 hsT => hα_ode ω s hs0) (fun s hs0 _ => hα_inv ω s hs0)
            ((hα_cont ω).mono Icc_subset_Ici_self) h_above
        exact le_trans (min_le_right _ _) (le_trans
          (bodyEquilibrium_lower_bound (γ ω) K ε₀ (le_of_lt (hγ_pos ω)) hK hε₀_pos) h_persist)
      · push_neg at h_above
        have h_nondecr := alpha_nondecreasing_below_equil (γ ω) K r (α ω) ε₀ t
            (le_of_lt (hγ_pos ω)) hK hε₀_pos hε₀_le ht_pos hr_bound hr_bdd
            (fun s hs0 hsT => hα_ode ω s hs0) (fun s hs0 _ => hα_inv ω s hs0)
            ((hα_cont ω).mono Icc_subset_Ici_self) (le_of_lt h_above)
        exact le_trans (min_le_left _ _) h_nondecr
    calc ε₀ < ∫ ω, min (α ω 0) (K * ε₀ / (2 * γ ω + K * ε₀)) ∂μ := h_int_gt
      _ ≤ ∫ ω, α ω t ∂μ := integral_mono h_min_int (hα_int t) h_min_bound
  obtain ⟨ε₀, hε₀_pos, hε₀_le, hε₀_lt_r0, h_self_improve⟩ := h_bootstrap
  suffices h_no_cross : ∀ t, 0 ≤ t → ε₀ ≤ r t from ⟨ε₀, hε₀_pos, hε₀_le, h_no_cross⟩
  by_contra h_cross
  push_neg at h_cross
  obtain ⟨t_bad, ht_bad_nn, ht_bad_lt⟩ := h_cross
  have hS_closed : IsClosed {t : ℝ | 0 ≤ t ∧ r t ≤ ε₀} :=
    (isClosed_Ici.preimage continuous_id).inter (isClosed_Iic.preimage hr_cont)
  set T := sInf {t | 0 ≤ t ∧ r t ≤ ε₀}
  have hS_ne : ({t | 0 ≤ t ∧ r t ≤ ε₀} : Set ℝ).Nonempty :=
    ⟨t_bad, ht_bad_nn, le_of_lt ht_bad_lt⟩
  have hS_bdd : BddBelow {t : ℝ | 0 ≤ t ∧ r t ≤ ε₀} := ⟨0, fun t ht => ht.1⟩
  have hT_mem : T ∈ {t : ℝ | 0 ≤ t ∧ r t ≤ ε₀} := hS_closed.csInf_mem hS_ne hS_bdd
  have hT_nn : (0 : ℝ) ≤ T := hT_mem.1
  have hT_pos : (0 : ℝ) < T := by
    rcases eq_or_lt_of_le hT_nn with h | h
    · linarith [show r 0 ≤ ε₀ from h ▸ hT_mem.2, hε₀_lt_r0]
    · exact h
  have hr_above : ∀ s, 0 ≤ s → s ≤ T → ε₀ ≤ r s := by
    have h_closed : IsClosed {s : ℝ | ε₀ ≤ r s} := isClosed_Ici.preimage hr_cont
    have h_Ico : Set.Ico 0 T ⊆ {s : ℝ | ε₀ ≤ r s} := by
      intro s ⟨hs_nn, hs_lt⟩
      by_contra h_neg
      exact absurd (csInf_le hS_bdd ⟨hs_nn, (not_le.mp h_neg).le⟩) (not_le.mpr hs_lt)
    intro s hs_nn hs_le
    exact h_closed.closure_subset (closure_mono h_Ico
      (by rw [closure_Ico (ne_of_lt hT_pos)]; exact ⟨hs_nn, hs_le⟩))
  have hrT : r T = ε₀ := le_antisymm hT_mem.2 (hr_above T hT_nn le_rfl)
  linarith [h_self_improve T hT_pos hr_above,
    show r T = ∫ ω, α ω T ∂μ from h_sc T (le_of_lt hT_pos)]

/-- **SUPERCRITICAL GLOBAL CONVERGENCE** — the main theorem.
    For K > Kc: r(t) → r* unconditionally (no basin condition, no axioms).
    Composes: K > Kc → r ≥ r_min > 0 → body persistence → V → 0 → r → r*. -/
theorem kuramoto_supercritical_convergence [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (h_init_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_min, hr_min_pos, hr_min_le, hr_floor⟩ :=
    r_stays_positive_supercritical γ K r α hK hγ_pos hγ_int hγ_level
      h_inv_int h_inv_pos h_super hr_cont hr_bdd hα_ode hα_cont hα_neg
      hα_inv h_sc hα_int h_init_body
  exact kuramoto_standard_tendsto_of_r_floor γ K hK hγ_pos hγ_level hγ_int
    r α hr_cont hr_bdd hα_ode hα_cont hα_neg h_sc hα_int hα_inv
    α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int
    hr_star_eq hα_star_equil hα_sq_int h_init_body r_min hr_min_pos
    hr_min_le hr_floor

end
