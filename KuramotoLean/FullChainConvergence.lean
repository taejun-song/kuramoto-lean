/-
  Kuramoto Stability — Full Chain: Instability → Convergence
  ============================================================

  Proves r → r* from NPoleBarrierData + K > K_c + α(0) ∈ (0,1)^n,
  WITHOUT assuming persistence as a hypothesis.

  Chain:
    InfiniteEscape → shifted barrier → r-bound on propagation interval
    → component propagation (RPersistenceComponent + forward invariance)
    → shifted barrier on drop interval → V-drop (pair coercivity)
    → Barbalat → V → 0 → Cauchy-Schwarz → r → r*

  0 sorry target.
-/

import KuramotoLean.InfiniteEscape
import KuramotoLean.ShiftedBarrier
import KuramotoLean.ComponentForwardInvariance
import KuramotoLean.DropFromComponentBound
import KuramotoLean.EndToEndConvergence
import KuramotoLean.ContinuumBarbalat

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Full chain data -/

structure FullChainData (n : ℕ) extends NPoleBarrierData n where
  hn : 0 < n
  α_star : Fin n → ℝ
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hc_sum : ∑ k, c k = 1
  hα_init_pos : ∀ k, 0 < α 0 k
  hα_init_lt_one : ∀ k, α 0 k < 1
  lam : ℝ
  hlam : 0 < lam
  hdisp : npoleDispersion γ c K lam = 1
  γ_max : ℝ
  hγ_max_pos : 0 < γ_max
  hγ_max : ∀ k, γ k ≤ γ_max
  δ_star : ℝ
  hδ_star_pos : 0 < δ_star
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  c_min : ℝ
  hc_min_pos : 0 < c_min
  hc_min : ∀ k, c_min ≤ c k
  ε_inst : ℝ
  hε_pos : 0 < ε_inst
  hε_small : (K / 2) * (∑ k, c k) * ε_inst ^ 2 ≤ lam / 2
  hε_beta : K * (c_min * ε_inst * exp (-2)) ≤ 2 * γ_max

/-! ## Derived constants -/

def FullChainData.δ₁ (D : FullChainData n) : ℝ :=
  D.c_min * D.ε_inst * exp (-2)

def FullChainData.β_val (D : FullChainData n) : ℝ :=
  D.K * D.δ₁ / (4 * D.γ_max)

def FullChainData.S_prop (D : FullChainData n) : ℝ :=
  2 / D.γ_max

def FullChainData.δ_drop (D : FullChainData n) : ℝ :=
  D.β_val * exp (-D.γ_max)

def FullChainData.Δ_total (D : FullChainData n) : ℝ :=
  D.S_prop + 1

def FullChainData.q_val (D : FullChainData n) : ℝ :=
  exp (-(D.K * D.δ_drop * D.δ_star))

/-! ## Positivity and bound lemmas -/

theorem FullChainData.hδ₁_pos (D : FullChainData n) : 0 < D.δ₁ := by
  unfold FullChainData.δ₁; exact mul_pos (mul_pos D.hc_min_pos D.hε_pos) (exp_pos _)

theorem FullChainData.hβ_pos (D : FullChainData n) : 0 < D.β_val := by
  unfold FullChainData.β_val
  exact div_pos (mul_pos D.hK D.hδ₁_pos) (mul_pos (by norm_num : (0:ℝ) < 4) D.hγ_max_pos)

theorem FullChainData.hβ_half (D : FullChainData n) : D.β_val ≤ 1 / 2 := by
  have h : D.K * D.δ₁ ≤ 2 * D.γ_max := by unfold FullChainData.δ₁; linarith [D.hε_beta]
  unfold FullChainData.β_val
  rw [div_le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) D.hγ_max_pos) (by norm_num : (0:ℝ) < 2)]
  linarith

theorem FullChainData.hβ_small (D : FullChainData n) (k : Fin n) :
    D.β_val ≤ D.K * D.δ₁ / (4 * D.γ k) := by
  unfold FullChainData.β_val
  apply div_le_div_of_nonneg_left (le_of_lt (mul_pos D.hK D.hδ₁_pos))
    (mul_pos (by norm_num : (0:ℝ) < 4) (D.hγ k))
    (mul_le_mul_of_nonneg_left (D.hγ_max k) (le_of_lt (by norm_num : (0:ℝ) < 4)))

theorem FullChainData.hS_prop_pos (D : FullChainData n) : 0 < D.S_prop := by
  unfold FullChainData.S_prop; exact div_pos (by norm_num : (0:ℝ) < 2) D.hγ_max_pos

theorem FullChainData.hΔ_total_pos (D : FullChainData n) : 0 < D.Δ_total := by
  unfold FullChainData.Δ_total; linarith [D.hS_prop_pos]

theorem FullChainData.hδ_drop_pos (D : FullChainData n) : 0 < D.δ_drop := by
  unfold FullChainData.δ_drop; exact mul_pos D.hβ_pos (exp_pos _)

theorem FullChainData.hq_nn (D : FullChainData n) : 0 ≤ D.q_val :=
  le_of_lt (by unfold FullChainData.q_val; exact exp_pos _)

theorem FullChainData.hq_lt_one (D : FullChainData n) : D.q_val < 1 := by
  unfold FullChainData.q_val
  have h : 0 < D.K * D.δ_drop * D.δ_star :=
    mul_pos (mul_pos D.hK D.hδ_drop_pos) D.hδ_star_pos
  calc exp (-(D.K * D.δ_drop * D.δ_star))
      < exp 0 := exp_lt_exp.mpr (by linarith)
    _ = 1 := exp_zero

theorem FullChainData.hα_lt (D : FullChainData n) (t : ℝ) (ht : 0 ≤ t) (k : Fin n) :
    D.α t k < 1 :=
  component_strict_lt_one D.toNPoleBarrierData D.hα_init_lt_one t ht k

/-! ## V antitone -/

theorem FullChainData.hV_anti (D : FullChainData n) :
    Antitone (l2_ext D.c D.α D.α_star) :=
  l2_ext_antitone D.toNPoleBarrierData D.α_star D.hα_star_pos
    D.hα_star_lt D.h_equil D.hα_init_pos (fun t ht k => D.hα_lt t ht k)

/-! ## Escape time matches propagation time -/

theorem FullChainData.escape_le_Sprop (D : FullChainData n) :
    8 * D.β_val / (D.K * D.δ₁) ≤ D.S_prop := by
  have heq : 8 * D.β_val / (D.K * D.δ₁) = D.S_prop := by
    unfold FullChainData.β_val FullChainData.S_prop
    field_simp [ne_of_gt D.hK, ne_of_gt D.hδ₁_pos, ne_of_gt D.hγ_max_pos]
    ring
  linarith

/-! ## Step 1: Escape → r-bound on propagation interval -/

theorem FullChainData.r_bound_from_escape (D : FullChainData n)
    (k₀ : Fin n) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hα_k₀ : D.ε_inst < D.α t₀ k₀) :
    ∀ s, t₀ ≤ s → s ≤ t₀ + D.S_prop → D.δ₁ ≤ D.toNPoleBarrierData.r s := by
  intro s hs_lo hs_hi
  have h_shift := component_lower_shifted D.toNPoleBarrierData k₀ t₀ D.S_prop
    ht₀ (le_of_lt D.hS_prop_pos) s hs_lo hs_hi
  have h_exp : exp (-2 : ℝ) ≤ exp (-(D.γ k₀) * D.S_prop) := by
    apply exp_le_exp.mpr
    have h1 : -(D.γ_max) * D.S_prop ≤ -(D.γ k₀) * D.S_prop :=
      mul_le_mul_of_nonneg_right (neg_le_neg (D.hγ_max k₀)) (le_of_lt D.hS_prop_pos)
    have h2 : -(D.γ_max) * D.S_prop = -2 := by
      unfold FullChainData.S_prop; rw [neg_mul, mul_div_cancel₀ _ (ne_of_gt D.hγ_max_pos)]
    linarith
  calc D.δ₁ = D.c_min * (D.ε_inst * exp (-2 : ℝ)) := by unfold FullChainData.δ₁; ring
    _ ≤ D.c k₀ * (D.ε_inst * exp (-2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (D.hc_min k₀)
        exact mul_nonneg (le_of_lt D.hε_pos) (exp_nonneg _)
    _ ≤ D.c k₀ * (D.α t₀ k₀ * exp (-(D.γ k₀) * D.S_prop)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (D.hc k₀))
        exact mul_le_mul (le_of_lt hα_k₀) h_exp (exp_nonneg _) (D.hα_nn t₀ ht₀ k₀)
    _ ≤ D.c k₀ * D.α s k₀ :=
        mul_le_mul_of_nonneg_left h_shift (le_of_lt (D.hc k₀))
    _ ≤ D.toNPoleBarrierData.r s :=
        single_le_sum (fun j _ => mul_nonneg (le_of_lt (D.hc j))
          (D.hα_nn s (le_trans ht₀ hs_lo) j)) (mem_univ k₀)

/-! ## Step 2: All components ≥ β at propagation time -/

theorem FullChainData.component_at_prop (D : FullChainData n)
    (j : Fin n) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hr : ∀ s, t₀ ≤ s → s ≤ t₀ + D.S_prop → D.δ₁ ≤ D.toNPoleBarrierData.r s) :
    D.β_val ≤ D.α (t₀ + D.S_prop) j := by
  obtain ⟨t_j, ht_lo, ht_hi, hα_j⟩ := component_must_exceed D.toNPoleBarrierData j
    D.δ₁ D.β_val D.hδ₁_pos D.hβ_pos (D.hβ_small j) D.hβ_half
    t₀ D.S_prop ht₀ D.hS_prop_pos D.escape_le_Sprop hr
    (component_positive D.toNPoleBarrierData j (D.hα_init_pos j) t₀ ht₀)
  exact component_threshold_forward_inv D.toNPoleBarrierData j D.δ₁ D.β_val
    D.hδ₁_pos D.hβ_pos (D.hβ_small j) D.hβ_half
    t_j (t₀ + D.S_prop) (le_trans ht₀ ht_lo) ht_hi
    (fun s hs1 hs2 => hr s (le_trans ht_lo hs1) hs2)
    (le_of_lt hα_j) (t₀ + D.S_prop) ht_hi le_rfl

/-! ## Step 3: Component bound on drop interval via shifted barrier -/

theorem FullChainData.component_on_drop (D : FullChainData n)
    (j : Fin n) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hα_j : D.β_val ≤ D.α (t₀ + D.S_prop) j)
    (s : ℝ) (hs_lo : t₀ + D.S_prop ≤ s) (hs_hi : s ≤ t₀ + D.S_prop + 1) :
    D.δ_drop ≤ D.α s j := by
  unfold FullChainData.δ_drop
  have h_shift := component_lower_shifted D.toNPoleBarrierData j (t₀ + D.S_prop) 1
    (by linarith [D.hS_prop_pos]) (by norm_num) s hs_lo hs_hi
  calc D.β_val * exp (-D.γ_max)
      ≤ D.β_val * exp (-(D.γ j) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt D.hβ_pos)
        apply exp_le_exp.mpr; nlinarith [D.hγ_max j]
    _ ≤ D.α (t₀ + D.S_prop) j * exp (-(D.γ j) * 1) :=
        mul_le_mul_of_nonneg_right hα_j (exp_nonneg _)
    _ ≤ D.α s j := h_shift

/-! ## Step 4: V-drop from escape event -/

theorem FullChainData.V_drop_from_escape (D : FullChainData n)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (k₀ : Fin n) (hα_k₀ : D.ε_inst < D.α t₀ k₀) :
    l2Distance D.c (D.α (t₀ + D.S_prop + 1)) D.α_star ≤
      l2Distance D.c (D.α (t₀ + D.S_prop)) D.α_star *
        exp (-(D.K * D.δ_drop * D.δ_star) * 1) := by
  have hr := D.r_bound_from_escape k₀ t₀ ht₀ hα_k₀
  have hcomp : ∀ j, D.β_val ≤ D.α (t₀ + D.S_prop) j :=
    fun j => D.component_at_prop j t₀ ht₀ hr
  have hα_lb : ∀ s, t₀ + D.S_prop ≤ s → s ≤ t₀ + D.S_prop + 1 → ∀ j, D.δ_drop ≤ D.α s j :=
    fun s hs1 hs2 j => D.component_on_drop j t₀ ht₀ (hcomp j) s hs1 hs2
  have ha : 0 ≤ t₀ + D.S_prop := by linarith [D.hS_prop_pos]
  exact l2_drop_from_bounds D.γ D.c D.K D.α D.α_star
    D.hK D.hγ D.hc D.h_equil D.hα_star_pos D.hα_star_lt
    D.δ_drop D.δ_star D.hδ_drop_pos D.hδ_star_pos D.hα_star_lb D.hc_sum
    (t₀ + D.S_prop) 1 ha (by norm_num) hα_lb
    (fun s hs1 hs2 k => D.hα_lt s (by linarith) k)
    (fun s hs => D.hα_ode s (by linarith))
    (l2_continuousOn D.c D.α D.α_star D.hα_cont |>.mono
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha)))

/-! ## Step 5: Infinitely many V-drops -/

theorem FullChainData.infinite_drops (D : FullChainData n) :
    ∀ T : ℝ, ∃ t, T ≤ t ∧
      l2_ext D.c D.α D.α_star (t + D.Δ_total) ≤
        D.q_val * l2_ext D.c D.α D.α_star t := by
  intro T
  set T' := max T 0
  have hT' : 0 ≤ T' := le_max_right T 0
  obtain ⟨t₀, ht₀, k₀, hα_k₀⟩ := instability_infinite_escape D.toNPoleBarrierData D.hn
    D.lam D.hlam D.hdisp D.ε_inst D.hε_pos D.hε_small D.hα_init_pos T' hT'
  refine ⟨t₀, le_trans (le_max_left T 0) ht₀, ?_⟩
  have ht₀_nn : 0 ≤ t₀ := le_trans hT' ht₀
  rw [l2_ext_eq D.c D.α D.α_star (t₀ + D.Δ_total) (by linarith [D.hΔ_total_pos]),
      l2_ext_eq D.c D.α D.α_star t₀ ht₀_nn]
  unfold FullChainData.q_val FullChainData.Δ_total
  rw [show t₀ + (D.S_prop + 1) = t₀ + D.S_prop + 1 from by ring]
  have hV_drop := D.V_drop_from_escape t₀ ht₀_nn k₀ hα_k₀
  have hV_at_prop : l2Distance D.c (D.α (t₀ + D.S_prop)) D.α_star ≤
      l2Distance D.c (D.α t₀) D.α_star := by
    have h1 : l2_ext D.c D.α D.α_star (t₀ + D.S_prop) ≤ l2_ext D.c D.α D.α_star t₀ :=
      D.hV_anti (by linarith [D.hS_prop_pos])
    rwa [l2_ext_eq D.c D.α D.α_star (t₀ + D.S_prop) (by linarith [D.hS_prop_pos]),
         l2_ext_eq D.c D.α D.α_star t₀ ht₀_nn] at h1
  calc l2Distance D.c (D.α (t₀ + D.S_prop + 1)) D.α_star
      ≤ l2Distance D.c (D.α (t₀ + D.S_prop)) D.α_star *
          exp (-(D.K * D.δ_drop * D.δ_star) * 1) := hV_drop
    _ ≤ l2Distance D.c (D.α t₀) D.α_star *
          exp (-(D.K * D.δ_drop * D.δ_star) * 1) :=
        mul_le_mul_of_nonneg_right hV_at_prop (exp_nonneg _)
    _ = exp (-(D.K * D.δ_drop * D.δ_star)) * l2Distance D.c (D.α t₀) D.α_star := by ring

/-! ## Step 6: V → 0 and r → r* -/

theorem FullChainData.V_tendsto_zero (D : FullChainData n) :
    Tendsto (l2_ext D.c D.α D.α_star) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuous_barbalat_general (l2_ext D.c D.α D.α_star) D.q_val D.Δ_total
    (l2_ext_nonneg D.c D.α D.α_star D.hc) D.hV_anti
    D.hq_nn D.hq_lt_one D.hΔ_total_pos D.infinite_drops ε hε
  exact ⟨T, fun s hs => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (l2_ext_nonneg D.c D.α D.α_star D.hc s)]
    exact hT s hs⟩

theorem full_chain_convergence (D : FullChainData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.toNPoleBarrierData.r t - ∑ k, D.c k * D.α_star k| < ε := by
  intro ε hε
  have hV := D.V_tendsto_zero
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T₁, hT₁⟩ := hV (ε ^ 2) (by positivity)
  refine ⟨max T₁ 0, fun t ht => ?_⟩
  have ht_nn : 0 ≤ t := le_trans (le_max_right T₁ 0) ht
  have hT₁_le : T₁ ≤ t := le_trans (le_max_left T₁ 0) ht
  have hV_t := hT₁ t hT₁_le
  simp only [Real.dist_eq, sub_zero] at hV_t
  rw [abs_of_nonneg (l2_ext_nonneg D.c D.α D.α_star D.hc t),
      l2_ext_eq D.c D.α D.α_star t ht_nn] at hV_t
  have hcs := order_parameter_sq_le_l2 D.c (D.α t) D.α_star
    (fun k => le_of_lt (D.hc k)) D.hc_sum
  unfold NPoleBarrierData.r
  have h_eq : ∑ k, D.c k * D.α t k - ∑ k, D.c k * D.α_star k =
      ∑ k, D.c k * (D.α t k - D.α_star k) := by
    rw [← sum_sub_distrib]; congr 1; ext k; ring
  rw [h_eq]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hcs hV_t) (le_of_lt hε)

end
