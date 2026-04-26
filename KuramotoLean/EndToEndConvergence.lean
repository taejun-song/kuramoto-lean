/-
  Kuramoto Stability — End-to-End N-Pole Convergence
  ====================================================

  Single theorem from ODE trajectory data to r → r*, combining:
  1. V antitone from trajectory Lyapunov (derives hV_anti from the ODE)
  2. Component persistence from r-persistence
  3. Multiplicative V-drops from uniform rate
  4. Barbalat → V → 0 → r → r*

  Key new result: l2_antitoneOn derives V antitone along the n-pole
  ODE trajectory from the pair bound, eliminating the hV_anti hypothesis
  that all previous proof paths assumed.

  0 sorry target.
-/

import KuramotoLean.SelfContainedConvergence
import KuramotoLean.ComponentForwardInvariance
import KuramotoLean.DropFromComponentBound
import KuramotoLean.TrajectoryLyapunov
import KuramotoLean.OrderParameterRate
import KuramotoLean.UpperBarrier

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## V continuous along trajectory -/

theorem l2_continuousOn (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (hα_cont : ∀ k, ContinuousOn (fun t => α t k) (Ici (0 : ℝ))) :
    ContinuousOn (fun t => l2Distance c (α t) α_star) (Ici (0 : ℝ)) := by
  unfold l2Distance
  apply continuousOn_finset_sum; intro k _
  exact continuousOn_const.mul (((hα_cont k).sub continuousOn_const).pow 2)

/-! ## V antitone on [0,∞) from the ODE

This derives V antitone from the ODE structure, rather than assuming it.
The proof:
  1. trajectory_lyapunov_qualitative gives dV/dt ≤ 0 at each t > 0
  2. component_positive gives α_k(t) > 0 for t > 0 (from Gronwall barrier)
  3. hα_strict_lt gives α_k(t) < 1 (ODE invariance)
  4. antitoneOn_of_deriv_nonpos (Mathlib MVT) gives V antitone -/

theorem l2_antitoneOn (D : NPoleBarrierData n)
    (α_star : Fin n → ℝ)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE D.γ D.c D.K α_star k = 0)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (hα_strict_lt : ∀ t, 0 ≤ t → ∀ k, D.α t k < 1) :
    AntitoneOn (fun t => l2Distance D.c (D.α t) α_star) (Ici (0 : ℝ)) := by
  set V := fun t => l2Distance D.c (D.α t) α_star
  have hV_cont : ContinuousOn V (Ici 0) :=
    l2_continuousOn D.c D.α α_star D.hα_cont
  have hV_diff : DifferentiableOn ℝ V (Ioi 0) := by
    intro t ht
    have ht_pos := mem_Ioi.mp ht
    obtain ⟨_, hderiv, _⟩ := trajectory_lyapunov_qualitative D.γ D.c D.K D.α α_star t
      D.hK D.hγ D.hc
      (fun k => component_positive D k (hα_init_pos k) t (le_of_lt ht_pos))
      (hα_strict_lt t (le_of_lt ht_pos))
      hα_star_pos hα_star_lt h_equil (D.hα_ode t ht_pos)
    exact hderiv.differentiableAt.differentiableWithinAt
  have hV_le : ∀ t ∈ Ioi (0 : ℝ), deriv V t ≤ 0 := by
    intro t ht
    have ht_pos := mem_Ioi.mp ht
    obtain ⟨_, hderiv, hle⟩ := trajectory_lyapunov_qualitative D.γ D.c D.K D.α α_star t
      D.hK D.hγ D.hc
      (fun k => component_positive D k (hα_init_pos k) t (le_of_lt ht_pos))
      (hα_strict_lt t (le_of_lt ht_pos))
      hα_star_pos hα_star_lt h_equil (D.hα_ode t ht_pos)
    rw [hderiv.deriv]; exact hle
  exact antitoneOn_of_deriv_nonpos (convex_Ici (𝕜 := ℝ) 0) hV_cont
    (by rwa [interior_Ici]) (by rwa [interior_Ici])

/-! ## Antitone extension to all of ℝ -/

def l2_ext (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ) (t : ℝ) : ℝ :=
  l2Distance c (α (max t 0)) α_star

theorem l2_ext_antitone (D : NPoleBarrierData n)
    (α_star : Fin n → ℝ)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE D.γ D.c D.K α_star k = 0)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (hα_strict_lt : ∀ t, 0 ≤ t → ∀ k, D.α t k < 1) :
    Antitone (l2_ext D.c D.α α_star) := by
  have hanti := l2_antitoneOn D α_star hα_star_pos hα_star_lt h_equil
    hα_init_pos hα_strict_lt
  intro a b hab
  unfold l2_ext
  exact hanti (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
    (max_le_max_right 0 hab)

theorem l2_ext_nonneg (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (t : ℝ) :
    0 ≤ l2_ext c α α_star t :=
  l2Distance_nonneg c (α (max t 0)) α_star (fun k => le_of_lt (hc k))

theorem l2_ext_eq (c : Fin n → ℝ) (α : ℝ → Fin n → ℝ) (α_star : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    l2_ext c α α_star t = l2Distance c (α t) α_star := by
  unfold l2_ext; rw [max_eq_left ht]

/-! ## End-to-end convergence structure -/

structure EndToEndData (n : ℕ) extends NPoleBarrierData n where
  α_star : Fin n → ℝ
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hc_sum : ∑ k, c k = 1
  hα_init_pos : ∀ k, 0 < α 0 k
  hα_strict_lt : ∀ t, 0 ≤ t → ∀ k, α t k < 1
  comp_lb : ℝ
  equil_lb : ℝ
  hcomp_lb : 0 < comp_lb
  hequil_lb : 0 < equil_lb
  hequil_lb_bound : ∀ k, equil_lb ≤ α_star k
  T₀ : ℝ
  hT₀ : 0 ≤ T₀
  hcomponent_lb : ∀ t, T₀ ≤ t → ∀ k, comp_lb ≤ α t k

/-! ## Multiplicative drops from component persistence -/

theorem end_to_end_drop (D : EndToEndData n)
    (a : ℝ) (ha : D.T₀ ≤ a) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    l2Distance D.c (D.α (a + Δ)) D.α_star ≤
      l2Distance D.c (D.α a) D.α_star *
        exp (-(D.K * D.comp_lb * D.equil_lb) * Δ) :=
  l2_drop_from_bounds D.γ D.c D.K D.α D.α_star
    D.hK D.hγ D.hc D.h_equil D.hα_star_pos D.hα_star_lt
    D.comp_lb D.equil_lb D.hcomp_lb D.hequil_lb D.hequil_lb_bound D.hc_sum
    a Δ (le_trans D.hT₀ ha) hΔ
    (fun t ht1 _ => D.hcomponent_lb t (le_trans ha ht1))
    (fun t ht1 _ => D.hα_strict_lt t (le_trans (le_trans D.hT₀ ha) ht1))
    (fun t ht => D.hα_ode t (lt_of_le_of_lt (le_trans D.hT₀ ha) ht))
    ((l2_continuousOn D.c D.α D.α_star D.hα_cont).mono
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr (le_trans D.hT₀ ha))))

theorem end_to_end_drops (D : EndToEndData n) :
    ∀ T : ℝ, ∃ t, T ≤ t ∧
      l2_ext D.c D.α D.α_star (t + 1) ≤
        exp (-(D.K * D.comp_lb * D.equil_lb)) *
          l2_ext D.c D.α D.α_star t := by
  intro T
  set a := max T D.T₀
  have ha_T₀ : D.T₀ ≤ a := le_max_right _ _
  have ha_nn : 0 ≤ a := le_trans D.hT₀ ha_T₀
  refine ⟨a, le_max_left T D.T₀, ?_⟩
  rw [l2_ext_eq D.c D.α D.α_star (a + 1) (by linarith),
      l2_ext_eq D.c D.α D.α_star a ha_nn]
  have h := end_to_end_drop D a ha_T₀ 1 zero_le_one
  calc l2Distance D.c (D.α (a + 1)) D.α_star
      ≤ l2Distance D.c (D.α a) D.α_star *
          exp (-(D.K * D.comp_lb * D.equil_lb) * 1) := h
    _ = exp (-(D.K * D.comp_lb * D.equil_lb)) *
          l2Distance D.c (D.α a) D.α_star := by ring

/-! ## V → 0 and r → r* -/

theorem end_to_end_V_tendsto (D : EndToEndData n) :
    Tendsto (l2_ext D.c D.α D.α_star) atTop (nhds 0) := by
  set μ := D.K * D.comp_lb * D.equil_lb
  have hμ : 0 < μ := mul_pos (mul_pos D.hK D.hcomp_lb) D.hequil_lb
  set q := exp (-μ)
  have hq0 : 0 ≤ q := le_of_lt (exp_pos _)
  have hq1 : q < 1 := by
    calc exp (-μ) < exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := exp_zero
  exact continuous_barbalat_tendsto (l2_ext D.c D.α D.α_star) q
    (l2_ext_nonneg D.c D.α D.α_star D.hc)
    (l2_ext_antitone D.toNPoleBarrierData D.α_star D.hα_star_pos
      D.hα_star_lt D.h_equil D.hα_init_pos D.hα_strict_lt)
    hq0 hq1 (end_to_end_drops D)

theorem end_to_end_convergence (D : EndToEndData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, D.c k * (D.α t k - D.α_star k)| < ε := by
  intro ε hε
  have hV := end_to_end_V_tendsto D
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
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hcs hV_t) (le_of_lt hε)

theorem end_to_end_r_convergence (D : EndToEndData n) (r_star : ℝ)
    (hr_star : r_star = ∑ k, D.c k * D.α_star k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, D.c k * D.α t k - r_star| < ε := by
  subst hr_star
  intro ε hε
  obtain ⟨T, hT⟩ := end_to_end_convergence D ε hε
  exact ⟨T, fun t ht => by
    have h := hT t ht
    have : ∑ k, D.c k * D.α t k - ∑ k, D.c k * D.α_star k =
        ∑ k, D.c k * (D.α t k - D.α_star k) := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
    rwa [this]⟩

/-! ## Hypothesis elimination: hα_strict_lt from initial data

The UpperBarrier (component_lt_one_uniform) derives α_k(t) < 1 from
α_k(0) < 1 + ODE structure. This eliminates hα_strict_lt from the
EndToEndData structure — it can be derived from α_k(0) < 1. -/

theorem strict_lt_from_init (D : NPoleBarrierData n)
    (hc_sum : ∑ k, D.c k = 1)
    (hα_init_lt_one : ∀ k, D.α 0 k < 1) :
    ∀ t, 0 ≤ t → ∀ k, D.α t k < 1 :=
  fun t ht k => component_lt_one_uniform D k 1 (le_of_eq hc_sum) (hα_init_lt_one k) t ht

/-! ## Full chain from initial conditions

Given NPoleBarrierData + equilibrium + α(0) ∈ (0, 2α*) + γ_max + δ_star,
derive component persistence and construct EndToEndData. -/

structure InitialConditionData (n : ℕ) extends NPoleBarrierData n where
  hn : 0 < n
  α_star : Fin n → ℝ
  γ_max : ℝ
  δ_star : ℝ
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  hγ_max_pos : 0 < γ_max
  hγ_max : ∀ k, γ k ≤ γ_max
  hδ_star_pos : 0 < δ_star
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hc_sum : ∑ k, c k = 1
  hα_init_pos : ∀ k, 0 < α 0 k
  hα_init_lt : ∀ k, α 0 k < 2 * α_star k
  hα_init_lt_one : ∀ k, α 0 k < 1

def InitialConditionData.δ₁ (I : InitialConditionData n) : ℝ :=
  (V_incoherent I.c I.α_star - l2Distance I.c (I.α 0) I.α_star) / 2

theorem InitialConditionData.hV_init (I : InitialConditionData n) :
    l2Distance I.c (I.α 0) I.α_star < V_incoherent I.c I.α_star :=
  V_initial_lt_V_incoherent I.c (I.α 0) I.α_star I.hn I.hc
    I.hα_init_pos I.hα_init_lt I.hα_star_pos

theorem InitialConditionData.hδ₁_pos (I : InitialConditionData n) :
    0 < I.δ₁ := by
  unfold InitialConditionData.δ₁; linarith [I.hV_init]

theorem InitialConditionData.r_persist (I : InitialConditionData n) :
    ∀ t, 0 ≤ t → I.δ₁ ≤ I.toNPoleBarrierData.r t := by
  intro t ht
  set α_ext : ℝ → Fin n → ℝ := fun s => I.α (max s 0)
  have hα_lt : ∀ t, 0 ≤ t → ∀ k, I.α t k < 1 :=
    fun t ht k => component_strict_lt_one I.toNPoleBarrierData I.hα_init_lt_one t ht k
  have hV_anti : Antitone (fun s => l2Distance I.c (α_ext s) I.α_star) :=
    l2_ext_antitone I.toNPoleBarrierData I.α_star I.hα_star_pos
      I.hα_star_lt I.h_equil I.hα_init_pos hα_lt
  have hV_init : l2Distance I.c (α_ext 0) I.α_star < V_incoherent I.c I.α_star := by
    show l2Distance I.c (I.α (max 0 0)) I.α_star < _
    rw [max_self]; exact I.hV_init
  have h := quantitative_persistence I.c α_ext I.α_star 1 one_pos
    (fun k => le_of_lt (I.hα_star_lt k)) I.hc
    (fun s k => I.hα_nn (max s 0) (le_max_right s 0) k)
    (fun s k => I.hα_le (max s 0) (le_max_right s 0) k)
    hV_anti hV_init t ht
  simp only [mul_one] at h
  have h_ext_t : ∀ k, α_ext t k = I.α t k := fun k => by simp [α_ext, max_eq_left ht]
  have h_ext_0 : α_ext 0 = I.α 0 := by simp [α_ext, max_self]
  simp only [h_ext_t, h_ext_0] at h
  exact h

def InitialConditionData.β (I : InitialConditionData n) : ℝ :=
  min (I.K * I.δ₁ / (4 * I.γ_max)) (1 / 2)

theorem InitialConditionData.hβ_pos (I : InitialConditionData n) :
    0 < I.β :=
  lt_min (div_pos (mul_pos I.hK I.hδ₁_pos)
    (mul_pos (by norm_num : (0:ℝ) < 4) I.hγ_max_pos)) (by norm_num)

theorem InitialConditionData.hβ_small (I : InitialConditionData n)
    (k : Fin n) : I.β ≤ I.K * I.δ₁ / (4 * I.γ k) := by
  calc I.β ≤ I.K * I.δ₁ / (4 * I.γ_max) := min_le_left _ _
    _ ≤ I.K * I.δ₁ / (4 * I.γ k) := by
        apply div_le_div_of_nonneg_left (le_of_lt (mul_pos I.hK I.hδ₁_pos))
          (mul_pos (by norm_num : (0:ℝ) < 4) (I.hγ k))
          (mul_le_mul_of_nonneg_left (I.hγ_max k) (by norm_num : (0:ℝ) ≤ 4))

theorem InitialConditionData.hβ_half (I : InitialConditionData n) :
    I.β ≤ 1 / 2 := min_le_right _ _

theorem InitialConditionData.component_persist (I : InitialConditionData n)
    (k : Fin n) :
    ∀ t, escapeTime I.K I.δ₁ I.β ≤ t → I.β ≤ I.α t k := by
  intro t ht
  have h := component_persistence_from_r I.toNPoleBarrierData k I.δ₁ I.β
    I.hδ₁_pos I.hβ_pos (I.hβ_small k) I.hβ_half I.hα_init_pos
    0 le_rfl (fun s hs => I.r_persist s (by linarith)) t (by linarith [ht])
  exact h

def InitialConditionData.toEndToEnd (I : InitialConditionData n) :
    EndToEndData n :=
  { I.toNPoleBarrierData with
    α_star := I.α_star
    hα_star_pos := I.hα_star_pos
    hα_star_lt := I.hα_star_lt
    h_equil := I.h_equil
    hc_sum := I.hc_sum
    hα_init_pos := I.hα_init_pos
    hα_strict_lt := fun t ht k => component_strict_lt_one I.toNPoleBarrierData
      I.hα_init_lt_one t ht k
    comp_lb := I.β
    equil_lb := I.δ_star
    hcomp_lb := I.hβ_pos
    hequil_lb := I.hδ_star_pos
    hequil_lb_bound := I.hα_star_lb
    T₀ := escapeTime I.K I.δ₁ I.β
    hT₀ := le_of_lt (escapeTime_pos I.K I.δ₁ I.β I.hK I.hδ₁_pos I.hβ_pos)
    hcomponent_lb := fun t ht k => I.component_persist k t ht }

theorem initial_condition_convergence (I : InitialConditionData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, I.c k * (I.α t k - I.α_star k)| < ε :=
  end_to_end_convergence I.toEndToEnd

theorem initial_condition_r_convergence (I : InitialConditionData n)
    (r_star : ℝ) (hr_star : r_star = ∑ k, I.c k * I.α_star k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |∑ k, I.c k * I.α t k - r_star| < ε :=
  end_to_end_r_convergence I.toEndToEnd r_star hr_star

end
