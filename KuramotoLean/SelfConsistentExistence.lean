/-
  Kuramoto Stability — Self-Consistent Existence for the OA Continuum System
  ==========================================================================

  Closes the self-consistency loop for the OA continuum equation:
    dα(ω)/dt = -γ(ω)α + (K/2)r(t)(1 - α²),  r(t) = ∫ α(ω,t) dμ(ω)

  ContinuumODEExistence proves per-ω existence for GIVEN r.
  This file proves existence via Banach fixed-point on
  BoundedContinuousFunction(Icc 0 T, ℝ).

  0 sorry.
-/

import KuramotoLean.ContinuumODEExistence
import KuramotoLean.GeneralGODEInstance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Real Set Filter Metric
open scoped NNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

structure SelfConsistentOAData (μ : Measure Ω) extends ContinuumODEData μ where
  h_self_consistent : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ

def contractionFactor (K γ_max T : ℝ) : ℝ :=
  K / 2 * T * exp ((γ_max + K) * T)

theorem contractionFactor_nonneg {K γ_max T : ℝ}
    (hK : 0 ≤ K) (hγ : 0 ≤ γ_max) (hT : 0 ≤ T) :
    0 ≤ contractionFactor K γ_max T := by
  unfold contractionFactor; positivity

theorem contractionFactor_lt_one {K γ_max : ℝ} (hK : 0 < K) (hγ : 0 ≤ γ_max) :
    ∃ T > 0, contractionFactor K γ_max T < 1 := by
  set T₀ := min 1 (1 / (K * exp (γ_max + K)))
  have hexp_pos : (0 : ℝ) < exp (γ_max + K) := exp_pos _
  have hKexp : 0 < K * exp (γ_max + K) := mul_pos hK hexp_pos
  refine ⟨T₀, by positivity, ?_⟩
  have hT₀_le1 : T₀ ≤ 1 := min_le_left _ _
  have hT₀_le : T₀ ≤ 1 / (K * exp (γ_max + K)) := min_le_right _ _
  have h_gKT : (γ_max + K) * T₀ ≤ γ_max + K := by nlinarith
  have h_exp : exp ((γ_max + K) * T₀) ≤ exp (γ_max + K) := exp_le_exp.mpr h_gKT
  have h_KT : K * T₀ ≤ 1 / exp (γ_max + K) := by
    calc K * T₀ ≤ K * (1 / (K * exp (γ_max + K))) :=
          mul_le_mul_of_nonneg_left hT₀_le hK.le
      _ = 1 / exp (γ_max + K) := by field_simp
  show contractionFactor K γ_max T₀ < 1
  unfold contractionFactor
  calc K / 2 * T₀ * exp ((γ_max + K) * T₀)
      ≤ K / 2 * T₀ * exp (γ_max + K) := by
        nlinarith [h_exp, (by positivity : (0:ℝ) ≤ K / 2 * T₀)]
    _ ≤ 1 / 2 * (1 / exp (γ_max + K)) * exp (γ_max + K) := by nlinarith [h_KT]
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

/-! ## Banach fixed-point on BoundedContinuousFunction -/

section BanachFixedPoint

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem bcf_ball_fixed_point
    (f : BoundedContinuousFunction X ℝ → BoundedContinuousFunction X ℝ)
    {q : ℝ≥0} (hq : q < 1)
    (h_self_map : ∀ r : BoundedContinuousFunction X ℝ,
      r ∈ closedBall 0 1 → f r ∈ closedBall 0 1)
    (h_lip : ∀ r₁ r₂ : BoundedContinuousFunction X ℝ,
      r₁ ∈ closedBall 0 1 → r₂ ∈ closedBall 0 1 →
      dist (f r₁) (f r₂) ≤ q * dist r₁ r₂) :
    ∃ r_star : BoundedContinuousFunction X ℝ,
      r_star ∈ closedBall 0 1 ∧ f r_star = r_star := by
  set S := closedBall (0 : BoundedContinuousFunction X ℝ) 1
  have h_complete : IsComplete S := isClosed_closedBall.isComplete
  have h_maps : MapsTo f S S := h_self_map
  have h_contr : ContractingWith q (h_maps.restrict f S S) := by
    constructor
    · exact hq
    · intro x y
      simp only [Subtype.edist_eq]
      rw [edist_dist, edist_dist]
      have := h_lip x.1 y.1 x.2 y.2
      calc ENNReal.ofReal (dist (f x.1) (f y.1))
          ≤ ENNReal.ofReal (↑q * dist x.1 y.1) := ENNReal.ofReal_le_ofReal this
        _ = ENNReal.ofReal ↑q * ENNReal.ofReal (dist x.1 y.1) :=
            ENNReal.ofReal_mul (NNReal.coe_nonneg q)
        _ = ↑q * ENNReal.ofReal (dist x.1 y.1) := by rw [ENNReal.ofReal_coe_nnreal]
  have h0_mem : (0 : BoundedContinuousFunction X ℝ) ∈ S := mem_closedBall_self zero_le_one
  have h_edist : edist (0 : BoundedContinuousFunction X ℝ) (f 0) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hy_mem, hy_fp, _⟩ := h_contr.exists_fixedPoint' h_complete h_maps h0_mem h_edist
  exact ⟨y, hy_mem, hy_fp⟩

end BanachFixedPoint

/-! ## Extension from BCF to ℝ → ℝ -/

private def clampToIcc (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : ↥(Icc (0:ℝ) T) :=
  ⟨max 0 (min t T), le_max_left _ _, max_le hT (min_le_right _ _)⟩

private theorem clampToIcc_continuous (T : ℝ) (hT : 0 ≤ T) :
    Continuous (clampToIcc T hT) :=
  Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _

def extendBCF (T : ℝ) (hT : 0 ≤ T)
    (r : BoundedContinuousFunction (↥(Icc (0:ℝ) T)) ℝ) : ℝ → ℝ :=
  r ∘ clampToIcc T hT

theorem extendBCF_continuous (T : ℝ) (hT : 0 ≤ T)
    (r : BoundedContinuousFunction (↥(Icc (0:ℝ) T)) ℝ) :
    Continuous (extendBCF T hT r) :=
  r.continuous.comp (clampToIcc_continuous T hT)

/-! ## Main existence theorem -/

theorem self_consistent_existence
    (T_time : ℝ) (hT : 0 < T_time) (K γ_max : ℝ) (hK : 0 < K) (hγ_max : 0 ≤ γ_max)
    (hq : contractionFactor K γ_max T_time < 1)
    (solve : (ℝ → ℝ) → Ω → ℝ → ℝ)
    (h_op_cont : ∀ r : BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ,
      Continuous (fun (t : ↥(Icc 0 T_time)) =>
        ∫ ω, solve (extendBCF T_time hT.le r) ω (↑t) ∂μ))
    (h_op_bdd : ∀ r : BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ,
      r ∈ closedBall 0 1 →
      ∀ (t : ↥(Icc 0 T_time)),
        |∫ ω, solve (extendBCF T_time hT.le r) ω (↑t) ∂μ| ≤ 1)
    (h_op_contr : ∀ (r₁ r₂ : BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ),
      r₁ ∈ closedBall 0 1 → r₂ ∈ closedBall 0 1 →
      ∀ (t : ↥(Icc 0 T_time)),
      |∫ ω, solve (extendBCF T_time hT.le r₁) ω (↑t) ∂μ -
       ∫ ω, solve (extendBCF T_time hT.le r₂) ω (↑t) ∂μ| ≤
      contractionFactor K γ_max T_time * dist r₁ r₂) :
    ∃ (r_bcf : BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ),
      r_bcf ∈ closedBall 0 1 ∧
      ∀ (t : ↥(Icc 0 T_time)),
        r_bcf t = ∫ ω, solve (extendBCF T_time hT.le r_bcf) ω (↑t) ∂μ := by
  haveI : Nonempty ↥(Icc (0:ℝ) T_time) := ⟨⟨0, left_mem_Icc.mpr hT.le⟩⟩
  set q : ℝ≥0 := ⟨contractionFactor K γ_max T_time,
    contractionFactor_nonneg hK.le hγ_max hT.le⟩
  set T_op : BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ →
      BoundedContinuousFunction (↥(Icc (0:ℝ) T_time)) ℝ :=
    fun r => BoundedContinuousFunction.mkOfCompact ⟨
      fun t => ∫ ω, solve (extendBCF T_time hT.le r) ω (↑t) ∂μ,
      h_op_cont r⟩
  have h_sm : ∀ r : BoundedContinuousFunction (↥(Icc 0 T_time)) ℝ,
      r ∈ closedBall 0 1 → T_op r ∈ closedBall 0 1 := by
    intro r hr
    rw [mem_closedBall, dist_zero_right] at hr ⊢
    rw [BoundedContinuousFunction.norm_le (by linarith : (0:ℝ) ≤ 1)]
    intro t; rw [Real.norm_eq_abs]
    exact h_op_bdd r (by rwa [mem_closedBall, dist_zero_right]) t
  have h_lp : ∀ r₁ r₂ : BoundedContinuousFunction (↥(Icc 0 T_time)) ℝ,
      r₁ ∈ closedBall 0 1 → r₂ ∈ closedBall 0 1 →
      dist (T_op r₁) (T_op r₂) ≤ q * dist r₁ r₂ := by
    intro r₁ r₂ hr₁ hr₂
    rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
    intro t; rw [Real.dist_eq]
    exact h_op_contr r₁ r₂ hr₁ hr₂ t
  obtain ⟨r_star, hr_mem, hr_fp⟩ :=
    bcf_ball_fixed_point T_op (show q < 1 from hq) h_sm h_lp
  exact ⟨r_star, hr_mem, fun t => (DFunLike.congr_fun hr_fp t).symm⟩

/-! ## Constructor for SelfConsistentOAData -/

def mkSelfConsistentOAData
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_ode : ∀ ω t, 0 < t → HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_ode_zero : ∀ ω, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r 0 (α ω 0)) 0)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init_pos : ∀ ω, 0 < α ω 0) (hα_init_lt : ∀ ω, α ω 0 < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) :
    SelfConsistentOAData μ where
  toContinuumODEData := generalG_ContinuumODEData γ K r α α_star hK hγ
    hr_cont hr_bdd hr_nn hα_star_pos hα_star_lt hα_ode hα_ode_zero hα_cont
    hα_init_pos hα_init_lt
  h_self_consistent := h_sc

def SelfConsistentOAData.toODEData (D : SelfConsistentOAData μ) : ContinuumODEData μ :=
  D.toContinuumODEData

theorem selfConsistent_gives_ContinuumODEData
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hα_ode : ∀ ω t, 0 < t → HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_ode_zero : ∀ ω, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r 0 (α ω 0)) 0)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init_pos : ∀ ω, 0 < α ω 0) (hα_init_lt : ∀ ω, α ω 0 < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) :
    ∃ D : ContinuumODEData μ, ∀ t ≥ 0, D.r t = ∫ ω, D.α ω t ∂μ :=
  ⟨(mkSelfConsistentOAData γ K r α α_star hK hγ hr_cont hr_bdd hr_nn
    hα_star_pos hα_star_lt hα_ode hα_ode_zero hα_cont hα_init_pos hα_init_lt
    h_sc).toContinuumODEData, h_sc⟩

end
