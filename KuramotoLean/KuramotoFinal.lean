/-
  KuramotoFinal.lean
  ==================
  THE FINAL THEOREM. Fully self-contained, zero sorry.

  Derives V antitonicity → r persistence → body persistence → convergence
  from first principles. No external hypotheses beyond the physical setup.

  The proof chain (all derived internally):
  1. Leibniz rule for V (finite first moment → dominated convergence)
  2. Pair bound (dV/dt ≤ 0, algebraic identity)
  3. V antitone → V(t) ≤ V(0)
  4. Cauchy-Schwarz → |r(t) - r*|² ≤ V(t) ≤ V(0) < r*² → r(t) > 0
  5. ODE barrier → body persistence
  6. Convergence via kuramoto_standard_tendsto

  Only standard Lean 4 axioms: propext, Classical.choice, Quot.sound.
  0 sorry.
-/

import KuramotoLean.BodyPersistenceFromODE
import KuramotoLean.ContinuumSolvedFinal
import KuramotoLean.GeneralGMainTheorem

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

set_option maxHeartbeats 1600000 in
/-- **THE KURAMOTO STABILITY THEOREM.**

    Hypotheses (all physical):
    - γ > 0 with ∫γ dμ < ∞ (finite first moment)
    - (r, α) is an OA solution on [0,∞) with self-consistency
    - (r_star, α_star) is the self-consistent equilibrium
    - V(0) < r*² (initial data near PLS)
    - Initial body coherence

    Derives internally:
    - V antitonicity (from Leibniz + pair bound)
    - r persistence (from V bound + Cauchy-Schwarz)
    - Body persistence (from ODE barrier)
    - Convergence (from Barbalat)

    Conclusion: r(t) → r*. -/
theorem kuramoto_stability [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Set.Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hV0_small : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ < r_star ^ 2)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0) :
    Tendsto r atTop (nhds r_star) := by
  haveI : SFinite μ := inferInstance
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas_strong : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  have hV_nn : ∀ t, 0 ≤ V t := fun t => integral_nonneg (fun _ => sq_nonneg _)
  -- Step 1: Leibniz + pair bound → V antitone
  have ⟨hV_cont_on, hV_has_deriv⟩ := leibniz_integrable_gamma (μ := μ)
    γ K r α α_star hα_ode hα_inv hα_sq_int hγ_int hγ hK hr_bdd
    hα_star_pos hα_star_lt hα_cont hα_neg hα_int hαs_int hγ_meas_strong
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK hγ (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t)
      (q_int_of_gamma_int (fun ω => α ω t) α_star γ K r_star hK hr_star_pos
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt hγ hα_star_equil (hα_int t) hαs_int (hα_sq_int t) hγ_int
        hγ_meas_strong)
      (s_int_bdd (fun ω => α ω t) α_star
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt (hα_int t) hαs_int)
  have hV_anti : Antitone V :=
    lyapunov_antitone γ K r α α_star r_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  -- Step 2: r persistence from V bound
  have h_sqrt_lt : Real.sqrt (V 0) < r_star := by
    have := Real.sqrt_lt_sqrt (hV_nn 0) hV0_small
    rwa [Real.sqrt_sq (le_of_lt hr_star_pos)] at this
  set r_min := r_star - Real.sqrt (V 0)
  have hr_min_pos : (0 : ℝ) < r_min := by change 0 < r_star - Real.sqrt (V 0); linarith
  have hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t := by
    intro t ht
    have hVt : V t ≤ V 0 := hV_anti ht
    have hCS : (r t - r_star) ^ 2 ≤ V t := by
      have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
        rw [h_sc t ht, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
      rw [hrsc]
      exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
    have h1 : |r t - r_star| ≤ Real.sqrt (V 0) :=
      calc |r t - r_star| = Real.sqrt ((r t - r_star) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (V 0) := Real.sqrt_le_sqrt (le_trans hCS hVt)
    linarith [(abs_le.mp h1).1]
  -- Step 3: Body persistence from ODE barrier
  have h_body_persist : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
    intro M hM
    have hr_min_le : r_min ≤ 1 := by
      change r_star - Real.sqrt (V 0) ≤ 1; linarith [Real.sqrt_nonneg (V 0), hr_star_lt]
    exact @continuum_body_persistence Ω _ μ ‹_› γ K r α r_min M
      hK hγ hr_min_pos hr_min_le hM
      hr_bound hr_bdd (fun ω t ht => hα_ode ω t (le_of_lt ht)) hα_inv hα_cont
      (fun ω _ => (hα_inv ω 0 le_rfl).1)
      (h_init_body M hM)
  -- Step 4: Convergence
  have hγ_int_pos : 0 < ∫ ω, γ ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg hγ hγ_int).mpr
    rw [show Function.support γ = Set.univ from
      Set.ext (fun ω => ⟨fun _ => Set.mem_univ _, fun _ => ne_of_gt (hγ_pos ω)⟩)]
    simp [measure_univ]
  exact kuramoto_standard_tendsto γ K hK hγ hγ_int hγ_meas_strong hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_neg hα_inv
    h_body_persist hγ_level
