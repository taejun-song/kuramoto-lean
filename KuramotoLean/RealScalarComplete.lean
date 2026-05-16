/-
  Real Scalar OA Complete Theorem
  ================================
  Wires the full 228-file proof chain into a single self-contained theorem:
    V' ≤ 0 → V antitone → r stays positive → body persistence → r → r*

  NO body persistence hypothesis — derived internally from V(0) < r*².
  0 sorry, 0 axioms, 0 opaques.
-/

import KuramotoLean.KuramotoGlobal

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem real_scalar_complete [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ) (r_star : ℝ)
    (hK : 0 < K)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_int_pos : 0 < ∫ ω, γ ω ∂μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hV0_small : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ < r_star ^ 2) :
    Tendsto r atTop (nhds r_star) := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  -- Step 1: r_stays_positive from V(0) < r*² via V antitone + Cauchy-Schwarz
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq]
    have h_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ := integral_nonneg (fun ω => (hα_star_pos ω).le)
    rcases h_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      have := (integral_eq_zero_iff_of_nonneg (fun ω => (hα_star_pos ω).le) hαs_int).mp h.symm
      obtain ⟨ω, hω⟩ := this.exists; simp at hω; linarith [hα_star_pos ω]
  obtain ⟨r_min, hr_min_pos, hr_floor⟩ := r_stays_positive (μ := μ) γ K r α
    hK hγ_pos hγ_int hγ_level hr_cont hr_bdd hα_ode hα_cont hα_neg hα_inv h_sc hα_int
    α_star r_star hr_star_pos
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil hα_sq_int hV0_small
  -- Step 2: body persistence from r floor via continuum_body_persistence
  have h_body_persist : ∀ M, 0 < M → ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
    intro M hM
    have hr_le : r_min ≤ 1 := le_trans (hr_floor 0 le_rfl) (le_of_abs_le (hr_bdd 0))
    exact @continuum_body_persistence Ω _ μ _ γ K r α r_min M hK hγ hr_min_pos hr_le hM
      hr_floor hr_bdd (fun ω t ht => hα_ode ω t (le_of_lt ht)) hα_inv hα_cont
      (fun ω _ => (hα_inv ω 0 le_rfl).1)
      (h_init_body M hM)
  -- Step 3: final convergence
  exact kuramoto_standard_tendsto γ K hK hγ hγ_int hγ_meas hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_neg hα_inv
    h_body_persist hγ_level

end
