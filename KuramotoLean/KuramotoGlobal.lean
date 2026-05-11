/-
  KuramotoGlobal.lean
  ===================
  TARGET: TRUE global stability — remove V(0) < r*² assumption.

  For ANY r(0) > 0, prove r(t) → r*.

  Strategy: The Dietert energy identity dΨ/dt = K|r|² (complex OA) gives
  Ψ non-decreasing. If r → 0, then α → 0 (from ODE), then Ψ → 0,
  contradicting Ψ(t) ≥ Ψ(0) > 0. So r stays positive.

  Once r ≥ r_min > 0, body persistence follows, then V → 0 by our
  existing machinery. Since V is antitone (no initial data restriction),
  V eventually drops below r*², and kuramoto_stability applies.

  Proof chain:
  1. V antitone (already proved, no V(0) restriction)
  2. Energy identity: Ψ = ∫ -log(1-α²) g dω, dΨ/dt ≥ Kr² - 2∫γα²/(1-α²)g dω
  3. Ψ stays positive → α can't all decay → r stays positive
  4. r ≥ r_min → body persistence (existing)
  5. Body persistence → V → 0 (existing)
  6. V → 0 → r → r* (existing)
-/

import KuramotoLean.KuramotoFinal

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The energy functional Ψ -/

/-- The Dietert energy functional Ψ(t) = ∫ -log(1-α(ω,t)²) g(ω) dω.
    Measures total "locking energy" — increases as oscillators synchronize. -/
def psiEnergy (α : Ω → ℝ → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, -Real.log (1 - α ω t ^ 2) ∂μ

/-- Ψ is well-defined and non-negative when α ∈ (0,1). -/
theorem psiEnergy_nonneg
    (α : Ω → ℝ → ℝ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ psiEnergy α μ t := by
  unfold psiEnergy
  apply integral_nonneg
  intro ω
  have h := hα_inv ω t ht
  have h1 : 0 < 1 - α ω t ^ 2 := by nlinarith [h.1, h.2]
  have h2 : 1 - α ω t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω t)]
  simp only [neg_nonneg]
  exact neg_nonneg.mpr (Real.log_nonpos h1.le h2)

/-- Ψ(0) > 0 when r(0) > 0 (some α(ω,0) is bounded away from 0). -/
theorem psiEnergy_pos_of_r_pos [IsProbabilityMeasure μ]
    (α : Ω → ℝ → ℝ) (r : ℝ → ℝ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hr_pos : 0 < r 0) :
    0 < psiEnergy α μ 0 := by
  unfold psiEnergy
  sorry -- need: r(0) > 0 → ∃ set of positive measure where α(ω,0) ≥ δ > 0
         -- → -log(1-α²) ≥ -log(1-δ²) > 0 on that set → integral > 0

/-! ## Derivative of Ψ -/

/-- The pointwise derivative of -log(1-α²) along the OA flow.
    d/dt[-log(1-α²)] = 2αα̇/(1-α²) = -2γα²/(1-α²) + Krα -/
theorem psi_pointwise_deriv
    (γ_ω K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ) (t : ℝ)
    (hα_pos : 0 < α t) (hα_lt : α t < 1)
    (hα_ode : HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t) :
    HasDerivAt (fun s => -Real.log (1 - α s ^ 2))
      (-2 * γ_ω * (α t) ^ 2 / (1 - (α t) ^ 2) + K * r t * α t) t := by
  sorry -- chain rule: d/dt[-log(1-α²)] = 2αα̇/(1-α²), then expand α̇

/-- The integral form: dΨ/dt = Kr² - 2∫γα²/(1-α²) g dω.
    In the complex OA (iω instead of γ), the γ term vanishes and dΨ/dt = K|r|² ≥ 0.
    In the real scalar OA, dΨ/dt = Kr² - 2∫γα²/(1-α²) g dω (may be negative). -/
theorem psi_deriv_formula [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (t : ℝ)
    (hK : 0 < K) (ht : 0 < t)
    (hα_ode : ∀ ω, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω, 0 < α ω t ∧ α ω t < 1)
    (h_sc : r t = ∫ ω, α ω t ∂μ)
    (hα_int : Integrable (fun ω => α ω t) μ)
    (hψ_int : Integrable (fun ω => -Real.log (1 - α ω t ^ 2)) μ)
    (hγα_int : Integrable (fun ω => γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2)) μ) :
    HasDerivAt (psiEnergy α μ)
      (K * (r t) ^ 2 - 2 * ∫ ω, γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ) t := by
  sorry -- Leibniz for Ψ + substitute the pointwise derivative

/-! ## The global stability argument -/

/-- **r stays positive** — from the energy identity.
    If r(0) > 0, then r(t) ≥ r_min > 0 for all t.

    Argument (by contradiction):
    - Ψ(0) > 0 (from r(0) > 0)
    - If inf r(t) = 0, pick t_n with r(t_n) → 0
    - From ODE: α̇ ≈ -γα when r ≈ 0, so α decays exponentially
    - Eventually α → 0, so Ψ → 0
    - But V antitone gives... (need energy argument)

    For the real scalar OA, this requires bounding the dissipation term
    2∫γα²/(1-α²) g dω. Under finite first moment, this is bounded by
    2∫γ g dω · sup(α²/(1-α²)) which is finite. -/
theorem r_stays_positive [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω) (hγ_int : Integrable γ μ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hr_pos : 0 < r 0) :
    ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t := by
  sorry -- THE KEY GAP: energy identity → r persistence

/-- **TRUE GLOBAL STABILITY** — the original Kuramoto problem.
    For ANY r(0) > 0, r(t) → r*.

    Removes the V(0) < r*² assumption from kuramoto_stability. -/
theorem kuramoto_global [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
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
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    -- THE ONLY INITIAL CONDITION: r(0) > 0
    (hr_pos : 0 < r 0) :
    Tendsto r atTop (nhds r_star) := by
  -- Step 1: r stays positive (from energy identity)
  obtain ⟨r_min, hr_min_pos, hr_bound⟩ := r_stays_positive γ K r α hK hγ_pos hγ_int
    hr_cont hr_bdd hα_ode hα_inv h_sc hα_int hr_pos
  -- Step 2: V is antitone (no V(0) restriction needed)
  -- V(t) is decreasing, so eventually V(t) < r*²
  -- (because V(t) → L and if L ≥ r*² we get a contradiction from body persistence)
  sorry -- Wire: r_min → body persistence → V → 0 → r → r*
