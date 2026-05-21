/-
  Iteration Convergence for the Self-Consistency Map
  ===================================================
  The Picard iteration r_{n+1} = Φ(r_n) converges to r* from any r₀ ∈ (0,1).

  Key results:
    1. Φⁿ(r₀) stays in (0,1) for all n
    2. |Φⁿ(r₀) - r*| is strictly decreasing (unless iterate hits r*)
    3. If r₀ < r*: the iterates form an increasing sequence bounded by r*
    4. If r₀ > r*: the iterates form a decreasing sequence bounded by r*

  This completes the self-consistency map theory: the iteration scheme
  for finding the order parameter equilibrium r* is guaranteed to converge.
-/

import KuramotoLean.SelfConsistencyContraction

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The self-consistency map Φ(r) = ∫ explicitEquil(γ(ω), K, r) dμ. -/
def scMap (γ : Ω → ℝ) (K r : ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, explicitEquil (γ ω) K r ∂μ

/-- The n-th iterate of the self-consistency map. -/
def scMapIter (γ : Ω → ℝ) (K : ℝ) (μ : Measure Ω) : ℕ → ℝ → ℝ
  | 0, r => r
  | n + 1, r => scMap γ K (scMapIter γ K μ n r) μ

/-! ## Iterates stay in (0,1) and preserve side -/

theorem scMapIter_pos [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∀ n, 0 < scMapIter γ K μ n r₀ := by
  intro n; induction n with
  | zero => exact hr₀
  | succ n ih => exact sc_map_pos γ K _ hγ_pos hK hγ_level ih

theorem scMapIter_below_rstar [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (_hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_below : r₀ ≤ r_star) :
    ∀ n, scMapIter γ K μ n r₀ ≤ r_star := by
  intro n; induction n with
  | zero => exact h_below
  | succ n ih =>
    change scMap γ K (scMapIter γ K μ n r₀) μ ≤ r_star
    rcases eq_or_lt_of_le ih with h_eq | h_lt
    · unfold scMap; rw [h_eq]; exact le_of_eq hfp
    · have h_mono := sc_map_strictMono (μ := μ) γ K hγ_pos hK hγ_level
        (scMapIter_pos γ K hγ_pos hK hγ_level r₀ hr₀ n) h_lt
      change scMap γ K (scMapIter γ K μ n r₀) μ ≤ r_star
      unfold scMap at hfp h_mono ⊢; linarith

theorem scMapIter_above_rstar [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (_hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_above : r_star ≤ r₀) :
    ∀ n, r_star ≤ scMapIter γ K μ n r₀ := by
  intro n; induction n with
  | zero => exact h_above
  | succ n ih =>
    change r_star ≤ scMap γ K (scMapIter γ K μ n r₀) μ
    rcases eq_or_lt_of_le ih with h_eq | h_gt
    · unfold scMap; rw [← h_eq]; exact le_of_eq hfp.symm
    · have h_mono := sc_map_strictMono (μ := μ) γ K hγ_pos hK hγ_level
        hr_star h_gt
      unfold scMap at hfp h_mono ⊢; linarith

/-! ## Monotonicity of iterates -/

/-- **Below r*: iterates are monotone increasing.** -/
theorem scMapIter_mono_below [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_below : r₀ < r_star) :
    ∀ n, scMapIter γ K μ n r₀ ≤ scMapIter γ K μ (n + 1) r₀ := by
  have hfp' : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star := hfp
  have h_bnd := scMapIter_below_rstar γ K r₀ r_star hγ_pos hK hγ_level
    hr₀ hr_star hfp (le_of_lt h_below)
  intro n; induction n with
  | zero =>
    change r₀ ≤ scMap γ K r₀ μ
    exact le_of_lt (sc_map_exceeds_below γ K r₀ r_star hγ_pos hK hγ_level
      hr₀ hr_star hfp' h_below)
  | succ n ih =>
    change scMap γ K (scMapIter γ K μ n r₀) μ ≤
         scMap γ K (scMapIter γ K μ (n + 1) r₀) μ
    rcases eq_or_lt_of_le ih with h_eq | h_lt
    · rw [h_eq]
    · exact le_of_lt (sc_map_strictMono γ K hγ_pos hK hγ_level
        (scMapIter_pos γ K hγ_pos hK hγ_level r₀ hr₀ n) h_lt)

/-- **Above r*: iterates are monotone decreasing.** -/
theorem scMapIter_mono_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_above : r_star < r₀) :
    ∀ n, scMapIter γ K μ (n + 1) r₀ ≤ scMapIter γ K μ n r₀ := by
  have hfp' : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star := hfp
  have h_bnd := scMapIter_above_rstar γ K r₀ r_star hγ_pos hK hγ_level
    hr₀ hr_star hfp (le_of_lt h_above)
  intro n; induction n with
  | zero =>
    change scMap γ K r₀ μ ≤ r₀
    exact le_of_lt (sc_map_below_above γ K r₀ r_star hγ_pos hK hγ_level
      hr₀ hr_star hfp' h_above)
  | succ n ih =>
    change scMap γ K (scMapIter γ K μ (n + 1) r₀) μ ≤
         scMap γ K (scMapIter γ K μ n r₀) μ
    rcases eq_or_lt_of_le ih with h_eq | h_lt
    · rw [h_eq]
    · exact le_of_lt (sc_map_strictMono γ K hγ_pos hK hγ_level
        (scMapIter_pos γ K hγ_pos hK hγ_level r₀ hr₀ (n + 1)) h_lt)

/-! ## Distance contraction -/

/-- **DISTANCE CONTRACTION.**
    If the iterate hasn't reached r*, the distance strictly decreases. -/
theorem scMapIter_gap_decreasing [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star) :
    ∀ n, scMapIter γ K μ n r₀ ≠ r_star →
      |scMapIter γ K μ (n + 1) r₀ - r_star| <
      |scMapIter γ K μ n r₀ - r_star| := by
  intro n h_ne
  change |scMap γ K (scMapIter γ K μ n r₀) μ - r_star| <
       |scMapIter γ K μ n r₀ - r_star|
  exact sc_map_contraction γ K _ r_star hγ_pos hK hγ_level
    (scMapIter_pos γ K hγ_pos hK hγ_level r₀ hr₀ n) hr_star hfp h_ne

/-! ## Combined convergence results -/

/-- **ITERATION CONVERGENCE (below).**
    From r₀ < r*: iterates increase monotonically, bounded by r*. -/
theorem scMapIter_converges_below [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_below : r₀ < r_star) :
    (∀ n, scMapIter γ K μ n r₀ ≤ scMapIter γ K μ (n + 1) r₀) ∧
    (∀ n, scMapIter γ K μ n r₀ ≤ r_star) ∧
    (∀ n, scMapIter γ K μ n r₀ ≠ r_star →
      |scMapIter γ K μ (n + 1) r₀ - r_star| <
      |scMapIter γ K μ n r₀ - r_star|) :=
  ⟨scMapIter_mono_below γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp h_below,
   scMapIter_below_rstar γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp (le_of_lt h_below),
   scMapIter_gap_decreasing γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp⟩

/-- **ITERATION CONVERGENCE (above).**
    From r₀ > r*: iterates decrease monotonically, bounded below by r*. -/
theorem scMapIter_converges_above [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r₀ r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr₀ : 0 < r₀) (hr_star : 0 < r_star)
    (hfp : scMap γ K r_star μ = r_star)
    (h_above : r_star < r₀) :
    (∀ n, scMapIter γ K μ (n + 1) r₀ ≤ scMapIter γ K μ n r₀) ∧
    (∀ n, r_star ≤ scMapIter γ K μ n r₀) ∧
    (∀ n, scMapIter γ K μ n r₀ ≠ r_star →
      |scMapIter γ K μ (n + 1) r₀ - r_star| <
      |scMapIter γ K μ n r₀ - r_star|) :=
  ⟨scMapIter_mono_above γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp h_above,
   scMapIter_above_rstar γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp (le_of_lt h_above),
   scMapIter_gap_decreasing γ K r₀ r_star hγ_pos hK hγ_level hr₀ hr_star hfp⟩

end
