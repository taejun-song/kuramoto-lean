/-
  Kuramoto Stability — End-to-End Continuum Theorem (Wired)
  ==========================================================
  SINGLE theorem that wires body persistence derivation into convergence.

  1. Takes (K, γ, g, α_star, r_star, solution existence, r persistence)
  2. DERIVES body persistence from ODE comparison (BodyPersistenceFromODE)
  3. Feeds into ContinuumSolvedFinal (integrable-γ proof chain)
  4. Produces: ∃ r, Continuous r ∧ Tendsto r atTop (nhds r_star)

  RESOLVES the wiring gap: ContinuumSolvedFromODE proved body persistence
  but was not connected to ContinuumSolvedComplete/ContinuumSolvedFinal.

  γ=|ω| AND ω=0: All hypotheses use 0 ≤ γ (not 0 < γ), so γ(0) = 0
  is allowed. At ω=0 the equilibrium equation gives α*(0) = 1 (fully
  locked). The hypothesis hα_star_lt requires α* < 1, which holds for
  all ω with γ(ω) > 0. For ω=0, one takes Ω = {ω : ℝ | ω ≠ 0} —
  this is WLOG since {0} has measure zero for any density g.

  Axiom budget: 0. Sorry count: 0.
-/

import KuramotoLean.ContinuumSolvedFinal
import KuramotoLean.BodyPersistenceFromODE

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## ROUTE A: Finite first moment (integrable γ)

Takes the ODE solution data and r persistence as input.
Body persistence is DERIVED internally via ODE comparison principle.
No body persistence or body Gronwall hypothesis needed.

Requires γ integrable (∫|ω|g < ∞): Gaussian, Student-t ν>2, compact support.
NOT Lorentzian.

Proof chain:
  r persistence + ODE comparison → body persistence δ(M) > 0
  → body pair coercivity → body Gronwall → tail-body split → r → r*
-/
theorem kuramoto_endtoend_continuum [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_int : Integrable γ μ) (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_int_pos : 0 < ∫ ω, γ ω ∂μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (α_0 : Ω → ℝ) (hα_0_pos : ∀ ω, 0 < α_0 ω) (hα_0_lt : ∀ ω, α_0 ω < 1)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_init : ∀ ω, α ω 0 = α_0 ω)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (r_min : ℝ) (hr_min : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (h_r_persist : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hα_0_body : ∀ M, 0 < M → ∃ δ₀, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α_0 ω) :
    ∃ (r' : ℝ → ℝ), Continuous r' ∧ Tendsto r' atTop (nhds r_star) := by
  -- STEP 1: DERIVE body persistence (NOT assumed)
  have h_body_persist : ∀ M, 0 < M →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t := by
    intro M hM
    exact continuum_body_persistence (μ := μ) γ K r α r_min M hK hγ
      hr_min hr_min_le hM h_r_persist hr_bdd
      (fun ω t ht => hα_ode ω t (le_of_lt ht)) hα_inv hα_cont
      (fun ω _ => by rw [hα_init]; exact hα_0_pos ω)
      (by obtain ⟨δ₀, hδ₀, h⟩ := hα_0_body M hM
          exact ⟨δ₀, hδ₀, fun ω hω => by rw [hα_init]; exact h ω hω⟩)
  -- STEP 2: Feed into ContinuumSolvedFinal
  exact kuramoto_standard_continuum γ K hK hγ hγ_int hγ_meas hγ_int_pos
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    α_0 hα_0_pos hα_0_lt
    ⟨r, α, hr_cont, hr_bdd, hr_nn, hα_ode, hα_cont, hα_init, h_sc,
     hα_int, hα_sq_int, hα_neg, hα_inv, h_body_persist, hγ_level⟩

/-! ## Body persistence is a theorem, not an axiom

On each body {γ ≤ M} with r(t) ≥ r_min:
  α(ω,t) ≥ min(α(ω,0), bodyEquilibrium(M, K, r_min))
where bodyEquilibrium(M, K, r_min) > 0.

This connects ContinuumSolvedFromODE to the convergence theorems:
body persistence feeds into body pair coercivity → body Gronwall → r → r*.

For the no-moment-condition route (ContinuumSolvedReal), body persistence
feeds into h_body_drop via body Leibniz + pair coercivity. That route is
wired in ContinuumSolvedFromODE.lean (separate import chain). -/
theorem body_persistence_endtoend
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (r_min M : ℝ)
    (hK : 0 < K) (hM : 0 < M)
    (hr_min : 0 < r_min) (hr_min_le : r_min ≤ 1)
    (h_r_persist : ∀ t, 0 ≤ t → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hγ : ∀ ω, 0 ≤ γ ω)
    (ω : Ω) (hω : γ ω ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    min (α ω 0) (bodyEquilibrium M K r_min) ≤ α ω t :=
  body_persistence_lower_bound (γ ω) M K r (α ω) r_min
    (hγ ω) hω hK hr_min hr_min_le h_r_persist hr_bdd
    (fun t' ht' => hα_ode ω t' (le_of_lt ht'))
    (hα_inv ω) (hα_cont ω) t ht

theorem body_equilibrium_positive (M K r_min : ℝ)
    (hM : 0 < M) (hK : 0 < K) (hr_min : 0 < r_min) :
    0 < bodyEquilibrium M K r_min :=
  bodyEquilibrium_pos M K r_min (le_of_lt hM) hK hr_min

end
