/-
  Measure Approximation by Discrete (n-Pole) Measures
  ====================================================
  Approximation of integrals against probability measures by finite weighted sums,
  building on Mathlib's simple function density and Bochner integral infrastructure.

  MATHLIB AVAILABLE (used directly):
  - `SimpleFunc.approxOn` + `tendsto_integral_approxOn_of_measurable`: pointwise and
    L^1 convergence of simple function approximations to any integrable function.
  - `SimpleFunc.integral_eq_sum`: integral of a simple function = finite weighted sum.
  - `integral_dirac`, `integral_sum_dirac_eq_tsum`: integrals against Dirac sums.
  - `Lp.simpleFunc.isDenseEmbedding`: Lp simple functions are dense in Lp.
  - Portmanteau theorem (weak convergence characterizations).
  - Levy-Prokhorov metric on probability measures.

  MATHLIB MISSING (sorry'd below):
  - No Wasserstein / Kantorovich / optimal transport.
  - No direct "approximate a probability measure by n-pole measures" in the measure
    topology (only function-level simple function approximation exists).
  - The gap: converting simple-function-level approximation to a clean n-pole
    (weighted Dirac sum) measure statement requires a small bridge argument.

  0 axioms. Sorrys mark genuine Mathlib gaps.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal Topology MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Simple function integral = finite weighted sum (from Mathlib)

  `SimpleFunc.integral_eq_sum` gives:
    ∫ x, f x ∂μ = ∑ y in f.range, μ.real (f ⁻¹' {y}) • y

  This is already a finite weighted sum over the (finite) range of f.
  We record the specialization to ℝ-valued functions. -/

theorem simpleFunc_integral_eq_finite_sum
    {μ : Measure α} {f : α →ₛ ℝ} (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ y ∈ f.range, μ.real (f ⁻¹' {y}) * y := by
  rw [SimpleFunc.integral_eq_sum f hfi]
  congr 1 with y
  simp [smul_eq_mul]

/-! ## 2. Integral approximation via simple functions (from Mathlib)

  `tendsto_integral_approxOn_of_measurable_of_range_subset` gives:
  For measurable integrable f, the simple function approximations converge in integral.
  Each approximation's integral is a finite sum (by §1). -/

theorem integral_approx_by_simpleFunc_sum
    [PseudoEMetricSpace α] [OpensMeasurableSpace α] [BorelSpace ℝ]
    {μ : Measure α} {f : α → ℝ}
    (hfm : Measurable f) (hfi : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,
      |SimpleFunc.integral (SimpleFunc.approxOn f hfm (Set.range f ∪ {0}) 0
        (by simp) N) μ - ∫ x, f x ∂μ| < ε := by
  have htend := tendsto_integral_approxOn_of_measurable_of_range_subset
    hfm hfi (Set.range f ∪ {0}) le_rfl
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  exact ⟨N, by simpa [Real.dist_eq, abs_sub_comm] using hN N le_rfl⟩

/-! ## 3. Discrete (n-pole) measure: weighted sum of Diracs

  Define the n-pole measure as ∑ k, c_k • δ_{ω_k} and show its integral
  equals the weighted sum. This follows from Mathlib's `integral_sum_dirac_eq_tsum`
  specialized to `Fin n`. -/

def nPoleMeasure {n : ℕ} (ω : Fin n → α) (c : Fin n → ℝ≥0) : Measure α :=
  Measure.sum (fun k => (c k : ℝ≥0∞) • Measure.dirac (ω k))

theorem integral_nPoleMeasure [MeasurableSingletonClass α]
    {n : ℕ} {ω : Fin n → α} {c : Fin n → ℝ≥0} {f : α → ℝ} :
    ∫ x, f x ∂(nPoleMeasure ω c) = ∑ k : Fin n, (c k : ℝ) * f (ω k) := by
  simp only [nPoleMeasure]
  rw [integral_sum_dirac (fun i => ENNReal.coe_ne_top)]
  simp [tsum_fintype, smul_eq_mul]

theorem nPoleMeasure_isProbability [MeasurableSingletonClass α]
    {n : ℕ} (ω : Fin n → α) (c : Fin n → ℝ≥0) (hc_sum : ∑ k, (c k : ℝ≥0∞) = 1) :
    IsProbabilityMeasure (nPoleMeasure ω c) where
  measure_univ := by
    simp only [nPoleMeasure, Measure.sum_apply _ MeasurableSet.univ,
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _)]
    simpa using hc_sum

/-! ## 4. Main approximation theorem: integral against μ ≈ finite weighted sum

  For any integrable f and ε > 0, there exist n, points ω_k, and weights c_k > 0
  with ∑ c_k = 1 such that |∫ f dμ - ∑ c_k f(ω_k)| < ε.

  PROOF STRATEGY (sorry'd — not directly in Mathlib):
  1. Use `SimpleFunc.approxOn` to get g_N with |∫ f dμ - ∫ g_N dμ| < ε/2.
  2. g_N has finite range {y₁,...,y_m} with μ-measurable preimages Aⱼ = g⁻¹(yⱼ).
  3. For each Aⱼ with μ(Aⱼ) > 0, pick a representative ωⱼ ∈ Aⱼ.
  4. Set cⱼ = μ(Aⱼ). Then ∫ g_N dμ = ∑ⱼ cⱼ · g_N(ωⱼ) = ∑ⱼ cⱼ · yⱼ.
  5. Triangle: |∫ f dμ - ∑ cⱼ f(ωⱼ)| ≤ |∫ f dμ - ∫ g_N dμ| + |∫ g_N dμ - ∑ cⱼ f(ωⱼ)|.
     The second term needs |g_N(ωⱼ) - f(ωⱼ)| control, which comes from approxOn pointwise
     convergence. This step requires choosing N large enough for BOTH integral and pointwise
     approximation on the finite set of representatives.

  The gap is that Mathlib provides the pieces but does not assemble this particular statement.
  The `sorry` below marks a genuine proof obligation, not a missing concept. -/

theorem exists_discrete_approx (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      |∫ x, f x ∂μ - ∑ k, c k * f (ω k)| < ε := by
  sorry

/-! ## 5. Bounded continuous function variant

  For bounded continuous f, the approximation follows from the weak topology
  on probability measures. Mathlib has the portmanteau theorem
  (`MeasureTheory.tendsto_of_forall_isOpen_le_liminf`) and Levy-Prokhorov metric,
  but does NOT have:
  - density of finite discrete measures in ProbabilityMeasure ℝ
  - Wasserstein distance or optimal transport

  The following states the cleaner version for bounded continuous functions. -/

theorem exists_discrete_approx_bdd_cont (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf_cont : Continuous f) (B : ℝ) (hf_bdd : ∀ x, |f x| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      |∫ x, f x ∂μ - ∑ k, c k * f (ω k)| < ε := by
  sorry

/-! ## 6. Uniform approximation over a family of test functions

  The version needed for Kuramoto: approximate the integral simultaneously
  for a FINITE family of test functions (e.g., sin and cos components of the
  order parameter). This follows from the single-function version by taking
  the max of the required n's. -/

theorem exists_discrete_approx_finite_family (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℕ} (fs : Fin m → (ℝ → ℝ)) (hfs : ∀ j, Integrable (fs j) μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      ∀ j, |∫ x, fs j x ∂μ - ∑ k, c k * fs j (ω k)| < ε := by
  sorry

/-! ## 7. Bridge to existing NPole infrastructure

  Connect the measure-theoretic approximation to the existing
  NPoleODESolution/NPoleStabilityData structures in the Kuramoto project.
  The key observation: an n-pole Kuramoto system with weights c_k at
  frequencies ω_k corresponds exactly to the discrete measure
  μ_n = ∑ c_k δ_{ω_k}, and the order parameter is r = ∫ α(ω) dμ_n(ω). -/

structure DiscreteApproxData where
  n : ℕ
  ω : Fin n → ℝ
  c : Fin n → ℝ
  hc_pos : ∀ k, 0 ≤ c k
  hc_sum : ∑ k, c k = 1
  μ_target : Measure ℝ
  hμ : IsProbabilityMeasure μ_target

def DiscreteApproxData.approxError (D : DiscreteApproxData) (f : ℝ → ℝ) : ℝ :=
  |∫ x, f x ∂D.μ_target - ∑ k, D.c k * f (D.ω k)|

theorem discrete_approx_exists (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : DiscreteApproxData, D.μ_target = μ ∧ D.approxError f < ε := by
  obtain ⟨n, ω, c, hc_pos, hc_sum, happrox⟩ := exists_discrete_approx μ f hf ε hε
  exact ⟨⟨n, ω, c, hc_pos, hc_sum, μ, inferInstance⟩, rfl, happrox⟩

/-! ## Summary of Mathlib coverage

  AVAILABLE in Mathlib (used above or available for proofs):
  ┌──────────────────────────────────────────────────────────────────┐
  │ SimpleFunc.approxOn              — pointwise simple func approx │
  │ tendsto_approxOn_Lp_eLpNorm      — Lp convergence               │
  │ tendsto_integral_approxOn_of_measurable — integral convergence  │
  │ SimpleFunc.integral_eq_sum       — simple func integral = Σ     │
  │ Lp.simpleFunc.isDenseEmbedding   — Lp density                   │
  │ integral_dirac / integral_sum_dirac_eq_tsum — Dirac integrals   │
  │ integral_fintype / integral_countable — discrete space integrals│
  │ Portmanteau theorem              — weak convergence chars       │
  │ Levy-Prokhorov metric            — metrize weak convergence     │
  │ diracProba / continuous_diracProba — Dirac as ProbabilityMeasure│
  └──────────────────────────────────────────────────────────────────┘

  MISSING from Mathlib (sorry'd):
  ┌──────────────────────────────────────────────────────────────────┐
  │ Density of discrete measures in ProbabilityMeasure X            │
  │ Wasserstein distance / optimal transport                        │
  │ Direct "∫ f dμ ≈ Σ cₖ f(ωₖ)" assembly from simple func pieces │
  └──────────────────────────────────────────────────────────────────┘

  The assembly gap is small: all ingredients exist in Mathlib, but the
  specific "pick representatives from preimages" argument that converts
  simple-function integral approximation into a discrete weighted sum
  needs to be written. This is ~50 lines of real proof, not a deep
  mathematical gap.
-/

end
