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

  PROOF APPROACH (all theorems closed, 0 sorry):
  The key insight is that ∫ f dμ lies in the closure of the convex hull of
  range(f), by Convex.integral_mem. Elements of the convex hull are finite
  convex combinations ∑ cₖ f(ωₖ), so approximation follows from
  Metric.mem_closure_iff + mem_convexHull_iff_exists_fintype.

  0 axioms, 0 sorry.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.SpecificCodomains.Pi

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
    {μ : Measure α} {f : SimpleFunc α ℝ} (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ y ∈ f.range, μ.real (f ⁻¹' {y}) * y := by
  rw [SimpleFunc.integral_eq_sum f hfi]
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
      |(SimpleFunc.approxOn f hfm (Set.range f ∪ {0}) 0
        (by simp) N).integral μ - ∫ x, f x ∂μ| < ε := by
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

  PROOF: ∫ f dμ ∈ closure(convexHull ℝ (range f)) by Convex.integral_mem.
  By Metric.mem_closure_iff, approximate within ε by y ∈ convexHull ℝ (range f).
  By mem_convexHull_iff_exists_fintype, y = ∑ wᵢ • zᵢ with zᵢ ∈ range f.
  Pick ωₖ with f(ωₖ) = zₖ. Then ∑ cₖ f(ωₖ) = y ≈ ∫ f dμ. -/

private lemma simpleFunc_integral_as_finset_sum (μ : Measure ℝ)
    (g : SimpleFunc ℝ ℝ) (hgi : Integrable g μ) :
    ∫ x, g x ∂μ = ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y := by
  rw [SimpleFunc.integral_eq_sum g hgi]
  simp [smul_eq_mul]

private lemma simpleFunc_weights_nonneg (μ : Measure ℝ) (g : SimpleFunc ℝ ℝ) (y : ℝ) :
    0 ≤ μ.real (g ⁻¹' {y}) :=
  measureReal_nonneg

private lemma simpleFunc_weights_sum_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : SimpleFunc ℝ ℝ) :
    ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) = 1 := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]
  rw [g.sum_range_measure_preimage_singleton]
  simp [measure_univ]

private lemma mem_range_iff_preimage_nonempty (g : SimpleFunc ℝ ℝ) (y : ℝ) :
    y ∈ g.range → (g ⁻¹' {y}).Nonempty := by
  intro hy
  rw [SimpleFunc.mem_range] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx ▸ Set.mem_preimage.mpr (Set.mem_singleton _)⟩

private lemma simpleFunc_integral_approx_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : SimpleFunc ℝ ℝ) (hgi : Integrable g μ) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      ∫ x, g x ∂μ = ∑ k, c k * g (ω k) := by
  set n := g.range.card
  set e := g.range.orderEmbOfFin rfl with he_def
  have he_mem : ∀ k, e k ∈ g.range := fun k => Finset.orderEmbOfFin_mem _ rfl k
  set rep : Fin n → ℝ := fun k => (mem_range_iff_preimage_nonempty g (e k) (he_mem k)).some
  have hrep : ∀ k, g (rep k) = e k := by
    intro k
    have := (mem_range_iff_preimage_nonempty g (e k) (he_mem k)).some_mem
    exact Set.mem_preimage.mp this
  set c : Fin n → ℝ := fun k => μ.real (g ⁻¹' {e k})
  have he_inj : Function.Injective e := e.injective
  have he_image : Finset.image e Finset.univ = g.range :=
    Finset.image_orderEmbOfFin_univ g.range rfl
  have reindex : ∀ (h : ℝ → ℝ),
      ∑ y ∈ g.range, h y = ∑ k : Fin n, h (e k) := by
    intro h
    calc ∑ y ∈ g.range, h y
        = ∑ y ∈ Finset.image e Finset.univ, h y := by rw [he_image]
      _ = ∑ k ∈ Finset.univ, h (e k) :=
          Finset.sum_image (fun a _ b _ hab => he_inj hab)
      _ = ∑ k : Fin n, h (e k) := by rfl
  refine ⟨n, rep, c, fun k => measureReal_nonneg, ?_, ?_⟩
  · rw [← simpleFunc_weights_sum_one μ g, reindex]
  · rw [simpleFunc_integral_as_finset_sum μ g hgi, reindex]
    congr 1 with k
    rw [hrep]

theorem exists_discrete_approx (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      |∫ x, f x ∂μ - ∑ k, c k * f (ω k)| < ε := by
  have hmem : (∫ x, f x ∂μ) ∈ closure (convexHull ℝ (Set.range f)) := by
    apply Convex.integral_mem (Convex.closure (convex_convexHull ℝ _)) isClosed_closure
    · exact Eventually.of_forall fun x =>
        subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x))
    · exact hf
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy_mem, hy_dist⟩ := hmem ε hε
  rw [mem_convexHull_iff_exists_fintype] at hy_mem
  obtain ⟨ι, _, w, z, hw_pos, hw_sum, hz_range, hz_eq⟩ := hy_mem
  let n := Fintype.card ι
  let e := Fintype.equivFin ι
  have hzr : ∀ i, ∃ x, f x = z i := fun i => Set.mem_range.mp (hz_range i)
  let ω : Fin n → ℝ := fun k => (hzr (e.symm k)).choose
  let c : Fin n → ℝ := fun k => w (e.symm k)
  have hω_spec (k : Fin n) : f (ω k) = z (e.symm k) := by
    exact (hzr (e.symm k)).choose_spec
  have hc_sum : ∑ k, c k = 1 := by
    change ∑ k : Fin n, w (e.symm k) = 1
    rw [Equiv.sum_comp e.symm w]; exact hw_sum
  have happrox : |∫ x, f x ∂μ - ∑ k, c k * f (ω k)| < ε := by
    have key : y = ∑ k : Fin n, c k * f (ω k) := by
      have h1 : y = ∑ i : ι, w i • z i := by linarith [hz_eq]
      rw [h1, ← Equiv.sum_comp e.symm (fun i => w i • z i)]
      congr 1 with k
      simp only [c, ω, smul_eq_mul]
      rw [hω_spec k]
    rw [key] at hy_dist; rw [dist_comm, Real.dist_eq, abs_sub_comm] at hy_dist; exact hy_dist
  exact ⟨n, ω, c, fun k => hw_pos _, hc_sum, happrox⟩

/-! ## 5. Bounded continuous function variant

  For bounded continuous f, the approximation follows from the weak topology
  on probability measures. Mathlib has the portmanteau theorem
  (`MeasureTheory.tendsto_of_forall_isOpen_le_liminf`) and Levy-Prokhorov metric,
  but does NOT have:
  - density of finite discrete measures in ProbabilityMeasure ℝ
  - Wasserstein distance or optimal transport

  This follows directly from exists_discrete_approx since bounded continuous
  functions are integrable w.r.t. probability measures. -/

theorem exists_discrete_approx_bdd_cont (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf_cont : Continuous f) (B : ℝ) (hf_bdd : ∀ x, |f x| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      |∫ x, f x ∂μ - ∑ k, c k * f (ω k)| < ε := by
  apply exists_discrete_approx μ f _ ε hε
  exact Integrable.of_bound hf_cont.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf_bdd x)

/-! ## 6. Uniform approximation over a family of test functions

  The version needed for Kuramoto: approximate the integral simultaneously
  for a FINITE family of test functions (e.g., sin and cos components of the
  order parameter). Uses the same convex hull argument applied to the
  vector-valued function F(x) = (f₁(x),...,fₘ(x)) in (Fin m → ℝ). -/

theorem exists_discrete_approx_finite_family (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℕ} (fs : Fin m → (ℝ → ℝ)) (hfs : ∀ j, Integrable (fs j) μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℝ),
      (∀ k, 0 ≤ c k) ∧ (∑ k, c k = 1) ∧
      ∀ j, |∫ x, fs j x ∂μ - ∑ k, c k * fs j (ω k)| < ε := by
  let F : ℝ → (Fin m → ℝ) := fun x j => fs j x
  have hF : Integrable F μ := integrable_pi_iff.mpr (fun j => hfs j)
  have hmem : (∫ x, F x ∂μ) ∈ closure (convexHull ℝ (Set.range F)) :=
    Convex.integral_mem (Convex.closure (convex_convexHull ℝ _)) isClosed_closure
      (Eventually.of_forall fun x => subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x)))
      hF
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy_mem, hy_dist⟩ := hmem ε hε
  rw [mem_convexHull_iff_exists_fintype] at hy_mem
  obtain ⟨ι, _, w, zv, hw_pos, hw_sum, hz_range, hz_eq⟩ := hy_mem
  have hzr : ∀ i, ∃ x, F x = zv i := fun i => Set.mem_range.mp (hz_range i)
  let nn := Fintype.card ι
  let ee := Fintype.equivFin ι
  let ωf : Fin nn → ℝ := fun k => (hzr (ee.symm k)).choose
  let cf : Fin nn → ℝ := fun k => w (ee.symm k)
  have hωf_spec (k : Fin nn) : F (ωf k) = zv (ee.symm k) := (hzr (ee.symm k)).choose_spec
  have hcf_sum : ∑ k, cf k = 1 := by
    change ∑ k : Fin nn, w (ee.symm k) = 1
    rw [Equiv.sum_comp ee.symm w]; exact hw_sum
  have key : y = ∑ k : Fin nn, cf k • zv (ee.symm k) := by
    conv_lhs => rw [hz_eq.symm]
    exact (Equiv.sum_comp ee.symm (fun i => w i • zv i)).symm
  have happrox : ∀ j, |∫ x, fs j x ∂μ - ∑ k, cf k * fs j (ωf k)| < ε := by
    intro j
    have h_sum_j : (∑ k : Fin nn, cf k • zv (ee.symm k)) j =
        ∑ k : Fin nn, cf k * fs j (ωf k) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      congr 1 with k
      congr 1
      exact (congr_fun (hωf_spec k) j).symm
    have h_y_j : y j = ∑ k : Fin nn, cf k * fs j (ωf k) := by rw [key]; exact h_sum_j
    have h_int_j : (∫ x, F x ∂μ) j = ∫ x, fs j x ∂μ := by
      rw [eval_integral (fun i => hfs i) j]
    have h_dist_j : |(∫ x, F x ∂μ) j - y j| < ε := by
      calc |(∫ x, F x ∂μ) j - y j|
          = ‖((∫ x, F x ∂μ) - y) j‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖(∫ x, F x ∂μ) - y‖ := norm_le_pi_norm _ j
        _ = dist (∫ x, F x ∂μ) y := (dist_eq_norm _ _).symm
        _ < ε := hy_dist
    rwa [h_int_j, h_y_j] at h_dist_j
  exact ⟨nn, ωf, cf, fun k => hw_pos _, hcf_sum, happrox⟩

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

  ALL THEOREMS PROVED (0 sorry) using:
  ┌──────────────────────────────────────────────────────────────────┐
  │ Convex.integral_mem             — integral ∈ closed convex hull │
  │ mem_convexHull_iff_exists_fintype — convex hull = finite combos │
  │ Metric.mem_closure_iff          — ε-approximation in closure    │
  │ integrable_pi_iff               — Pi-type integrability         │
  │ eval_integral                   — component of Pi integral      │
  │ norm_le_pi_norm                 — sup norm ≥ component norm     │
  └──────────────────────────────────────────────────────────────────┘
-/

end
