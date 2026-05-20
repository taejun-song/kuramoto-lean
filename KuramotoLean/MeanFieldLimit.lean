/-
  Mean-Field Limit for Kuramoto Oscillators
  ==========================================
  Skeleton for the propagation of chaos: N-particle empirical measure
  converges to the continuum Vlasov-type PDE as N → ∞.

  APPROACH (Tier 1 — deterministic Gronwall):
  The sin coupling is 1-Lipschitz, so the N-particle ODE is Lipschitz
  in the ℓ¹ metric. Two solutions starting ε-close remain ε·e^(Kt)-close.
  This is the finite-N backbone of the mean-field limit.

  MATHLIB USED:
  - `norm_sub_le` for Lipschitz bounds on sin
  - `GronwallBound` from `Mathlib.Analysis.ODE.Gronwall`
  - `Finset.sum` for particle averages

  STATUS: skeleton with sorry — establishes the theorem structure.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Finset Real MeasureTheory
open scoped BigOperators

noncomputable section

namespace MeanFieldLimit

/-! ## 1. N-particle Kuramoto system -/

/-- The velocity field for particle i in the N-particle Kuramoto system. -/
def particleVelocity (N : ℕ) (K : ℝ) (ω : Fin N → ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  ω i + (K / N) * ∑ j : Fin N, sin (θ j - θ i)

/-- The N-particle Kuramoto ODE: θ̇ᵢ = ωᵢ + (K/N) Σⱼ sin(θⱼ - θᵢ). -/
def kuramotoODE (N : ℕ) (K : ℝ) (ω : Fin N → ℝ) (θ : Fin N → ℝ) : Fin N → ℝ :=
  particleVelocity N K ω θ

/-! ## 2. Lipschitz property of the coupling -/

/-- sin is 1-Lipschitz. -/
theorem sin_lipschitz : LipschitzWith 1 sin := lipschitzWith_sin

/-- The mean-field coupling (1/N)Σ sin(θⱼ - θᵢ) is Lipschitz in the ℓ¹ sense. -/
theorem coupling_lipschitz (N : ℕ) (hN : 0 < N) (K : ℝ) (hK : 0 ≤ K)
    (ω : Fin N → ℝ) (θ₁ θ₂ : Fin N → ℝ) :
    ∑ i : Fin N, |particleVelocity N K ω θ₁ i - particleVelocity N K ω θ₂ i|
      ≤ 2 * K * ∑ i : Fin N, |θ₁ i - θ₂ i| := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hKN : 0 ≤ K / ↑N := div_nonneg hK hN'.le
  have step1 : ∀ i : Fin N,
      |particleVelocity N K ω θ₁ i - particleVelocity N K ω θ₂ i| ≤
        K / ↑N * ∑ j, (|θ₁ j - θ₂ j| + |θ₁ i - θ₂ i|) := by
    intro i
    change |ω i + K / ↑N * ∑ j, sin (θ₁ j - θ₁ i) -
          (ω i + K / ↑N * ∑ j, sin (θ₂ j - θ₂ i))| ≤ _
    have : ω i + K / ↑N * ∑ j, sin (θ₁ j - θ₁ i) -
        (ω i + K / ↑N * ∑ j, sin (θ₂ j - θ₂ i)) =
        K / ↑N * (∑ j, sin (θ₁ j - θ₁ i) - ∑ j, sin (θ₂ j - θ₂ i)) := by ring
    rw [this, abs_mul, abs_of_nonneg hKN]
    gcongr
    rw [← Finset.sum_sub_distrib]
    calc |∑ j : Fin N, (sin (θ₁ j - θ₁ i) - sin (θ₂ j - θ₂ i))|
        ≤ ∑ j : Fin N, |sin (θ₁ j - θ₁ i) - sin (θ₂ j - θ₂ i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin N, |(θ₁ j - θ₁ i) - (θ₂ j - θ₂ i)| :=
          Finset.sum_le_sum fun j _ => abs_sin_sub_sin_le _ _
      _ ≤ ∑ j : Fin N, (|θ₁ j - θ₂ j| + |θ₁ i - θ₂ i|) :=
          Finset.sum_le_sum fun j _ => by
            have : (θ₁ j - θ₁ i) - (θ₂ j - θ₂ i) = (θ₁ j - θ₂ j) - (θ₁ i - θ₂ i) := by ring
            rw [this]
            exact (abs_sub_le (θ₁ j - θ₂ j) 0 (θ₁ i - θ₂ i)).trans (by simp [abs_sub_comm])
  calc ∑ i, |particleVelocity N K ω θ₁ i - particleVelocity N K ω θ₂ i|
      ≤ ∑ i, K / ↑N * ∑ j, (|θ₁ j - θ₂ j| + |θ₁ i - θ₂ i|) :=
        Finset.sum_le_sum fun i _ => step1 i
    _ = K / ↑N * ∑ i, ∑ j, (|θ₁ j - θ₂ j| + |θ₁ i - θ₂ i|) := by
        rw [← Finset.mul_sum]
    _ = K / ↑N * ∑ i : Fin N, (∑ j : Fin N, |θ₁ j - θ₂ j| + ↑N * |θ₁ i - θ₂ i|) := by
        congr 1; apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = K / ↑N * (↑N * ∑ i : Fin N, |θ₁ i - θ₂ i| + ↑N * ∑ i : Fin N, |θ₁ i - θ₂ i|) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
            Finset.mul_sum]
    _ = 2 * K * ∑ i : Fin N, |θ₁ i - θ₂ i| := by
        field_simp; ring

/-! ## 3. Gronwall estimate: finite-N synchronization bound -/

/-- If two solutions of the N-particle ODE start ε-close in ℓ¹,
    they remain ε·e^(2Kt)-close for all t ≥ 0. -/
theorem finite_N_gronwall_bound (N : ℕ) (hN : 0 < N) (K : ℝ) (hK : 0 ≤ K)
    (ω : Fin N → ℝ)
    (θ₁ θ₂ : ℝ → Fin N → ℝ)
    (hθ₁ : ∀ t i, HasDerivAt (fun s => θ₁ s i) (kuramotoODE N K ω (θ₁ t) i) t)
    (hθ₂ : ∀ t i, HasDerivAt (fun s => θ₂ s i) (kuramotoODE N K ω (θ₂ t) i) t)
    (ε : ℝ) (hε : ∑ i : Fin N, |θ₁ 0 i - θ₂ 0 i| ≤ ε)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ i : Fin N, |θ₁ t i - θ₂ t i| ≤ ε * exp (2 * K * t) := by
  set u : ℝ → ℝ := fun s => ∑ i : Fin N, |θ₁ s i - θ₂ s i|
  set u' : ℝ → ℝ := fun s =>
    ∑ i : Fin N, |kuramotoODE N K ω (θ₁ s) i - kuramotoODE N K ω (θ₂ s) i|
  have h_cont_comp : ∀ i : Fin N, Continuous (fun s => θ₁ s i - θ₂ s i) :=
    fun i => (Differentiable.continuous (fun x => (hθ₁ x i).sub (hθ₂ x i) |>.differentiableAt))
  have hu_cont : ContinuousOn u (Set.Icc 0 t) :=
    (continuous_finset_sum _ fun i _ => (h_cont_comp i).abs).continuousOn
  have h_diff : ∀ x (i : Fin N), HasDerivAt (fun s => θ₁ s i - θ₂ s i)
      (kuramotoODE N K ω (θ₁ x) i - kuramotoODE N K ω (θ₂ x) i) x :=
    fun x i => (hθ₁ x i).sub (hθ₂ x i)
  have hu_liminf : ∀ x ∈ Set.Ico 0 t, ∀ r, u' x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), (z - x)⁻¹ * (u z - u x) < r := by
    intro x _ r hr
    have h_slope_lim : Filter.Tendsto
        (fun z => ∑ i : Fin N, |(z - x)⁻¹ * ((θ₁ z i - θ₂ z i) - (θ₁ x i - θ₂ x i))|)
        (nhdsWithin x (Set.Ioi x)) (nhds (u' x)) := by
      change Filter.Tendsto _ _ (nhds (∑ i : Fin N,
        |kuramotoODE N K ω (θ₁ x) i - kuramotoODE N K ω (θ₂ x) i|))
      apply tendsto_finset_sum
      intro i _
      have h_right := (hasDerivAt_iff_tendsto_slope_left_right.mp (h_diff x i)).2
      have h_eq : ∀ z ≠ x, slope (fun s => θ₁ s i - θ₂ s i) x z =
          (z - x)⁻¹ * ((θ₁ z i - θ₂ z i) - (θ₁ x i - θ₂ x i)) := by
        intro z hz; simp [slope_def_field, div_eq_inv_mul]
      exact (h_right.congr' (eventually_nhdsWithin_of_forall fun z hz => h_eq z (ne_of_gt hz))).abs
    have h_bound : ∀ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (u z - u x) ≤
        ∑ i : Fin N, |(z - x)⁻¹ * ((θ₁ z i - θ₂ z i) - (θ₁ x i - θ₂ x i))| := by
      filter_upwards [self_mem_nhdsWithin] with z (hz : x < z)
      have hzx : 0 < z - x := sub_pos.mpr hz
      rw [← Finset.sum_sub_distrib]
      calc (z - x)⁻¹ * ∑ i, (|θ₁ z i - θ₂ z i| - |θ₁ x i - θ₂ x i|)
          ≤ (z - x)⁻¹ * ∑ i, |(θ₁ z i - θ₂ z i) - (θ₁ x i - θ₂ x i)| :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _ => abs_sub_abs_le_abs_sub _ _)
              (le_of_lt (inv_pos.mpr hzx))
        _ = ∑ i, |(z - x)⁻¹ * ((θ₁ z i - θ₂ z i) - (θ₁ x i - θ₂ x i))| := by
            rw [Finset.mul_sum]
            congr 1; ext i
            rw [abs_mul, abs_of_pos (inv_pos.mpr hzx)]
    have h_ev : ∀ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (u z - u x) < r := by
      filter_upwards [h_bound, h_slope_lim.eventually (Iio_mem_nhds hr)] with z hle hlt
      exact lt_of_le_of_lt hle hlt
    exact h_ev.frequently
  have hu_bound : ∀ x ∈ Set.Ico (0 : ℝ) t, u' x ≤ (2 * K) * u x + 0 := by
    intro x _; rw [add_zero]; exact coupling_lipschitz N hN K hK ω (θ₁ x) (θ₂ x)
  have hgw := le_gronwallBound_of_liminf_deriv_right_le hu_cont hu_liminf hε hu_bound t
    (Set.right_mem_Icc.mpr ht)
  rwa [sub_zero, gronwallBound_ε0] at hgw

/-! ## 4. Empirical measure and weak convergence (Tier 2 skeleton) -/

/-- The empirical measure of N particles on ℝ (or 𝕋). -/
def empiricalMeasure (N : ℕ) (θ : Fin N → ℝ) : Measure ℝ :=
  (1 / (N : ENNReal)) • Measure.sum (fun i : Fin N => Measure.dirac (θ i))

/-- The continuum velocity field v(θ,t) = ω + K ∫ sin(θ'-θ) f(θ') dθ'. -/
def continuumVelocity (K : ℝ) (ω : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ω + K * ∫ x, sin (x - θ) * f x

/-! ## 5. Wasserstein distance (Tier 2 — definitions only) -/

/-- A coupling of two measures: a measure on the product with correct marginals. -/
structure Coupling (μ ν : Measure ℝ) where
  joint : Measure (ℝ × ℝ)
  marginal_left : joint.map Prod.fst = μ
  marginal_right : joint.map Prod.snd = ν

/-- The 1-Wasserstein distance between two probability measures (inf over couplings). -/
def wasserstein1 (μ ν : Measure ℝ) : ℝ :=
  ⨅ (c : Coupling μ ν), ∫ p : ℝ × ℝ, |p.1 - p.2| ∂c.joint

/-! ## 6. Mean-field limit theorem (Tier 3 — statement only) -/

/-- The mean-field limit: empirical measure of the N-particle system converges
    to the continuum solution in Wasserstein distance.

    Deterministic version: if W₁(μ_N(0), f₀) ≤ ε, then
    W₁(μ_N(t), f(t)) ≤ ε · e^(Kt) for all t ∈ [0,T]. -/
theorem mean_field_limit_deterministic (N : ℕ) (hN : 0 < N) (K : ℝ) (hK : 0 ≤ K)
    (ω : Fin N → ℝ) (θ : ℝ → Fin N → ℝ)
    (f : ℝ → Measure ℝ)
    (hθ_sol : ∀ t i, HasDerivAt (fun s => θ s i) (particleVelocity N K ω (θ t) i) t)
    (hf_sol : True) -- placeholder: f solves the continuity equation
    (ε : ℝ) (hε : wasserstein1 (empiricalMeasure N (θ 0)) (f 0) ≤ ε)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    wasserstein1 (empiricalMeasure N (θ t)) (f t) ≤ ε * exp (K * t) := by
  sorry

/-! ## 7. Corollary: convergence as N → ∞ (probabilistic, Tier 3) -/

/-- For i.i.d. initial conditions drawn from f₀, the expected Wasserstein distance
    between empirical measure and continuum solution vanishes as N → ∞.
    This is the propagation of chaos result. -/
theorem propagation_of_chaos
    (K : ℝ) (hK : 0 ≤ K) (T : ℝ) (hT : 0 < T)
    (f₀ : Measure ℝ) [IsProbabilityMeasure f₀] :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      True := by -- placeholder: full statement needs probability space
  intro ε hε; exact ⟨1, fun _ _ => trivial⟩

end MeanFieldLimit
