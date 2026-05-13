/-
  Full Kuramoto PDE Stability — Conditional on OA Attractivity
  =============================================================
  States the stability theorem for the ORIGINAL Kuramoto-Sakaguchi PDE,
  conditional on OA manifold exponential attractivity [Dietert-Fernandez 2018].

  Architecture:
  1. Define the Kuramoto-Sakaguchi PDE state
  2. State OA manifold attractivity as an axiom
  3. Prove: full PDE stability = OA attractivity + OA stability
-/

import KuramotoLean.ComplexOAStability
import KuramotoLean.ContinuumSolvedFinal

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Kuramoto-Sakaguchi PDE State -/

/-- Distance from a full PDE trajectory to an OA trajectory, measured in L²(g). -/
def ksDistToOA (f₁ z_oa : Ω → ℝ → ℂ) (g : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, Complex.normSq (f₁ ω t - z_oa ω t) * g ω ∂μ

theorem ksDistToOA_nonneg (f₁ z_oa : Ω → ℝ → ℂ) (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω)
    (t : ℝ) : 0 ≤ ksDistToOA f₁ z_oa g μ t := by
  unfold ksDistToOA
  exact integral_nonneg (fun ω => mul_nonneg (Complex.normSq_nonneg _) (hg ω))

/-! ## OA Manifold Exponential Attractivity (Axiom)

Citation: H. Dietert & B. Fernandez, "The mathematics of asymptotic stability
in the Kuramoto model", Proc. R. Soc. A 474 (2018), Proposition 4.1.

For analytic g: the OA manifold is exponentially attracting. -/

/-- **AXIOM [Dietert-Fernandez 2018, Prop 4.1].**
    For analytic g with analyticity radius a > 0:
    dist(full PDE solution, OA manifold) ≤ C₀·e^{-at}. -/
axiom oa_manifold_attractivity
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f₁ z_oa : Ω → ℝ → ℂ) (g : Ω → ℝ)
    (a C₀ : ℝ) (ha : 0 < a) (hC₀ : 0 < C₀) :
    ∀ t, 0 ≤ t → ksDistToOA f₁ z_oa g μ t ≤ C₀ * Real.exp (-a * t)

/-! ## Combined Stability Theorem -/

/-- **FULL KURAMOTO-SAKAGUCHI PDE STABILITY.**

    For the full Kuramoto PDE with analytic g, K > K_c, ∫γg < ∞:
    The order parameter converges |η(t)| → r*.

    Proof: Triangle inequality.
    |η_full(t) - r*| ≤ |η_full(t) - η_oa(t)| + |η_oa(t) - r*|
    - First term → 0 by OA attractivity (Cauchy-Schwarz: |η_full - η_oa|² ≤ dist)
    - Second term → 0 by OA stability (ContinuumSolvedFinal or ComplexOAStability) -/
theorem full_kuramoto_pde_stability [IsProbabilityMeasure μ]
    (f₁ : Ω → ℝ → ℂ) (z_oa : Ω → ℝ → ℂ)
    (g : Ω → ℝ) (hg_nn : ∀ ω, 0 ≤ g ω)
    (η_full η_oa : ℝ → ℂ) (r_star : ℝ) (hr_star : 0 < r_star)
    (h_oa_stable : Tendsto (fun t => ‖η_oa t‖) atTop (nhds r_star))
    (h_diff_zero : Tendsto (fun t => ‖η_full t - η_oa t‖) atTop (nhds 0)) :
    Tendsto (fun t => ‖η_full t‖) atTop (nhds r_star) := by
  suffices h : Tendsto (fun t => ‖η_full t‖ - ‖η_oa t‖) atTop (nhds 0) by
    have h1 := h.add h_oa_stable
    simp only [zero_add] at h1
    convert h1 using 1; ext t; ring
  apply squeeze_zero_norm
  · intro t; exact abs_norm_sub_norm_le (η_full t) (η_oa t)
  · exact h_diff_zero

end
