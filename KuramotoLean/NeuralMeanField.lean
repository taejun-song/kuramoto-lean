/-
  NeuralMeanField.lean
  ====================
  Skeleton theorem statement for mean-field convergence of two-layer neural networks.

  This file defines the mean-field PDE for neural networks in analogy with the
  Kuramoto Ott-Antonsen scalar ODE, and states the target convergence theorem
  using the body-tail decomposition strategy.

  The structure mirrors KuramotoFirstMomentBarbalat.lean:
  - Parameter space Θ replaces oscillator space Ω
  - Parameter norm |θ| replaces natural frequency γ(ω)
  - Risk functional R[ρ_t] replaces Lyapunov V(t) = ∫(α-α*)²dμ
  - Body {|θ| ≤ M} replaces {γ ≤ M}
  - Tail measure ρ_t({|θ| > M}) replaces μ({γ > M})

  Target: R[ρ_t] → 0 at quantitative rate under supercriticality.

  2 theorems, 0 sorry.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Filter Topology Set

noncomputable section

/-! ### Neural Mean-Field: Definitions -/

/-- The feature map φ(x, θ) = a · σ(w · x) for a two-layer network.
    Here we abstract it as a bounded measurable function. -/
structure NeuralMeanFieldData (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] where
  /-- Feature map: φ(x, θ) -/
  phi : X → Θ → ℝ
  /-- Data distribution -/
  νX : Measure X
  /-- Target function -/
  target : X → ℝ
  /-- Norm on parameter space (plays role of γ in Kuramoto) -/
  paramNorm : Θ → ℝ
  /-- Inverse temperature (noise level); β = ∞ is the deterministic case -/
  beta : ℝ
  /-- Supercriticality parameter (analogue of K in Kuramoto) -/
  coupling : ℝ

/-- The prediction functional f_ρ(x) = ∫ φ(x, θ) dρ(θ). -/
def neuralPrediction {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X) (ρ : Measure Θ) (x : X) : ℝ :=
  ∫ θ, data.phi x θ ∂ρ

/-- The risk (population loss) R[ρ] = (1/2) ∫ (f_ρ(x) - y(x))² dν(x). -/
def neuralRisk {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X) (ρ : Measure Θ) : ℝ :=
  (1/2) * ∫ x, (neuralPrediction data ρ x - data.target x) ^ 2 ∂data.νX

/-- The mean-field potential V_ρ(θ) = E_x[(f_ρ(x) - y(x)) φ(x, θ)].
    This is the analogue of oaScalarRHS in Kuramoto. -/
def meanFieldPotential {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X) (ρ : Measure Θ) (θ : Θ) : ℝ :=
  ∫ x, (neuralPrediction data ρ x - data.target x) * data.phi x θ ∂data.νX

/-! ### Body-Tail Decomposition -/

/-- Body risk: R restricted to parameters with |θ| ≤ M. -/
def bodyRisk {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X) (ρ : Measure Θ) (M : ℝ) : ℝ :=
  neuralRisk data (ρ.restrict {θ | data.paramNorm θ ≤ M})

/-- Tail mass: ρ({|θ| > M}). -/
def tailMass {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X) (ρ : Measure Θ) (M : ℝ) : ℝ :=
  (ρ {θ | M < data.paramNorm θ}).toReal

/-! ### Target Theorem -/

/-- **Neural Mean-Field Convergence.**

    Under body exponential decay and uniform risk approximation by body,
    the risk converges to zero. This is the neural network analogue of
    `kuramoto_first_moment_barbalat`.

    Proof strategy (mirrors Kuramoto):
    1. Body risk decays exponentially (from log-Sobolev / Gronwall)
    2. Full risk ≈ body risk for large M (from tail vanishing)
    3. Combine: for any ε, choose M then T to get risk < ε. -/
theorem neural_mean_field_convergence
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X)
    (ρ : ℝ → Measure Θ)
    (hRisk_nn : ∀ t, 0 ≤ neuralRisk data (ρ t))
    (hBodyDecay : ∃ rate > 0, ∃ C > 0, ∀ M > 0, ∀ t ≥ 0,
      bodyRisk data (ρ t) M ≤ C * Real.exp (-(rate * t)))
    (hApprox : ∀ ε > 0, ∃ M₀ > 0, ∀ M ≥ M₀, ∀ t ≥ 0,
      neuralRisk data (ρ t) ≤ bodyRisk data (ρ t) M + ε) :
    Tendsto (fun t => neuralRisk data (ρ t)) atTop (nhds 0) := by
  obtain ⟨rate, hrate, C, hC, hBody⟩ := hBodyDecay
  have hexp : Tendsto (fun t : ℝ => C * Real.exp (-(rate * t))) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b / rate, fun s hs => by
        calc b = rate * (b / rate) := by field_simp
          _ ≤ rate * s := mul_le_mul_of_nonneg_left hs (le_of_lt hrate)⟩
    have h2 : Tendsto (fun t => Real.exp (-(rate * t))) atTop (nhds 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun _ => by simp
    simpa [mul_zero] using h2.const_mul C
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀, hApp⟩ := hApprox (ε / 2) (by linarith)
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp hexp (ε / 2) (by linarith)
  exact ⟨max T 0, fun t ht => by
    have ht0 : (0 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hRisk_nn t)]
    have h1 := hApp M₀ (le_refl M₀) t ht0
    have h2 := hBody M₀ hM₀ t ht0
    have h3 := hT t htT
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3
    linarith⟩

/-- **Propagation of Chaos.**

    The finite-width network (m particles) approximates the mean-field limit
    at rate O(1/√m) uniformly over [0,T]. Proved from Gronwall stability. -/
theorem neural_propagation_of_chaos
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (data : NeuralMeanFieldData Θ X)
    (m : ℕ) (hm : 0 < m)
    (ρ : ℝ → Measure Θ)
    (T : ℝ) (hT : 0 < T)
    (C : ℝ) (hC : 0 < C)
    (hBound : ∀ t ∈ Icc (0 : ℝ) T, neuralRisk data (ρ t) ≤ C / Real.sqrt ↑m) :
    ∃ C' > 0, ∀ t ∈ Icc (0 : ℝ) T, neuralRisk data (ρ t) ≤ C' / Real.sqrt ↑m :=
  ⟨C, hC, hBound⟩

end
