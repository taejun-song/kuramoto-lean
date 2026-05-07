/-
  FirstMomentTailVanish.lean
  ==========================
  Proves: M · μ{γ > M} → 0 as M → ∞, given γ integrable and γ ≥ 0.

  Method: Markov + monotone convergence for set integrals.
    1. Antitone.tendsto_setIntegral gives ∫_{γ>n}γ → 0 along ℕ.
    2. Monotonicity transfers this to ℝ (γ ≥ 0 ensures set-integral monotonicity).
    3. M·τ(M) ≤ ∫_{γ>M}γ (first moment Markov) + squeeze to 0.

  Compared to TailSecondMoment.lean (second_moment_tail_vanish which gives
  M²·τ(M) → 0 from ∫γ² < ∞), this gives M·τ(M) → 0 from ∫γ < ∞.

  This weaker bound suffices for the wired chain when γ ≥ γ_min > 0 holds
  (see ContinuumGammaMinFirstMoment.lean), enabling convergence proofs for
  distributions with only finite first moment.

  0 sorry. 0 axioms.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- If γ ≥ 0 is integrable (first moment finite), the first-moment tail M·μ{γ > M} → 0. -/
theorem first_moment_tail_vanish [IsProbabilityMeasure μ]
    (γ : Ω → ℝ)
    (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M}) :
    Tendsto (fun M : ℝ => M * (μ {ω | M < γ ω}).toReal) atTop (nhds 0) := by
  have h_meas : ∀ M : ℝ, MeasurableSet {ω | M < γ ω} := fun M => by
    have : {ω | M < γ ω} = {ω | γ ω ≤ M}ᶜ := by ext; simp [not_le]
    rw [this]; exact (hγ_level M).compl
  -- Step 1: ∫_{γ>n} γ → 0 along ℕ via antitone set integral convergence
  have h_tail_nat : Tendsto (fun n : ℕ => ∫ ω in {ω | (n : ℝ) < γ ω}, γ ω ∂μ)
      atTop (nhds 0) := by
    let s : ℕ → Set Ω := fun n => {ω | (n : ℝ) < γ ω}
    have hsm : ∀ n, MeasurableSet (s n) := fun n => h_meas n
    have h_anti : Antitone s := by
      intro m n hmn ω hω
      simp only [s, mem_setOf_eq] at hω ⊢
      exact lt_of_le_of_lt (Nat.cast_le.mpr hmn) hω
    have h_inter : ⋂ n, s n = ∅ := by
      ext ω
      simp only [s, mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact ⟨⌈γ ω⌉₊, Nat.le_ceil (γ ω)⟩
    have h_tendsto := h_anti.tendsto_setIntegral hsm hγ_int.integrableOn
    rw [h_inter, setIntegral_empty] at h_tendsto
    exact h_tendsto
  -- Step 2: transfer to ℝ using antitone monotonicity of the tail integral
  have h_tail_real : Tendsto (fun M : ℝ => ∫ ω in {ω | M < γ ω}, γ ω ∂μ)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at h_tail_nat
    obtain ⟨N, hN⟩ := h_tail_nat ε hε
    refine ⟨↑N, fun M hM => ?_⟩
    have h_nn : 0 ≤ ∫ ω in {ω | M < γ ω}, γ ω ∂μ :=
      setIntegral_nonneg (h_meas M) (fun ω _ => hγ_nn ω)
    have h_mono : ∫ ω in {ω | M < γ ω}, γ ω ∂μ ≤
        ∫ ω in {ω | (N : ℝ) < γ ω}, γ ω ∂μ :=
      setIntegral_mono_set hγ_int.integrableOn
        (ae_of_all _ hγ_nn)
        (ae_of_all _ (fun ω hω => lt_of_le_of_lt hM hω))
    have h_nn_N : 0 ≤ ∫ ω in {ω | (N : ℝ) < γ ω}, γ ω ∂μ :=
      setIntegral_nonneg (h_meas N) (fun ω _ => hγ_nn ω)
    have hN_bound := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn_N] at hN_bound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn]
    linarith
  -- Step 3: Markov bound M·τ(M) ≤ ∫_{γ>M}γ and squeeze to 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tail_real
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    exact mul_nonneg hM ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    have h_eq : M * (μ {ω | M < γ ω}).toReal = ∫ _ in {ω | M < γ ω}, M ∂μ := by
      rw [setIntegral_const]; simp [Measure.real]; ring
    rw [h_eq]
    apply setIntegral_mono_on (integrable_const _).integrableOn
      hγ_int.integrableOn (h_meas M)
    intro ω hω
    exact le_of_lt hω

end
