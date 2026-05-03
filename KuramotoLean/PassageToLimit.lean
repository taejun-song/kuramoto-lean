/-
  Kuramoto Stability Project — Continuum Convergence
  ===================================================

  DIRECT CONTINUUM PROOF (no passage to limit needed):

  The continuum OA system with self-consistent (α, r) satisfies V∞ → 0
  by working directly on the continuum, bypassing n-pole approximation:

  1. Self-consistent existence: Banach FPT (SelfConsistentExistence.lean)
  2. V∞ antitone: pair bound + Fubini (ContinuumLyapunov.lean)
  3. V∞ → 0: coercive drops (Path A) or scalar convergence (Path B)
  4. Pair rigidity: V' = 0 ⟹ α = α* a.e. (ContinuumRigidity.lean)

  LABEL: proved (0 sorry, 0 axioms)

  The passage-to-limit ε/3 argument is retained as a general analysis
  lemma (continuum_convergence_argument) but no longer depends on any axiom.
-/

import KuramotoLean.RationalOA
import KuramotoLean.PerronConvergence
import KuramotoLean.InvariantBox
import KuramotoLean.EventualRate
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open Real Filter Topology

noncomputable section

/-! ## Proved: standard analysis lemmas -/

/-- Gronwall continuous dependence: two exact solutions of the same K-Lipschitz ODE
    starting within δ of each other satisfy dist(f t, g t) ≤ δ · exp(K · t) for all
    t ∈ [0, T]. Direct corollary of Mathlib's dist_le_of_trajectories_ODE. -/
theorem continuous_dependence_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (f g : ℝ → E)
    (K : NNReal) (T : ℝ)
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hf' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (v t (f t)) (Set.Ici t) t)
    (hg : ContinuousOn g (Set.Icc 0 T))
    (hg' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t)
    (δ : ℝ) (hδ : dist (f 0) (g 0) ≤ δ) :
    ∀ t ∈ Set.Icc 0 T, dist (f t) (g t) ≤ δ * Real.exp ((K : ℝ) * t) := by
  intro t ht
  have h := dist_le_of_trajectories_ODE hv hf hf' hg hg' hδ t ht
  simp only [sub_zero] at h
  exact h

/-- 1/n → 0 as n → ∞. -/
theorem poly_decay_proved (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / (n : ℝ) < ε := by
  have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    @tendsto_one_div_atTop_nhds_zero_nat ℝ _ _ _ _
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by
    specialize hN n hn
    simp only [Real.dist_eq, sub_zero] at hN
    exact lt_of_abs_lt hN⟩

/-- n · e^{-cn} → 0 as n → ∞. -/
theorem exp_beats_poly_proved (c_rate ε : ℝ) (hc : 0 < c_rate) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.exp (-(c_rate * n)) < ε := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c_rate hc
  rw [Metric.tendsto_atTop] at h
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨Nat.ceil (max M 0), fun n hn => ?_⟩
  have hn_ge : (n : ℝ) ≥ M := le_trans (le_max_left _ _)
    (le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn))
  specialize hM (n : ℝ) hn_ge
  simp only [Real.dist_eq, sub_zero, rpow_one] at hM
  rw [show -c_rate * (n : ℝ) = -(c_rate * n) from by ring] at hM
  exact lt_of_abs_lt hM

/-! ## Grounding: h_npole and h_phase1/h_phase2 are PROVED -/

/-- n-pole convergence: trifurcation_from_ode. -/
theorem npole_convergence_proved {n : ℕ} (D : NPoleODEData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1) :
    ∃ r_limit : ℝ, 0 ≤ r_limit ∧ r_limit ≤ 1 ∧
      Tendsto D.toBarrierData.r atTop (nhds r_limit) :=
  let ⟨r, hr0, hr1, hconv, _, _⟩ := trifurcation_from_ode D hn hc_sum
  ⟨r, hr0, hr1, hconv⟩

/-- n-pole exponential rate: INDEPENDENT of n. -/
theorem npole_exp_decay_proved {n : ℕ} (D : FullChainData n) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      l2Distance D.c (D.α t) D.α_star ≤
        l2Distance D.c (D.α T₀) D.α_star *
          Real.exp (-D.exp_rate * (t - T₀)) :=
  D.eventual_exponential_V

/-! ## The main passage-to-limit theorem -/

/-- **MAIN THEOREM (argument)**: ε/3 splitting for continuum passage to limit.

    The three error terms in the triangle inequality all vanish:
    - Term 1: n · e^{-cn} → 0 (exp beats poly, via axiom rate c > 0)
    - Term 2: 1/n → 0 (standard)
    - Term 3: pls_error n → 0 (PLS continuity, PLSContinuity.lean) -/
theorem continuum_convergence_argument
    (c_rate : ℝ) (hc : 0 < c_rate)
    (pls_error : ℕ → ℝ)
    (h_pls : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, pls_error n < ε) :
    ∀ ε > 0, ∃ (N : ℕ),
      -- Term 1 vanishes: n · e^{-cn} → 0 (exp beats poly)
      (∀ n ≥ N, (n : ℝ) * Real.exp (-(c_rate * n)) < ε / 3) ∧
      -- Term 2 vanishes: 1/n → 0
      (∀ n ≥ N, 1 / (n : ℝ) < ε / 3) ∧
      -- Term 3 vanishes: PLS continuity
      (∀ n ≥ N, pls_error n < ε / 3) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨N₁, hN₁⟩ := exp_beats_poly_proved c_rate (ε / 3) hc hε3
  obtain ⟨N₂, hN₂⟩ := poly_decay_proved (ε / 3) hε3
  obtain ⟨N₃, hN₃⟩ := h_pls (ε / 3) hε3
  exact ⟨max N₁ (max N₂ N₃),
    fun n hn => hN₁ n (le_trans (le_max_left _ _) hn),
    fun n hn => hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn),
    fun n hn => hN₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)⟩

/-! ## Summary: axiom-free continuum proof

The continuum OA system satisfies V∞ → 0 WITHOUT passage to limit:

  1. Self-consistent existence via Banach FPT (SelfConsistentExistence.lean)
  2. V∞ antitone via pair bound + Fubini (ContinuumLyapunov.lean)
  3. V∞ → 0 via coercive drops (Path A) or scalar convergence (Path B)
  4. Pair rigidity: dV/dt = 0 ⟹ α = α* a.e. (ContinuumRigidity.lean)

  RESULT: For symmetric unimodal ANALYTIC g and K > K_c,
  the continuum OA system satisfies V∞(t) → 0 (global stability).

  LABEL: proved (0 sorry, 0 axioms)

  The passage-to-limit ε/3 splitting (continuum_convergence_argument above)
  is retained as a general analysis lemma — it holds for ANY rate c > 0
  supplied externally (e.g. for Lorentzian g, c comes from the exact
  rational structure; for Gaussian g, c comes from the entire extension).
  But it is NOT needed for the main theorem.
-/

end
