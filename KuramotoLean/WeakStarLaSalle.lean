/-
  Kuramoto Stability — LaSalle Convergence for Antitone Lyapunov
  ===============================================================
  V >= 0 antitone + dissipation vanishes + quantitative coercivity -> V -> 0.

  Combined with the mean value theorem: differentiable V -> L implies
  |V'| vanishes on a subsequence, giving hP_vanish.

  For the continuum Kuramoto (V = integral (alpha-alpha*)^2 g, P = double integral pair):
  - hP_vanish: follows from MVT + V differentiable (proved here)
  - h_coercive: proved for bounded gamma (pair coercivity P >= c*V)
                OPEN for unbounded gamma (coercivity degenerates)

  0 sorry.
-/

import KuramotoLean.AntitoneConvergence
import KuramotoLean.ContinuumRigidity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Filter Topology Set

namespace WeakStarLaSalle

noncomputable section

/-! ## Antitone increment vanishes -/

/-- If V -> L, then V(t) - V(t + delta) -> 0. -/
theorem antitone_increment_vanishes (V : ℝ → ℝ) (L δ : ℝ)
    (hV_lim : Tendsto V atTop (nhds L)) :
    Tendsto (fun t => V t - V (t + δ)) atTop (nhds 0) := by
  have hshift : Tendsto (fun t => V (t + δ)) atTop (nhds L) :=
    hV_lim.comp (Filter.tendsto_atTop_atTop.mpr
      fun b => ⟨b - δ, fun x hx => by linarith⟩)
  have h := hV_lim.sub hshift
  rwa [sub_self] at h

/-- Nonneg version: V antitone and delta >= 0 gives V(t) - V(t+delta) >= 0. -/
theorem antitone_increment_nonneg (V : ℝ → ℝ) (δ : ℝ)
    (hV_anti : Antitone V) (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ V t - V (t + δ) :=
  sub_nonneg.mpr (hV_anti (le_add_of_nonneg_right hδ))

/-! ## Abstract LaSalle convergence

The two hypotheses:
- `hP_vanish`: the dissipation rate P eventually dips below any epsilon
- `h_coercive`: small P implies small V (quantitative rigidity)

Together with V antitone, these give V -> 0. The proof is simple:
once P(t0) < delta, coercivity gives V(t0) < epsilon, and
antitonicity propagates forward: V(s) <= V(t0) < epsilon for s >= t0. -/

/-- **Abstract LaSalle convergence for antitone Lyapunov functions.** -/
theorem lasalle_convergence (V P : ℝ → ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hP_vanish : ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ P t < ε)
    (h_coercive : ∀ ε > 0, ∃ δ > 0, ∀ t, P t < δ → V t < ε) :
    Tendsto V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := h_coercive ε hε
  obtain ⟨t₀, _, hPt⟩ := hP_vanish δ hδ 0
  exact ⟨t₀, fun s hs => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hV_nn s)]
    exact lt_of_le_of_lt (hV_anti hs) (hc t₀ hPt)⟩

/-- The limit L of an antitone Lyapunov function is 0 under LaSalle. -/
theorem lasalle_limit_zero (V P : ℝ → ℝ) (L : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hV_lim : Tendsto V atTop (nhds L))
    (hP_vanish : ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ P t < ε)
    (h_coercive : ∀ ε > 0, ∃ δ > 0, ∀ t, P t < δ → V t < ε) :
    L = 0 :=
  tendsto_nhds_unique hV_lim
    (lasalle_convergence V P hV_nn hV_anti hP_vanish h_coercive)

/-! ## Linear coercivity -/

/-- Linear coercivity P >= c*V implies the general coercivity condition. -/
theorem linear_coercivity (V P : ℝ → ℝ) (c : ℝ)
    (hc : 0 < c) (h : ∀ t, c * V t ≤ P t) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, P t < δ → V t < ε := by
  intro ε hε
  exact ⟨c * ε, mul_pos hc hε, fun t hPt => by
    by_contra h_ge; push Not at h_ge
    linarith [h t, mul_le_mul_of_nonneg_left h_ge (le_of_lt hc)]⟩

/-! ## LaSalle data structure -/

/-- Packages the hypotheses for LaSalle convergence. -/
structure AntitoneLaSalleData where
  V : ℝ → ℝ
  P : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hP_vanish : ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ P t < ε
  h_coercive : ∀ ε > 0, ∃ δ > 0, ∀ t, P t < δ → V t < ε

theorem AntitoneLaSalleData.convergence (D : AntitoneLaSalleData) :
    Tendsto D.V atTop (nhds 0) :=
  lasalle_convergence D.V D.P D.hV_nn D.hV_anti D.hP_vanish D.h_coercive

theorem AntitoneLaSalleData.limit_zero (D : AntitoneLaSalleData) (L : ℝ)
    (hL : Tendsto D.V atTop (nhds L)) : L = 0 :=
  tendsto_nhds_unique hL D.convergence

/-! ## Mean value theorem: derivative vanishes on subsequence

The key lemma for hP_vanish. If V is differentiable and V -> L,
then the mean value theorem forces V'(c_n) -> 0 on some sequence
c_n -> infinity. Combined with V' = -K*P, this gives P -> 0 on
a subsequence.

Proof: V -> L implies V(a+1) - V(a) -> 0 for any a -> infinity.
By MVT on [a, a+1]: exists c in (a, a+1) with V'(c) = V(a+1) - V(a).
So |V'(c)| = |V(a+1) - V(a)| < epsilon for a large enough. -/

/-- **Derivative vanishes on subsequence.** If V is differentiable
    and V -> L, then for any epsilon > 0 and T, there exists t >= T
    with |deriv V t| < epsilon. -/
theorem deriv_vanishes_on_subsequence (V : ℝ → ℝ) (L : ℝ)
    (hV_lim : Tendsto V atTop (nhds L))
    (hV_diff : Differentiable ℝ V) :
    ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ |deriv V t| < ε := by
  intro ε hε T
  rw [Metric.tendsto_atTop] at hV_lim
  obtain ⟨N, hN⟩ := hV_lim (ε / 2) (by linarith)
  set a := max T N with ha_def
  have ha_T : T ≤ a := le_max_left _ _
  have ha_N : N ≤ a := le_max_right _ _
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope V (deriv V)
    (show a < a + 1 from lt_add_one a)
    hV_diff.continuous.continuousOn
    (fun x _ => (hV_diff x).hasDerivAt)
  have hc_ge : T ≤ c := le_trans ha_T (le_of_lt hc_mem.1)
  have h_simpl : deriv V c = V (a + 1) - V a := by
    rw [hc_eq, show a + 1 - a = (1 : ℝ) from by ring, div_one]
  have h1 : |V (a + 1) - L| < ε / 2 := by
    rw [← Real.dist_eq]; exact hN _ (by linarith)
  have h2 : |V a - L| < ε / 2 := by
    rw [← Real.dist_eq]; exact hN _ ha_N
  exact ⟨c, hc_ge, by
    rw [h_simpl]
    calc |V (a + 1) - V a|
        ≤ |V (a + 1) - L| + |L - V a| := abs_sub_le _ L _
      _ = |V (a + 1) - L| + |V a - L| := by rw [abs_sub_comm L]
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring⟩

/-- **Derivative controls dissipation.** If V' = -K*P with K > 0
    and |V'| vanishes on a subsequence, then P vanishes on a subsequence. -/
theorem dissipation_vanishes_of_deriv (V P : ℝ → ℝ) (K L : ℝ)
    (hK : 0 < K)
    (hV_lim : Tendsto V atTop (nhds L))
    (hV_diff : Differentiable ℝ V)
    (_hP_nn : ∀ t, 0 ≤ P t)
    (hVP : ∀ t, deriv V t = -(K * P t)) :
    ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ P t < ε := by
  intro ε hε T
  obtain ⟨t, ht, hd⟩ := deriv_vanishes_on_subsequence V L hV_lim hV_diff
    (K * ε) (by positivity) T
  refine ⟨t, ht, ?_⟩
  have h_eq : K * P t = -(deriv V t) := by linarith [hVP t]
  have h_abs : K * P t ≤ |deriv V t| := by
    rw [h_eq, ← abs_neg (deriv V t)]; exact le_abs_self _
  exact lt_of_mul_lt_mul_left (lt_of_le_of_lt h_abs hd) (le_of_lt hK)

/-! ## Continuum LaSalle application

For the continuum OA system with measure mu (representing g(omega) d omega):
  V(t) = integral (alpha(omega,t) - alpha*(omega))^2 d mu
  P(t) = double integral pairIntegrand d mu d mu

**Proved** (ContinuumLyapunov + ContinuumRigidity):
  - V >= 0, V antitone (pair bound)
  - P >= 0 (pair bound pointwise)
  - P = 0 iff alpha = alpha* a.e. (qualitative rigidity)

**From MVT** (deriv_vanishes_on_subsequence + dissipation_vanishes_of_deriv):
  - V differentiable + V -> L => hP_vanish (dissipation vanishes on subsequence)
  - Requires: V differentiable (Leibniz integral rule for d/dt integral (alpha-alpha*)^2)
  - For the ODE alpha' = -gamma*alpha + (K/2)*r*(1-alpha^2):
    d/dt(alpha-alpha*)^2 = 2*(alpha-alpha*)*alpha'
    Bounded by 2*(gamma + K) which is integrable over {gamma <= M} but
    NOT over all of R when gamma = |omega| is unbounded.
  - Resolution: use V_body on {gamma <= M} where Leibniz works,
    then pass to limit. The n-pole UniformRate gives V_body' = -K*P_body.

**OPEN** for unbounded gamma:
  - h_coercive: P < delta => V < epsilon (quantitative rigidity)
  - Proved for bounded gamma: pair coercivity gives P >= c*V with
    c = K*delta_S*delta_star (PairCoercivity), so linear_coercivity applies.
  - For unbounded gamma: alpha* -> 0 as |omega| -> infinity,
    so the coercivity constant c -> 0. The orbit is NOT precompact
    in L^2(g). Promoting qualitative rigidity (P=0 => V=0) to
    quantitative (P<delta => V<epsilon) requires compactness that fails.

Together: LaSalle convergence reduces the open problem to a single
hypothesis h_coercive. This is a quantitative strengthening of
ContinuumRigidity (already proved qualitatively). -/

open MeasureTheory in
/-- **Continuum LaSalle data.** Packages the proved and open ingredients. -/
structure ContinuumAntitoneLaSalleData {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  α : Ω → ℝ → ℝ
  α_star : Ω → ℝ
  V : ℝ → ℝ
  P : ℝ → ℝ
  hV_def : ∀ t, V t = ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hP_nn : ∀ t, 0 ≤ P t
  hP_vanish : ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ P t < ε
  h_coercive : ∀ ε > 0, ∃ δ > 0, ∀ t, P t < δ → V t < ε

open MeasureTheory in
/-- **Continuum LaSalle convergence.** V -> 0 from the packaged data. -/
theorem ContinuumAntitoneLaSalleData.convergence {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (D : ContinuumAntitoneLaSalleData μ) :
    Tendsto D.V atTop (nhds 0) :=
  lasalle_convergence D.V D.P D.hV_nn D.hV_anti D.hP_vanish D.h_coercive

open MeasureTheory in
/-- **Continuum LaSalle: r -> r*.** If V -> 0 and |r-r*|^2 <= V, then r -> r*. -/
theorem ContinuumAntitoneLaSalleData.r_convergence {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (D : ContinuumAntitoneLaSalleData μ)
    (r : ℝ → ℝ) (r_star : ℝ)
    (hr_bound : ∀ t, (r t - r_star) ^ 2 ≤ D.V t) :
    Tendsto r atTop (nhds r_star) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV := D.convergence
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T, hT⟩ := hV (ε ^ 2) (by positivity)
  exact ⟨T, fun t ht => by
    rw [Real.dist_eq]
    have hVt : D.V t < ε ^ 2 := by
      have h := hT t ht
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (D.hV_nn t)] at h
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt (hr_bound t) hVt) (le_of_lt hε)⟩

/-! ## Reduction: what remains for the standard continuum model

The standard continuum Kuramoto with gamma(omega) = |omega| reduces to:

  OPEN HYPOTHESIS (h_coercive):
    For all epsilon > 0, there exists delta > 0 such that
    for all t >= 0: double integral pair(alpha(.,t)) < delta
    implies integral (alpha(.,t) - alpha*)^2 g < epsilon.

  Equivalently (by contrapositive):
    integral (alpha - alpha*)^2 g >= epsilon implies
    double integral pair(alpha) >= delta.

This is a QUANTITATIVE version of ContinuumRigidity:
  - QUALITATIVE (proved, 0 sorry):
    double integral pair = 0 => alpha = alpha* a.e.
  - QUANTITATIVE (open):
    double integral pair < delta => V = integral (alpha-alpha*)^2 < epsilon

The gap is compactness: the qualitative-to-quantitative promotion
requires the orbit {alpha(.,t)} to be precompact in a topology where
both V and the pair integral are continuous. For bounded gamma, the
orbit is precompact in L^2(g) and pair coercivity gives P >= c*V.
For unbounded gamma, L^2(g) precompactness fails at the lock/drift
boundary |omega| = Kr*, and the coercivity constant degenerates. -/

end

end WeakStarLaSalle
