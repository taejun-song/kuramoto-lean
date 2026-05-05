/-
  Kuramoto Stability — Absorbing Barbalat for Continuum Kuramoto
  ==============================================================
  Reduces V∞ → 0 for unbounded γ to TIME-AVERAGED coercivity:

    V(t+1) ≥ ε ⟹ V(t) - V(t+1) ≥ δ(ε)

  This is WEAKER than pointwise coercivity (h_coercive: P < δ ⟹ V < ε)
  because it only requires the Lyapunov drop over a unit window to be
  positive when V is positive — not pointwise dissipation control.

  The argument:
  1. V antitone, V ≥ 0 → V → L (AntitoneConvergence)
  2. V(t) - V(t+1) → 0 (V converges)
  3. If L > 0: V(t+1) ≥ L/2 for large t → V(t)-V(t+1) ≥ δ(L/2), contradicting (2)

  0 sorry.
-/

import KuramotoLean.WeakStarLaSalle

open Filter Topology Set

noncomputable section

namespace AbsorbingBarbalat

/-! ## Time-averaged coercivity -/

/-- **Time-averaged coercivity.**
    If V stays above ε at time t+1, then the Lyapunov drop over [t,t+1]
    is bounded below by δ. Since V' = -KP, this means ∫_t^{t+1} P ≥ δ/K.

    This is weaker than pointwise coercivity because it allows P to dip
    momentarily, requiring only that cumulative dissipation remains positive. -/
def TimeAveragedCoercivity (V : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, V (t + 1) ≥ ε → V t - V (t + 1) ≥ δ

/-! ## Main convergence theorem -/

/-- **Absorbing Barbalat.** V antitone + V ≥ 0 + V(t)-V(t+1) → 0
    + time-averaged coercivity → V → 0.

    Proof by contradiction:
    - V → L ≥ 0 (antitone bounded)
    - V(t) - V(t+1) → 0 (convergence)
    - If L > 0: V(t+1) ≥ L/2 eventually → V(t)-V(t+1) ≥ δ(L/2) > 0
    - But V(t)-V(t+1) → 0. Contradiction. -/
theorem absorbing_barbalat (V : ℝ → ℝ) (L : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hV_lim : Tendsto V atTop (nhds L))
    (hL_nn : 0 ≤ L)
    (h_tac : TimeAveragedCoercivity V) :
    L = 0 := by
  by_contra hL_pos
  have hL : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL_pos)
  obtain ⟨δ, hδ, hcoer⟩ := h_tac (L / 2) (by linarith)
  have h_drop := WeakStarLaSalle.antitone_increment_vanishes V L 1 hV_lim
  rw [Metric.tendsto_atTop] at h_drop hV_lim
  obtain ⟨T₁, hT₁⟩ := h_drop δ hδ
  obtain ⟨T₂, hT₂⟩ := hV_lim (L / 2) (by linarith)
  set T := max T₁ T₂
  have hVT : V (T + 1) ≥ L / 2 := by
    have h := hT₂ (T + 1) (by linarith [le_max_right T₁ T₂])
    rw [Real.dist_eq] at h
    have := abs_lt.mp h
    linarith
  have h_drop_big : V T - V (T + 1) ≥ δ := hcoer T hVT
  have h_drop_small : dist (V T - V (T + 1)) 0 < δ := hT₁ T (le_max_left T₁ T₂)
  rw [Real.dist_eq, sub_zero] at h_drop_small
  have h_nn_drop : 0 ≤ V T - V (T + 1) :=
    sub_nonneg.mpr (hV_anti (by linarith : T ≤ T + 1))
  linarith [abs_of_nonneg h_nn_drop]

/-- **Absorbing Barbalat (Tendsto form).** V → 0 from time-averaged coercivity. -/
theorem absorbing_barbalat_tendsto (V : ℝ → ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (h_tac : TimeAveragedCoercivity V) :
    Tendsto V atTop (nhds 0) := by
  obtain ⟨L, hL_nn, hV_lim⟩ := antitone_bounded_converges V hV_anti hV_nn
  have hL := absorbing_barbalat V L hV_nn hV_anti hV_lim hL_nn h_tac
  rwa [← hL]

/-! ## Relationship to persistence drops (ContinuumBarbalat)

TimeAveragedCoercivity is equivalent to a persistence-drop condition:
  V(t+1) ≥ ε ⟹ V(t) - V(t+1) ≥ δ
  ⟺ V(t+1) ≥ ε ⟹ V(t) ≥ V(t+1) + δ ≥ ε + δ
  ⟺ V(t+1) ≤ V(t) - δ whenever V(t+1) ≥ ε

This is strictly weaker than the ratio drop V(t+1) ≤ q*V(t) used in
continuous_barbalat_persistence, because it only requires an additive drop
when V is large, not a multiplicative contraction at every drop time. -/

/-- Ratio drop implies time-averaged coercivity. -/
theorem ratio_drop_implies_tac (V : ℝ → ℝ) (q : ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (_hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpersist : ∀ t, V (t + 1) ≤ q * V t) :
    TimeAveragedCoercivity V := by
  intro ε hε
  refine ⟨(1 - q) * ε, by nlinarith, fun t hVt => ?_⟩
  have hVt_ge : V t ≥ ε := le_trans hVt (hV_anti (by linarith : t ≤ t + 1))
  calc V t - V (t + 1)
      ≥ V t - q * V t := by linarith [hpersist t]
    _ = (1 - q) * V t := by ring
    _ ≥ (1 - q) * ε := by nlinarith

/-! ## Comparison with WeakStarLaSalle h_coercive

WeakStarLaSalle uses pointwise coercivity:
  h_coercive: ∀ ε > 0, ∃ δ > 0, ∀ t, P(t) < δ → V(t) < ε

When V' = -KP (K > 0, P ≥ 0):
  V(t) - V(t+1) = K · ∫_t^{t+1} P(s) ds

Pointwise coercivity says: if P is small EVERYWHERE, then V is small.
Time-averaged coercivity says: if V is large, then the INTEGRAL of P is large.

The contrapositive of h_coercive:
  V(t) ≥ ε → P(t) ≥ δ (pointwise, at each t)
  → ∫_t^{t+1} P ≥ δ (integrate)
  → V(t) - V(t+1) ≥ Kδ

So pointwise coercivity implies time-averaged coercivity. The converse fails:
time-averaged allows P to dip below δ at individual times, as long as the
integral stays above threshold. For unbounded γ, the tail oscillators have
P small pointwise (coercivity degenerates) but their cumulative time-integrated
contribution might still be positive. -/

/-- Pointwise coercivity + V antitone implies time-averaged coercivity.
    (Shows TimeAveragedCoercivity is weaker than h_coercive.)

    Proof: if V(t+1) ≥ ε, then V(t) ≥ ε (antitone), so P(t) ≥ δ at least
    at the endpoints. Since V(t)-V(t+1) = K∫P ≥ 0 and V(t) ≥ ε forces
    non-trivial drop, this gives the bound.

    In practice: for the continuum model, h_coercive gives P(t) ≥ δ at
    time t, hence V(t) - V(t+1) = K∫P ≥ Kδ. We formalize the abstract
    implication without needing the integral identity. -/
theorem pointwise_coercive_implies_tac (V P : ℝ → ℝ) (K : ℝ)
    (hK : 0 < K)
    (hV_anti : Antitone V)
    (hVP_drop : ∀ t, V t - V (t + 1) ≥ K * P t)
    (h_coercive : ∀ ε > 0, ∃ δ > 0, ∀ t, V t ≥ ε → P t ≥ δ) :
    TimeAveragedCoercivity V := by
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := h_coercive ε hε
  refine ⟨K * δ, by positivity, fun t hVt => ?_⟩
  have hVt_ge : V t ≥ ε := le_trans hVt (hV_anti (by linarith : t ≤ t + 1))
  have hPt := hc t hVt_ge
  have hKP : K * δ ≤ K * P t := by nlinarith
  linarith [hVP_drop t]

/-! ## Full reduction structure -/

/-- **Continuum absorbing Barbalat data.**
    Packages V with time-averaged coercivity.
    The ONLY open hypothesis is h_tac. -/
structure ContinuumAbsorbingData where
  V : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  h_tac : TimeAveragedCoercivity V

theorem ContinuumAbsorbingData.convergence (D : ContinuumAbsorbingData) :
    Tendsto D.V atTop (nhds 0) :=
  absorbing_barbalat_tendsto D.V D.hV_nn D.hV_anti D.h_tac

/-! ## The open problem reduced to one hypothesis

For the standard continuum Kuramoto with γ(ω) = |ω|, g ∈ L¹(ℝ):

PROVED (0 sorry, in existing files):
  - V(t) = ∫(α(ω,t) - α*(ω))² g(ω) dω ≥ 0
  - V antitone (pair bound, ContinuumLyapunov.lean)
  - V → L ≥ 0 (AntitoneConvergence.lean)
  - P = 0 ⟹ α = α* a.e. (ContinuumRigidity.lean)
  - V > 0 ⟹ P > 0 (continuum_strict_lyapunov)
  - ∃ t_n → ∞, P(t_n) → 0 (deriv_vanishes_on_subsequence, WeakStarLaSalle.lean)

OPEN (single hypothesis): TimeAveragedCoercivity V
  i.e., V(t+1) ≥ ε ⟹ V(t) - V(t+1) ≥ δ(ε)

Equivalently (since V(t)-V(t+1) = K·∫_t^{t+1} P(s)ds by FTC):
  V(t+1) ≥ ε ⟹ ∫_t^{t+1} P(s) ds ≥ δ(ε)/K

Physical meaning: if the trajectory stays ε-far from equilibrium in L²(g),
then the cumulative dissipation (time-integral of the pair functional)
over any unit time window is bounded below. The pair functional captures
ALL pairwise frequency interactions; even if individual oscillators at
large |ω| contribute little pointwise, their cumulative effect over time
might suffice. -/

end AbsorbingBarbalat

end
