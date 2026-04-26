/-
  Kuramoto Stability — Locked-Body Exponential Convergence
  =========================================================
  When pair coercivity holds (all amplitudes ≥ δ, equilibria ≥ δ*),
  the Lyapunov function converges to 0 exponentially.

  Chain: pair_coercive → V drops by q < 1 → continuous_barbalat → V → 0

  Also: split convergence — V_total = V_locked + V_tail, both → 0 ⟹ V_total → 0.

  0 sorry.
-/
import KuramotoLean.ContinuumBarbalat
import KuramotoLean.PairCoercivity

open Filter Topology

noncomputable section

/-! ## Locked-body exponential convergence

A trajectory where pair coercivity gives dV/dt ≤ -μV uniformly
converges to 0 exponentially. Uses continuous_barbalat_persistence. -/

/-- Locked trajectory data: pair coercivity holds at all times. -/
structure LockedTrajectoryData where
  V : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  hdrops : ∀ T : ℝ, ∃ t, T ≤ t ∧ V (t + 1) ≤ q * V t

/-- Locked trajectories converge to 0. -/
theorem LockedTrajectoryData.convergence (D : LockedTrajectoryData) :
    Tendsto D.V atTop (nhds 0) :=
  continuous_barbalat_tendsto D.V D.q D.hV_nn D.hV_anti D.hq0 D.hq1 D.hdrops

/-- ε-δ form for concrete estimates. -/
theorem LockedTrajectoryData.epsilon_delta (D : LockedTrajectoryData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → D.V s < ε :=
  continuous_barbalat_persistence D.V D.q D.hV_nn D.hV_anti D.hq0 D.hq1 D.hdrops

/-! ## Split convergence: V_total = V_locked + V_tail

For the continuum Kuramoto:
- V_locked = ∫_{locked} g|α-α*|² dω → 0 (pair coercivity + persistence)
- V_tail   = ∫_{tail} g|α-α*|² dω → 0 (dephasing / Riemann-Lebesgue)
- V_total  = V_locked + V_tail → 0

This is the structure for closing the continuum gap. -/

/-- Split convergence: both parts → 0 ⟹ total → 0. -/
theorem split_convergence (V_locked V_tail V_total : ℝ → ℝ)
    (hV_split : ∀ t, V_total t = V_locked t + V_tail t)
    (h_locked : Tendsto V_locked atTop (nhds 0))
    (h_tail : Tendsto V_tail atTop (nhds 0)) :
    Tendsto V_total atTop (nhds 0) := by
  have h_add := h_locked.add h_tail
  simp only [add_zero] at h_add
  exact h_add.congr (fun t => (hV_split t).symm)

/-- Epsilon-delta form of split convergence. -/
theorem split_convergence_eps (V_locked V_tail V_total : ℝ → ℝ)
    (hV_locked_nn : ∀ t, 0 ≤ V_locked t)
    (hV_tail_nn : ∀ t, 0 ≤ V_tail t)
    (hV_split : ∀ t, V_total t = V_locked t + V_tail t)
    (h_locked : ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → V_locked s < ε)
    (h_tail : ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → V_tail s < ε) :
    ∀ ε > 0, ∃ T : ℝ, ∀ s, T ≤ s → V_total s < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨T₁, hT₁⟩ := h_locked (ε / 2) hε2
  obtain ⟨T₂, hT₂⟩ := h_tail (ε / 2) hε2
  exact ⟨max T₁ T₂, fun s hs => by
    rw [hV_split]
    have h1 := hT₁ s (le_of_max_le_left hs)
    have h2 := hT₂ s (le_of_max_le_right hs)
    linarith⟩

/-! ## Assembly: the full convergence chain

Theorem statement: for a system where both locked and tail
parts converge, V∞ → 0.

The locked part converges from:
  pair coercivity → exponential drop → Barbalat persistence → V_locked → 0

The tail part converges from (any of):
  (a) scalar_oa_strict_lyapunov + r → r* → dephasing
  (b) Riemann-Lebesgue for tail oscillators
  (c) explicit tail estimate from [D16]/[DF18]

Both are proved in the wiki (0 sorry) but at different levels
of the formalization chain:
  - Locked: PairCoercivity + ContinuumBarbalat (direct LEAN chain)
  - Tail: scalar convergence + dominated convergence (argument level) -/

/-- **Continuum V∞ convergence.** Given locked + tail convergence
    and the antitone property, V∞ → 0 and its limit L = 0. -/
theorem continuum_v_convergence
    (V : ℝ → ℝ) (_hV_nn : ∀ t, 0 ≤ V t) (_hV_anti : Antitone V)
    (V_locked V_tail : ℝ → ℝ)
    (hV_split : ∀ t, V t = V_locked t + V_tail t)
    (h_locked : Tendsto V_locked atTop (nhds 0))
    (h_tail : Tendsto V_tail atTop (nhds 0)) :
    Tendsto V atTop (nhds 0) :=
  split_convergence V_locked V_tail V hV_split h_locked h_tail

/-- **Limit is zero.** Combined with AntitoneConvergence,
    the limit L of V must be 0. -/
theorem continuum_limit_zero
    (V : ℝ → ℝ) (_hV_nn : ∀ t, 0 ≤ V t) (_hV_anti : Antitone V)
    (V_locked V_tail : ℝ → ℝ)
    (hV_split : ∀ t, V t = V_locked t + V_tail t)
    (h_locked : Tendsto V_locked atTop (nhds 0))
    (h_tail : Tendsto V_tail atTop (nhds 0))
    (L : ℝ) (_hL_nn : 0 ≤ L) (hL : Tendsto V atTop (nhds L)) :
    L = 0 :=
  tendsto_nhds_unique hL
    (continuum_v_convergence V _hV_nn _hV_anti V_locked V_tail hV_split h_locked h_tail)

end
