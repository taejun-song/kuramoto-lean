/-
  Kuramoto Stability — Complete Trifurcation
  ============================================
  For ALL coupling strengths K > 0, the n-pole OA system converges:
    K < K_c : r → 0  (incoherence globally attracting)
    K = K_c : r → 0  (critical cubic decay)
    K > K_c : r → r*  (unique PLS globally attracting)

  Single theorem, single structure, all three regimes.
  0 sorry.
-/

import KuramotoLean.CriticalConvergence
import KuramotoLean.ExtendedConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

theorem trifurcation (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hinit_pos : ∀ k, 0 < D.α 0 k)
    (hinit_lt : ∀ k, D.α 0 k < 1) :
    ∃ r_limit : ℝ, 0 ≤ r_limit ∧ r_limit ≤ 1 ∧
      Tendsto D.r atTop (nhds r_limit) ∧
      (D.K ≤ npoleCriticalK D.γ D.c → r_limit = 0) ∧
      (npoleCriticalK D.γ D.c < D.K → 0 < r_limit ∧ r_limit < 1) := by
  rcases lt_trichotomy D.K (npoleCriticalK D.γ D.c) with hlt | heq | hgt
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_subcritical_convergence D hn hlt,
      fun _ => rfl,
      fun h => absurd h (not_lt.mpr (le_of_lt hlt))⟩
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_critical_convergence D hn heq,
      fun _ => rfl,
      fun h => absurd h (by linarith)⟩
  · obtain ⟨r_star, hr_pos, hr_lt, hr_conv⟩ :=
      parametric_convergence D hn hc_sum hgt hinit_pos hinit_lt
    refine ⟨r_star, le_of_lt hr_pos, le_of_lt hr_lt, ?_, ?_, ?_⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨T, hT⟩ := hr_conv ε hε
      exact ⟨T, fun t ht => by rw [Real.dist_eq]; exact hT t ht⟩
    · intro h; linarith
    · intro _; exact ⟨hr_pos, hr_lt⟩

/-- **Maximal trifurcation**: covers ALL initial data in [0,1]^n \ {0}.
    For K ≤ K_c, r → 0. For K > K_c, r → r* ∈ (0,1).
    No restriction on upper/lower boundary — components at 0 or 1 are allowed. -/
theorem maximal_trifurcation (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hα_some_pos : ∃ j, 0 < D.α 0 j) :
    ∃ r_limit : ℝ, 0 ≤ r_limit ∧ r_limit ≤ 1 ∧
      Tendsto D.r atTop (nhds r_limit) ∧
      (D.K ≤ npoleCriticalK D.γ D.c → r_limit = 0) ∧
      (npoleCriticalK D.γ D.c < D.K → 0 < r_limit ∧ r_limit < 1) := by
  rcases lt_trichotomy D.K (npoleCriticalK D.γ D.c) with hlt | heq | hgt
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_subcritical_convergence D hn hlt,
      fun _ => rfl,
      fun h => absurd h (not_lt.mpr (le_of_lt hlt))⟩
  · exact ⟨0, le_refl 0, zero_le_one,
      parametric_critical_convergence D hn heq,
      fun _ => rfl,
      fun h => absurd h (by linarith)⟩
  · obtain ⟨r_star, hr_pos, hr_lt, hr_conv⟩ :=
      maximal_convergence D hn hc_sum hgt hα_some_pos
    refine ⟨r_star, le_of_lt hr_pos, le_of_lt hr_lt, ?_, ?_, ?_⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨T, hT⟩ := hr_conv ε hε
      exact ⟨T, fun t ht => by rw [Real.dist_eq]; exact hT t ht⟩
    · intro h; linarith
    · intro _; exact ⟨hr_pos, hr_lt⟩

end
