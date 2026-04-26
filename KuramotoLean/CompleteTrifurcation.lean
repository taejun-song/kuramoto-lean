/-
  Kuramoto Stability — Complete Trifurcation
  ===========================================
  Unified classification for ALL K > 0:
    K ≤ K_c  →  r(t) → 0     (incoherence globally attracting)
    K > K_c  →  r(t) → r*    (PLS globally attracting, maximal initial data)

  Combines:
  - parametric_subcritical_convergence (K < K_c)
  - parametric_critical_convergence   (K = K_c)
  - maximal_convergence               (K > K_c)

  0 sorry.
-/

import KuramotoLean.CriticalConvergence
import KuramotoLean.ExtendedConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

theorem incoherence_convergence (D : NPoleBarrierData n)
    (hn : 0 < n) (hK_le : D.K ≤ npoleCriticalK D.γ D.c) :
    Tendsto D.r atTop (nhds 0) := by
  rcases eq_or_lt_of_le hK_le with heq | hlt
  · exact parametric_critical_convergence D hn heq
  · exact parametric_subcritical_convergence D hn hlt

theorem maximal_convergence_tendsto (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K)
    (hα_some_pos : ∃ j, 0 < D.α 0 j) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
      Tendsto D.r atTop (nhds r_star) := by
  obtain ⟨r_star, hr_pos, hr_lt, hconv⟩ :=
    maximal_convergence D hn hc_sum hK_super hα_some_pos
  exact ⟨r_star, hr_pos, hr_lt, by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := hconv ε hε
    exact ⟨T, fun t ht => by rw [Real.dist_eq]; exact hT t ht⟩⟩

theorem complete_trifurcation (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hα_some_pos : ∃ j, 0 < D.α 0 j) :
    (D.K ≤ npoleCriticalK D.γ D.c ∧ Tendsto D.r atTop (nhds 0)) ∨
    (npoleCriticalK D.γ D.c < D.K ∧
      ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
        Tendsto D.r atTop (nhds r_star)) := by
  by_cases h : D.K ≤ npoleCriticalK D.γ D.c
  · exact Or.inl ⟨h, incoherence_convergence D hn h⟩
  · exact Or.inr ⟨not_le.mp h, maximal_convergence_tendsto D hn hc_sum (not_le.mp h) hα_some_pos⟩

end
