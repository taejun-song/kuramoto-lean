/-
  Kuramoto Stability — Bifurcation Dichotomy
  ============================================
  Unified statement: K < K_c → r → 0, K > K_c → r → r*.

  0 sorry.
-/

import KuramotoLean.SubcriticalConvergence
import KuramotoLean.GlobalStabilitySupercritical

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

theorem bifurcation_dichotomy (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_ne : D.K ≠ npoleCriticalK D.γ D.c)
    (hinit_pos : ∀ k, 0 < D.α 0 k)
    (hinit_lt : ∀ k, D.α 0 k < 1) :
    (D.K < npoleCriticalK D.γ D.c ∧ Tendsto D.r atTop (nhds 0)) ∨
    (npoleCriticalK D.γ D.c < D.K ∧
      ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
        ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - r_star| < ε) := by
  rcases lt_or_gt_of_ne hK_ne with hlt | hgt
  · exact Or.inl ⟨hlt, parametric_subcritical_convergence D hn hlt⟩
  · exact Or.inr ⟨hgt, parametric_convergence D hn hc_sum hgt hinit_pos hinit_lt⟩

end
