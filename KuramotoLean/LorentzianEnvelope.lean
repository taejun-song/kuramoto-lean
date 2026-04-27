/-
  Kuramoto Stability — Lorentzian Envelope Convergence
  ====================================================

  Proves r(n) → r* for the Lorentzian OA model via a Lyapunov envelope,
  without ANY step-size constraint or non-degeneracy assumption.

  Key idea: V(n) = W₀·exp(-2Ψ(n))/r*² is antitone, bounds (r-r*)²,
  and drops by q = exp(-2Kδ²) at persistence times.

  Chain: hlyap → envelope antitone → persistence drops → Barbalat → r → r*

  Works for ALL K > 2γ unconditionally.

  0 sorry.
-/

import KuramotoLean.LorentzianInstance
import KuramotoLean.NPoleGlobalStability

open Real

noncomputable section

private theorem rstar_sq_eq (S : LorentzianSolution) :
    S.r_star ^ 2 = 1 - 2 * S.γ / S.K :=
  sq_sqrt (le_of_lt (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt))

/-! ## Lyapunov envelope -/

private def envelope (S : LorentzianSolution) (n : ℕ) : ℝ :=
  S.hlyap_coeff * exp (-2 * S.Ψ n) / S.r_star ^ 2

private theorem envelope_nonneg (S : LorentzianSolution) (n : ℕ) :
    0 ≤ envelope S n :=
  div_nonneg (mul_nonneg (le_of_lt S.hlyap_coeff_pos) (exp_nonneg _)) (sq_nonneg _)

private theorem Ψ_le_succ (S : LorentzianSolution) (n : ℕ) :
    S.Ψ n ≤ S.Ψ (n + 1) := by
  linarith [S.Ψ_growth n, mul_nonneg (le_of_lt S.hK_pos) (sq_nonneg (S.r n))]

private theorem envelope_mono (S : LorentzianSolution) :
    ∀ n, envelope S (n + 1) ≤ envelope S n := by
  intro n
  unfold envelope
  apply div_le_div_of_nonneg_right _ (sq_nonneg S.r_star)
  exact mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by linarith [Ψ_le_succ S n]))
    (le_of_lt S.hlyap_coeff_pos)

/-! ## Persistence drops -/

private theorem envelope_drop (S : LorentzianSolution) (n : ℕ)
    (hδ : S.δ ≤ S.r n) :
    envelope S (n + 1) ≤ exp (-2 * S.K * S.δ ^ 2) * envelope S n := by
  have hr2 : (0 : ℝ) < S.r_star ^ 2 := sq_pos_of_pos S.r_star_pos
  set C := S.hlyap_coeff with hC_def
  suffices hnum : C * exp (-2 * S.Ψ (n + 1)) ≤
      exp (-2 * S.K * S.δ ^ 2) * (C * exp (-2 * S.Ψ n)) by
    simp only [envelope]
    exact calc C * exp (-2 * S.Ψ (n + 1)) / S.r_star ^ 2
          ≤ exp (-2 * S.K * S.δ ^ 2) * (C * exp (-2 * S.Ψ n)) / S.r_star ^ 2 :=
            div_le_div_of_nonneg_right hnum (le_of_lt hr2)
        _ = exp (-2 * S.K * S.δ ^ 2) * (C * exp (-2 * S.Ψ n) / S.r_star ^ 2) :=
            mul_div_assoc _ _ _
  have hΨ_eq : -2 * S.Ψ (n + 1) = -2 * S.Ψ n + (-2 * S.K * S.r n ^ 2) := by
    linarith [S.Ψ_growth n]
  calc C * exp (-2 * S.Ψ (n + 1))
      = C * (exp (-2 * S.Ψ n) * exp (-2 * S.K * S.r n ^ 2)) := by
        rw [hΨ_eq, exp_add]
    _ = exp (-2 * S.K * S.r n ^ 2) * (C * exp (-2 * S.Ψ n)) := by ring
    _ ≤ exp (-2 * S.K * S.δ ^ 2) * (C * exp (-2 * S.Ψ n)) :=
        mul_le_mul_of_nonneg_right
          (exp_le_exp.mpr (by
            nlinarith [pow_le_pow_left₀ (le_of_lt S.hδ) hδ 2, S.hK_pos]))
          (mul_nonneg (le_of_lt S.hlyap_coeff_pos) (exp_nonneg _))

/-! ## Envelope controls r -/

private theorem controls_r (S : LorentzianSolution) (n : ℕ) :
    (S.r n - S.r_star) ^ 2 ≤ envelope S n := by
  unfold envelope
  rw [le_div_iff₀ (sq_pos_of_pos S.r_star_pos)]
  calc (S.r n - S.r_star) ^ 2 * S.r_star ^ 2
      ≤ (S.r n - S.r_star) ^ 2 * (S.r n + S.r_star) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_of_lt S.r_star_pos)
            (by linarith [(S.hr_bdd n).1]) 2)
          (sq_nonneg _)
    _ = (S.r n ^ 2 - S.r_star ^ 2) ^ 2 := by ring
    _ = (S.r n ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2 := by rw [rstar_sq_eq S]
    _ ≤ S.hlyap_coeff * exp (-2 * S.Ψ n) := S.hlyap n

/-! ## Main convergence theorem -/

/-- **Lorentzian global stability via Lyapunov envelope.**
    No step-size constraint. No non-degeneracy assumption.
    Works for ALL K > 2γ unconditionally. -/
theorem lorentzian_envelope_stability (S : LorentzianSolution) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |S.r n - S.r_star| < ε := by
  have hV := barbalat_from_persistence (envelope S) (exp (-2 * S.K * S.δ ^ 2))
    (envelope_nonneg S)
    (envelope_mono S)
    (le_of_lt (exp_pos _))
    (exp_lt_one_iff.mpr (by linarith [mul_pos S.hK_pos (sq_pos_of_pos S.hδ)]))
    (fun M => by
      obtain ⟨m, hm, hδ⟩ := S.hpersist M
      exact ⟨m, hm, envelope_drop S m hδ⟩)
  intro ε hε
  obtain ⟨N, hN⟩ := hV (ε ^ 2) (by positivity)
  exact ⟨N, fun n hn =>
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt (controls_r S n) (hN n hn)) (le_of_lt hε)⟩

end
