/-
  Kuramoto Stability — Continuous Lorentzian Instance
  ====================================================
  Applies continuous_global_stability to the Lorentzian OA ODE.
  No step-size constraint. Works for ALL K > 2γ.
  0 sorry.
-/

import KuramotoLean.ContinuousStability
import KuramotoLean.LorentzianInstance

open Real

noncomputable section

private theorem cont_lorentzian_hΦ_unique (K γ : ℝ) (hK : 0 < K) (hKγ : K > 2 * γ) :
    ∀ x, 0 ≤ x → x ≤ 1 →
    lorentzianPhi K γ x = x → x = 0 ∨ x = Real.sqrt (1 - 2 * γ / K) := by
  intro x hx0 _ hfp
  rcases lorentzianPhi_unique K γ x hK hKγ hfp with h | h
  · exact Or.inl h
  · right
    rw [(Real.sqrt_sq hx0).symm, h]

/-- Construct ContinuousKuramotoData from a continuous Lorentzian solution. -/
def continuousLorentzianData (K γ : ℝ) (hK : 0 < K) (hKγ : K > 2 * γ)
    (r : ℝ → ℝ) (hr_cont : Continuous r)
    (hr_bdd : ∀ t, 0 ≤ r t ∧ r t ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ δ ≤ r t)
    (hsc_decay : ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |lorentzianODE K γ (r t)| < ε) :
    ContinuousKuramotoData where
  r := r
  r_star := Real.sqrt (1 - 2 * γ / K)
  hr_star := Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hKγ)
  hr_bdd := hr_bdd
  hr_cont := hr_cont
  δ := δ
  hδ := hδ
  hpersist := hpersist
  Φ := lorentzianPhi K γ
  hΦ_unique := cont_lorentzian_hΦ_unique K γ hK hKγ
  hΦ_continuous := lorentzianPhi_continuous K γ
  hsc_decay := fun ε hε => by
    obtain ⟨T, hT⟩ := hsc_decay ε hε
    exact ⟨T, fun t ht => by rw [lorentzianPhi_sc_err]; exact hT t ht⟩

/-- **Continuous Lorentzian global stability.** For ALL K > 2γ.
    Given any continuous solution r(t) of the Lorentzian ODE with
    persistence and self-consistency decay, r(t) → r*. -/
theorem lorentzian_continuous_global_stability (K γ : ℝ)
    (hK : 0 < K) (hKγ : K > 2 * γ)
    (r : ℝ → ℝ) (hr_cont : Continuous r)
    (hr_bdd : ∀ t, 0 ≤ r t ∧ r t ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hpersist : ∀ T : ℝ, ∃ t, T ≤ t ∧ δ ≤ r t)
    (hsc_decay : ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |lorentzianODE K γ (r t)| < ε) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |r t - Real.sqrt (1 - 2 * γ / K)| < ε :=
  continuous_global_stability
    (continuousLorentzianData K γ hK hKγ r hr_cont hr_bdd δ hδ hpersist hsc_decay)

end
