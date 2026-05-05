/-
  Body LaSalle Convergence: V → 0 via LaSalle on each body truncation
  ===================================================================
  Proves V → 0 for the standard continuum Kuramoto (γ = |ω|, g ∈ L¹)
  via a clean LaSalle invariance argument applied to each body truncation.

  The argument:
  1. For each M: V_body(M,·) is antitone, nonneg, differentiable,
     with V_body'(M,t) = -K·P_body(M,t) (from Leibniz on bounded body)
  2. V_body(M,·) → L_M ≥ 0 (antitone bounded convergence)
  3. MVT on [n, n+1]: ∃ t_n → ∞ with |V_body'(M, t_n)| → 0
     hence P_body(M, t_n) → 0
  4. Body pair coercivity (eventually): P_body(M) ≥ c(M)·V_body(M)
     Combined with (3): V_body(M, t_n) → 0
  5. V_body(M,·) antitone, so V_body(M,t) ≤ V_body(M, t_n) < ε for t ≥ t_n
     Therefore V_body(M,·) → 0, i.e., L_M = 0
  6. V(t) ≤ V_body(M,t) + tail_mass(M) with tail_mass(M) → 0 as M → ∞
  7. V antitone + (5) + (6) → V → 0

  No finite first moment needed. Works for Lorentzian.
  Alternative proof path to ContinuumBodyLeibniz.BodyODEData.convergence
  (which uses EventualTAC). This one goes through the MVT subsequence.

  0 sorry.
-/

import KuramotoLean.ContinuumBodyLeibniz
import KuramotoLean.WeakStarLaSalle

open Filter Topology Set

noncomputable section

namespace BodyLaSalleConvergence

/-- An antitone nonneg function that dips below every ε converges to 0. -/
theorem antitone_subseq_zero (f : ℝ → ℝ)
    (h_anti : Antitone f) (h_nn : ∀ t, 0 ≤ f t)
    (h_dip : ∀ ε > 0, ∀ T : ℝ, ∃ t, T ≤ t ∧ f t < ε) :
    Tendsto f atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t₀, _, hf⟩ := h_dip ε hε 0
  exact ⟨t₀, fun s hs => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (h_nn s)]
    exact lt_of_le_of_lt (h_anti hs) hf⟩

/-- V_body(M,·) → 0 via MVT + body coercivity. -/
theorem body_tendsto_zero (D : ContinuumBodyLeibniz.BodyODEData) (M : ℝ) (hM : 0 < M) :
    Tendsto (D.V_body M) atTop (nhds 0) := by
  apply antitone_subseq_zero _ (D.Vb_antitone M) (D.hVb_nn M)
  intro ε hε T
  have h_diff : Differentiable ℝ (D.V_body M) :=
    fun t => (D.h_Vb_hasDerivAt M t).differentiableAt
  obtain ⟨L, _, hL⟩ := antitone_bounded_converges (D.V_body M) (D.Vb_antitone M) (D.hVb_nn M)
  have hc := D.h_coer_pos M hM
  have hKc : 0 < D.K * D.coercivity M := mul_pos D.hK hc
  obtain ⟨T₀, hT₀⟩ := D.h_body_coer M hM
  obtain ⟨t, ht, hd⟩ := WeakStarLaSalle.deriv_vanishes_on_subsequence
    (D.V_body M) L hL h_diff (D.K * D.coercivity M * ε) (by positivity) (max T T₀)
  refine ⟨t, le_trans (le_max_left T T₀) ht, ?_⟩
  have h_eq : deriv (D.V_body M) t = -(D.K * D.P_body M t) :=
    (D.h_Vb_hasDerivAt M t).deriv
  have h_neg : deriv (D.V_body M) t ≤ 0 := by
    rw [h_eq]; linarith [mul_nonneg (le_of_lt D.hK) (D.hPb_nn M t)]
  have hKP : D.K * D.P_body M t < D.K * D.coercivity M * ε := by
    have h1 : -(deriv (D.V_body M) t) = D.K * D.P_body M t := by linarith [h_eq]
    have h2 : -(deriv (D.V_body M) t) < D.K * D.coercivity M * ε := by
      calc -(deriv (D.V_body M) t) = |deriv (D.V_body M) t| := (abs_of_nonpos h_neg).symm
        _ < D.K * D.coercivity M * ε := hd
    linarith
  have hKcV : D.K * D.coercivity M * D.V_body M t ≤ D.K * D.P_body M t := by
    have h1 := hT₀ t (le_trans (le_max_right T T₀) ht)
    have h2 : D.K * (D.coercivity M * D.V_body M t) ≤ D.K * D.P_body M t :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt D.hK)
    linarith [show D.K * (D.coercivity M * D.V_body M t) =
      D.K * D.coercivity M * D.V_body M t from by ring]
  exact lt_of_mul_lt_mul_left (lt_of_le_of_lt hKcV hKP) (le_of_lt hKc)

/-- **V → 0 via Body LaSalle.** For each M, V_body(M) → 0.
    Combined with tail vanishing and V antitone: V → 0. -/
theorem convergence (D : ContinuumBodyLeibniz.BodyODEData) :
    Tendsto D.V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_tv := D.h_tail_vanish
  rw [Metric.tendsto_atTop] at h_tv
  obtain ⟨N, hN⟩ := h_tv (ε / 2) (by linarith)
  set M := max N 1
  have hM : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_tail : D.tail_mass M < ε / 2 := by
    have h := hN M (le_max_left N 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.h_tail_mass_nn M)] at h; exact h
  have hVb := body_tendsto_zero D M hM
  rw [Metric.tendsto_atTop] at hVb
  obtain ⟨T, hT⟩ := hVb (ε / 2) (by linarith)
  exact ⟨T, fun t ht => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.hV_nn t)]
    have hVb_t : D.V_body M t < ε / 2 := by
      have := hT t ht
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (D.hVb_nn M t)] at this
    linarith [D.h_tail_bound M t]⟩

end BodyLaSalleConvergence

end
