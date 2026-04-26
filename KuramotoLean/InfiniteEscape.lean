/-
  Kuramoto Stability — Infinite Escape from Instability
  ======================================================

  Proves that ChetaevEscape (one-time exit from ε-ball) extends to
  infinitely many escapes: for any T ≥ 0, there exists t ≥ T with
  some α_k(t) > ε.

  Key result: comparison_growth_from — exponential growth on [T₀, ∞),
  proved by reducing to comparison_growth via time shift.

  This is the missing link for deriving persistence from instability.

  0 sorry target.
-/

import KuramotoLean.ChetaevEscape

open Real Set Filter Finset

noncomputable section

variable {n : ℕ}

/-! ## Time-shift helpers -/

private theorem shift_continuousOn (W : ℝ → ℝ) (T₀ : ℝ)
    (hW_cont : ContinuousOn W (Ici T₀)) :
    ContinuousOn (fun s => W (s + T₀)) (Ici 0) :=
  hW_cont.comp (continuous_add_const T₀).continuousOn
    (fun _ hx => mem_Ici.mpr (le_add_of_nonneg_left (mem_Ici.mp hx)))

private theorem shift_hasDerivAt (W W' : ℝ → ℝ) (T₀ s : ℝ)
    (hW : HasDerivAt W (W' (s + T₀)) (s + T₀)) :
    HasDerivAt (fun u => W (u + T₀)) (W' (s + T₀)) s := by
  have := hW.comp s ((hasDerivAt_id s).add_const T₀)
  simp only [mul_one] at this
  exact this

/-! ## Shifted comparison growth -/

/-- **Comparison growth from arbitrary start time.**
    If W'(t) ≥ μW(t) for t > T₀, then W(t) ≥ W(T₀)·exp(μ(t-T₀)).
    Proved by time-shifting to comparison_growth. -/
theorem comparison_growth_from (W W' : ℝ → ℝ) (μ T₀ : ℝ)
    (_hT₀ : 0 ≤ T₀)
    (hW_cont : ContinuousOn W (Ici T₀))
    (hW_hasderiv : ∀ t, T₀ < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, T₀ < t → μ * W t ≤ W' t) :
    ∀ t, T₀ ≤ t → W T₀ * exp (μ * (t - T₀)) ≤ W t := by
  have hcg := comparison_growth (fun s => W (s + T₀)) (fun s => W' (s + T₀)) μ
    (shift_continuousOn W T₀ hW_cont)
    (fun s hs => shift_hasDerivAt W W' T₀ s (hW_hasderiv (s + T₀) (by linarith)))
    (fun s hs => hW_bound (s + T₀) (by linarith))
  intro t ht
  have h := hcg (t - T₀) (by linarith)
  simp only [zero_add, sub_add_cancel] at h
  exact h

/-- **Comparison growth escape from T₀.**
    W(T₀) > 0 + growth ⟹ W eventually exceeds any level. -/
theorem comparison_growth_escape_from (W W' : ℝ → ℝ) (μ T₀ : ℝ)
    (_hT₀ : 0 ≤ T₀) (hμ : 0 < μ)
    (hW_cont : ContinuousOn W (Ici T₀))
    (hW_hasderiv : ∀ t, T₀ < t → HasDerivAt W (W' t) t)
    (hW_bound : ∀ t, T₀ < t → μ * W t ≤ W' t)
    (hW0 : 0 < W T₀) (η : ℝ) :
    ∃ T, T₀ ≤ T ∧ η ≤ W T := by
  have hβ0 : 0 < (fun s => W (s + T₀)) 0 := by simp only [zero_add]; exact hW0
  obtain ⟨T, hT_nn, hT_bound⟩ := comparison_growth_escape
    (fun s => W (s + T₀)) (fun s => W' (s + T₀)) μ hμ
    (shift_continuousOn W T₀ hW_cont)
    (fun s hs => shift_hasDerivAt W W' T₀ s (hW_hasderiv (s + T₀) (by linarith)))
    (fun s hs => hW_bound (s + T₀) (by linarith))
    hβ0 η
  exact ⟨T + T₀, by linarith, hT_bound⟩

/-! ## Infinite escape from instability -/

/-- **Infinite escape.** For the n-pole ODE with K > K_c and α(0) > 0,
    the trajectory escapes the ε-ball infinitely often:
    for any T ≥ 0, ∃ t ≥ T, k with α_k(t) > ε.

    Proof: at time T, W(T) > 0 (component positivity). If all α_k(t) ≤ ε
    for t ≥ T, comparison_growth_from gives W(t) ≥ W(T)exp(μ(t-T)) → ∞.
    But W(t) ≤ (2/K)ε. Contradiction. -/
theorem instability_infinite_escape (D : NPoleBarrierData n)
    (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam)
    (hdisp : npoleDispersion D.γ D.c D.K lam = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (D.K / 2) * (∑ k, D.c k) * ε ^ 2 ≤ lam / 2)
    (hα_init_pos : ∀ k, 0 < D.α 0 k) :
    ∀ T : ℝ, 0 ≤ T → ∃ t : ℝ, T ≤ t ∧ ∃ k : Fin n, ε < D.α t k := by
  intro T hT
  by_contra h_stay
  simp only [not_exists, not_and, not_lt] at h_stay
  have hα_pos_T : ∀ k, 0 < D.α T k :=
    fun k => component_positive D k (hα_init_pos k) T hT
  have hW_pos : 0 < instabilityW D.c D.γ lam D.α T := by
    unfold instabilityW
    exact Finset.sum_pos
      (fun k _ => mul_pos (mul_pos (D.hc k) (unstableEigenvector_pos D.γ lam D.hγ hlam k))
        (hα_pos_T k))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hW_cont : ContinuousOn (instabilityW D.c D.γ lam D.α) (Ici T) :=
    (instabilityW_cont D lam).mono (Ici_subset_Ici.mpr hT)
  set W := instabilityW D.c D.γ lam D.α
  set W' := fun t => ∑ k, D.c k * unstableEigenvector D.γ lam k *
    nPoleODE D.γ D.c D.K (D.α t) k
  have hW_deriv : ∀ t, T < t → HasDerivAt W (W' t) t :=
    fun t ht => hasDerivAt_instabilityW D.c D.γ D.K lam D.α t (D.hα_ode t (by linarith))
  have hW_growth : ∀ t, T < t → lam / 2 * W t ≤ W' t := by
    intro t ht
    have hα_nn := fun k => D.hα_nn t (by linarith : 0 ≤ t) k
    have hα_le := h_stay t (by linarith : T ≤ t)
    have h_igr := instability_growth_rate D.γ D.c D.K lam (D.α t) ε
      D.hγ D.hc hlam D.hK hε hdisp hα_nn hα_le
    have hW_nn : 0 ≤ W t :=
      instabilityW_nonneg D.c D.γ lam D.α t D.hc D.hγ hlam hα_nn
    calc lam / 2 * W t
        ≤ (lam - (D.K / 2) * (∑ k, D.c k) * ε ^ 2) * W t :=
          mul_le_mul_of_nonneg_right (by linarith) hW_nn
      _ ≤ W' t := h_igr
  obtain ⟨t₀, ht₀_ge, ht₀_bound⟩ := comparison_growth_escape_from W W'
    (lam / 2) T hT (by linarith) hW_cont hW_deriv hW_growth hW_pos
    (2 / D.K * ε + 1)
  have hW_upper : W t₀ ≤ 2 / D.K * ε :=
    instabilityW_le_in_ball D.c D.γ D.K lam ε (D.α t₀)
      D.hK D.hγ D.hc hlam hdisp (D.hα_nn t₀ (by linarith)) (h_stay t₀ ht₀_ge)
  linarith

end
