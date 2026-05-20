/-
  Barbalat's Lemma and Global Dichotomy
  ======================================
  For dΨ/dt = K·f with f ≥ 0 and f uniformly continuous:
    - f frequently ≥ ε ⟹ Ψ unbounded (strengthens eta_sq_drops_below)
    - Ψ bounded ⟹ f → 0 (Barbalat's lemma)

  For the complex OA (f = |η|², Ψ monotone), this gives:
    Either |η(t)|² → 0 (incoherence) or Ψ(t) → ∞ (sync onset).
  For K > Kc the incoherent state is unstable, so Ψ → ∞ unconditionally.

  4 theorems, 0 sorry.
-/

import KuramotoLean.PsiBarbalatBridge

open MeasureTheory Complex Real Set Filter Topology

noncomputable section

/-- **UC growth from frequent excursions.** If dΨ/dt = K·f with f ≥ 0,
    f is uniformly continuous, and f ≥ ε infinitely often, then Ψ → ∞.
    Proof: UC converts each point f(t) ≥ ε into an interval of length δ/2
    where f ≥ ε/2, giving Ψ growth ≥ K(ε/2)(δ/2) per event. Iterating
    n times gives Ψ ≥ Ψ(0) + n·K(ε/2)(δ/2), which exceeds any bound. -/
theorem psi_diverges_of_frequent_eta
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (f : ℝ → ℝ) (hf_nn : ∀ t, 0 ≤ f t)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * f t) t)
    (h_uc : ∀ ε > 0, ∃ δ > 0, ∀ s t, |s - t| < δ → |f s - f t| < ε)
    (ε : ℝ) (hε : 0 < ε) (h_freq : ∀ T : ℝ, ∃ t, T ≤ t ∧ ε ≤ f t) :
    ∀ C, ∃ t, C < Ψ t := by
  obtain ⟨δ, hδ, h_uc_δ⟩ := h_uc (ε / 2) (by linarith)
  have hΨ_mono := psi_monotone_of_energy_identity Ψ K (le_of_lt hK) f hf_nn h_deriv
  set step := K * (ε / 2) * (δ / 2)
  have hstep : 0 < step := by positivity
  have h_growth : ∀ n : ℕ, ∃ T, Ψ 0 + ↑n * step ≤ Ψ T := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨T₀, hT₀⟩ := ih
      obtain ⟨s, hs, hfs⟩ := h_freq T₀
      have h_lb : ∀ u, s ≤ u → u ≤ s + δ / 2 → ε / 2 ≤ f u := by
        intro u hsu hud
        have h_close : |u - s| < δ := by rw [abs_of_nonneg (by linarith)]; linarith
        have h_diff := h_uc_δ u s h_close
        rw [abs_lt] at h_diff
        linarith
      have h_psi := psi_growth_lower Ψ K hK f h_deriv s (s + δ / 2)
        (by linarith) (ε / 2) h_lb
      refine ⟨s + δ / 2, ?_⟩
      rw [show s + δ / 2 - s = δ / 2 from by ring] at h_psi
      have h_psi' : step ≤ Ψ (s + δ / 2) - Ψ s := h_psi
      push_cast
      have : (↑n + 1 : ℝ) * step = ↑n * step + step := by ring
      linarith [hΨ_mono hs]
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - Ψ 0) / step)
  obtain ⟨T, hT⟩ := h_growth n
  exact ⟨T, by nlinarith [(div_lt_iff₀ hstep).mp hn]⟩

/-- **Barbalat's lemma.** If dΨ/dt = K·f with f ≥ 0, Ψ bounded above,
    and f uniformly continuous, then f(t) → 0 as t → ∞. -/
theorem barbalat_tendsto_zero
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (f : ℝ → ℝ) (hf_nn : ∀ t, 0 ≤ f t)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * f t) t)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (h_uc : ∀ ε > 0, ∃ δ > 0, ∀ s t, |s - t| < δ → |f s - f t| < ε) :
    Tendsto f atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  by_contra h_not
  push Not at h_not
  obtain ⟨ε, hε, h_freq⟩ := h_not
  have h_freq' : ∀ T : ℝ, ∃ t, T ≤ t ∧ ε ≤ f t := by
    intro T; obtain ⟨t, ht, hft⟩ := h_freq T
    exact ⟨t, ht, by rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nn t)] at hft⟩
  obtain ⟨t, ht⟩ := psi_diverges_of_frequent_eta Ψ K hK f hf_nn h_deriv h_uc ε hε h_freq' M
  linarith [hM t]

/-- **Global dichotomy.** For the complex OA energy system, either:
    (1) |η(t)|² → 0 (system approaches incoherence), or
    (2) Ψ(t) is unbounded above (synchronization onset).
    There is no third option when |η|² is uniformly continuous. -/
theorem psi_eta_dichotomy
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ) (hη_nn : ∀ t, 0 ≤ η_sq t)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (h_uc : ∀ ε > 0, ∃ δ > 0, ∀ s t, |s - t| < δ → |η_sq s - η_sq t| < ε) :
    Tendsto η_sq atTop (nhds 0) ∨ ∀ M, ∃ t, M < Ψ t := by
  by_cases hΨ : ∃ M, ∀ t, Ψ t ≤ M
  · obtain ⟨M, hM⟩ := hΨ
    exact Or.inl (barbalat_tendsto_zero Ψ K hK η_sq hη_nn h_deriv M hM h_uc)
  · push Not at hΨ
    exact Or.inr hΨ

/-- **Supercritical Ψ divergence.** If η² is uniformly continuous and
    does not converge to 0 (instability of incoherent state for K > Kc),
    then Ψ(t) → ∞. This is synchronization onset: oscillators approach
    the unit circle boundary. -/
theorem psi_diverges_of_instability
    (Ψ : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (η_sq : ℝ → ℝ) (hη_nn : ∀ t, 0 ≤ η_sq t)
    (h_deriv : ∀ t, HasDerivAt Ψ (K * η_sq t) t)
    (h_uc : ∀ ε > 0, ∃ δ > 0, ∀ s t, |s - t| < δ → |η_sq s - η_sq t| < ε)
    (M : ℝ) (hM : ∀ t, Ψ t ≤ M)
    (h_instab : ¬Tendsto η_sq atTop (nhds 0)) :
    False :=
  h_instab (barbalat_tendsto_zero Ψ K hK η_sq hη_nn h_deriv M hM h_uc)

end
