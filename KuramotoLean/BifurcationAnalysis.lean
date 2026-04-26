/-
  Kuramoto Stability — Bifurcation Analysis at Incoherence
  =========================================================

  Completes the bifurcation analysis for the n-pole OA ODE at α = 0.
  The dispersion function h(λ) = (K/2)Σ c_k/(λ+γ_k) is strictly
  decreasing on [0,∞), which gives:
  - K < K_c: h(λ) < 1 for all λ ≥ 0 (incoherence linearly stable)
  - K = K_c: h(0) = 1, h(λ) < 1 for λ > 0 (marginal stability)
  - K > K_c: unique λ* > 0 with h(λ*) = 1 (incoherence unstable)

  0 sorry.
-/

import KuramotoLean.IncoherenceInstability

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-! ## Strict anti-monotonicity of the dispersion function -/

theorem npoleDispersion_strictAntiOn (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K) :
    StrictAntiOn (npoleDispersion γ c K) (Ici 0) := by
  intro a ha b hb hab
  have ha_nn := mem_Ici.mp ha
  unfold npoleDispersion
  apply mul_lt_mul_of_pos_left _ (by linarith : (0 : ℝ) < K / 2)
  exact sum_lt_sum
    (fun k _ => le_of_lt (div_lt_div_of_pos_left (hc k)
      (by linarith [hγ k]) (by linarith)))
    ⟨hn.some, mem_univ _, div_lt_div_of_pos_left (hc hn.some)
      (by linarith [hγ hn.some]) (by linarith)⟩

/-! ## Critical coupling: h(0) = 1 exactly -/

theorem npoleDispersion_at_critical (γ c : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) :
    npoleDispersion γ c (npoleCriticalK γ c) 0 = 1 := by
  rw [npoleDispersion_at_zero]
  unfold npoleCriticalK
  set s := ∑ k, c k / γ k
  have hs : s ≠ 0 := ne_of_gt (sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty)
  field_simp

/-! ## Subcritical stability: no unstable eigenvalue -/

theorem incoherence_stable_subcritical (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hK_sub : K < npoleCriticalK γ c) :
    ∀ lam, 0 ≤ lam → npoleDispersion γ c K lam < 1 := by
  intro lam hlam
  have hsum_pos : (0 : ℝ) < ∑ k, c k / γ k :=
    sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty
  have h0 : npoleDispersion γ c K 0 < 1 := by
    rw [npoleDispersion_at_zero]
    unfold npoleCriticalK at hK_sub
    have : K * (∑ k, c k / γ k) < 2 := by
      rwa [lt_div_iff₀ hsum_pos] at hK_sub
    nlinarith
  rcases eq_or_lt_of_le hlam with rfl | hlam_pos
  · exact h0
  · exact lt_trans
      (npoleDispersion_strictAntiOn γ c K hγ hc hn hK
        (mem_Ici.mpr le_rfl) (mem_Ici.mpr hlam) hlam_pos) h0

theorem incoherence_no_unstable_eigenvalue (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hK_sub : K < npoleCriticalK γ c) :
    ¬∃ lam, 0 ≤ lam ∧ npoleDispersion γ c K lam = 1 := by
  rintro ⟨lam, hlam, heq⟩
  linarith [incoherence_stable_subcritical γ c K hγ hc hn hK hK_sub lam hlam]

/-! ## Critical case: marginal stability -/

theorem critical_no_positive_eigenvalue (γ c : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) :
    ∀ lam, 0 < lam → npoleDispersion γ c (npoleCriticalK γ c) lam < 1 := by
  intro lam hlam
  have hKc_pos : 0 < npoleCriticalK γ c := by
    unfold npoleCriticalK
    exact div_pos two_pos
      (sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty)
  exact lt_of_lt_of_le
    (npoleDispersion_strictAntiOn γ c (npoleCriticalK γ c) hγ hc hn hKc_pos
      (mem_Ici.mpr le_rfl) (mem_Ici.mpr (le_of_lt hlam)) hlam)
    (le_of_eq (npoleDispersion_at_critical γ c hγ hc hn))

/-! ## Supercritical uniqueness: exactly one unstable eigenvalue -/

theorem unstable_eigenvalue_unique (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (lam1 lam2 : ℝ) (h1_nn : 0 ≤ lam1) (h2_nn : 0 ≤ lam2)
    (h1 : npoleDispersion γ c K lam1 = 1)
    (h2 : npoleDispersion γ c K lam2 = 1) :
    lam1 = lam2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · linarith [npoleDispersion_strictAntiOn γ c K hγ hc hn hK
      (mem_Ici.mpr h1_nn) (mem_Ici.mpr h2_nn) h]
  · linarith [npoleDispersion_strictAntiOn γ c K hγ hc hn hK
      (mem_Ici.mpr h2_nn) (mem_Ici.mpr h1_nn) h]

/-! ## K_c is the exact bifurcation threshold -/

theorem npoleCriticalK_pos (γ c : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) :
    0 < npoleCriticalK γ c := by
  unfold npoleCriticalK
  exact div_pos two_pos
    (sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty)

theorem bifurcation_iff (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K) :
    (∃ lam, 0 < lam ∧ npoleDispersion γ c K lam = 1) ↔
    npoleCriticalK γ c < K := by
  constructor
  · rintro ⟨lam, hlam, heq⟩
    by_contra h
    push Not at h
    rcases lt_or_eq_of_le h with hlt | heq_K
    · linarith [incoherence_stable_subcritical γ c K hγ hc hn hK hlt lam (le_of_lt hlam)]
    · rw [heq_K] at heq
      linarith [critical_no_positive_eigenvalue γ c hγ hc hn lam hlam]
  · exact fun hK_super => incoherence_unstable γ c K hγ hc hn hK hK_super

end
