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

/-! ## K_c monotonicity: more damping → harder to synchronize -/

theorem npoleCriticalK_mono_gamma (γ₁ γ₂ c : Fin n → ℝ)
    (hγ₁ : ∀ k, 0 < γ₁ k) (hγ₂ : ∀ k, 0 < γ₂ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n))
    (hle : ∀ k, γ₁ k ≤ γ₂ k) :
    npoleCriticalK γ₁ c ≤ npoleCriticalK γ₂ c := by
  unfold npoleCriticalK
  apply div_le_div_of_nonneg_left (le_of_lt two_pos)
    (sum_pos (fun k _ => div_pos (hc k) (hγ₂ k)) univ_nonempty)
    (sum_le_sum fun k _ => div_le_div_of_nonneg_left (le_of_lt (hc k)) (hγ₁ k) (hle k))

/-! ## Eigenvalue upper bound: λ* ≤ K/2 - γ_min -/

theorem eigenvalue_upper_bound (γ c : Fin n → ℝ) (K lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hc_sum : ∑ k, c k = 1)
    (hlam_pos : 0 < lam) (hdisp : npoleDispersion γ c K lam = 1)
    (γ_min : ℝ) (hγ_min : ∀ k, γ_min ≤ γ k) :
    lam ≤ K / 2 - γ_min := by
  by_contra h_neg
  push Not at h_neg
  have h_strict : ∀ k, K / 2 < lam + γ k := fun k => by linarith [hγ_min k]
  have h_sum : ∑ k, c k / (lam + γ k) < ∑ k, c k / (K / 2) :=
    sum_lt_sum
      (fun k _ => le_of_lt (div_lt_div_of_pos_left (hc k) (by linarith) (h_strict k)))
      ⟨hn.some, mem_univ _, div_lt_div_of_pos_left (hc hn.some) (by linarith) (h_strict hn.some)⟩
  have h_rhs : (∑ k, c k / (K / 2)) = (∑ k, c k) / (K / 2) := (Finset.sum_div ..).symm
  have : npoleDispersion γ c K lam < 1 := by
    unfold npoleDispersion
    calc (K / 2) * ∑ k, c k / (lam + γ k)
        < (K / 2) * ∑ k, c k / (K / 2) :=
          mul_lt_mul_of_pos_left h_sum (by linarith)
      _ = (K / 2) * ((∑ k, c k) / (K / 2)) := by rw [h_rhs]
      _ = 1 := by rw [hc_sum]; field_simp
  linarith

/-! ## Eigenvalue lower bound: λ* ≥ 2(K - K_c)/(K · K_c · Σ c_k/γ_k²) -/

theorem dispersion_difference (γ c : Fin n → ℝ) (K lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hlam_nn : 0 ≤ lam) :
    npoleDispersion γ c K 0 - npoleDispersion γ c K lam =
    (K / 2) * ∑ k, c k * lam / (γ k * (lam + γ k)) := by
  unfold npoleDispersion
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _
  have hγk : (0 : ℝ) < γ k := hγ k
  have hlg : (0 : ℝ) < lam + γ k := by linarith
  field_simp
  ring

theorem eigenvalue_lower_bound (γ c : Fin n → ℝ) (K lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK : 0 < K)
    (hlam_pos : 0 < lam) (hdisp : npoleDispersion γ c K lam = 1)
    (hK_super : npoleCriticalK γ c < K) :
    2 * (K - npoleCriticalK γ c) / (K * npoleCriticalK γ c * ∑ k, c k / γ k ^ 2) ≤ lam := by
  have hKc_pos := npoleCriticalK_pos γ c hγ hc hn
  have hsum_pos : (0 : ℝ) < ∑ k, c k / γ k :=
    sum_pos (fun k _ => div_pos (hc k) (hγ k)) univ_nonempty
  have hsum2_pos : (0 : ℝ) < ∑ k, c k / γ k ^ 2 :=
    sum_pos (fun k _ => div_pos (hc k) (sq_pos_of_pos (hγ k))) univ_nonempty
  have h_diff : npoleDispersion γ c K 0 - 1 =
      (K / 2) * ∑ k, c k * lam / (γ k * (lam + γ k)) := by
    rw [← hdisp, dispersion_difference γ c K lam hγ (le_of_lt hlam_pos)]
  have h0_val : npoleDispersion γ c K 0 = (K / 2) * ∑ k, c k / γ k :=
    npoleDispersion_at_zero γ c K
  rw [h0_val] at h_diff
  have h_gap : (K / 2) * ∑ k, c k / γ k - 1 =
      (K / 2) * ∑ k, c k * lam / (γ k * (lam + γ k)) := h_diff
  have h_bound : ∀ k, c k * lam / (γ k * (lam + γ k)) ≤ c k * lam / γ k ^ 2 := by
    intro k
    have hγk := hγ k
    have hlg : (0 : ℝ) < lam + γ k := by linarith
    apply div_le_div_of_nonneg_left (le_of_lt (mul_pos (hc k) hlam_pos))
      (sq_pos_of_pos hγk)
      (by rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hγk))
  have h_sum_bound : ∑ k, c k * lam / (γ k * (lam + γ k)) ≤
      lam * ∑ k, c k / γ k ^ 2 := by
    calc ∑ k, c k * lam / (γ k * (lam + γ k))
        ≤ ∑ k, c k * lam / γ k ^ 2 := sum_le_sum fun k _ => h_bound k
      _ = lam * ∑ k, c k / γ k ^ 2 := by
          symm; rw [Finset.mul_sum]; congr 1; ext k; ring
  have h_ineq : (K / 2) * ∑ k, c k / γ k - 1 ≤
      (K / 2) * (lam * ∑ k, c k / γ k ^ 2) := by
    linarith [mul_le_mul_of_nonneg_left h_sum_bound (by linarith : (0 : ℝ) ≤ K / 2)]
  have h_Kc_form : (K / 2) * ∑ k, c k / γ k = K / npoleCriticalK γ c := by
    unfold npoleCriticalK; field_simp
  rw [h_Kc_form] at h_ineq
  have h_gap_val : K / npoleCriticalK γ c - 1 = (K - npoleCriticalK γ c) / npoleCriticalK γ c := by
    field_simp
  rw [h_gap_val] at h_ineq
  have h_rhs : (K / 2) * (lam * ∑ k, c k / γ k ^ 2) =
      K * (∑ k, c k / γ k ^ 2) / 2 * lam := by ring
  rw [h_rhs] at h_ineq
  rw [div_le_iff₀ (by positivity : 0 < K * npoleCriticalK γ c * ∑ k, c k / γ k ^ 2)]
  have h_scaled := mul_le_mul_of_nonneg_right h_ineq
    (show (0 : ℝ) ≤ 2 * npoleCriticalK γ c from by positivity)
  have lhs_eq : (K - npoleCriticalK γ c) / npoleCriticalK γ c *
      (2 * npoleCriticalK γ c) = 2 * (K - npoleCriticalK γ c) := by
    field_simp [ne_of_gt hKc_pos]
  have rhs_eq : (K * ∑ k, c k / γ k ^ 2) / 2 * lam *
      (2 * npoleCriticalK γ c) =
      lam * (K * npoleCriticalK γ c * ∑ k, c k / γ k ^ 2) := by ring
  linarith

end
