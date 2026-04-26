/-
  Kuramoto Stability — Self-Consistency Fixed Point
  ===================================================

  For the n-pole OA system with K > K_c, the self-consistency map
  Φ(r) = Σ c_k · α*_k(γ_k, K, r) has a fixed point r* ∈ (0,1).

  Key idea: Φ(r) = r · S(r) with slope function
    S(r) = Σ c_k · K / (γ_k + √(γ_k² + K²r²))
  S(0) = K/K_c > 1 (supercritical), S(1) < 1 (dissipation).
  Continuity + IVT gives r* with Φ(r*) = r*.

  0 sorry target.
-/

import KuramotoLean.EquilibriumFormula
import KuramotoLean.IncoherenceInstability

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Definitions -/

def scSlope (γ c : Fin n → ℝ) (K r : ℝ) : ℝ :=
  ∑ k, c k * K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r ^ 2))

def scMapR (γ c : Fin n → ℝ) (K r : ℝ) : ℝ :=
  r * scSlope γ c K r

/-! ## Denominator helpers -/

private theorem den_pos (γ_k : ℝ) (hγ : 0 < γ_k) (K r : ℝ) :
    (0 : ℝ) < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
  have := sqrt_nonneg (γ_k ^ 2 + K ^ 2 * r ^ 2); linarith

private theorem den_ne_zero (γ_k : ℝ) (hγ : 0 < γ_k) (K r : ℝ) :
    γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) ≠ 0 :=
  ne_of_gt (den_pos γ_k hγ K r)

private theorem den_continuous (γ_k K : ℝ) :
    Continuous (fun r : ℝ => γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) :=
  continuous_const.add (Real.continuous_sqrt.comp
    (continuous_const.add (continuous_const.mul (continuous_pow 2))))

/-! ## Continuity -/

theorem scSlope_continuous (γ c : Fin n → ℝ) (K : ℝ) (hγ : ∀ k, 0 < γ k) :
    Continuous (scSlope γ c K) := by
  unfold scSlope; apply continuous_finset_sum; intro k _
  exact continuous_const.div (den_continuous (γ k) K)
    (fun r => den_ne_zero (γ k) (hγ k) K r)

/-! ## Slope at r = 0 equals K/K_c -/

theorem scSlope_at_zero (γ c : Fin n → ℝ) (K : ℝ) (hγ : ∀ k, 0 < γ k) :
    scSlope γ c K 0 = (K / 2) * ∑ k, c k / γ k := by
  unfold scSlope; rw [Finset.mul_sum]; congr 1; ext k
  have : sqrt ((γ k) ^ 2 + K ^ 2 * (0 : ℝ) ^ 2) = γ k := by
    rw [show (γ k) ^ 2 + K ^ 2 * (0 : ℝ) ^ 2 = (γ k) ^ 2 from by ring]
    exact sqrt_sq (le_of_lt (hγ k))
  rw [this]; ring

theorem scSlope_zero_gt_one (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hn : Nonempty (Fin n))
    (hK_super : npoleCriticalK γ c < K) :
    1 < scSlope γ c K 0 := by
  rw [scSlope_at_zero γ c K hγ, ← npoleDispersion_at_zero]
  exact npoleDispersion_supercritical γ c K hγ hc hn hK_super

/-! ## Slope at r = 1 is < 1 -/

private theorem K_lt_den_at_one (γ_k K : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) :
    K < γ_k + sqrt (γ_k ^ 2 + K ^ 2 * (1 : ℝ) ^ 2) := by
  have h1 : K ≤ sqrt (γ_k ^ 2 + K ^ 2 * 1 ^ 2) := by
    calc K = sqrt (K ^ 2) := (sqrt_sq (le_of_lt hK)).symm
      _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * 1 ^ 2) :=
        sqrt_le_sqrt (by nlinarith [sq_nonneg γ_k])
  linarith

theorem scSlope_one_lt (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) (hc_sum : ∑ k : Fin n, c k = 1) :
    scSlope γ c K 1 < 1 := by
  have h : scSlope γ c K 1 < ∑ k : Fin n, c k := by
    unfold scSlope
    have step_lt : ∀ k : Fin n,
        c k * K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * 1 ^ 2)) < c k := by
      intro k
      rw [mul_div_assoc]
      calc c k * (K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * 1 ^ 2)))
          < c k * 1 := mul_lt_mul_of_pos_left
            ((div_lt_one (den_pos (γ k) (hγ k) K 1)).mpr
              (K_lt_den_at_one (γ k) K (hγ k) hK)) (hc k)
        _ = c k := mul_one _
    exact Finset.sum_lt_sum (fun k _ => le_of_lt (step_lt k))
      ⟨hn.some, mem_univ _, step_lt hn.some⟩
  linarith

/-! ## Existence of r₀ > 0 with slope > 1 -/

theorem exists_slope_gt_one (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hn : Nonempty (Fin n))
    (hK_super : npoleCriticalK γ c < K) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ 1 < scSlope γ c K r₀ := by
  have hcont := scSlope_continuous γ c K hγ
  have hgt := scSlope_zero_gt_one γ c K hγ hc hn hK_super
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hcont) 0 hgt
  refine ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  exact hball (Metric.mem_ball.mpr (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)))

/-! ## Fixed point existence via IVT -/

theorem sc_fixed_point_exists (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) (hK_super : npoleCriticalK γ c < K)
    (hc_sum : ∑ k : Fin n, c k = 1) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      scMapR γ c K r_star = r_star := by
  obtain ⟨r₀, hr₀_pos, hr₀_lt, hr₀_slope⟩ :=
    exists_slope_gt_one γ c K hγ hc hn hK_super
  have hr₀_le : r₀ ≤ 1 := le_of_lt hr₀_lt
  have hr₀_gt : r₀ < scMapR γ c K r₀ := by
    unfold scMapR
    calc r₀ = r₀ * 1 := (mul_one _).symm
      _ < r₀ * scSlope γ c K r₀ := mul_lt_mul_of_pos_left hr₀_slope hr₀_pos
  have h1_lt : scMapR γ c K 1 < 1 := by
    unfold scMapR; rw [one_mul]
    exact scSlope_one_lt γ c K hγ hc hK hn hc_sum
  set h := fun r => scMapR γ c K r - r
  have hh_cont : Continuous h :=
    ((continuous_id.mul (scSlope_continuous γ c K hγ)).sub continuous_id)
  obtain ⟨r_star, hr_mem, hr_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr hr₀_le) (right_mem_Icc.mpr hr₀_le)
      continuousOn_const hh_cont.continuousOn
      (le_of_lt (sub_pos.mpr hr₀_gt)) (le_of_lt (sub_neg.mpr h1_lt))
  obtain ⟨hr_lo, hr_hi⟩ := mem_Icc.mp hr_mem
  exact ⟨r_star,
    lt_of_lt_of_le hr₀_pos hr_lo,
    lt_of_le_of_ne hr_hi (fun heq => by subst heq; linarith),
    by linarith [hr_eq.symm]⟩

/-! ## Rationalization identity -/

theorem explicitEquil_rationalized (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    explicitEquil γ_k K r = K * r / (γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)) := by
  unfold explicitEquil
  set S := sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
  have hS_sq : S ^ 2 = γ_k ^ 2 + K ^ 2 * r ^ 2 := sq_sqrt (by positivity)
  have hS_ge : γ_k ≤ S := by
    calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
      _ ≤ S := sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
  rw [div_eq_div_iff (ne_of_gt (mul_pos hK hr)) (ne_of_gt (by linarith : 0 < γ_k + S))]
  have h1 : (-γ_k + S) * (γ_k + S) = S ^ 2 - γ_k ^ 2 := by ring
  have h2 : K * r * (K * r) = K ^ 2 * r ^ 2 := by ring
  linarith [h1, h2, hS_sq]

/-! ## Connection to equilibrium: the fixed point grounds α* -/

theorem sc_fixed_point_grounds (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) (hK_super : npoleCriticalK γ c < K)
    (hc_sum : ∑ k : Fin n, c k = 1) :
    ∃ r_star : ℝ, 0 < r_star ∧ r_star < 1 ∧
      (∀ k, 0 < explicitEquil (γ k) K r_star) ∧
      (∀ k, explicitEquil (γ k) K r_star < 1) ∧
      (∀ k, componentEquil (γ k) K r_star (explicitEquil (γ k) K r_star) = 0) ∧
      ∑ k, c k * explicitEquil (γ k) K r_star = r_star := by
  obtain ⟨r_star, hr_pos, hr_lt, hr_eq⟩ :=
    sc_fixed_point_exists γ c K hγ hc hK hn hK_super hc_sum
  refine ⟨r_star, hr_pos, hr_lt,
    fun k => explicitEquil_pos (γ k) K r_star (hγ k) hK hr_pos,
    fun k => explicitEquil_lt_one (γ k) K r_star (hγ k) hK hr_pos,
    fun k => explicitEquil_solves (γ k) K r_star (hγ k) hK hr_pos,
    ?_⟩
  have h_eq : scMapR γ c K r_star = ∑ k, c k * explicitEquil (γ k) K r_star := by
    unfold scMapR scSlope
    rw [Finset.mul_sum]; congr 1; ext k
    rw [explicitEquil_rationalized (γ k) K r_star (hγ k) hK hr_pos]; ring
  rw [← h_eq]; exact hr_eq

/-! ## Strict monotonicity of slope → uniqueness of fixed point -/

theorem scSlope_strictAntiOn (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) :
    StrictAntiOn (scSlope γ c K) (Ici 0) := by
  intro r₁ hr₁ r₂ hr₂ h12
  unfold scSlope
  have step : ∀ k : Fin n,
      c k * K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r₂ ^ 2)) <
      c k * K / (γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r₁ ^ 2)) := by
    intro k
    have h_sq : (γ k) ^ 2 + K ^ 2 * r₁ ^ 2 < (γ k) ^ 2 + K ^ 2 * r₂ ^ 2 := by
      have h1 : r₁ ^ 2 < r₂ ^ 2 := by nlinarith [mem_Ici.mp hr₁]
      linarith [mul_lt_mul_of_pos_left h1 (sq_pos_of_pos hK)]
    have hd_lt : γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r₁ ^ 2) <
        γ k + sqrt ((γ k) ^ 2 + K ^ 2 * r₂ ^ 2) := by
      have := sqrt_lt_sqrt (by positivity : 0 ≤ (γ k) ^ 2 + K ^ 2 * r₁ ^ 2) h_sq
      linarith
    exact div_lt_div_of_pos_left (mul_pos (hc k) hK) (den_pos (γ k) (hγ k) K r₁) hd_lt
  exact Finset.sum_lt_sum (fun k _ => le_of_lt (step k))
    ⟨hn.some, mem_univ _, step hn.some⟩

theorem sc_fixed_point_unique (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n))
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : scMapR γ c K r₁ = r₁) (h₂ : scMapR γ c K r₂ = r₂) :
    r₁ = r₂ := by
  unfold scMapR at h₁ h₂
  have hs₁ : scSlope γ c K r₁ = 1 :=
    mul_left_cancel₀ (ne_of_gt hr₁) (h₁.trans (mul_one r₁).symm)
  have hs₂ : scSlope γ c K r₂ = 1 :=
    mul_left_cancel₀ (ne_of_gt hr₂) (h₂.trans (mul_one r₂).symm)
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · exfalso
    have := scSlope_strictAntiOn γ c K hγ hc hK hn
      (mem_Ici.mpr (le_of_lt hr₁)) (mem_Ici.mpr (le_of_lt hr₂)) h
    linarith
  · exact h
  · exfalso
    have := scSlope_strictAntiOn γ c K hγ hc hK hn
      (mem_Ici.mpr (le_of_lt hr₂)) (mem_Ici.mpr (le_of_lt hr₁)) h
    linarith

/-! ## Subcritical: no PLS fixed point -/

theorem scSlope_zero_le_one (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hn : Nonempty (Fin n))
    (hK_sub : K ≤ npoleCriticalK γ c) :
    scSlope γ c K 0 ≤ 1 := by
  rw [scSlope_at_zero γ c K hγ]
  have hsum_pos : 0 < ∑ k : Fin n, c k / γ k :=
    Finset.sum_pos (fun k _ => div_pos (hc k) (hγ k))
      (Finset.univ_nonempty (α := Fin n))
  unfold npoleCriticalK at hK_sub
  rw [le_div_iff₀ hsum_pos] at hK_sub
  linarith

theorem no_pls_subcritical (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) (hK_sub : K ≤ npoleCriticalK γ c) :
    ∀ r, 0 < r → scMapR γ c K r < r := by
  intro r hr
  have hs_lt : scSlope γ c K r < 1 := by
    have hs0 := scSlope_zero_le_one γ c K hγ hc hn hK_sub
    have hanti := scSlope_strictAntiOn γ c K hγ hc hK hn
    calc scSlope γ c K r
        < scSlope γ c K 0 := hanti (mem_Ici.mpr (le_refl _))
          (mem_Ici.mpr (le_of_lt hr)) hr
      _ ≤ 1 := hs0
  unfold scMapR
  calc r * scSlope γ c K r < r * 1 := mul_lt_mul_of_pos_left hs_lt hr
    _ = r := mul_one _

theorem no_pls_fixed_point_subcritical (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n)) (hK_sub : K ≤ npoleCriticalK γ c) :
    ∀ r, 0 < r → scMapR γ c K r ≠ r :=
  fun r hr => ne_of_lt (no_pls_subcritical γ c K hγ hc hK hn hK_sub r hr)

/-! ## Attractivity of the fixed point: Φ pushes toward r* -/

theorem sc_map_above_r (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n))
    (r_star : ℝ) (hr_pos : 0 < r_star)
    (h_fp : scMapR γ c K r_star = r_star)
    (r : ℝ) (hr : 0 < r) (hr_lt : r < r_star) :
    r < scMapR γ c K r := by
  unfold scMapR
  have hs_star : scSlope γ c K r_star = 1 :=
    mul_left_cancel₀ (ne_of_gt hr_pos) (h_fp.trans (mul_one r_star).symm)
  have hs_gt : 1 < scSlope γ c K r := by
    rw [← hs_star]
    exact scSlope_strictAntiOn γ c K hγ hc hK hn
      (mem_Ici.mpr (le_of_lt hr)) (mem_Ici.mpr (le_of_lt hr_pos)) hr_lt
  calc r = r * 1 := (mul_one _).symm
    _ < r * scSlope γ c K r := mul_lt_mul_of_pos_left hs_gt hr

theorem sc_map_below_r (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) (hK : 0 < K)
    (hn : Nonempty (Fin n))
    (r_star : ℝ) (hr_pos : 0 < r_star)
    (h_fp : scMapR γ c K r_star = r_star)
    (r : ℝ) (hr : 0 < r) (hr_gt : r_star < r) :
    scMapR γ c K r < r := by
  unfold scMapR
  have hs_star : scSlope γ c K r_star = 1 :=
    mul_left_cancel₀ (ne_of_gt hr_pos) (h_fp.trans (mul_one r_star).symm)
  have hs_lt : scSlope γ c K r < 1 := by
    rw [← hs_star]
    exact scSlope_strictAntiOn γ c K hγ hc hK hn
      (mem_Ici.mpr (le_of_lt hr_pos)) (mem_Ici.mpr (le_of_lt hr)) hr_gt
  calc r * scSlope γ c K r < r * 1 := mul_lt_mul_of_pos_left hs_lt hr
    _ = r := mul_one _

/-! ## Equilibrium monotonicity in r: larger order parameter → larger equilibrium -/

theorem explicitEquil_mono_r (γ_k K r₁ r₂ : ℝ) (hγ : 0 < γ_k) (hK : 0 < K)
    (hr₁ : 0 < r₁) (h : r₁ < r₂) :
    explicitEquil γ_k K r₁ < explicitEquil γ_k K r₂ := by
  have hr₂ : 0 < r₂ := lt_trans hr₁ h
  have hα₁_pos := explicitEquil_pos γ_k K r₁ hγ hK hr₁
  have hα₁_lt := explicitEquil_lt_one γ_k K r₁ hγ hK hr₁
  have hα₁_sol := explicitEquil_solves γ_k K r₁ hγ hK hr₁
  have hα₂_sol := explicitEquil_solves γ_k K r₂ hγ hK hr₂
  have h_pos_at_α₁ : 0 < componentEquil γ_k K r₂ (explicitEquil γ_k K r₁) := by
    have : componentEquil γ_k K r₂ (explicitEquil γ_k K r₁) -
        componentEquil γ_k K r₁ (explicitEquil γ_k K r₁) =
        (K / 2) * (r₂ - r₁) * (1 - (explicitEquil γ_k K r₁) ^ 2) := by
      unfold componentEquil; ring
    rw [hα₁_sol, sub_zero] at this
    rw [this]; apply mul_pos (mul_pos (by linarith) (by linarith))
    nlinarith [hα₁_lt]
  have hα₂_pos := explicitEquil_pos γ_k K r₂ hγ hK hr₂
  have hα₂_lt := explicitEquil_lt_one γ_k K r₂ hγ hK hr₂
  by_contra h_not
  push_neg at h_not
  have h_le := h_not
  have h_anti := componentEquil_strictAntiOn γ_k K r₂ hγ hK hr₂
  rcases eq_or_lt_of_le h_le with heq | hlt
  · linarith [heq ▸ hα₂_sol]
  · have := h_anti ⟨le_of_lt hα₂_pos, le_of_lt hα₂_lt⟩
      ⟨le_of_lt hα₁_pos, le_of_lt hα₁_lt⟩ hlt
    linarith [hα₂_sol]

/-! ## Equilibrium monotonicity in γ: larger damping → smaller equilibrium -/

theorem explicitEquil_anti_gamma (γ₁ γ₂ K r : ℝ)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hK : 0 < K) (hr : 0 < r)
    (h : γ₁ < γ₂) :
    explicitEquil γ₂ K r < explicitEquil γ₁ K r := by
  rw [explicitEquil_rationalized γ₁ K r hγ₁ hK hr,
      explicitEquil_rationalized γ₂ K r hγ₂ hK hr]
  have h_sq : γ₁ ^ 2 + K ^ 2 * r ^ 2 < γ₂ ^ 2 + K ^ 2 * r ^ 2 := by nlinarith
  have hden_lt : γ₁ + sqrt (γ₁ ^ 2 + K ^ 2 * r ^ 2) <
      γ₂ + sqrt (γ₂ ^ 2 + K ^ 2 * r ^ 2) := by
    have := sqrt_lt_sqrt (by positivity : 0 ≤ γ₁ ^ 2 + K ^ 2 * r ^ 2) h_sq
    linarith
  exact div_lt_div_of_pos_left (mul_pos hK hr)
    (den_pos γ₁ hγ₁ K r) hden_lt

theorem explicitEquil_mono_gamma (γ₁ γ₂ K r : ℝ)
    (hγ₁ : 0 < γ₁) (hK : 0 < K) (hr : 0 < r)
    (h : γ₁ ≤ γ₂) :
    explicitEquil γ₂ K r ≤ explicitEquil γ₁ K r := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (explicitEquil_anti_gamma γ₁ γ₂ K r hγ₁
      (lt_trans hγ₁ hlt) hK hr hlt)

/-! ## Equilibrium monotonicity in K: larger coupling → larger equilibrium -/

theorem explicitEquil_mono_K (γ_k K₁ K₂ r : ℝ) (hγ : 0 < γ_k)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hr : 0 < r) (h : K₁ < K₂) :
    explicitEquil γ_k K₁ r < explicitEquil γ_k K₂ r := by
  have hα₁_pos := explicitEquil_pos γ_k K₁ r hγ hK₁ hr
  have hα₁_lt := explicitEquil_lt_one γ_k K₁ r hγ hK₁ hr
  have hα₁_sol := explicitEquil_solves γ_k K₁ r hγ hK₁ hr
  have hα₂_sol := explicitEquil_solves γ_k K₂ r hγ hK₂ hr
  have h_pos_at_α₁ : 0 < componentEquil γ_k K₂ r (explicitEquil γ_k K₁ r) := by
    have : componentEquil γ_k K₂ r (explicitEquil γ_k K₁ r) -
        componentEquil γ_k K₁ r (explicitEquil γ_k K₁ r) =
        ((K₂ - K₁) / 2) * r * (1 - (explicitEquil γ_k K₁ r) ^ 2) := by
      unfold componentEquil; ring
    rw [hα₁_sol, sub_zero] at this
    rw [this]; apply mul_pos (mul_pos (by linarith) hr); nlinarith [hα₁_lt]
  have hα₂_pos := explicitEquil_pos γ_k K₂ r hγ hK₂ hr
  have hα₂_lt := explicitEquil_lt_one γ_k K₂ r hγ hK₂ hr
  by_contra h_not
  push_neg at h_not
  rcases eq_or_lt_of_le h_not with heq | hlt
  · linarith [heq ▸ hα₂_sol]
  · have := componentEquil_strictAntiOn γ_k K₂ r hγ hK₂ hr
      ⟨le_of_lt hα₂_pos, le_of_lt hα₂_lt⟩
      ⟨le_of_lt hα₁_pos, le_of_lt hα₁_lt⟩ hlt
    linarith [hα₂_sol]

/-! ## Quantitative bounds on equilibrium -/

theorem explicitEquil_upper (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    explicitEquil γ_k K r ≤ K * r / (2 * γ_k) := by
  rw [explicitEquil_rationalized γ_k K r hγ hK hr]
  have hden : 2 * γ_k ≤ γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) := by
    have : γ_k ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
      calc γ_k = sqrt (γ_k ^ 2) := (sqrt_sq (le_of_lt hγ)).symm
        _ ≤ sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) :=
          sqrt_le_sqrt (by nlinarith [sq_nonneg (K * r)])
    linarith
  exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hK hr)) (by positivity) hden

theorem explicitEquil_lower (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    K * r / (2 * γ_k + K * r) ≤ explicitEquil γ_k K r := by
  rw [explicitEquil_rationalized γ_k K r hγ hK hr]
  have hKr : 0 < K * r := mul_pos hK hr
  have hden : γ_k + sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) ≤ 2 * γ_k + K * r := by
    have : sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2) ≤ γ_k + K * r := by
      calc sqrt (γ_k ^ 2 + K ^ 2 * r ^ 2)
          ≤ sqrt ((γ_k + K * r) ^ 2) :=
            sqrt_le_sqrt (by nlinarith [mul_pos hγ hKr])
        _ = γ_k + K * r := sqrt_sq (by linarith)
    linarith
  exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hK hr)) (by positivity) hden

theorem explicitEquil_tail_bound (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    K * r / (2 * γ_k + K * r) ≤ explicitEquil γ_k K r ∧
    explicitEquil γ_k K r ≤ K * r / (2 * γ_k) :=
  ⟨explicitEquil_lower γ_k K r hγ hK hr, explicitEquil_upper γ_k K r hγ hK hr⟩

theorem explicitEquil_lower_from_gamma_max (γ_k K r γ_max : ℝ)
    (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r)
    (hγ_le : γ_k ≤ γ_max) :
    K * r / (2 * γ_max + K * r) ≤ explicitEquil γ_k K r :=
  le_trans (by
    have hKr := le_of_lt (mul_pos hK hr)
    exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hK hr))
      (by positivity) (by linarith))
    (explicitEquil_lower γ_k K r hγ hK hr)

end
