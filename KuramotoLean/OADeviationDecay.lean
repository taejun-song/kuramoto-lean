/-
  OADeviationDecay.lean
  ======================
  Gronwall decay bound for the single-oscillator OA deviation.

  For a single oscillator with γ > 0:
    φ(t) = (α(t) - α*)²
  satisfies the absorbing-ball estimate:
    φ(t) ≤ φ(0)·exp(-γ·t) + K²/(4γ²)

  The decay rate is γ (not (2γ-3K)/2). The proof uses:
    2p·ODE_RHS = -2γp² + Kp·(r(1-α²) - r*(1-α*²))
    |Kp·cross_term| ≤ K|p| ≤ γp² + K²/(4γ)    [AM-GM: (√γ|p| - K/(2√γ))² ≥ 0]
  giving 2p·ODE_RHS ≤ -γp² + K²/(4γ).

  0 sorry.
-/

import KuramotoLean.ContinuumDerivedGronwall
import KuramotoLean.ContinuumODEExistence

open Real Set Filter Topology

noncomputable section

/-! ## Core algebraic bound -/

/-- **Pointwise Gronwall bound on the OA deviation derivative.**

    For α, α* ∈ (0,1), r ∈ [0,1], r* ∈ (0,1] with equilibrium γα* = K/2·r*(1-α*²):
      2·(α-α*)·ODE_RHS ≤ -γ·(α-α*)² + K²/(4γ)

    Proof: use equilibrium to expand as -2γp² + Kp·cross, bound cross ≤ |p|,
    apply AM-GM (γ|p| - K/2)² ≥ 0. -/
lemma phi_deriv_le_gronwall_form (γ K r r_star α α_star : ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hα : 0 < α) (hα1 : α < 1)
    (hαs : 0 < α_star) (hαs1 : α_star < 1)
    (hr_bdd : |r| ≤ 1) (hr_nn : 0 ≤ r)
    (hr_star_le : r_star ≤ 1) (hr_star_pos : 0 < r_star)
    (hequil : γ * α_star = K / 2 * r_star * (1 - α_star ^ 2)) :
    2 * (α - α_star) * (-γ * α + K / 2 * r * (1 - α ^ 2)) ≤
    -γ * (α - α_star) ^ 2 + K ^ 2 / (4 * γ) := by
  set p := α - α_star with hp_def
  have hr_le : r ≤ 1 := (abs_le.mp hr_bdd).2
  have h1nn : 0 ≤ 1 - α_star ^ 2 := by nlinarith [sq_nonneg α_star]
  have hstar_nn : 0 ≤ r_star * (1 - α_star ^ 2) := mul_nonneg (le_of_lt hr_star_pos) h1nn
  -- Algebraic expansion using equilibrium
  have hexp : 2 * p * (-γ * α + K / 2 * r * (1 - α ^ 2)) =
      -2 * γ * p ^ 2 + K * p * (r * (1 - α ^ 2) - r_star * (1 - α_star ^ 2)) := by
    rw [hp_def]
    linear_combination -2 * (α - α_star) * hequil
  -- Cross term: K*p*(r(1-α²) - r*(1-α*²)) ≤ K*|p|
  have hcross_bdd : |r * (1 - α ^ 2) - r_star * (1 - α_star ^ 2)| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg α, mul_nonneg hr_nn (by nlinarith [sq_nonneg α] : (0:ℝ) ≤ 1 - α^2)]
    · nlinarith [sq_nonneg α, mul_nonneg hr_nn (by nlinarith [sq_nonneg α] : (0:ℝ) ≤ 1 - α^2),
                 mul_nonneg (le_of_lt hr_star_pos) h1nn]
  have hcross : K * p * (r * (1 - α ^ 2) - r_star * (1 - α_star ^ 2)) ≤ K * |p| := by
    by_cases hp : 0 ≤ p
    · rw [abs_of_nonneg hp]
      nlinarith [(abs_le.mp hcross_bdd).2, mul_nonneg (le_of_lt hK) hp]
    · push_neg at hp
      rw [abs_of_neg hp]
      nlinarith [(abs_le.mp hcross_bdd).1, mul_nonpos_of_nonpos_of_nonneg hp.le (le_of_lt hK)]
  -- AM-GM: K|p| ≤ γ·p² + K²/(4γ)  from (2γ|p| - K)² ≥ 0 → 4γ²p² - 4γK|p| + K² ≥ 0
  have hamgm : K * |p| ≤ γ * p ^ 2 + K ^ 2 / (4 * γ) := by
    have h4γ : (0 : ℝ) < 4 * γ := by linarith
    have key : γ * p ^ 2 + K ^ 2 / (4 * γ) - K * |p| =
        (2 * γ * |p| - K) ^ 2 / (4 * γ) := by
      field_simp
      nlinarith [sq_abs p]
    linarith [div_nonneg (sq_nonneg (2 * γ * |p| - K)) h4γ.le]
  -- Combine
  calc 2 * (α - α_star) * (-γ * α + K / 2 * r * (1 - α ^ 2))
      = 2 * p * (-γ * α + K / 2 * r * (1 - α ^ 2)) := by rw [hp_def]
    _ = -2 * γ * p ^ 2 + K * p * (r * (1 - α ^ 2) - r_star * (1 - α_star ^ 2)) := hexp
    _ ≤ -2 * γ * p ^ 2 + K * |p| := by linarith
    _ ≤ -2 * γ * p ^ 2 + γ * p ^ 2 + K ^ 2 / (4 * γ) := by linarith
    _ = -γ * (α - α_star) ^ 2 + K ^ 2 / (4 * γ) := by rw [hp_def]; ring

/-! ## Main theorem: OA deviation decay -/

/-- **Single-oscillator OA deviation decay.**

    For γ > 0 with equilibrium condition, the squared deviation
    (α(t) - α*)² satisfies an absorbing-ball estimate with exponential decay. -/
theorem oa_scalar_deviation_decay (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ) (α_star r_star : ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hr_star_pos : 0 < r_star) (hr_star_le : r_star ≤ 1)
    (hαs : 0 < α_star) (hαs1 : α_star < 1)
    (hequil : γ * α_star = K / 2 * r_star * (1 - α_star ^ 2))
    (hα_ode : ∀ t ≥ 0, HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) :
    ∀ t ≥ 0, (α t - α_star) ^ 2 ≤
      (α 0 - α_star) ^ 2 * rexp (-γ * t) +
      K ^ 2 / (4 * γ ^ 2) := by
  set φ : ℝ → ℝ := fun t => (α t - α_star) ^ 2
  have hφ_cont : ContinuousOn φ (Ici 0) :=
    (hα_cont.sub continuousOn_const).pow 2
  have hφ_deriv : ∀ t, 0 < t →
      HasDerivAt φ (2 * (α t - α_star) * oaScalarRHS γ K r t (α t)) t := by
    intro t ht
    have h_sub := (hα_ode t (le_of_lt ht)).sub_const α_star
    have h_sq := h_sub.pow 2
    convert h_sq using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hc_nn : 0 ≤ K ^ 2 / (4 * γ) := by positivity
  have hφ_bound : ∀ t, 0 < t →
      2 * (α t - α_star) * oaScalarRHS γ K r t (α t) ≤
      -γ * φ t + K ^ 2 / (4 * γ) := by
    intro t ht
    have hαv := hα_inv t (le_of_lt ht)
    have h : 2 * (α t - α_star) * (-γ * (α t) + K / 2 * r t * (1 - (α t) ^ 2)) ≤
        -γ * (α t - α_star) ^ 2 + K ^ 2 / (4 * γ) :=
      phi_deriv_le_gronwall_form γ K (r t) r_star (α t) α_star
        hγ hK hαv.1 hαv.2 hαs hαs1 (hr_bdd t) (hr_nn t (le_of_lt ht))
        hr_star_le hr_star_pos hequil
    simp only [oaScalarRHS, φ]
    linarith
  have h_gronwall := gronwall_with_forcing φ
    (fun t => 2 * (α t - α_star) * oaScalarRHS γ K r t (α t))
    γ (K ^ 2 / (4 * γ))
    hγ hc_nn hφ_cont hφ_deriv hφ_bound
  intro t ht
  have h := h_gronwall t ht
  simp only [φ] at h
  have hdiv : K ^ 2 / (4 * γ) / γ = K ^ 2 / (4 * γ ^ 2) := by
    field_simp
  linarith [hdiv ▸ h]

/-! ## Corollary: uniform bound -/

theorem oa_scalar_deviation_bounded (γ K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ) (α_star r_star : ℝ)
    (hγ : 0 < γ) (hK : 0 < K)
    (hr_bdd : ∀ t, |r t| ≤ 1) (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hr_star_pos : 0 < r_star) (hr_star_le : r_star ≤ 1)
    (hαs : 0 < α_star) (hαs1 : α_star < 1)
    (hequil : γ * α_star = K / 2 * r_star * (1 - α_star ^ 2))
    (hα_ode : ∀ t ≥ 0, HasDerivAt α (oaScalarRHS γ K r t (α t)) t)
    (hα_cont : ContinuousOn α (Ici 0))
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) :
    ∀ t ≥ 0, (α t - α_star) ^ 2 ≤
      (α 0 - α_star) ^ 2 + K ^ 2 / (4 * γ ^ 2) := by
  intro t ht
  have h := oa_scalar_deviation_decay γ K r α α_star r_star
    hγ hK hr_bdd hr_nn hr_star_pos hr_star_le hαs hαs1 hequil hα_ode hα_cont hα_inv t ht
  have hexp_le : rexp (-γ * t) ≤ 1 := by
    calc rexp (-γ * t) ≤ rexp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := exp_zero
  nlinarith [sq_nonneg (α 0 - α_star), exp_nonneg (-γ * t)]

end
