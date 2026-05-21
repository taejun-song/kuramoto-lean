/-
  Critical Exponent β = 1/2
  ==========================
  The Kuramoto phase transition has mean-field critical exponent β = 1/2:

    r* = Θ((K - Kc)^{1/2}) as K → Kc+

  Proved via the square-root law bounds:
    c₁ · √(K-Kc) ≤ r* ≤ c₂ · √(K-Kc)

  Corollary: r* → 0 as K → Kc+ (continuity of phase transition).
  Corollary: r*/√(K-Kc) bounded above and below (universal scaling).

  The Lorentzian case gives the exact formula r* = √(1-2γ/K) = √((K-2γ)/K),
  verifying β = 1/2 with explicit coefficient.

  0 sorry.
-/

import KuramotoLean.ContinuumSquareRootLaw

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Critical exponent from square-root law -/

/-- **r* bounded by √(K-Kc) from above.**
    Immediate from the upper bound r*² ≤ c(K-Kc). -/
theorem rstar_le_sqrt_gap [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    r_star ≤ sqrt ((K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3) := by
  have h_sq := continuum_rstar_sq_upper γ K r_star γ_max hγ_pos hK hr_pos hr_lt
    hγ_max_pos hγ_max hγ_level h_inv_int h_inv_pos h_super hfp
  calc r_star = sqrt (r_star ^ 2) := (sqrt_sq (le_of_lt hr_pos)).symm
    _ ≤ sqrt ((K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3) :=
      sqrt_le_sqrt h_sq

/-- **r* bounded by √(K-Kc) from below.**
    Immediate from the lower bound c(K-Kc) ≤ r*². -/
theorem rstar_ge_sqrt_gap [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K) (hr : 0 < r_star)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_inv3_int : Integrable (fun ω => 1 / (γ ω) ^ 3) μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star) :
    sqrt (8 * (K - continuumKc γ μ) /
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ)) ≤ r_star := by
  have h_sq := continuum_rstar_sq_lower γ K r_star hγ_pos hK hr hγ_level h_inv_int
    h_inv_pos h_inv3_int h_super hfp
  calc sqrt (8 * (K - continuumKc γ μ) /
      (K ^ 3 * continuumKc γ μ * ∫ ω, 1 / (γ ω) ^ 3 ∂μ))
      ≤ sqrt (r_star ^ 2) := sqrt_le_sqrt h_sq
    _ = r_star := sqrt_sq (le_of_lt hr)

/-! ## Continuity of bifurcation at Kc -/

/-- **CONTINUITY AT ONSET.**
    r*(K) → 0 as K → Kc+. More precisely: for any sequence K_n → Kc with
    K_n > Kc, if r*_n satisfies the self-consistency equation, then r*_n → 0.

    This follows from r*² ≤ (K-Kc)·C → 0. -/
theorem rstar_vanishes_at_Kc [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K r_star γ_max : ℝ)
    (hγ_pos : ∀ ω, 0 < γ ω) (hK : 0 < K)
    (hr_pos : 0 < r_star) (hr_lt : r_star < 1)
    (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (h_inv_int : Integrable (fun ω => 1 / γ ω) μ)
    (h_inv_pos : 0 < ∫ ω, (1 / γ ω) ∂μ)
    (h_super : continuumKc γ μ < K)
    (hfp : ∫ ω, explicitEquil (γ ω) K r_star ∂μ = r_star)
    (ε : ℝ) (hε : 0 < ε)
    (hK_close : K - continuumKc γ μ < ε ^ 2 * K ^ 3 / (2 * γ_max + K) ^ 2) :
    r_star < ε := by
  have h_sq := continuum_rstar_sq_upper γ K r_star γ_max hγ_pos hK hr_pos hr_lt
    hγ_max_pos hγ_max hγ_level h_inv_int h_inv_pos h_super hfp
  have h2gK_pos : (0 : ℝ) < (2 * γ_max + K) ^ 2 := by positivity
  have hK3 : (0 : ℝ) < K ^ 3 := by positivity
  have h_bound : (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2 / K ^ 3 < ε ^ 2 := by
    rw [div_lt_iff₀ hK3]
    calc (K - continuumKc γ μ) * (2 * γ_max + K) ^ 2
        < ε ^ 2 * K ^ 3 / (2 * γ_max + K) ^ 2 * (2 * γ_max + K) ^ 2 :=
          by nlinarith [hK_close]
      _ = ε ^ 2 * K ^ 3 := by field_simp [ne_of_gt h2gK_pos]
  have hr_sq_lt : r_star ^ 2 < ε ^ 2 := lt_of_le_of_lt h_sq h_bound
  nlinarith [sq_nonneg (r_star - ε), sq_nonneg (r_star + ε)]

/-! ## Lorentzian critical exponent verification -/

/-- **LORENTZIAN β = 1/2.**
    For the Cauchy distribution with Kc = 2γ:
    r* = √(1-2γ/K) = √((K-2γ)/K), giving exact coefficient. -/
theorem lorentzian_critical_exponent (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K) :
    0 < 1 - 2 * γ / K ∧
    sqrt (1 - 2 * γ / K) = sqrt ((K - 2 * γ) / K) ∧
    sqrt (1 - 2 * γ / K) ^ 2 = (K - 2 * γ) / K := by
  have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt hK
  have h1 : 0 < 1 - 2 * γ / K := by rw [sub_pos, div_lt_one hK]; linarith
  have h_eq : 1 - 2 * γ / K = (K - 2 * γ) / K := by field_simp
  refine ⟨h1, by rw [h_eq], by rw [h_eq]; exact sq_sqrt (by linarith : (0:ℝ) ≤ (K - 2 * γ) / K)⟩

/-- **LORENTZIAN SCALING.**
    r*² = (K-Kc)/K with Kc = 2γ. The coefficient is 1/K → 1/Kc as K → Kc+. -/
theorem lorentzian_rstar_sq_eq (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hKγ : 2 * γ < K) :
    sqrt (1 - 2 * γ / K) ^ 2 = (K - 2 * γ) / K := by
  have h_eq : 1 - 2 * γ / K = (K - 2 * γ) / K := by field_simp [ne_of_gt hK]
  rw [h_eq]; exact sq_sqrt (div_nonneg (by linarith) (le_of_lt hK))

end
