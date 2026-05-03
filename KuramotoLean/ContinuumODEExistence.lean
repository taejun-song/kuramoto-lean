/-
  Kuramoto Stability — Continuum ODE Existence via Picard-Lindelöf
  =================================================================

  The OA equation for general g is a parameterized scalar ODE:
    dα/dt(ω) = F(t, α) = -γ(ω)·α + (K/2)·r(t)·(1 - α²)

  We prove F is locally Lipschitz in α and continuous in t, then
  apply Mathlib's IsPicardLindelof to extract HasDerivWithinAt.

  0 sorry.
-/

import KuramotoLean.ContinuumLyapunov
import Mathlib.Analysis.ODE.PicardLindelof

open MeasureTheory Real Filter Set Metric

noncomputable section

/-- The scalar OA velocity field. -/
def oaScalarRHS (γ K : ℝ) (r : ℝ → ℝ) (t : ℝ) (α : ℝ) : ℝ :=
  -γ * α + (K / 2) * r t * (1 - α ^ 2)

theorem oaScalar_diff (γ K : ℝ) (r : ℝ → ℝ) (t α β : ℝ) :
    oaScalarRHS γ K r t α - oaScalarRHS γ K r t β =
    (α - β) * (-γ - (K / 2) * r t * (α + β)) := by
  unfold oaScalarRHS; ring

/-- **Scalar OA ODE existence via Picard-Lindelöf.** -/
theorem oaScalar_picard_lindelof (γ K : ℝ) (r : ℝ → ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (α₀ : ℝ) (t₀ : ℝ) :
    ∃ (tmin tmax : ℝ), tmin < t₀ ∧ t₀ < tmax ∧
    ∃ α : ℝ → ℝ, α t₀ = α₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α
        (oaScalarRHS γ K r t (α t)) (Icc tmin tmax) t := by
  -- Parameters
  have hab : 0 < |α₀| + 2 := by positivity
  set R : ℝ := 2 * |α₀| + 2
  have hR : 0 < R := by positivity
  set L_norm : ℝ := γ * R + K / 2 * (1 + R ^ 2)
  have hLn : 0 < L_norm := by positivity
  set K_lip : ℝ := γ + K * R
  have hKl : 0 < K_lip := by positivity
  set ball_r : ℝ := |α₀| + 2
  have hbr : 0 < ball_r := hab
  set half_t : ℝ := ball_r / (2 * L_norm)
  have hht : 0 < half_t := div_pos hbr (by positivity)
  -- The interval [t₀ - half_t, t₀ + half_t]
  have ht_mem : t₀ ∈ Icc (t₀ - half_t) (t₀ + half_t) := ⟨by linarith, by linarith⟩
  -- Any x in closedBall α₀ ball_r has |x| ≤ R
  have hmem_bound : ∀ x, x ∈ closedBall α₀ ball_r → |x| ≤ R := by
    intro x hx
    rw [mem_closedBall, dist_comm, Real.dist_eq] at hx
    rw [abs_le] at hx ⊢
    exact ⟨by linarith [neg_abs_le α₀], by linarith [le_abs_self α₀]⟩
  -- Build IsPicardLindelof
  have hpl : IsPicardLindelof (oaScalarRHS γ K r)
      ⟨t₀, ht_mem⟩ α₀
      ⟨ball_r, hbr.le⟩ 0 ⟨L_norm, hLn.le⟩ ⟨K_lip, hKl.le⟩ := by
    constructor
    · -- lipschitzOnWith
      intro t _
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      show dist (oaScalarRHS γ K r t x) (oaScalarRHS γ K r t y) ≤ K_lip * dist x y
      rw [Real.dist_eq, oaScalar_diff, abs_mul, Real.dist_eq]
      obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp (hmem_bound x hx)
      obtain ⟨hy_lo, hy_hi⟩ := abs_le.mp (hmem_bound y hy)
      have hrt_lo : -1 ≤ r t := neg_le_of_abs_le (hr_bdd t)
      have hrt_hi : r t ≤ 1 := le_of_abs_le (hr_bdd t)
      have hp1 : 0 ≤ (1 - r t) * (x + y + 2 * R) :=
        mul_nonneg (by linarith) (by linarith)
      have hp2 : 0 ≤ (1 + r t) * (2 * R - x - y) :=
        mul_nonneg (by linarith) (by linarith)
      have hp3 : 0 ≤ (1 + r t) * (x + y + 2 * R) :=
        mul_nonneg (by linarith) (by linarith)
      have hp4 : 0 ≤ (1 - r t) * (2 * R - x - y) :=
        mul_nonneg (by linarith) (by linarith)
      have hcoeff : |-γ - K / 2 * r t * (x + y)| ≤ K_lip := by
        rw [abs_le]; constructor <;> nlinarith
      calc |x - y| * |-γ - K / 2 * r t * (x + y)|
          ≤ |x - y| * K_lip := mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
        _ = K_lip * |x - y| := mul_comm _ _
    · -- continuousOn
      intro x _
      show ContinuousOn (fun t => oaScalarRHS γ K r t x) (Icc _ _)
      unfold oaScalarRHS; fun_prop
    · -- norm_le
      intro t _ x hx
      show ‖oaScalarRHS γ K r t x‖ ≤ L_norm
      obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp (hmem_bound x hx)
      have hrt := abs_le.mp (hr_bdd t)
      show |oaScalarRHS γ K r t x| ≤ L_norm
      have hrt_lo : -1 ≤ r t := neg_le_of_abs_le (hr_bdd t)
      have hrt_hi : r t ≤ 1 := le_of_abs_le (hr_bdd t)
      unfold oaScalarRHS
      have hRx : x ^ 2 ≤ R ^ 2 := by nlinarith [mul_nonneg (show (0:ℝ) ≤ R + x by linarith) (show (0:ℝ) ≤ R - x by linarith)]
      -- Decompose: 1 + R² + r t - r t * x² ≥ 0
      -- = (1 - r t) * (1 - x²) + (1 + r t) * x² + R²  ... nah
      -- = (1 + r t) + R² - r t * x²
      -- Case r t ≥ 0: (1+rt) ≥ 1, R² - rt*x² ≥ R² - x² ≥ 0
      -- Case r t < 0: (1+rt) ≥ 0, R² ≥ 0, -rt*x² = |rt|*x² ≥ 0
      have hkey : 0 ≤ 1 + R ^ 2 + r t * (1 - x ^ 2) := by
        nlinarith [sq_nonneg x, sq_nonneg (r t), hRx,
          mul_nonneg (show (0:ℝ) ≤ 1 + r t by linarith)
            (show (0:ℝ) ≤ x ^ 2 by exact sq_nonneg x),
          mul_nonneg (show (0:ℝ) ≤ 1 - r t by linarith)
            (show (0:ℝ) ≤ 1 by linarith)]
      rw [abs_le]
      have h_nn_lo := add_nonneg
        (mul_nonneg hγ.le (show (0:ℝ) ≤ R - x from by linarith))
        (mul_nonneg (show (0:ℝ) ≤ K / 2 from by linarith) hkey)
      have h_ring_lo : γ * (R - x) + K / 2 * (1 + R ^ 2 + r t * (1 - x ^ 2)) =
          γ * R - γ * x + K / 2 * (1 + R ^ 2) + K / 2 * r t * (1 - x ^ 2) := by ring
      have hkey2 : 0 ≤ 1 + R ^ 2 - r t * (1 - x ^ 2) := by
        nlinarith [sq_nonneg x, hRx,
          mul_nonneg (show (0:ℝ) ≤ 1 - r t by linarith) (show (0:ℝ) ≤ x ^ 2 from sq_nonneg x),
          mul_nonneg (show (0:ℝ) ≤ 1 + r t by linarith) (show (0:ℝ) ≤ 1 by norm_num)]
      have h_nn_hi := add_nonneg
        (mul_nonneg hγ.le (show (0:ℝ) ≤ R + x from by linarith))
        (mul_nonneg (show (0:ℝ) ≤ K / 2 from by linarith) hkey2)
      have h_ring_hi : γ * (R + x) + K / 2 * (1 + R ^ 2 - r t * (1 - x ^ 2)) =
          γ * R + γ * x + K / 2 * (1 + R ^ 2) - K / 2 * r t * (1 - x ^ 2) := by ring
      have hL_def : L_norm = γ * R + K / 2 * (1 + R ^ 2) := rfl
      constructor <;> linarith
    · -- mul_max_le
      show L_norm * max ((t₀ + half_t) - t₀) (t₀ - (t₀ - half_t)) ≤ ball_r - 0
      have h1 : (t₀ + half_t) - t₀ = half_t := by ring
      have h2 : t₀ - (t₀ - half_t) = half_t := by ring
      rw [h1, h2, max_self, sub_zero]
      show L_norm * half_t ≤ ball_r
      calc L_norm * half_t = L_norm * (ball_r / (2 * L_norm)) := rfl
        _ = ball_r / 2 := by field_simp
        _ ≤ ball_r := by linarith
  obtain ⟨α, hα_init, hα_deriv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨t₀ - half_t, t₀ + half_t, by linarith, by linarith, α, hα_init, hα_deriv⟩

/-! ## Continuum ODE existence structure -/

/-- **Continuum ODE existence data** for the full OA system. -/
structure ContinuumODEData {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  γ : Ω → ℝ
  K : ℝ
  hK : 0 < K
  hγ : ∀ ω, 0 < γ ω
  r : ℝ → ℝ
  hr_cont : Continuous r
  hr_bdd : ∀ t, |r t| ≤ 1
  α : Ω → ℝ → ℝ
  α_star : Ω → ℝ
  hα_star : ∀ ω, 0 < α_star ω
  hα_star_lt : ∀ ω, α_star ω < 1
  hα_ode : ∀ ω, ∀ t ≥ 0,
    HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t
  hα_pos : ∀ ω, ∀ t ≥ 0, 0 < α ω t
  hα_lt : ∀ ω, ∀ t ≥ 0, α ω t < 1

theorem ContinuumODEData.pointwise_lyapunov_nn
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : ContinuumODEData μ) (ω : Ω) (t : ℝ) :
    0 ≤ (D.α ω t - D.α_star ω) ^ 2 :=
  sq_nonneg _

theorem oaScalar_equilibrium (γ K r_star α_star : ℝ)
    (h_eq : γ * α_star = (K / 2) * r_star * (1 - α_star ^ 2)) :
    oaScalarRHS γ K (fun _ => r_star) 0 α_star = 0 := by
  unfold oaScalarRHS; linarith

end
