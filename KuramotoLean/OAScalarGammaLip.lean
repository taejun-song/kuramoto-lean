/-
  OAScalarGammaLip.lean
  =====================
  Lipschitz continuity of the OA scalar ODE solution in the damping parameter γ.

  MAIN RESULT: oa_scalar_gamma_gronwall
    If α₁, α₂ both solve the OA scalar ODE with parameters γ₁, γ₂ (resp.)
    and the same initial condition α₀ on [0,T], with α₁,α₂ ∈ [0,1], then:

      dist(α₁(t), α₂(t)) ≤ gronwallBound 0 (γ₂+K) |γ₁-γ₂| t

    Concretely: dist ≤ (|γ₁-γ₂| / (γ₂+K)) * (exp((γ₂+K)*t) - 1)

  Proof: treat α₁ as an ε-approximate solution to v₂ = oaScalarRHS γ₂ K r
  with ε = |γ₁-γ₂| (the γ-mismatch in the RHS), and apply
  dist_le_of_approx_trajectories_ODE_of_mem (Mathlib Gronwall).

  0 sorry.
-/

import KuramotoLean.ContinuumODEExistence
import Mathlib.Analysis.ODE.Gronwall

open MeasureTheory Real Set Filter Topology Metric

noncomputable section

private lemma oaScalarRHS_lipschitzOnWith (γ K : ℝ) (r : ℝ → ℝ) (t : ℝ)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hr_bdd : |r t| ≤ 1) :
    LipschitzOnWith ⟨γ + K, by positivity⟩ (oaScalarRHS γ K r t) (Icc 0 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simp only [Real.dist_eq]
  unfold oaScalarRHS
  rw [show -γ * x + K / 2 * r t * (1 - x ^ 2) - (-γ * y + K / 2 * r t * (1 - y ^ 2))
      = (x - y) * (-γ - K / 2 * r t * (x + y)) from by ring, abs_mul]
  have hx0 := hx.1; have hx1 := hx.2
  have hy0 := hy.1; have hy1 := hy.2
  have hr_hi := le_of_abs_le hr_bdd
  have hr_lo := neg_le_of_abs_le hr_bdd
  have hxy_nn : 0 ≤ x + y := by linarith
  have h1rt_nn : 0 ≤ 1 + r t := by linarith
  have h1rt_hi : 0 ≤ 1 - r t := by linarith
  have hcoeff : |-γ - K / 2 * r t * (x + y)| ≤ γ + K := by
    rw [abs_le]; constructor <;>
      nlinarith [mul_nonneg h1rt_nn hxy_nn,
                 mul_nonneg (by linarith : 0 ≤ K / 2) (mul_nonneg h1rt_nn hxy_nn),
                 mul_nonneg h1rt_hi hxy_nn,
                 mul_nonneg (by linarith : 0 ≤ K / 2) (mul_nonneg h1rt_hi hxy_nn)]
  calc |x - y| * |-γ - K / 2 * r t * (x + y)|
      ≤ |x - y| * (γ + K) := mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
    _ = (γ + K) * |x - y| := by ring

private lemma oaScalarRHS_gamma_diff (γ₁ γ₂ K : ℝ) (r : ℝ → ℝ) (t x : ℝ) (hx : x ∈ Icc 0 1) :
    dist (oaScalarRHS γ₁ K r t x) (oaScalarRHS γ₂ K r t x) ≤ |γ₁ - γ₂| := by
  rw [Real.dist_eq, show oaScalarRHS γ₁ K r t x - oaScalarRHS γ₂ K r t x
      = (γ₂ - γ₁) * x from by unfold oaScalarRHS; ring, abs_mul]
  calc |γ₂ - γ₁| * |x|
      ≤ |γ₁ - γ₂| * 1 := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) (abs_nonneg _)
    _ = |γ₁ - γ₂| := mul_one _

/-- **Gronwall γ-sensitivity for the OA scalar ODE.**
    Two solutions with parameters γ₁, γ₂ and the same initial condition satisfy
    dist(α₁(t), α₂(t)) ≤ gronwallBound 0 (γ₂+K) |γ₁-γ₂| t on [0,T].
    This gives Lipschitz continuity of the solution in γ with constant
    |γ₁-γ₂|/(γ₂+K) * (exp((γ₂+K)*t) - 1). -/
theorem oa_scalar_gamma_gronwall
    (γ₁ γ₂ K : ℝ) (r : ℝ → ℝ) (T : ℝ)
    (hγ₂ : 0 ≤ γ₂) (hK : 0 ≤ K)
    (hr_bdd : ∀ t ∈ Icc 0 T, |r t| ≤ 1)
    (α₀ : ℝ)
    (α₁ α₂ : ℝ → ℝ)
    (hα₁_init : α₁ 0 = α₀) (hα₂_init : α₂ 0 = α₀)
    (hα₁_ode : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt α₁ (oaScalarRHS γ₁ K r t (α₁ t)) (Ici t) t)
    (hα₂_ode : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt α₂ (oaScalarRHS γ₂ K r t (α₂ t)) (Ici t) t)
    (hα₁_cont : ContinuousOn α₁ (Icc 0 T))
    (hα₂_cont : ContinuousOn α₂ (Icc 0 T))
    (hα₁_bdd : ∀ t ∈ Ico (0 : ℝ) T, α₁ t ∈ Icc (0 : ℝ) 1)
    (hα₂_bdd : ∀ t ∈ Ico (0 : ℝ) T, α₂ t ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    dist (α₁ t) (α₂ t) ≤ gronwallBound 0 (γ₂ + K) |γ₁ - γ₂| t := by
  -- Apply dist_le_of_approx_trajectories_ODE_of_mem treating α₁ as approx to v₂
  have hK_nn : (0 : ℝ) ≤ γ₂ + K := by linarith
  set L : NNReal := ⟨γ₂ + K, hK_nn⟩
  set εf : ℝ := |γ₁ - γ₂|
  have hδ : dist (α₁ 0) (α₂ 0) ≤ 0 := by rw [hα₁_init, hα₂_init]; simp
  have key := dist_le_of_approx_trajectories_ODE_of_mem (E := ℝ)
    (v := fun s x => oaScalarRHS γ₂ K r s x)
    (s := fun _ => Icc (0 : ℝ) 1) (a := 0) (b := T)
    (f := α₁) (f' := fun s => oaScalarRHS γ₁ K r s (α₁ s))
    (g := α₂) (g' := fun s => oaScalarRHS γ₂ K r s (α₂ s))
    (K := L) (δ := 0) (εf := εf) (εg := 0)
    (fun s hs => oaScalarRHS_lipschitzOnWith γ₂ K r s hγ₂ hK (hr_bdd s (Ico_subset_Icc_self hs)))
    hα₁_cont hα₁_ode
    (fun s hs => oaScalarRHS_gamma_diff γ₁ γ₂ K r s (α₁ s) (hα₁_bdd s hs))
    hα₁_bdd hα₂_cont hα₂_ode
    (fun _ _ => by rw [dist_self])
    hα₂_bdd hδ
  have ht_icc := key t ht
  have hL_eq : (↑L : ℝ) = γ₂ + K := rfl
  simp only [hL_eq, add_zero, sub_zero] at ht_icc
  exact ht_icc

end
