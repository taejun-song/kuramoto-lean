/-
  ODEContinuousDependence.lean
  ============================
  Continuous dependence of OA solutions on the frequency distribution g.

  Main results:
  - oaScalarRHS_r_diff: RHS mismatch from different order parameters
  - oa_scalar_r_gronwall: per-ω Gronwall with r-mismatch
  - oa_self_consistent_r_stability: Gronwall fixed-point bound on r-difference
  - oa_continuous_dependence_on_g: full continuous dependence on g

  2 sorry (order_param_diff_bound, oa_self_consistent_r_stability).
-/

import KuramotoLean.OAScalarGammaLip
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real Set Filter Topology Metric

noncomputable section

/-! ## Order parameter difference from distributional mismatch -/

theorem order_param_diff_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α₁ α₂ : Ω → ℝ) (g₁ g₂ : Ω → ℝ)
    (_hα₁_bdd : ∀ ω, |α₁ ω| ≤ 1) (_hα₂_bdd : ∀ ω, |α₂ ω| ≤ 1)
    (_hg₁_int : Integrable g₁ μ) (_hg₂_int : Integrable g₂ μ)
    (_hα₁g₁_int : Integrable (fun ω => α₁ ω * g₁ ω) μ)
    (_hα₂g₂_int : Integrable (fun ω => α₂ ω * g₂ ω) μ)
    (_hα₁g₂_int : Integrable (fun ω => α₁ ω * g₂ ω) μ) :
    |∫ ω, α₁ ω * g₁ ω ∂μ - ∫ ω, α₂ ω * g₂ ω ∂μ| ≤
      ∫ ω, |α₁ ω - α₂ ω| ∂μ + ∫ ω, |g₁ ω - g₂ ω| ∂μ := by
  sorry

/-! ## Lipschitz bound (local copy; the original is private in OAScalarGammaLip) -/

private lemma oaScalarRHS_lipschitzOnWith' (γ K : ℝ) (r : ℝ → ℝ) (t : ℝ)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hr_bdd : |r t| ≤ 1) :
    LipschitzOnWith ⟨γ + K, by positivity⟩ (oaScalarRHS γ K r t) (Icc 0 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simp only [Real.dist_eq]
  unfold oaScalarRHS
  rw [show -γ * x + K / 2 * r t * (1 - x ^ 2) - (-γ * y + K / 2 * r t * (1 - y ^ 2))
      = (x - y) * (-γ - K / 2 * r t * (x + y)) from by ring, abs_mul]
  have hx0 := hx.1; have hx1 := hx.2; have hy0 := hy.1; have hy1 := hy.2
  have hr_hi := le_of_abs_le hr_bdd; have hr_lo := neg_le_of_abs_le hr_bdd
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

/-! ## Per-ω Gronwall estimate with r-mismatch -/

theorem oaScalarRHS_r_diff (γ K : ℝ) (r₁ r₂ : ℝ → ℝ) (t x : ℝ)
    (hK : 0 ≤ K) (hx : x ∈ Icc (0 : ℝ) 1) :
    |oaScalarRHS γ K r₁ t x - oaScalarRHS γ K r₂ t x| ≤
      K / 2 * |r₁ t - r₂ t| := by
  unfold oaScalarRHS
  rw [show -γ * x + K / 2 * r₁ t * (1 - x ^ 2) -
        (-γ * x + K / 2 * r₂ t * (1 - x ^ 2))
      = K / 2 * (r₁ t - r₂ t) * (1 - x ^ 2) from by ring]
  rw [abs_mul, abs_mul]
  have hK2 : |K / 2| = K / 2 := abs_of_nonneg (by linarith)
  have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1x_le : |1 - x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg h1x]; nlinarith [hx.1, hx.2]
  calc |K / 2| * |r₁ t - r₂ t| * |1 - x ^ 2|
      ≤ |K / 2| * |r₁ t - r₂ t| * 1 :=
        mul_le_mul_of_nonneg_left h1x_le
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |K / 2| * |r₁ t - r₂ t| := mul_one _
    _ = K / 2 * |r₁ t - r₂ t| := by rw [hK2]

/-- Per-ω Gronwall: two OA solutions with different forcings r₁, r₂
    satisfy dist(α₁(t), α₂(t)) ≤ gronwallBound 0 (γ+K) ((K/2)·εr) t. -/
theorem oa_scalar_r_gronwall
    (γ K : ℝ) (r₁ r₂ : ℝ → ℝ) (T : ℝ)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (_hr₁_bdd : ∀ t ∈ Icc 0 T, |r₁ t| ≤ 1)
    (hr₂_bdd : ∀ t ∈ Icc 0 T, |r₂ t| ≤ 1)
    (εr : ℝ) (hεr : ∀ t ∈ Icc 0 T, |r₁ t - r₂ t| ≤ εr)
    (x₀ : ℝ) (f g : ℝ → ℝ)
    (hf_init : f 0 = x₀) (hg_init : g 0 = x₀)
    (hf_ode : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt f (oaScalarRHS γ K r₁ t (f t)) (Ici t) t)
    (hg_ode : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt g (oaScalarRHS γ K r₂ t (g t)) (Ici t) t)
    (hf_cont : ContinuousOn f (Icc 0 T))
    (hg_cont : ContinuousOn g (Icc 0 T))
    (hf_bdd : ∀ t ∈ Ico (0 : ℝ) T, f t ∈ Icc (0 : ℝ) 1)
    (hg_bdd : ∀ t ∈ Ico (0 : ℝ) T, g t ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    dist (f t) (g t) ≤ gronwallBound 0 (γ + K) (K / 2 * εr) t := by
  have hgK_nn : (0 : ℝ) ≤ γ + K := by linarith
  set L : NNReal := ⟨γ + K, hgK_nn⟩
  have hδ : dist (f 0) (g 0) ≤ 0 := by rw [hf_init, hg_init]; simp
  have f_bound : ∀ s ∈ Ico (0 : ℝ) T,
      dist (oaScalarRHS γ K r₁ s (f s)) (oaScalarRHS γ K r₂ s (f s)) ≤ K / 2 * εr := by
    intro s hs
    rw [Real.dist_eq]
    exact le_trans (oaScalarRHS_r_diff γ K r₁ r₂ s (f s) hK (hf_bdd s hs))
      (mul_le_mul_of_nonneg_left (hεr s (Ico_subset_Icc_self hs)) (by linarith))
  have key := dist_le_of_approx_trajectories_ODE_of_mem (E := ℝ)
    (v := fun s x => oaScalarRHS γ K r₂ s x)
    (s := fun _ => Icc (0 : ℝ) 1) (a := 0) (b := T)
    (f := f) (f' := fun s => oaScalarRHS γ K r₁ s (f s))
    (g := g) (g' := fun s => oaScalarRHS γ K r₂ s (g s))
    (K := L) (δ := 0) (εf := K / 2 * εr) (εg := 0)
    (fun s hs => oaScalarRHS_lipschitzOnWith' γ K r₂ s (by linarith) hK
      (hr₂_bdd s (Ico_subset_Icc_self hs)))
    hf_cont hf_ode f_bound hf_bdd
    hg_cont hg_ode (fun _ _ => by rw [dist_self]) hg_bdd hδ
  have ht_icc := key t ht
  have hL_eq : (↑L : ℝ) = γ + K := rfl
  simp only [hL_eq, add_zero, sub_zero] at ht_icc
  exact ht_icc

/-! ## Self-consistent system: combined estimate -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Gronwall fixed-point bound on r-difference.
    For self-consistent systems r_i(t) = ∫ α_i(ω,t) g_i(ω) dμ with
    ‖g₁ - g₂‖₁ ≤ δ, on a short interval [0,T] where contraction holds:
      sup_{[0,T]} |r₁ - r₂| ≤ δ / (1 - q)
    where q = K/2 · T · exp((γ_max + K)·T) < 1. -/
theorem oa_self_consistent_r_stability [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K T : ℝ)
    (_hK : 0 < K) (_hT : 0 < T)
    (_hγ_pos : ∀ ω, 0 < γ ω)
    (γ_max : ℝ) (_hγ_max : ∀ ω, γ ω ≤ γ_max)
    (_g₁ _g₂ : Ω → ℝ) (δ : ℝ)
    (_hg_diff : ∫ ω, |_g₁ ω - _g₂ ω| ∂μ ≤ δ)
    (r₁ r₂ : ℝ → ℝ) (α₁ α₂ : Ω → ℝ → ℝ)
    (_h_sc₁ : ∀ t ∈ Icc 0 T, r₁ t = ∫ ω, α₁ ω t * _g₁ ω ∂μ)
    (_h_sc₂ : ∀ t ∈ Icc 0 T, r₂ t = ∫ ω, α₂ ω t * _g₂ ω ∂μ)
    (_hα₁_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₁ ω) (oaScalarRHS (γ ω) K r₁ t (α₁ ω t)) (Ici t) t)
    (_hα₂_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₂ ω) (oaScalarRHS (γ ω) K r₂ t (α₂ ω t)) (Ici t) t)
    (_hα_same_init : ∀ ω, α₁ ω 0 = α₂ ω 0)
    (_hα₁_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₁ ω t ∈ Icc (0 : ℝ) 1)
    (_hα₂_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₂ ω t ∈ Icc (0 : ℝ) 1)
    (hsmall_T : K / 2 * T * exp ((γ_max + K) * T) < 1) :
    ∀ t ∈ Icc 0 T,
      |r₁ t - r₂ t| ≤ δ / (1 - K / 2 * T * exp ((γ_max + K) * T)) := by
  -- Sketch: define Φ(ε) = sup|r₁-r₂| on [0,T].
  -- Per-ω Gronwall gives |α₁(ω,t)-α₂(ω,t)| ≤ (K/2)·ε/(γ+K)·(exp((γ+K)t)-1)
  -- ≤ K/2 · ε · t · exp((γ_max+K)·T) (linearizing gronwallBound).
  -- Integrating: |r₁(t)-r₂(t)| ≤ q·ε + δ where q = K/2·T·exp((γ_max+K)·T).
  -- Fixed point: ε ≤ q·ε + δ, so ε ≤ δ/(1-q).
  sorry

/-- **Main continuous dependence theorem.**
    Two self-consistent OA systems with distributions g₁, g₂ and same IC:
      |α₁(ω,t) - α₂(ω,t)| ≤ C(K, γ_max, T) · ‖g₁ - g₂‖₁
    for all ω and t ∈ [0,T], provided T is in the contraction regime. -/
theorem oa_continuous_dependence_on_g [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K T : ℝ)
    (hK : 0 < K) (hT : 0 < T)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (γ_max : ℝ) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (g₁ g₂ : Ω → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hg_diff : ∫ ω, |g₁ ω - g₂ ω| ∂μ ≤ δ)
    (r₁ r₂ : ℝ → ℝ) (α₁ α₂ : Ω → ℝ → ℝ)
    (_hr₁_bdd : ∀ t ∈ Icc 0 T, |r₁ t| ≤ 1)
    (hr₂_bdd : ∀ t ∈ Icc 0 T, |r₂ t| ≤ 1)
    (h_sc₁ : ∀ t ∈ Icc 0 T, r₁ t = ∫ ω, α₁ ω t * g₁ ω ∂μ)
    (h_sc₂ : ∀ t ∈ Icc 0 T, r₂ t = ∫ ω, α₂ ω t * g₂ ω ∂μ)
    (hα₁_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₁ ω) (oaScalarRHS (γ ω) K r₁ t (α₁ ω t)) (Ici t) t)
    (hα₂_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₂ ω) (oaScalarRHS (γ ω) K r₂ t (α₂ ω t)) (Ici t) t)
    (hα₁_cont : ∀ ω, ContinuousOn (α₁ ω) (Icc 0 T))
    (hα₂_cont : ∀ ω, ContinuousOn (α₂ ω) (Icc 0 T))
    (hα_same_init : ∀ ω, α₁ ω 0 = α₂ ω 0)
    (hα₁_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₁ ω t ∈ Icc (0 : ℝ) 1)
    (hα₂_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₂ ω t ∈ Icc (0 : ℝ) 1)
    (hsmall_T : K / 2 * T * exp ((γ_max + K) * T) < 1) :
    ∀ ω, ∀ t ∈ Icc 0 T,
      |α₁ ω t - α₂ ω t| ≤
        gronwallBound 0 (γ_max + K)
          (K / 2 * (δ / (1 - K / 2 * T * exp ((γ_max + K) * T)))) t := by
  -- Step 1: bound sup|r₁-r₂| via oa_self_consistent_r_stability
  set q := K / 2 * T * exp ((γ_max + K) * T)
  set εr := δ / (1 - q)
  have hεr_bound : ∀ t ∈ Icc 0 T, |r₁ t - r₂ t| ≤ εr :=
    oa_self_consistent_r_stability γ K T hK hT hγ_pos γ_max hγ_max
      g₁ g₂ δ hg_diff r₁ r₂ α₁ α₂ h_sc₁ h_sc₂ hα₁_ode hα₂_ode
      hα_same_init hα₁_inv hα₂_inv hsmall_T
  intro ω s hs
  have hgmK_nn : (0 : ℝ) ≤ γ_max + K := by linarith [hγ_pos ω, hγ_max ω]
  have hgmK_pos : 0 < γ_max + K := by linarith [hγ_pos ω, hγ_max ω]
  set L : NNReal := ⟨γ_max + K, hgmK_nn⟩
  have hδ0 : dist (α₁ ω 0) (α₂ ω 0) ≤ 0 := by rw [hα_same_init ω]; simp
  have hgwK_nn : (0 : ℝ) ≤ γ ω + K := by linarith [hγ_pos ω]
  have hle : (⟨γ ω + K, hgwK_nn⟩ : NNReal) ≤ L := by
    change (γ ω + K : ℝ) ≤ (γ_max + K : ℝ)
    linarith [hγ_max ω]
  have hlip : ∀ u ∈ Ico (0 : ℝ) T,
      LipschitzOnWith L (oaScalarRHS (γ ω) K r₂ u) (Icc 0 1) := by
    intro u hu
    exact (oaScalarRHS_lipschitzOnWith' (γ ω) K r₂ u (le_of_lt (hγ_pos ω)) (le_of_lt hK)
      (hr₂_bdd u (Ico_subset_Icc_self hu))).weaken hle
  have f_bound : ∀ u ∈ Ico (0 : ℝ) T,
      dist (oaScalarRHS (γ ω) K r₁ u (α₁ ω u))
           (oaScalarRHS (γ ω) K r₂ u (α₁ ω u)) ≤ K / 2 * εr := by
    intro u hu
    rw [Real.dist_eq]
    exact le_trans (oaScalarRHS_r_diff (γ ω) K r₁ r₂ u (α₁ ω u) (le_of_lt hK) (hα₁_inv ω u hu))
      (mul_le_mul_of_nonneg_left (hεr_bound u (Ico_subset_Icc_self hu)) (by linarith))
  have key := dist_le_of_approx_trajectories_ODE_of_mem (E := ℝ)
    (v := fun u x => oaScalarRHS (γ ω) K r₂ u x)
    (s := fun _ => Icc (0 : ℝ) 1) (a := 0) (b := T)
    (f := α₁ ω) (f' := fun u => oaScalarRHS (γ ω) K r₁ u (α₁ ω u))
    (g := α₂ ω) (g' := fun u => oaScalarRHS (γ ω) K r₂ u (α₂ ω u))
    (K := L) (δ := 0) (εf := K / 2 * εr) (εg := 0)
    hlip (hα₁_cont ω) (hα₁_ode ω) f_bound (hα₁_inv ω)
    (hα₂_cont ω) (hα₂_ode ω) (fun _ _ => by rw [dist_self]) (hα₂_inv ω) hδ0
  have := key s hs
  rw [Real.dist_eq] at this
  simp only [add_zero, sub_zero] at this
  exact this

/-- Contraction regime exists: for any K, γ_max, there exists T > 0 small
    enough that K/2 · T · exp((γ_max+K)·T) < 1. -/
theorem contraction_regime_exists (K γ_max : ℝ) (hK : 0 < K) (hγ : 0 ≤ γ_max) :
    ∃ T > 0, K / 2 * T * exp ((γ_max + K) * T) < 1 := by
  refine ⟨min 1 (1 / (K * exp (γ_max + K))), by positivity, ?_⟩
  have hexp_pos : (0 : ℝ) < exp (γ_max + K) := exp_pos _
  have hKexp : 0 < K * exp (γ_max + K) := mul_pos hK hexp_pos
  have hT₀_le1 : min 1 (1 / (K * exp (γ_max + K))) ≤ 1 := min_le_left _ _
  have hT₀_le : min 1 (1 / (K * exp (γ_max + K))) ≤
      1 / (K * exp (γ_max + K)) := min_le_right _ _
  set T₀ := min 1 (1 / (K * exp (γ_max + K)))
  have hgKT : (γ_max + K) * T₀ ≤ γ_max + K := by nlinarith
  have hexp_le : exp ((γ_max + K) * T₀) ≤ exp (γ_max + K) := exp_le_exp.mpr hgKT
  have hKT : K * T₀ ≤ 1 / exp (γ_max + K) := by
    calc K * T₀ ≤ K * (1 / (K * exp (γ_max + K))) :=
          mul_le_mul_of_nonneg_left hT₀_le hK.le
      _ = 1 / exp (γ_max + K) := by field_simp
  calc K / 2 * T₀ * exp ((γ_max + K) * T₀)
      ≤ K / 2 * T₀ * exp (γ_max + K) := by
        nlinarith [hexp_le, (by positivity : (0 : ℝ) ≤ K / 2 * T₀)]
    _ ≤ 1 / 2 * (1 / exp (γ_max + K)) * exp (γ_max + K) := by nlinarith [hKT]
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

end
