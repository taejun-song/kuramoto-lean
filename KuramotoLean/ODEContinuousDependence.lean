/-
  ODEContinuousDependence.lean
  ============================
  Continuous dependence of OA solutions on the frequency distribution g.

  Main results:
  - oaScalarRHS_r_diff: RHS mismatch from different order parameters
  - oa_scalar_r_gronwall: per-ω Gronwall with r-mismatch
  - oa_self_consistent_r_stability: Gronwall fixed-point bound on r-difference
  - oa_continuous_dependence_on_g: full continuous dependence on g

  0 sorry.
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
    (hα₁_bdd : ∀ ω, |α₁ ω| ≤ 1) (hα₂_bdd : ∀ ω, |α₂ ω| ≤ 1)
    (hg₁_bdd : ∀ ω, |g₁ ω| ≤ 1)
    (hα₁_int : Integrable α₁ μ) (hα₂_int : Integrable α₂ μ)
    (_hg₁_int : Integrable g₁ μ) (_hg₂_int : Integrable g₂ μ)
    (hα₁g₁_int : Integrable (fun ω => α₁ ω * g₁ ω) μ)
    (hα₂g₂_int : Integrable (fun ω => α₂ ω * g₂ ω) μ)
    (hα₂g₁_int : Integrable (fun ω => α₂ ω * g₁ ω) μ) :
    |∫ ω, α₁ ω * g₁ ω ∂μ - ∫ ω, α₂ ω * g₂ ω ∂μ| ≤
      ∫ ω, |α₁ ω - α₂ ω| ∂μ + ∫ ω, |g₁ ω - g₂ ω| ∂μ := by
  -- Split: α₁g₁ - α₂g₂ = (α₁ - α₂)g₁ + α₂(g₁ - g₂)
  have h_split : ∀ ω, α₁ ω * g₁ ω - α₂ ω * g₂ ω =
      (α₁ ω - α₂ ω) * g₁ ω + α₂ ω * (g₁ ω - g₂ ω) := fun ω => by ring
  have h_diff_int : Integrable (fun ω => α₁ ω * g₁ ω - α₂ ω * g₂ ω) μ :=
    hα₁g₁_int.sub hα₂g₂_int
  have h_term1_int : Integrable (fun ω => (α₁ ω - α₂ ω) * g₁ ω) μ := by
    have : (fun ω => (α₁ ω - α₂ ω) * g₁ ω) =
        (fun ω => α₁ ω * g₁ ω - α₂ ω * g₁ ω) := by ext ω; ring
    rw [this]; exact hα₁g₁_int.sub hα₂g₁_int
  have h_term2_int : Integrable (fun ω => α₂ ω * (g₁ ω - g₂ ω)) μ := by
    have : (fun ω => α₂ ω * (g₁ ω - g₂ ω)) =
        (fun ω => α₂ ω * g₁ ω - α₂ ω * g₂ ω) := by ext ω; ring
    rw [this]; exact hα₂g₁_int.sub hα₂g₂_int
  rw [show ∫ ω, α₁ ω * g₁ ω ∂μ - ∫ ω, α₂ ω * g₂ ω ∂μ =
      ∫ ω, (α₁ ω * g₁ ω - α₂ ω * g₂ ω) ∂μ from
      (integral_sub hα₁g₁_int hα₂g₂_int).symm]
  conv_lhs => rw [show (fun ω => α₁ ω * g₁ ω - α₂ ω * g₂ ω) =
      (fun ω => (α₁ ω - α₂ ω) * g₁ ω + α₂ ω * (g₁ ω - g₂ ω)) from
      by ext ω; ring]
  have h_gdiff_int : Integrable (fun ω => g₁ ω - g₂ ω) μ := _hg₁_int.sub _hg₂_int
  have h_ae_nn1 : 0 ≤ᶠ[ae μ] fun ω => |(α₁ ω - α₂ ω) * g₁ ω| :=
    ae_of_all _ (fun ω => abs_nonneg _)
  have h_ae_nn2 : 0 ≤ᶠ[ae μ] fun ω => |α₂ ω * (g₁ ω - g₂ ω)| :=
    ae_of_all _ (fun ω => abs_nonneg _)
  calc |∫ ω, ((α₁ ω - α₂ ω) * g₁ ω + α₂ ω * (g₁ ω - g₂ ω)) ∂μ|
      ≤ |∫ ω, (α₁ ω - α₂ ω) * g₁ ω ∂μ| + |∫ ω, α₂ ω * (g₁ ω - g₂ ω) ∂μ| := by
        rw [integral_add h_term1_int h_term2_int]; exact abs_add_le _ _
    _ ≤ ∫ ω, |(α₁ ω - α₂ ω) * g₁ ω| ∂μ + ∫ ω, |α₂ ω * (g₁ ω - g₂ ω)| ∂μ := by
        apply add_le_add
        · rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
        · rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |α₁ ω - α₂ ω| ∂μ + ∫ ω, |g₁ ω - g₂ ω| ∂μ := by
        apply add_le_add
        · apply integral_mono h_term1_int.norm
          · exact (hα₁_int.sub hα₂_int).norm
          · intro ω; simp only [Real.norm_eq_abs]
            exact (abs_mul _ _).le.trans (mul_le_of_le_one_right (abs_nonneg _) (hg₁_bdd ω))
        · apply integral_mono h_term2_int.norm
          · exact h_gdiff_int.norm
          · intro ω; simp only [Real.norm_eq_abs]
            exact (abs_mul _ _).le.trans (mul_le_of_le_one_left (abs_nonneg _) (hα₂_bdd ω))

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

/-- Algebraic contraction lemma: if x ≤ q*x + d with 0 ≤ q < 1 then x ≤ d/(1-q). -/
private lemma le_div_of_contraction {x q d : ℝ} (hq1 : q < 1) (_hq0 : 0 ≤ q)
    (_hd : 0 ≤ d) (h : x ≤ q * x + d) : x ≤ d / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  rw [le_div_iff₀ h1q]
  linarith

/-- gronwallBound 0 L ε t ≤ ε * t * exp(L * T) for 0 ≤ t ≤ T and 0 < L. -/
private lemma gronwallBound_zero_le_linear {L ε t T : ℝ}
    (hL : 0 < L) (ht : 0 ≤ t) (htT : t ≤ T) (hε : 0 ≤ ε) :
    gronwallBound 0 L ε t ≤ ε * t * exp (L * T) := by
  rw [gronwallBound_of_K_ne_0 (ne_of_gt hL)]
  simp only [zero_mul, zero_add]
  have hLt_nn : 0 ≤ L * t := by positivity
  have heLt : 0 ≤ exp (L * t) - 1 := by linarith [add_one_le_exp (L * t)]
  have hkey : exp (L * t) - 1 ≤ L * t * exp (L * t) := by
    -- From exp(-y) ≥ 1 - y, multiply by exp(y): 1 ≥ exp(y) - y*exp(y)
    have h_neg := add_one_le_exp (-(L * t))
    have h_exp := exp_pos (L * t)
    -- h_neg: -(L*t) + 1 ≤ exp(-(L*t)) i.e. 1 - L*t ≤ exp(-L*t)
    -- multiply both sides by exp(L*t):
    -- (1 - L*t)*exp(L*t) ≤ exp(-L*t)*exp(L*t) = 1
    have := mul_le_mul_of_nonneg_right h_neg h_exp.le
    rw [← exp_add, neg_add_cancel, exp_zero] at this
    nlinarith
  calc ε / L * (exp (L * t) - 1)
      ≤ ε / L * (L * t * exp (L * t)) :=
        mul_le_mul_of_nonneg_left hkey (div_nonneg hε hL.le)
    _ = ε * t * exp (L * t) := by field_simp
    _ ≤ ε * t * exp (L * T) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (mul_nonneg hε ht)
        exact mul_le_mul_of_nonneg_left htT hL.le

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Gronwall fixed-point bound on r-difference.
    For self-consistent systems r_i(t) = ∫ α_i(ω,t) g_i(ω) dμ with
    ‖g₁ - g₂‖₁ ≤ δ, on a short interval [0,T] where contraction holds:
      sup_{[0,T]} |r₁ - r₂| ≤ δ / (1 - q)
    where q = K/2 · T · exp((γ_max + K)·T) < 1. -/
theorem oa_self_consistent_r_stability [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K T : ℝ)
    (hK : 0 < K) (hT : 0 < T)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (γ_max : ℝ) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (g₁ g₂ : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hg_diff : ∫ ω, |g₁ ω - g₂ ω| ∂μ ≤ δ)
    (r₁ r₂ : ℝ → ℝ) (α₁ α₂ : Ω → ℝ → ℝ)
    (hr₁_bdd : ∀ t ∈ Icc 0 T, |r₁ t| ≤ 1)
    (hr₂_bdd : ∀ t ∈ Icc 0 T, |r₂ t| ≤ 1)
    (h_sc₁ : ∀ t ∈ Icc 0 T, r₁ t = ∫ ω, α₁ ω t * g₁ ω ∂μ)
    (h_sc₂ : ∀ t ∈ Icc 0 T, r₂ t = ∫ ω, α₂ ω t * g₂ ω ∂μ)
    (hα₁_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₁ ω) (oaScalarRHS (γ ω) K r₁ t (α₁ ω t)) (Ici t) t)
    (hα₂_ode : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (α₂ ω) (oaScalarRHS (γ ω) K r₂ t (α₂ ω t)) (Ici t) t)
    (hα_same_init : ∀ ω, α₁ ω 0 = α₂ ω 0)
    (hα₁_cont : ∀ ω, ContinuousOn (α₁ ω) (Icc 0 T))
    (hα₂_cont : ∀ ω, ContinuousOn (α₂ ω) (Icc 0 T))
    (hα₁_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₁ ω t ∈ Icc (0 : ℝ) 1)
    (hα₂_inv : ∀ ω, ∀ t ∈ Ico (0 : ℝ) T, α₂ ω t ∈ Icc (0 : ℝ) 1)
    (hα₁_bdd : ∀ ω, ∀ t ∈ Icc 0 T, |α₁ ω t| ≤ 1)
    (hα₂_bdd : ∀ ω, ∀ t ∈ Icc 0 T, |α₂ ω t| ≤ 1)
    (hg₁_bdd : ∀ ω, |g₁ ω| ≤ 1)
    (hg₂_bdd : ∀ ω, |g₂ ω| ≤ 1)
    (hα₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₁ ω t) μ)
    (hα₂_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t) μ)
    (hα₁g₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₁ ω t * g₁ ω) μ)
    (hα₂g₂_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t * g₂ ω) μ)
    (hα₂g₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t * g₁ ω) μ)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hr_cont : ContinuousOn (fun t => r₁ t - r₂ t) (Icc 0 T))
    (hsmall_T : K / 2 * T * exp ((γ_max + K) * T) < 1) :
    ∀ t ∈ Icc 0 T,
      |r₁ t - r₂ t| ≤ δ / (1 - K / 2 * T * exp ((γ_max + K) * T)) := by
  set q := K / 2 * T * exp ((γ_max + K) * T)
  set L := γ_max + K
  have : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := @MeasureTheory.IsProbabilityMeasure.measure_univ _ _ μ _
    simp [Set.univ_eq_empty_iff.mpr h] at this
  have hL : 0 < L := by linarith [hγ_pos (Classical.arbitrary Ω), hγ_max (Classical.arbitrary Ω)]
  have hq0 : 0 ≤ q := by positivity
  have h1q : 0 < 1 - q := by linarith
  -- Step 1: The function |r₁ - r₂| is continuous on [0,T], compact, so attains its max
  have hIcc_compact : IsCompact (Icc (0:ℝ) T) := isCompact_Icc
  have hIcc_ne : (Icc (0:ℝ) T).Nonempty := ⟨0, left_mem_Icc.mpr hT.le⟩
  have h_abs_cont : ContinuousOn (fun t => |r₁ t - r₂ t|) (Icc 0 T) :=
    continuous_abs.comp_continuousOn hr_cont
  obtain ⟨t_max, ht_max_mem, ht_max_ge⟩ :=
    hIcc_compact.exists_isMaxOn hIcc_ne h_abs_cont
  set M := |r₁ t_max - r₂ t_max|
  have hM_bound : ∀ t ∈ Icc 0 T, |r₁ t - r₂ t| ≤ M := fun t ht =>
    ht_max_ge ht
  -- Step 2: One-step contraction — for each t, |r₁(t) - r₂(t)| ≤ q * M + δ
  have h_contraction : ∀ t ∈ Icc 0 T, |r₁ t - r₂ t| ≤ q * M + δ := by
    intro t ht
    -- Per-ω Gronwall: |α₁(ω,t) - α₂(ω,t)| ≤ gronwallBound 0 (γ(ω)+K) (K/2*M) t
    -- ≤ gronwallBound 0 L (K/2*M) t ≤ K/2*M*t*exp(L*T) ≤ q*M
    have hMnn : 0 ≤ M := abs_nonneg _
    have hα_diff : ∀ ω, |α₁ ω t - α₂ ω t| ≤ q * M := by
      intro ω
      have hgw : 0 < γ ω := hγ_pos ω
      have hgwK : 0 < γ ω + K := by linarith
      -- Use oa_scalar_r_gronwall for each ω
      have h_grw := oa_scalar_r_gronwall (γ ω) K r₁ r₂ T (le_of_lt hgw)
        (le_of_lt hK) hr₁_bdd hr₂_bdd M hM_bound (α₁ ω 0) (α₁ ω) (α₂ ω)
        rfl (hα_same_init ω).symm (hα₁_ode ω) (hα₂_ode ω)
        (hα₁_cont ω) (hα₂_cont ω) (hα₁_inv ω) (hα₂_inv ω) t ht
      rw [Real.dist_eq] at h_grw
      have hgwK : 0 < γ ω + K := by linarith
      calc |α₁ ω t - α₂ ω t|
          ≤ gronwallBound 0 (γ ω + K) (K / 2 * M) t := h_grw
        _ ≤ K / 2 * M * t * exp ((γ ω + K) * t) :=
            gronwallBound_zero_le_linear hgwK ht.1 (le_refl t) (by positivity)
        _ ≤ K / 2 * M * t * exp (L * T) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by linarith : 0 ≤ K / 2) hMnn) ht.1)
            exact exp_le_exp.mpr (mul_le_mul (by linarith [hγ_max ω]) ht.2 ht.1 (by linarith [hγ_max ω]))
        _ ≤ K / 2 * M * T * exp (L * T) := by
            have hexp := exp_pos (L * T)
            have htT := ht.2
            nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ K / 2) hMnn) (le_of_lt hexp)]
        _ = q * M := by ring
    -- Now: |r₁(t) - r₂(t)| = |∫α₁g₁ - ∫α₂g₂| ≤ ∫|α₁-α₂| + ∫|g₁-g₂|
    rw [h_sc₁ t ht, h_sc₂ t ht]
    calc |∫ ω, α₁ ω t * g₁ ω ∂μ - ∫ ω, α₂ ω t * g₂ ω ∂μ|
        ≤ ∫ ω, |α₁ ω t - α₂ ω t| ∂μ + ∫ ω, |g₁ ω - g₂ ω| ∂μ :=
          order_param_diff_bound μ (fun ω => α₁ ω t) (fun ω => α₂ ω t) g₁ g₂
            (fun ω => hα₁_bdd ω t ht) (fun ω => hα₂_bdd ω t ht) hg₁_bdd
            (hα₁_int t ht) (hα₂_int t ht) hg₁_int hg₂_int
            (hα₁g₁_int t ht) (hα₂g₂_int t ht) (hα₂g₁_int t ht)
      _ ≤ ∫ _, q * M ∂μ + δ := by
          apply add_le_add
          · exact integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
              (integrable_const _) (ae_of_all _ (fun ω => hα_diff ω))
          · exact hg_diff
      _ = q * M + δ := by
          rw [integral_const]; simp [measure_univ]
  -- Step 3: Apply to M to get M ≤ q*M + δ, hence M ≤ δ/(1-q)
  have hM_le : M ≤ δ / (1 - q) :=
    le_div_of_contraction hsmall_T hq0 hδ (h_contraction t_max ht_max_mem)
  intro t ht
  exact le_trans (hM_bound t ht) hM_le

/-- **Main continuous dependence theorem.**
    Two self-consistent OA systems with distributions g₁, g₂ and same IC:
      |α₁(ω,t) - α₂(ω,t)| ≤ C(K, γ_max, T) · ‖g₁ - g₂‖₁
    for all ω and t ∈ [0,T], provided T is in the contraction regime. -/
theorem oa_continuous_dependence_on_g [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K T : ℝ)
    (hK : 0 < K) (hT : 0 < T)
    (hγ_pos : ∀ ω, 0 < γ ω)
    (γ_max : ℝ) (hγ_max : ∀ ω, γ ω ≤ γ_max)
    (g₁ g₂ : Ω → ℝ) (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (hg_diff : ∫ ω, |g₁ ω - g₂ ω| ∂μ ≤ δ)
    (r₁ r₂ : ℝ → ℝ) (α₁ α₂ : Ω → ℝ → ℝ)
    (hr₁_bdd : ∀ t ∈ Icc 0 T, |r₁ t| ≤ 1)
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
    (hα₁_bdd : ∀ ω, ∀ t ∈ Icc 0 T, |α₁ ω t| ≤ 1)
    (hα₂_bdd : ∀ ω, ∀ t ∈ Icc 0 T, |α₂ ω t| ≤ 1)
    (hg₁_bdd : ∀ ω, |g₁ ω| ≤ 1) (hg₂_bdd : ∀ ω, |g₂ ω| ≤ 1)
    (hα₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₁ ω t) μ)
    (hα₂_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t) μ)
    (hα₁g₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₁ ω t * g₁ ω) μ)
    (hα₂g₂_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t * g₂ ω) μ)
    (hα₂g₁_int : ∀ t ∈ Icc 0 T, Integrable (fun ω => α₂ ω t * g₁ ω) μ)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hr_cont : ContinuousOn (fun t => r₁ t - r₂ t) (Icc 0 T))
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
      g₁ g₂ δ hδ_nn hg_diff r₁ r₂ α₁ α₂ hr₁_bdd hr₂_bdd h_sc₁ h_sc₂
      hα₁_ode hα₂_ode hα_same_init hα₁_cont hα₂_cont hα₁_inv hα₂_inv
      hα₁_bdd hα₂_bdd hg₁_bdd hg₂_bdd hα₁_int hα₂_int
      hα₁g₁_int hα₂g₂_int hα₂g₁_int hg₁_int hg₂_int hr_cont hsmall_T
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
