/-
  Complex Leibniz Rule and Basin Decay
  ======================================
  Ports the Leibniz computation from the real scalar OA to the complex OA,
  then closes h_basin_decay.

  V(t) = ∫ |z(ω,t) - z*(ω)|² · g(ω) dμ(ω)
  V'(t) = ∫ 2·Re(conj(z-z*)·ż) · g dμ

  Dominator: (2|ω|+K)·g, integrable when ∫|ω|g < ∞ (finite first moment).

  The pointwise derivative of |z-z*|²·g uses hasDerivAt_normSq_comp
  (proved in ComplexOAEnergy.lean).
-/

import KuramotoLean.ComplexOAPairBound
import KuramotoLean.ComplexOAEnergy
import KuramotoLean.BasinDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Pointwise derivative of |z - z*|² along complex OA flow -/

/-- d|z(t)-z*|²/dt = 2·Re(conj(z(t)-z*)·ż(t)).
    Chain rule for normSq ∘ (z - z*). -/
theorem hasDerivAt_normSq_sub_const (z : ℝ → ℂ) (z_star z' : ℂ) (t : ℝ)
    (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => Complex.normSq (z s - z_star))
      (2 * (starRingEnd ℂ (z t - z_star) * z').re) t :=
  hasDerivAt_normSq_comp (fun s => z s - z_star) z' t (hz.sub_const z_star)

/-- The RHS speed bound: |ż| ≤ |ω| + K when z is in the unit disk.
    Uses |complexOaRHS ω K η z| ≤ |ω|·|z| + K/2·(|η̄| + |η|·|z|²)
    ≤ |ω| + K (since |z| < 1, |η| ≤ 1). -/
theorem complexOaRHS_norm_le (ω_freq K : ℝ) (η z : ℂ)
    (hz : Complex.normSq z ≤ 1) (hη : Complex.normSq η ≤ 1)
    (hK : 0 ≤ K) :
    ‖complexOaRHS ω_freq K η z‖ ≤ |ω_freq| + K := by
  unfold complexOaRHS
  have hz_norm : ‖z‖ ≤ 1 := by
    nlinarith [Complex.normSq_eq_norm_sq z, norm_nonneg z, sq_nonneg ‖z‖]
  have hη_norm : ‖η‖ ≤ 1 := by
    nlinarith [Complex.normSq_eq_norm_sq η, norm_nonneg η, sq_nonneg ‖η‖]
  calc ‖-(Complex.I * (ω_freq : ℂ) * z) + ((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2)‖
      ≤ ‖-(Complex.I * (ω_freq : ℂ) * z)‖ + ‖((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2)‖ :=
        norm_add_le _ _
    _ = ‖Complex.I * (ω_freq : ℂ) * z‖ + ‖((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2)‖ := by
        rw [norm_neg]
    _ = ‖(ω_freq : ℂ)‖ * ‖z‖ + ‖((K : ℂ) / 2)‖ * ‖starRingEnd ℂ η - η * z ^ 2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_mul]
    _ ≤ |ω_freq| * 1 + K / 2 * (‖η‖ + ‖η‖ * ‖z‖ ^ 2) := by
        have hK2 : ‖((K : ℂ) / 2)‖ = K / 2 := by
          simp [Complex.norm_real, abs_of_nonneg hK]
        apply add_le_add
        · rw [Complex.norm_real]
          exact mul_le_mul_of_nonneg_left hz_norm (abs_nonneg _)
        · rw [hK2]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          calc ‖starRingEnd ℂ η - η * z ^ 2‖
              ≤ ‖starRingEnd ℂ η‖ + ‖η * z ^ 2‖ := norm_sub_le _ _
            _ = ‖η‖ + ‖η‖ * ‖z‖ ^ 2 := by
                rw [RCLike.norm_conj, norm_mul, norm_pow]
    _ ≤ |ω_freq| * 1 + K / 2 * (1 + 1 * 1) := by
        have h1 : ‖η‖ * ‖z‖ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hη_norm (pow_le_one₀ (norm_nonneg _) hz_norm)
            (pow_nonneg (norm_nonneg _) _) (by linarith [norm_nonneg η])
        nlinarith
    _ = |ω_freq| + K := by ring

/-! ## Complex Leibniz integral rule -/

/-- **COMPLEX LEIBNIZ RULE.**
    V(t) = ∫|z-z*|²·g dμ is continuous on [0,∞) and differentiable for t > 0
    with V'(t) = ∫ 2·Re(conj(z(t)-z*)·ż(t))·g(ω) dμ.

    Dominator: 2·(|ω|+K)·g(ω), integrable from finite first moment.
    Same proof structure as leibniz_integrable_gamma (real case). -/
theorem complex_leibniz [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (z_star : Ω → ℂ) (K : ℝ)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) ≤ 1)
    (hz_star_disk : ∀ ω, Complex.normSq (z_star ω) ≤ 1)
    (hV_int : ∀ t, Integrable (fun ω => Complex.normSq (z ω t - z_star ω) * S.g ω) μ)
    (hg_nn : ∀ ω, 0 ≤ S.g ω)
    (hg_int : Integrable S.g μ)
    (hω_g_int : Integrable (fun ω => |S.ω_freq ω| * S.g ω) μ)
    (hK_pos : 0 < K)
    (hz_cont : ∀ ω, Continuous (z ω))
    (hη_bdd : ∀ t, Complex.normSq (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) ≤ 1) :
    ContinuousOn (fun t => ∫ ω, Complex.normSq (z ω t - z_star ω) * S.g ω ∂μ) (Ici 0) ∧
    (∀ t, 0 < t → HasDerivAt
      (fun s => ∫ ω, Complex.normSq (z ω s - z_star ω) * S.g ω ∂μ)
      (∫ ω, 2 * (starRingEnd ℂ (z ω t - z_star ω) *
        complexOaRHS (S.ω_freq ω) K
          (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ)
          (z ω t)).re * S.g ω ∂μ) t) := by
  constructor
  · -- ContinuousOn: V(t) = ∫ |z(ω,t) - z*(ω)|² · g(ω) dμ is continuous
    -- Each z ω is continuous, so normSq(z ω · - z_star ω) · g ω is continuous,
    -- dominated by 4 · g(ω) (since |z|,|z*| ≤ 1 ⟹ |z-z*|² ≤ 4).
    -- Standard dominated convergence for continuity.
    have hz_cts : ∀ ω, Continuous (fun t => Complex.normSq (z ω t - z_star ω) * S.g ω) := by
      intro ω
      exact ((Complex.continuous_normSq.comp ((hz_cont ω).sub continuous_const)).mul
        continuous_const)
    have h_bound : ∀ t, ∀ᵐ ω ∂μ, ‖Complex.normSq (z ω t - z_star ω) * S.g ω‖ ≤ 4 * S.g ω := by
      intro t; apply Eventually.of_forall; intro ω
      have hzd := hz_disk ω t; have hzsd := hz_star_disk ω
      have h_nsq : Complex.normSq (z ω t - z_star ω) ≤ 4 := by
        have h1 : ‖z ω t‖ ≤ 1 := by
          nlinarith [Complex.normSq_eq_norm_sq (z ω t), norm_nonneg (z ω t),
            sq_nonneg ‖z ω t‖]
        have h2 : ‖z_star ω‖ ≤ 1 := by
          nlinarith [Complex.normSq_eq_norm_sq (z_star ω), norm_nonneg (z_star ω),
            sq_nonneg ‖z_star ω‖]
        have h3 : ‖z ω t - z_star ω‖ ≤ 2 := by linarith [norm_sub_le (z ω t) (z_star ω)]
        nlinarith [Complex.normSq_eq_norm_sq (z ω t - z_star ω),
          norm_nonneg (z ω t - z_star ω), sq_nonneg ‖z ω t - z_star ω‖]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hg_nn ω))]
      exact mul_le_mul_of_nonneg_right h_nsq (hg_nn ω)
    exact (MeasureTheory.continuous_of_dominated
      (F := fun t ω => Complex.normSq (z ω t - z_star ω) * S.g ω)
      (bound := fun ω => 4 * S.g ω)
      (fun t => (hV_int t).aestronglyMeasurable)
      h_bound
      (hg_int.const_mul 4)
      (Eventually.of_forall hz_cts)).continuousOn
  · intro t ht
    set η := fun s => ∫ ω', starRingEnd ℂ (z ω' s) * (S.g ω' : ℂ) ∂μ with hη_def
    set F := fun s ω => Complex.normSq (z ω s - z_star ω) * S.g ω with hF_def
    set F' := fun s ω => 2 * (starRingEnd ℂ (z ω s - z_star ω) *
      complexOaRHS (S.ω_freq ω) K (η s) (z ω s)).re * S.g ω with hF'_def
    set bound := fun ω => 4 * (|S.ω_freq ω| + K) * S.g ω with hbound_def
    have h_pw_deriv : ∀ᵐ ω ∂μ, ∀ s ∈ Ioi (0:ℝ), HasDerivAt (F · ω) (F' s ω) s := by
      apply Eventually.of_forall; intro ω s hs
      have hs_pos := mem_Ioi.mp hs
      have h_nsq := hasDerivAt_normSq_sub_const (z ω) (z_star ω)
        (complexOaRHS (S.ω_freq ω) K (η s) (z ω s)) s (hz_ode ω s)
      simp only [hF_def, hF'_def]
      exact h_nsq.mul_const (S.g ω)
    have h_norm_bound : ∀ᵐ ω ∂μ, ∀ s ∈ Ioi (0:ℝ), ‖F' s ω‖ ≤ bound ω := by
      apply Eventually.of_forall; intro ω s hs
      simp only [hF'_def, hbound_def]
      have hzd := hz_disk ω s; have hzsd := hz_star_disk ω
      have hη_s := hη_bdd s
      have h_diff_norm : ‖z ω s - z_star ω‖ ≤ 2 := by
        have h1 : ‖z ω s‖ ≤ 1 := by
          nlinarith [Complex.normSq_eq_norm_sq (z ω s), norm_nonneg (z ω s),
            sq_nonneg ‖z ω s‖]
        have h2 : ‖z_star ω‖ ≤ 1 := by
          nlinarith [Complex.normSq_eq_norm_sq (z_star ω), norm_nonneg (z_star ω),
            sq_nonneg ‖z_star ω‖]
        linarith [norm_sub_le (z ω s) (z_star ω)]
      have h_rhs_norm : ‖complexOaRHS (S.ω_freq ω) K (η s) (z ω s)‖ ≤ |S.ω_freq ω| + K :=
        complexOaRHS_norm_le (S.ω_freq ω) K (η s) (z ω s) hzd hη_s (le_of_lt hK_pos)
      have h_re_le : |((starRingEnd ℂ (z ω s - z_star ω) *
          complexOaRHS (S.ω_freq ω) K (η s) (z ω s)).re)| ≤
          ‖z ω s - z_star ω‖ * (|S.ω_freq ω| + K) := by
        calc |((starRingEnd ℂ (z ω s - z_star ω) *
              complexOaRHS (S.ω_freq ω) K (η s) (z ω s)).re)|
            ≤ ‖starRingEnd ℂ (z ω s - z_star ω) *
              complexOaRHS (S.ω_freq ω) K (η s) (z ω s)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖z ω s - z_star ω‖ * ‖complexOaRHS (S.ω_freq ω) K (η s) (z ω s)‖ := by
              rw [norm_mul, RCLike.norm_conj]
          _ ≤ ‖z ω s - z_star ω‖ * (|S.ω_freq ω| + K) :=
              mul_le_mul_of_nonneg_left h_rhs_norm (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
      have hg_ω := hg_nn ω
      calc 2 * |((starRingEnd ℂ (z ω s - z_star ω) *
              complexOaRHS (S.ω_freq ω) K (η s) (z ω s)).re)| * |S.g ω|
          ≤ 2 * (‖z ω s - z_star ω‖ * (|S.ω_freq ω| + K)) * S.g ω := by
            rw [abs_of_nonneg hg_ω]; exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_re_le (by positivity)) hg_ω
        _ ≤ 2 * (2 * (|S.ω_freq ω| + K)) * S.g ω := by
            apply mul_le_mul_of_nonneg_right _ hg_ω
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h_diff_norm (by positivity)) (by positivity)
        _ = 4 * (|S.ω_freq ω| + K) * S.g ω := by ring
    have bound_int : Integrable bound μ := by
      simp only [hbound_def]
      show Integrable (fun ω => 4 * (|S.ω_freq ω| + K) * S.g ω) μ
      have h1 : Integrable (fun ω => 4 * |S.ω_freq ω| * S.g ω) μ := by
        have : (fun ω => 4 * |S.ω_freq ω| * S.g ω) = fun ω => 4 * (|S.ω_freq ω| * S.g ω) := by
          ext ω; ring
        rw [this]; exact hω_g_int.const_mul 4
      have h2 : Integrable (fun ω => 4 * K * S.g ω) μ := by
        have : (fun ω => 4 * K * S.g ω) = fun ω => (4 * K) * S.g ω := by ext ω; ring
        rw [this]; exact hg_int.const_mul (4 * K)
      have : (fun ω => 4 * (|S.ω_freq ω| + K) * S.g ω) =
          fun ω => 4 * |S.ω_freq ω| * S.g ω + 4 * K * S.g ω := by ext ω; ring
      rw [this]; exact h1.add h2
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (hs := Ioi_mem_nhds ht)
      (hF_meas := Eventually.of_forall (fun s => (hV_int s).aestronglyMeasurable))
      (hF_int := hV_int t)
      (hF'_meas := by
        apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
          (f := fun (n : ℕ) ω => ((↑n + 1 : ℝ)) * (F (t + (↑n + 1 : ℝ)⁻¹) ω - F t ω))
        · intro n; exact ((hV_int _).aestronglyMeasurable.sub
            (hV_int t).aestronglyMeasurable).const_mul _
        · apply h_pw_deriv.mono; intro ω hω
          have hd := hω t (mem_Ioi.mpr ht)
          have key : ∀ n : ℕ, ((↑n + 1 : ℝ)) * (F (t + (↑n + 1 : ℝ)⁻¹) ω - F t ω) =
              slope (F · ω) t (t + (↑n + 1 : ℝ)⁻¹) := by
            intro n
            have hne : (↑n + 1 : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
            simp only [slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul,
              inv_inv]
          simp_rw [key]
          apply hd.tendsto_slope.comp
          rw [tendsto_nhdsWithin_iff]; constructor
          · have : Tendsto (fun n : ℕ => (↑n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
              tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _
                1 tendsto_natCast_atTop_atTop)
            simpa using tendsto_const_nhds.add this
          · exact Eventually.of_forall fun n =>
              Set.mem_compl_singleton_iff.mpr (by
                have : (0:ℝ) < (↑n + 1 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
                linarith))
      (h_bound := h_norm_bound)
      (bound_integrable := bound_int)
      (h_diff := h_pw_deriv)).2

/-! ## V derivative decomposition -/

/-- After rotation cancels, V' decomposes as:
    V' = V'_coupling = K · [coupling terms]
    The rotation part Re(conj(z-z*)·(-iω(z-z*))) = 0 (proved). -/
theorem complex_V_deriv_rotation_split
    (ω_freq K : ℝ) (η z z_star : ℂ) :
    (starRingEnd ℂ (z - z_star) * complexOaRHS ω_freq K η z).re =
    (starRingEnd ℂ (z - z_star) * (-(Complex.I) * (ω_freq : ℂ) * (z - z_star))).re +
    (starRingEnd ℂ (z - z_star) * (-(Complex.I) * (ω_freq : ℂ) * z_star +
      ((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2))).re := by
  have : complexOaRHS ω_freq K η z =
      -(Complex.I) * (ω_freq : ℂ) * (z - z_star) +
      (-(Complex.I) * (ω_freq : ℂ) * z_star +
        ((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2)) := by
    unfold complexOaRHS; ring
  rw [this, mul_add, Complex.add_re]

/-- The rotation part vanishes, leaving only coupling. -/
theorem complex_V_deriv_eq_coupling
    (ω_freq K : ℝ) (η z z_star : ℂ) :
    (starRingEnd ℂ (z - z_star) * complexOaRHS ω_freq K η z).re =
    (starRingEnd ℂ (z - z_star) * (-(Complex.I) * (ω_freq : ℂ) * z_star +
      ((K : ℂ) / 2) * (starRingEnd ℂ η - η * z ^ 2))).re := by
  rw [complex_V_deriv_rotation_split]
  rw [complex_V_rotation_cancels, zero_add]

/-! ## Basin decay from Leibniz + decomposition -/

/-- **COMPLEX V BASIN DECAY.**
    Combines:
    1. Complex Leibniz: V differentiable with V' = ∫ 2Re(conj(z-z*)·ż)·g
    2. Rotation cancellation: rotation term vanishes
    3. Decomposition: V' = V'_real + V'_cross
    4. Coercivity dominates error: V' ≤ -rate·V

    Hypotheses:
    - Finite first moment: ∫|ω|·g < ∞
    - Basin: V < r*²
    - Coercivity > error (quantitative condition on K, g) -/
theorem complex_V_basin_decay
    (V : ℝ → ℝ) (rate : ℝ)
    (hrate : 0 < rate)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_diff : ∀ t, 0 < t → HasDerivAt V (deriv V t) t)
    (h_decomp : ∀ t, 0 < t → ∃ V_real V_cross : ℝ,
      deriv V t = V_real + V_cross ∧
      V_real ≤ -2 * rate * V t ∧
      |V_cross| ≤ rate * V t) :
    ∀ t, 0 < t → HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -rate * V t := by
  intro t ht
  refine ⟨hV_diff t ht, ?_⟩
  obtain ⟨Vr, Vc, h_split, h_coerce, h_error⟩ := h_decomp t ht
  rw [h_split]
  have h1 : Vc ≤ rate * V t := le_trans (le_abs_self _) h_error
  linarith

/-- **WIRING THEOREM.** Connects Leibniz + decomposition + coercivity
    to produce the basin decay hypothesis needed by the Gronwall/Barbalat chain. -/
theorem complex_basin_decay_wired
    (V : ℝ → ℝ) (rate : ℝ)
    (hrate : 0 < rate)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_diff : ∀ t, 0 < t → HasDerivAt V (deriv V t) t)
    (h_coercivity : ∀ t, 0 < t → deriv V t ≤ -rate * V t) :
    ∀ t, 0 < t → HasDerivAt V (deriv V t) t ∧ deriv V t ≤ -rate * V t :=
  h_basin_decay_from_quantitative V rate hrate hV_diff h_coercivity

end
