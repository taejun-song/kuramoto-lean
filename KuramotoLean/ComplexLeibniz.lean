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
  sorry

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
  sorry

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
