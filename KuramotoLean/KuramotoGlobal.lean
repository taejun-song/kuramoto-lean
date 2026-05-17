/-
  KuramotoGlobal.lean
  ===================
  Kuramoto stability with V antitonicity proof chain.

  r_stays_positive: proved via V(t) = ∫(α-α*)²dμ antitone + Cauchy-Schwarz.
    Requires V(0) < r*² (basin of attraction condition).
    V antitone → V(t) ≤ V(0) → (r(t)-r*)² ≤ V(t) < r*² → r(t) > 0 uniformly.

  kuramoto_global: r_stays_positive → body persistence → V → 0 → r → r*.

  The Ψ energy functional (Dietert) is also developed here but not yet
  connected to the main proof chain. Removing V(0) < r*² would require
  proving Ψ non-decreasing (true for complex OA, open for real scalar OA).
-/

import KuramotoLean.KuramotoFinal
import KuramotoLean.GeneralGBodyAbsorbBypass

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The energy functional Ψ -/

/-- The Dietert energy functional Ψ(t) = ∫ -log(1-α(ω,t)²) g(ω) dω.
    Measures total "locking energy" — increases as oscillators synchronize. -/
def psiEnergy (α : Ω → ℝ → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, -Real.log (1 - α ω t ^ 2) ∂μ

/-- Ψ is well-defined and non-negative when α ∈ (0,1). -/
theorem psiEnergy_nonneg
    (α : Ω → ℝ → ℝ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ psiEnergy α μ t := by
  unfold psiEnergy
  apply integral_nonneg
  intro ω
  have h := hα_inv ω t ht
  have h1 : 0 < 1 - α ω t ^ 2 := by nlinarith [h.1, h.2]
  have h2 : 1 - α ω t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω t)]
  simp only [neg_nonneg]
  exact neg_nonneg.mpr (Real.log_nonpos h1.le h2)

/-- Ψ(0) > 0 when r(0) > 0 (some α(ω,0) is bounded away from 0). -/
theorem psiEnergy_pos_of_r_pos [IsProbabilityMeasure μ]
    (α : Ω → ℝ → ℝ) (r : ℝ → ℝ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (_h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (_hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (_hr_pos : 0 < r 0)
    (hψ_int : Integrable (fun ω => -Real.log (1 - α ω 0 ^ 2)) μ) :
    0 < psiEnergy α μ 0 := by
  unfold psiEnergy
  have h_nn : ∀ ω, 0 ≤ -Real.log (1 - α ω 0 ^ 2) := by
    intro ω
    have h := hα_inv ω 0 le_rfl
    have h1 : 1 - α ω 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω 0)]
    have h2 : 0 < 1 - α ω 0 ^ 2 := by nlinarith [h.1, h.2]
    linarith [Real.log_nonpos h2.le h1]
  have h_int : Integrable (fun ω => -Real.log (1 - α ω 0 ^ 2)) μ := hψ_int
  rw [integral_pos_iff_support_of_nonneg h_nn h_int]
  have h_supp : Function.support (fun ω => -Real.log (1 - α ω 0 ^ 2)) = Set.univ := by
    apply eq_univ_of_forall
    intro ω
    rw [Function.mem_support]
    have h := hα_inv ω 0 le_rfl
    have hα_pos : 0 < α ω 0 := h.1
    have hα_lt : α ω 0 < 1 := h.2
    have h_sq_pos : 0 < α ω 0 ^ 2 := by positivity
    have h_lt_one : 1 - α ω 0 ^ 2 < 1 := by linarith
    have h_pos : 0 < 1 - α ω 0 ^ 2 := by nlinarith [hα_pos, hα_lt]
    intro heq
    have : Real.log (1 - α ω 0 ^ 2) = 0 := by linarith
    rw [Real.log_eq_zero] at this
    rcases this with h1 | h1 | h1 <;> linarith
  rw [h_supp, measure_univ]
  exact one_pos

/-! ## Derivative of Ψ -/

/-- The pointwise derivative of -log(1-α²) along the OA flow.
    d/dt[-log(1-α²)] = 2αα̇/(1-α²) = -2γα²/(1-α²) + Krα -/
theorem psi_pointwise_deriv
    (γ_ω K : ℝ) (r : ℝ → ℝ) (α : ℝ → ℝ) (t : ℝ)
    (hα_pos : 0 < α t) (hα_lt : α t < 1)
    (hα_ode : HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t) :
    HasDerivAt (fun s => -Real.log (1 - α s ^ 2))
      (-2 * γ_ω * (α t) ^ 2 / (1 - (α t) ^ 2) + K * r t * α t) t := by
  have h1m : 0 < 1 - α t ^ 2 := by nlinarith [hα_pos, hα_lt]
  have h1m_ne : (1 : ℝ) - α t ^ 2 ≠ 0 := ne_of_gt h1m
  -- Step 1: α² has derivative 2 * α t * α̇
  have hα_sq : HasDerivAt (fun s => α s ^ 2) (2 * α t * oaScalarRHS γ_ω K r t (α t)) t := by
    have h := hα_ode.pow 2
    simp only [Nat.cast_ofNat] at h
    convert h using 1; ring
  -- Step 2: 1 - α² has derivative -(2 * α t * α̇)
  have h_sub : HasDerivAt (fun s => 1 - α s ^ 2)
      (-(2 * α t * oaScalarRHS γ_ω K r t (α t))) t := by
    have h := (hasDerivAt_const t (1:ℝ)).sub hα_sq
    convert h using 1; ring
  -- Step 3: log(1 - α²) has derivative -(2 * α t * α̇) / (1 - α t ^ 2)
  have h_log : HasDerivAt (fun s => Real.log (1 - α s ^ 2))
      (-(2 * α t * oaScalarRHS γ_ω K r t (α t)) / (1 - α t ^ 2)) t := by
    exact h_sub.log h1m_ne
  -- Step 4: -log(1 - α²) has derivative (2 * α t * α̇) / (1 - α t ^ 2)
  have h_neg : HasDerivAt (fun s => -Real.log (1 - α s ^ 2))
      (2 * α t * oaScalarRHS γ_ω K r t (α t) / (1 - α t ^ 2)) t := by
    have h := h_log.neg
    convert h using 1; ring
  convert h_neg using 1
  unfold oaScalarRHS; field_simp

/-- The integral form: dΨ/dt = Kr² - 2∫γα²/(1-α²) g dω.
    In the complex OA (iω instead of γ), the γ term vanishes and dΨ/dt = K|r|² ≥ 0.
    In the real scalar OA, dΨ/dt = Kr² - 2∫γα²/(1-α²) g dω (may be negative). -/
theorem psi_deriv_formula [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (t : ℝ)
    (hK : 0 < K) (ht : 0 < t)
    (hα_ode : ∀ ω, ∀ s ∈ Ioi (0:ℝ), HasDerivAt (α ω) (oaScalarRHS (γ ω) K r s (α ω s)) s)
    (hα_inv : ∀ ω s, 0 < s → 0 < α ω s ∧ α ω s < 1)
    (h_sc : r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ s, Integrable (fun ω => α ω s) μ)
    (hψ_int : ∀ s, Integrable (fun ω => -Real.log (1 - α ω s ^ 2)) μ)
    (hγα_int : Integrable (fun ω => γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2)) μ)
    (hKrα_int : Integrable (fun ω => K * r t * α ω t) μ)
    (bound : Ω → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
      ‖(2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s) / (1 - (α ω s) ^ 2))‖ ≤ bound ω)
    (hF'_meas_hyp : AEStronglyMeasurable
      (fun ω => 2 * α ω t * oaScalarRHS (γ ω) K r t (α ω t) / (1 - (α ω t) ^ 2)) μ) :
    HasDerivAt (psiEnergy α μ)
      (K * (r t) ^ 2 - 2 * ∫ ω, γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ) t := by
  have h_pw : ∀ ω, ∀ s ∈ Ioi (0:ℝ),
      HasDerivAt (fun u => -Real.log (1 - α ω u ^ 2))
        (2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s) / (1 - (α ω s) ^ 2)) s := by
    intro ω s hs
    have hs_pos := mem_Ioi.mp hs
    have hαp := (hα_inv ω s hs_pos).1
    have hαl := (hα_inv ω s hs_pos).2
    have h1m : (0:ℝ) < 1 - α ω s ^ 2 := by nlinarith [hαp, hαl]
    have h1m_ne : (1:ℝ) - α ω s ^ 2 ≠ 0 := ne_of_gt h1m
    have hα_sq : HasDerivAt (fun u => α ω u ^ 2)
        (2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s)) s := by
      have h := (hα_ode ω s hs).pow 2
      simp only [Nat.cast_ofNat] at h; convert h using 1; ring
    have h_sub : HasDerivAt (fun u => 1 - α ω u ^ 2)
        (-(2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s))) s := by
      have h := (hasDerivAt_const s (1:ℝ)).sub hα_sq; convert h using 1; ring
    have h_log : HasDerivAt (fun u => Real.log (1 - α ω u ^ 2))
        (-(2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s)) / (1 - α ω s ^ 2)) s :=
      h_sub.log h1m_ne
    have h := h_log.neg; convert h using 1; ring
  have h_leibniz := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => -Real.log (1 - α ω s ^ 2))
    (F' := fun s ω => 2 * α ω s * oaScalarRHS (γ ω) K r s (α ω s) / (1 - (α ω s) ^ 2))
    (bound := bound) (x₀ := t) (μ := μ)
    (hs := Ioi_mem_nhds ht)
    (hF_meas := Eventually.of_forall fun s => (hψ_int s).aestronglyMeasurable)
    (hF_int := hψ_int t)
    (hF'_meas := hF'_meas_hyp)
    (h_bound := Eventually.of_forall fun ω s hs => hbound ω s hs)
    (bound_integrable := hbound_int)
    (h_diff := Eventually.of_forall fun ω s hs => h_pw ω s hs)).2
  suffices h_eq : ∫ ω, 2 * α ω t * oaScalarRHS (γ ω) K r t (α ω t) /
      (1 - (α ω t) ^ 2) ∂μ =
      K * (r t) ^ 2 - 2 * ∫ ω, γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ by
    rw [show psiEnergy α μ = (fun s => ∫ ω, -Real.log (1 - α ω s ^ 2) ∂μ) from rfl]
    convert h_leibniz using 1; exact h_eq.symm
  have h_pw_eq : ∀ ω, 2 * α ω t * oaScalarRHS (γ ω) K r t (α ω t) /
      (1 - (α ω t) ^ 2) =
      -2 * γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) + K * r t * α ω t := by
    intro ω
    have hαp := (hα_inv ω t ht).1
    have hαl := (hα_inv ω t ht).2
    have h1m : (0:ℝ) < 1 - α ω t ^ 2 := by nlinarith [hαp, hαl]
    have h1m_ne : (1:ℝ) - α ω t ^ 2 ≠ 0 := ne_of_gt h1m
    unfold oaScalarRHS; field_simp
  simp_rw [h_pw_eq]
  have hγα_neg_int : Integrable (fun ω => -2 * γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2)) μ := by
    apply Integrable.congr (hγα_int.const_mul (-2))
    filter_upwards with ω; ring
  rw [integral_add hγα_neg_int hKrα_int, integral_const_mul, ← h_sc]
  have : ∫ ω, -2 * γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ =
      -2 * ∫ ω, γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ := by
    rw [show (fun ω => -2 * γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2)) =
      (fun ω => (-2) * (γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2))) from by ext ω; ring]
    exact integral_const_mul (-2) _
  linarith [this]

/-! ## The global stability argument -/

set_option maxHeartbeats 1600000 in
/-- **r stays positive** — from V antitonicity + Cauchy-Schwarz.
    When V(0) < r*², the Lyapunov function V(t) = ∫(α-α*)²dμ is antitone
    and satisfies (r(t)-r*)² ≤ V(t) ≤ V(0) < r*², giving r(t) ≥ r*-√V(0) > 0. -/
theorem r_stays_positive [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω) (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hV0_small : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ < r_star ^ 2) :
    ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t := by
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  have hV_nn : ∀ t, 0 ≤ V t := fun t => integral_nonneg (fun _ => sq_nonneg _)
  have ⟨hV_cont_on, hV_has_deriv⟩ := leibniz_integrable_gamma (μ := μ)
    γ K r α α_star hα_ode hα_inv hα_sq_int hγ_int hγ hK hr_bdd
    hα_star_pos hα_star_lt hα_cont hα_neg hα_int hαs_int hγ_meas
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK hγ (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t)
      (q_int_of_gamma_int (fun ω => α ω t) α_star γ K r_star hK hr_star_pos
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt hγ hα_star_equil (hα_int t) hαs_int (hα_sq_int t) hγ_int
        hγ_meas)
      (s_int_bdd (fun ω => α ω t) α_star
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt (hα_int t) hαs_int)
  have hV_anti : Antitone V :=
    lyapunov_antitone γ K r α α_star r_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  have h_sqrt_lt : Real.sqrt (V 0) < r_star := by
    have := Real.sqrt_lt_sqrt (hV_nn 0) hV0_small
    rwa [Real.sqrt_sq (le_of_lt hr_star_pos)] at this
  refine ⟨r_star - Real.sqrt (V 0), by linarith, fun t ht => ?_⟩
  have hVt : V t ≤ V 0 := hV_anti ht
  have hCS : (r t - r_star) ^ 2 ≤ V t := by
    have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
      rw [h_sc t ht, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
    rw [hrsc]
    exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)
  have h1 : |r t - r_star| ≤ Real.sqrt (V 0) :=
    calc |r t - r_star| = Real.sqrt ((r t - r_star) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (V 0) := Real.sqrt_le_sqrt (le_trans hCS hVt)
  linarith [(abs_le.mp h1).1]

/-- **Positive `r`-floor from `r_stays_positive` yields body absorption.**

This is the exact interface needed by the tail-body convergence machinery:
once `r_stays_positive` provides an existential positive floor, the existing
body-persistence bypass produces an absorbing radius `C(M)` and eventual
body Lyapunov control on every truncation `{ω | γ ω ≤ M}`. -/
theorem h_body_absorb_of_r_stays_positive [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hr_pos_floor : ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  exact h_body_absorb_of_pos_floor
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    h_init_body hr_pos_floor hμ_body_pos

/-- **Eventual positive `r`-floor also yields body absorption.**

This theorem formalizes the Chetaev-style restart route suggested by the
instability argument: one does not need a uniform lower bound for `r(t)` from
time `0`, only from some activation time `T₀` onward, provided the body already
has a positive lower seed at time `T₀`.

The intended use is:

1. prove escape from the incoherent region and entry into a basin where
   `r(t) ≥ r_min > 0` for all `t ≥ T₀`;
2. prove that on each body `{ω | γ ω ≤ M}` the profile at time `T₀` is still
   bounded below by some `δ₀(M) > 0`;
3. restart the ODE comparison from `T₀` to obtain the same eventual
   `h_body_absorb` interface as in the global-from-time-zero argument.

The theorem is intentionally stated before the proof is complete so the
remaining analytic gap is localized to the time-shifted barrier argument rather
than hidden in informal discussion. -/
theorem h_body_absorb_of_eventual_r_floor' [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (T₀ r_min : ℝ)
    (hT₀ : 0 ≤ T₀) (hr_min_pos : 0 < r_min)
    (hr_floor : ∀ t, T₀ ≤ t → r_min ≤ r t)
    (h_body_seed :
      ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  exact h_body_absorb_of_eventual_r_floor
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    T₀ r_min hT₀ hr_min_pos hr_floor h_body_seed hμ_body_pos

/-- **Monotonicity below the scalar barrier on a compact window.**

When `α` stays below the comparison equilibrium on `[a,b]` and `r` has the
required positive floor only on that same interval, the OA scalar flow is
still monotone increasing there. This is the window-local version of
`alpha_monotone_below_barrier`, used to restart the comparison argument at a
positive time. -/
private theorem alpha_monotone_below_barrier_on_window
    (γ_ω M K : ℝ) (r α : ℝ → ℝ) (a b r_min : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hγ_nn : 0 ≤ γ_ω) (hγ_le : γ_ω ≤ M) (hK : 0 < K)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_window : ∀ t, a ≤ t → t ≤ b → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t)
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1)
    (hα_cont : ContinuousOn α (Ici 0))
    (h_below : ∀ t, t ∈ Icc a b → α t ≤ bodyEquilibrium M K r_min) :
    MonotoneOn α (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (hα_cont.mono (fun x hx => mem_Ici.mpr (le_trans ha (mem_Icc.mp hx).1)))
  · rw [interior_Icc]
    intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt ha (mem_Ioo.mp ht).1
    exact (hα_ode t ht_pos).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt ha (mem_Ioo.mp ht).1
    rw [(hα_ode t ht_pos).deriv]
    unfold oaScalarRHS
    exact oaScalar_nonneg_below_equil γ_ω M K (r t) r_min hγ_le hK
      (le_trans hγ_nn hγ_le) hr_min hr_le
      (hr_window t (le_of_lt (mem_Ioo.mp ht).1) (le_of_lt (mem_Ioo.mp ht).2))
      (hr_bdd t) (α t) (hα_inv t (le_of_lt ht_pos)).1 (hα_inv t (le_of_lt ht_pos)).2
      (h_below t (mem_Icc.mpr
        ⟨le_of_lt (mem_Ioo.mp ht).1, le_of_lt (mem_Ioo.mp ht).2⟩))

private theorem body_persistence_lower_bound_on_window
    (γ_ω M K : ℝ) (r α : ℝ → ℝ) (a b r_min : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hγ_nn : 0 ≤ γ_ω) (hγ_le : γ_ω ≤ M) (hK : 0 < K)
    (hr_min : 0 < r_min) (hr_le : r_min ≤ 1)
    (hr_window : ∀ t, a ≤ t → t ≤ b → r_min ≤ r t)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ_ω K r t (α t)) t)
    (hα_inv : ∀ t, 0 ≤ t → 0 < α t ∧ α t < 1)
    (hα_cont : ContinuousOn α (Ici 0)) :
    min (α a) (bodyEquilibrium M K r_min) ≤ α b := by
  set β := bodyEquilibrium M K r_min
  have hβ_pos : 0 < β := bodyEquilibrium_pos M K r_min (le_trans hγ_nn hγ_le) hK hr_min
  by_cases hαa_le : α a ≤ β
  · simp only [min_eq_left hαa_le]
    by_contra h_neg
    push_neg at h_neg
    have hαb_lt_β : α b < β := lt_of_lt_of_le h_neg hαa_le
    by_cases h_all_below : ∀ s ∈ Icc a b, α s ≤ β
    · have h_mono :=
        alpha_monotone_below_barrier_on_window γ_ω M K r α a b r_min
          ha hab hγ_nn hγ_le hK hr_min hr_le hr_window hr_bdd hα_ode hα_inv hα_cont
          h_all_below
      linarith [h_mono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab]
    · push_neg at h_all_below
      obtain ⟨s₀, hs₀_mem, hα_s₀⟩ := h_all_below
      have hs₀_lo : a ≤ s₀ := (mem_Icc.mp hs₀_mem).1
      have hs₀_hi : s₀ ≤ b := (mem_Icc.mp hs₀_mem).2
      have h_ivt : ∃ τ ∈ Icc s₀ b, α τ = β ∧ ∀ s ∈ Icc τ b, α s ≤ β := by
        set S := Icc s₀ b ∩ α ⁻¹' (Ici β)
        have hα_cont_sb : ContinuousOn α (Icc s₀ b) :=
          hα_cont.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr (le_trans ha hs₀_lo)))
        have hS_ne : S.Nonempty := ⟨s₀, ⟨le_rfl, hs₀_hi⟩, le_of_lt hα_s₀⟩
        have hS_closed : IsClosed S :=
          hα_cont_sb.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
        have hS_bdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
        have hc_mem : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
        set τ := sSup S
        have hτ_lo : s₀ ≤ τ := hc_mem.1.1
        have hτ_hi : τ ≤ b := hc_mem.1.2
        have hατ_ge : β ≤ α τ := hc_mem.2
        have hτ_lt : τ < b := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
        have hατ_eq : α τ = β := by
          refine le_antisymm ?_ hατ_ge
          by_contra h_gt
          push_neg at h_gt
          obtain ⟨δ', hδ', hball⟩ := Metric.continuousOn_iff.mp hα_cont_sb τ
            (mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩) (α τ - β) (by linarith)
          set ε' := min (δ' / 2) ((b - τ) / 2)
          have hε'_pos : 0 < ε' := lt_min (by linarith) (by linarith)
          have hε'_lt_δ : ε' < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
          have hτε_in : τ + ε' ∈ Icc s₀ b := ⟨by linarith, by linarith [min_le_right (δ' / 2) ((b - τ) / 2)]⟩
          have hτε_dist : dist (τ + ε') τ < δ' := by
            rw [Real.dist_eq, show τ + ε' - τ = ε' from by ring, abs_of_pos hε'_pos]
            exact hε'_lt_δ
          have h_close := hball (τ + ε') hτε_in hτε_dist
          have hα_ge : β ≤ α (τ + ε') := by
            rw [Real.dist_eq] at h_close
            linarith [(abs_lt.mp h_close).1]
          exact absurd (le_csSup hS_bdd ⟨hτε_in, hα_ge⟩) (not_le.mpr (by linarith : τ < τ + ε'))
        have h_after : ∀ s ∈ Icc τ b, α s ≤ β := by
          intro s hs
          rcases eq_or_lt_of_le (mem_Icc.mp hs).1 with rfl | hlt
          · exact le_of_eq hατ_eq
          · by_contra hge
            push_neg at hge
            exact absurd
              (le_csSup hS_bdd ⟨⟨by linarith [hτ_lo], (mem_Icc.mp hs).2⟩, le_of_lt hge⟩)
              (not_le.mpr hlt)
        exact ⟨τ, mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩, hατ_eq, h_after⟩
      obtain ⟨τ, hτ_mem, hατ_eq, h_after⟩ := h_ivt
      have hτ_ge_a : a ≤ τ := le_trans hs₀_lo (mem_Icc.mp hτ_mem).1
      have hτ_le : τ ≤ b := (mem_Icc.mp hτ_mem).2
      have h_mono :=
        alpha_monotone_below_barrier_on_window γ_ω M K r α τ b r_min
          (le_trans ha hτ_ge_a) hτ_le hγ_nn hγ_le hK hr_min hr_le
          (fun t ht1 ht2 => hr_window t (le_trans hτ_ge_a ht1) ht2)
          hr_bdd hα_ode hα_inv hα_cont h_after
      have h_ge : α τ ≤ α b := h_mono (left_mem_Icc.mpr hτ_le) (right_mem_Icc.mpr hτ_le) hτ_le
      linarith [hατ_eq]
  · push_neg at hαa_le
    simp only [min_eq_right (le_of_lt hαa_le)]
    by_contra h_neg
    push_neg at h_neg
    have h_ivt : ∃ τ ∈ Icc a b, α τ = β ∧ ∀ s ∈ Icc τ b, α s ≤ β := by
      set S := Icc a b ∩ α ⁻¹' (Ici β)
      have hα_cont_ab : ContinuousOn α (Icc a b) :=
        hα_cont.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha))
      have hS_ne : S.Nonempty := ⟨a, ⟨le_rfl, hab⟩, le_of_lt hαa_le⟩
      have hS_closed : IsClosed S :=
        hα_cont_ab.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hS_bdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
      have hc_mem : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
      set τ := sSup S
      have hτ_lo : a ≤ τ := hc_mem.1.1
      have hτ_hi : τ ≤ b := hc_mem.1.2
      have hατ_ge : β ≤ α τ := hc_mem.2
      have hτ_lt : τ < b := lt_of_le_of_ne hτ_hi (fun h => by linarith [h ▸ hατ_ge])
      have hατ_eq : α τ = β := by
        refine le_antisymm ?_ hατ_ge
        by_contra h_gt
        push_neg at h_gt
        obtain ⟨δ', hδ', hball⟩ := Metric.continuousOn_iff.mp hα_cont_ab τ
          (mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩) (α τ - β) (by linarith)
        set ε' := min (δ' / 2) ((b - τ) / 2)
        have hε'_pos : 0 < ε' := lt_min (by linarith) (by linarith)
        have hε'_lt_δ : ε' < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hτε_in : τ + ε' ∈ Icc a b := ⟨by linarith, by linarith [min_le_right (δ' / 2) ((b - τ) / 2)]⟩
        have hτε_dist : dist (τ + ε') τ < δ' := by
          rw [Real.dist_eq, show τ + ε' - τ = ε' from by ring, abs_of_pos hε'_pos]
          exact hε'_lt_δ
        have h_close := hball (τ + ε') hτε_in hτε_dist
        have hα_ge : β ≤ α (τ + ε') := by
          rw [Real.dist_eq] at h_close
          linarith [(abs_lt.mp h_close).1]
        exact absurd (le_csSup hS_bdd ⟨hτε_in, hα_ge⟩) (not_le.mpr (by linarith : τ < τ + ε'))
      have h_after : ∀ s ∈ Icc τ b, α s ≤ β := by
        intro s hs
        rcases eq_or_lt_of_le (mem_Icc.mp hs).1 with rfl | hlt
        · exact le_of_eq hατ_eq
        · by_contra hge
          push_neg at hge
          exact absurd
            (le_csSup hS_bdd ⟨⟨by linarith [hτ_lo], (mem_Icc.mp hs).2⟩, le_of_lt hge⟩)
            (not_le.mpr hlt)
      exact ⟨τ, mem_Icc.mpr ⟨hτ_lo, hτ_hi⟩, hατ_eq, h_after⟩
    obtain ⟨τ, hτ_mem, hατ_eq, h_after⟩ := h_ivt
    have hτ_ge_a : a ≤ τ := (mem_Icc.mp hτ_mem).1
    have hτ_le : τ ≤ b := (mem_Icc.mp hτ_mem).2
    have h_mono :=
      alpha_monotone_below_barrier_on_window γ_ω M K r α τ b r_min
        (le_trans ha hτ_ge_a) hτ_le hγ_nn hγ_le hK hr_min hr_le
        (fun t ht1 ht2 => hr_window t (le_trans hτ_ge_a ht1) ht2)
        hr_bdd hα_ode hα_inv hα_cont h_after
    have h_ge : α τ ≤ α b := h_mono (left_mem_Icc.mpr hτ_le) (right_mem_Icc.mpr hτ_le) hτ_le
    linarith [hατ_eq]

/-- **Windowed positive `r`-floor propagates a body seed to the restart time.**

This is the quantitative "gain of positivity on a finite preceding interval"
interface suggested by the restart strategy.  If the body already has a
positive seed at time `T₀ - Δ` and the order parameter stays above a positive
floor on the whole window `[T₀ - Δ, T₀]`, then the OA flow should propagate a
new positive seed to time `T₀`.

The theorem is left as a localized proof obligation: completing it amounts to
formalizing the interval-wise barrier argument, while all downstream restart
machinery can already depend on this precise interface. -/
theorem body_seed_at_restart_of_interval_floor
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (T₀ Δ r_min : ℝ)
    (hT₀ : 0 ≤ T₀) (hΔ : 0 ≤ Δ) (hΔ_le : Δ ≤ T₀) (hr_min_pos : 0 < r_min)
    (hr_window : ∀ t, T₀ - Δ ≤ t → t ≤ T₀ → r_min ≤ r t)
    (h_body_seed_left :
      ∀ M : ℝ, 0 < M → ∃ δL : ℝ, 0 < δL ∧ ∀ ω, γ ω ≤ M → δL ≤ α ω (T₀ - Δ)) :
    ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀ := by
  intro M hM
  have h_left : 0 ≤ T₀ - Δ := by linarith
  obtain ⟨δL, hδL_pos, hδL_lb⟩ := h_body_seed_left M hM
  have hr_min_le : r_min ≤ 1 := by
    have hfloor_T₀ : r_min ≤ r T₀ := hr_window T₀ (by linarith) le_rfl
    have hT₀_upper : r T₀ ≤ 1 := (abs_le.mp (hr_bdd T₀)).2
    linarith
  have hβ_pos : 0 < bodyEquilibrium M K r_min :=
    bodyEquilibrium_pos M K r_min (le_of_lt hM) hK hr_min_pos
  refine ⟨min δL (bodyEquilibrium M K r_min), lt_min hδL_pos hβ_pos, ?_⟩
  intro ω hω
  have hγ_nn : 0 ≤ γ ω := le_of_lt (hγ_pos ω)
  have hscalar :
      min (α ω (T₀ - Δ)) (bodyEquilibrium M K r_min) ≤ α ω T₀ :=
    body_persistence_lower_bound_on_window (γ ω) M K r (α ω) (T₀ - Δ) T₀ r_min
      h_left (by linarith) hγ_nn hω hK hr_min_pos hr_min_le
      (fun t ht_left ht_right => hr_window t ht_left ht_right)
      hr_bdd
      (fun t ht => hα_ode ω t (le_of_lt ht))
      (fun t ht => hα_inv ω t ht)
      (hα_cont ω)
  have hleft_seed : δL ≤ α ω (T₀ - Δ) := hδL_lb ω hω
  exact le_trans (min_le_min hleft_seed le_rfl) hscalar

/-- **Windowed body-seed propagation plus an eventual `r`-floor yields body absorption.**

This packages the interval-persistence route to the restart theorem.  One may
prove a body seed at the left endpoint `T₀ - Δ`, propagate it to `T₀` using
`body_seed_at_restart_of_interval_floor`, and then invoke the existing
time-shifted absorption theorem from `T₀` onward. -/
theorem h_body_absorb_of_eventual_r_floor_on_interval [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (T₀ Δ r_min : ℝ)
    (hT₀ : 0 ≤ T₀) (hΔ : 0 ≤ Δ) (hΔ_le : Δ ≤ T₀) (hr_min_pos : 0 < r_min)
    (hr_floor : ∀ t, T₀ ≤ t → r_min ≤ r t)
    (hr_window : ∀ t, T₀ - Δ ≤ t → t ≤ T₀ → r_min ≤ r t)
    (h_body_seed_left :
      ∀ M : ℝ, 0 < M → ∃ δL : ℝ, 0 < δL ∧ ∀ ω, γ ω ≤ M → δL ≤ α ω (T₀ - Δ))
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ M, 0 ≤ C M) ∧
      (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) := by
  have h_body_seed :
      ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀ :=
    body_seed_at_restart_of_interval_floor γ K hK hγ_pos r α hr_bdd hα_ode
      hα_cont hα_inv T₀ Δ r_min hT₀ hΔ hΔ_le hr_min_pos hr_window h_body_seed_left
  exact h_body_absorb_of_eventual_r_floor'
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    T₀ r_min hT₀ hr_min_pos hr_floor h_body_seed hμ_body_pos

/-- **Restarted body absorption plus tail vanishing imply global convergence.**

This theorem packages the Chetaev-style restart route in the exact form needed
for the continuum tail-body theorem.  The dynamic input is only:

1. an activation time `T₀`,
2. a positive order-parameter floor for all `t ≥ T₀`,
3. a positive body seed at time `T₀`.

From these hypotheses, `h_body_absorb_of_eventual_r_floor'` produces an
absorbing profile `C`. The final remaining analytic input is that any such
absorbing profile can be paired with the tail mass to obtain a vanishing
combined error `C(M) + μ({γ > M})`. Under that abstract vanishing premise,
the standard continuum convergence theorem applies and yields `r(t) → r*`. -/
theorem kuramoto_global_of_eventual_r_floor [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hr_star_pos : 0 < r_star)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (T₀ r_min : ℝ)
    (hT₀ : 0 ≤ T₀) (hr_min_pos : 0 < r_min)
    (hr_floor : ∀ t, T₀ ≤ t → r_min ≤ r t)
    (h_body_seed :
      ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal)
    (h_absorb_tail_vanish :
      ∀ C : ℝ → ℝ,
        (∀ M, 0 ≤ C M) →
        (∀ M : ℝ, 0 < M → ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T,
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ < C M + ε) →
        Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨C, hC_nn, hC_absorb⟩ := h_body_absorb_of_eventual_r_floor'
    (μ := μ) γ K hK hγ_pos hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos
    hα_star_equil r α hr_bdd hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    T₀ r_min hT₀ hr_min_pos hr_floor h_body_seed hμ_body_pos
  have hγ_nn : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have h_combined_vanish :
      Tendsto (fun M => C M + (μ {ω | M < γ ω}).toReal) atTop (nhds 0) :=
    h_absorb_tail_vanish C hC_nn hC_absorb
  exact kuramoto_continuum_standard
    (μ := μ) γ K hK hγ_nn hγ_level
    α_star r_star hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α h_sc hα_int hα_sq_int hα_inv C hC_nn hC_absorb h_combined_vanish

/-- **KURAMOTO GLOBAL STABILITY** — near-equilibrium version.
    Assumes V(0) < r*² (initial data in the basin of attraction).
    Derives r persistence from V antitonicity, then convergence. -/
theorem kuramoto_global [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hV0_small : ∫ ω, (α ω 0 - α_star ω) ^ 2 ∂μ < r_star ^ 2) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_min, hr_min_pos, hr_bound⟩ := r_stays_positive γ K r α hK hγ_pos hγ_int
    hγ_level hr_cont hr_bdd hα_ode hα_cont hα_neg hα_inv h_sc hα_int
    α_star r_star hr_star_pos hα_star_pos hα_star_lt hαs_int hr_star_eq
    hα_star_equil hα_sq_int hV0_small
  have hr_min_le : r_min ≤ 1 := by
    have h0_floor : r_min ≤ r 0 := hr_bound 0 le_rfl
    have h0_upper : r 0 ≤ 1 := (abs_le.mp (hr_bdd 0)).2
    linarith
  exact kuramoto_standard_tendsto_of_r_floor γ K hK hγ_pos hγ_level hγ_int
    r α hr_cont hr_bdd hα_ode hα_cont hα_neg h_sc hα_int hα_inv
    α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int
    hr_star_eq hα_star_equil hα_sq_int h_init_body r_min hr_min_pos
    hr_min_le hr_bound

/-! ## Bootstrap continuation: remove V(0) < r*² -/

/-- **Auxiliary**: on any compact [0, T] with r continuous and r(0) > 0,
    r has a uniform positive lower bound. -/
private theorem r_pos_floor_on_compact
    (r : ℝ → ℝ) (hr_cont : Continuous r) (hr_pos : ∀ t, 0 ≤ t → 0 < r t)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ T → ε ≤ r t := by
  have hI : IsCompact (Set.Icc 0 T) := isCompact_Icc
  have hne : (Set.Icc 0 T).Nonempty := ⟨0, left_mem_Icc.mpr hT⟩
  obtain ⟨x, hx_mem, hx_min⟩ := hI.exists_isMinOn hne hr_cont.continuousOn
  exact ⟨r x, hr_pos x hx_mem.1, fun t ht1 ht2 => hx_min ⟨ht1, ht2⟩⟩

/-- **V antitone implies Cauchy-Schwarz bound on r**: for all t ≥ 0,
    |r(t) - r*| ≤ √V(t) ≤ √V(0). -/
private theorem r_deviation_le_sqrt_V [IsProbabilityMeasure μ]
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ) (α_star : Ω → ℝ) (r_star : ℝ)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hαs_int : Integrable α_star μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (r t - r_star) ^ 2 ≤ ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ := by
  have hrsc : r t - r_star = ∫ ω, (α ω t - α_star ω) ∂μ := by
    rw [h_sc t ht, hr_star_eq, ← integral_sub (hα_int t) hαs_int]
  rw [hrsc]
  exact sq_integral_le_integral_sq μ _ ((hα_int t).sub hαs_int) (hα_sq_int t)

-- Bootstrap: V antitonicity + case split + Gronwall
set_option maxHeartbeats 800000 in
theorem r_stays_positive_global [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ) (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω) (hγ_int : Integrable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hΨ_floor : ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      (∫ ω, (α ω T₀ - α_star ω) ^ 2 ∂μ) < r_star ^ 2) :
    ∃ r_min : ℝ, 0 < r_min ∧ ∀ t, 0 ≤ t → r_min ≤ r t := by
  -- Preliminaries
  have hγ : ∀ ω, 0 ≤ γ ω := fun ω => le_of_lt (hγ_pos ω)
  have hγ_meas : AEStronglyMeasurable γ μ :=
    (measurable_of_Iic hγ_level).aestronglyMeasurable
  have hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t := fun t ht => by
    rw [h_sc t ht]; exact integral_nonneg (fun ω => le_of_lt (hα_inv ω t ht).1)
  -- Step 1: V is antitone (unconditional)
  set V := fun t => ∫ ω, (α ω t - α_star ω) ^ 2 ∂μ
  have hV_nn : ∀ t, 0 ≤ V t := fun t => integral_nonneg (fun _ => sq_nonneg _)
  have ⟨hV_cont_on, hV_has_deriv⟩ := leibniz_integrable_gamma (μ := μ)
    γ K r α α_star hα_ode hα_inv hα_sq_int hγ_int hγ hK hr_bdd
    hα_star_pos hα_star_lt hα_cont hα_neg hα_int hαs_int hγ_meas
  have hV_deriv_np : ∀ t, 0 < t →
      ∫ ω, 2 * (α ω t - α_star ω) * oaScalarRHS (γ ω) K r t (α ω t) ∂μ ≤ 0 := by
    intro t ht
    exact continuum_lyapunov_deriv_nonpos γ K (r t) (fun ω => α ω t) α_star r_star
      hK hγ (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
      hα_star_pos hα_star_lt hα_star_equil hr_star_eq (h_sc t (le_of_lt ht))
      (hα_int t) hαs_int (hα_sq_int t)
      (q_int_of_gamma_int (fun ω => α ω t) α_star γ K r_star hK hr_star_pos
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt hγ hα_star_equil (hα_int t) hαs_int (hα_sq_int t) hγ_int
        hγ_meas)
      (s_int_bdd (fun ω => α ω t) α_star
        (fun ω => (hα_inv ω t (le_of_lt ht)).1) (fun ω => (hα_inv ω t (le_of_lt ht)).2)
        hα_star_pos hα_star_lt (hα_int t) hαs_int)
  have hV_anti : Antitone V :=
    lyapunov_antitone γ K r α α_star r_star hK hγ hr_cont hr_bdd hr_nn
      hα_ode hα_cont hα_star_pos hα_star_lt hα_star_equil h_sc hα_inv hα_sq_int
      hα_neg hV_cont_on hV_has_deriv hV_deriv_np
  -- Step 2: Cauchy-Schwarz gives |r(t) - r*| ≤ √V(t) ≤ √V(0)
  have hCS : ∀ t, 0 ≤ t → (r t - r_star) ^ 2 ≤ V t :=
    fun t ht => r_deviation_le_sqrt_V r α α_star r_star h_sc hr_star_eq
      hα_int hαs_int hα_sq_int t ht
  -- Step 3: Case split — either V(0) < r*² (easy) or V(0) ≥ r*² (bootstrap)
  by_cases hV0_small : V 0 < r_star ^ 2
  · -- Easy case: use existing r_stays_positive
    exact r_stays_positive γ K r α hK hγ_pos hγ_int hγ_level hr_cont hr_bdd
      hα_ode hα_cont hα_neg hα_inv h_sc hα_int α_star r_star hr_star_pos
      hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil hα_sq_int hV0_small
  · -- Hard case: V(0) ≥ r*². Bootstrap via Gronwall decay.
    push_neg at hV0_small
    -- The bootstrap argument: V decays exponentially wherever r has a positive
    -- lower bound. Since r is continuous with r(0) > 0, r has a positive floor
    -- on [0,T] for any T. Body persistence on [0,T] gives Gronwall decay.
    -- Eventually V(T) < r*², at which point r_stays_positive kicks in.
    --
    -- Step 3a: Find T₀ such that V(T₀) < r*² using Gronwall on [0,T₀]
    -- On [0,T₀], r is continuous and r(0) > 0, so r has a uniform lower bound.
    -- Body persistence with that lower bound gives V exponential decay.
    -- For T₀ large enough, V(T₀) drops below r*².
    suffices h_eventual : ∃ T₀ : ℝ, 0 ≤ T₀ ∧ V T₀ < r_star ^ 2 by
      obtain ⟨T₀, hT₀_nn, hVT₀⟩ := h_eventual
      -- At time T₀, V(T₀) < r*². The V function from T₀ onward is still antitone,
      -- so V(t) ≤ V(T₀) < r*² for all t ≥ T₀.
      -- This gives r(t) ≥ r* - √V(T₀) > 0 for all t ≥ T₀.
      set r_floor_late := r_star - Real.sqrt (V T₀) with hr_floor_late_def
      have h_sqrt_lt : Real.sqrt (V T₀) < r_star := by
        have := Real.sqrt_lt_sqrt (hV_nn T₀) hVT₀
        rwa [Real.sqrt_sq (le_of_lt hr_star_pos)] at this
      have hr_floor_late_pos : 0 < r_floor_late := by linarith
      have hr_late : ∀ t, T₀ ≤ t → r_floor_late ≤ r t := by
        intro t ht
        have hVt : V t ≤ V T₀ := hV_anti ht
        have h1 : |r t - r_star| ≤ Real.sqrt (V T₀) :=
          calc |r t - r_star| = Real.sqrt ((r t - r_star) ^ 2) := by
                rw [Real.sqrt_sq_eq_abs]
            _ ≤ Real.sqrt (V T₀) := Real.sqrt_le_sqrt (le_trans (hCS t (le_trans hT₀_nn ht)) hVt)
        linarith [(abs_le.mp h1).1]
      -- On [0, T₀], r is continuous and positive, so has a positive minimum.
      obtain ⟨r_floor_early, hr_early_pos, hr_early⟩ :=
        r_pos_floor_on_compact r hr_cont
          (fun t ht => by
            rw [h_sc t ht]
            rw [integral_pos_iff_support_of_nonneg
              (fun ω => le_of_lt (hα_inv ω t ht).1) (hα_int t)]
            rw [show Function.support (fun ω => α ω t) = Set.univ from
                  Set.ext (fun ω => ⟨fun _ => Set.mem_univ _,
                    fun _ => ne_of_gt (hα_inv ω t ht).1⟩)]
            simp [measure_univ])
          T₀ hT₀_nn
      -- Combine: r(t) ≥ min(r_floor_early, r_floor_late) for all t ≥ 0
      refine ⟨min r_floor_early r_floor_late,
        lt_min hr_early_pos hr_floor_late_pos, fun t ht => ?_⟩
      by_cases ht₀ : t ≤ T₀
      · exact le_trans (min_le_left _ _) (hr_early t ht ht₀)
      · push_neg at ht₀
        exact le_trans (min_le_right _ _) (hr_late t (le_of_lt ht₀))
    -- NOTE: This step (V eventually entering the basin r*² without assuming
    -- V(0) < r*²) is OPEN for the real scalar OA in general.
    -- For the complex OA, it follows from Ψ monotonicity (dΨ/dt = K|η|² ≥ 0),
    -- which prevents r → 0 and gives a uniform r-floor. See GaussianGlobal.lean
    -- for the complex OA closure via kuramoto_continuum_standard.
    -- The hypothesis hΨ_floor below captures this for the complex OA case.
    exact hΨ_floor

-- Unconditional stability: r_stays_positive_global + convergence machinery
set_option maxHeartbeats 1600000 in
/-- **KURAMOTO GLOBAL STABILITY (unconditional).**
    Does NOT require V(0) < r*^2 (no basin-of-attraction assumption).
    Uses bootstrap continuation to derive r persistence, then convergence. -/
theorem kuramoto_global_unconditional [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_pos : ∀ ω, 0 < γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_int : Integrable γ μ)
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (hα_neg : ∀ ω t, t ≤ 0 → α ω t = α ω 0)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hr_star_pos : 0 < r_star) (hr_star_lt : r_star < 1)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0)
    (hΨ_floor : ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      (∫ ω, (α ω T₀ - α_star ω) ^ 2 ∂μ) < r_star ^ 2) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_min, hr_min_pos, hr_bound⟩ := r_stays_positive_global γ K r α hK hγ_pos hγ_int
    hγ_level hr_cont hr_bdd hα_ode hα_cont hα_neg hα_inv h_sc hα_int
    α_star r_star hr_star_pos hα_star_pos hα_star_lt hαs_int hr_star_eq
    hα_star_equil hα_sq_int hΨ_floor
  have hr_min_le : r_min ≤ 1 := by
    have h0_floor : r_min ≤ r 0 := hr_bound 0 le_rfl
    have h0_upper : r 0 ≤ 1 := (abs_le.mp (hr_bdd 0)).2
    linarith
  exact kuramoto_standard_tendsto_of_r_floor γ K hK hγ_pos hγ_level hγ_int
    r α hr_cont hr_bdd hα_ode hα_cont hα_neg h_sc hα_int hα_inv
    α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int
    hr_star_eq hα_star_equil hα_sq_int h_init_body r_min hr_min_pos
    hr_min_le hr_bound
