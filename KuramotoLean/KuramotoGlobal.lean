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
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hr_pos : 0 < r 0) :
    0 < psiEnergy α μ 0 := by
  unfold psiEnergy
  have h_nn : ∀ ω, 0 ≤ -Real.log (1 - α ω 0 ^ 2) := by
    intro ω
    have h := hα_inv ω 0 le_rfl
    have h1 : 1 - α ω 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ω 0)]
    have h2 : 0 < 1 - α ω 0 ^ 2 := by nlinarith [h.1, h.2]
    linarith [Real.log_nonpos h2.le h1]
  have h_int : Integrable (fun ω => -Real.log (1 - α ω 0 ^ 2)) μ := by
    sorry
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
    (hα_ode : ∀ ω, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_inv : ∀ ω, 0 < α ω t ∧ α ω t < 1)
    (h_sc : r t = ∫ ω, α ω t ∂μ)
    (hα_int : Integrable (fun ω => α ω t) μ)
    (hψ_int : Integrable (fun ω => -Real.log (1 - α ω t ^ 2)) μ)
    (hγα_int : Integrable (fun ω => γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2)) μ) :
    HasDerivAt (psiEnergy α μ)
      (K * (r t) ^ 2 - 2 * ∫ ω, γ ω * (α ω t) ^ 2 / (1 - (α ω t) ^ 2) ∂μ) t := by
  sorry -- Leibniz for Ψ + substitute the pointwise derivative

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
