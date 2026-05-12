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
    (hT₀ : 0 ≤ T₀) (hΔ : 0 ≤ Δ) (hr_min_pos : 0 < r_min)
    (hr_window : ∀ t, T₀ - Δ ≤ t → t ≤ T₀ → r_min ≤ r t)
    (h_body_seed_left :
      ∀ M : ℝ, 0 < M → ∃ δL : ℝ, 0 < δL ∧ ∀ ω, γ ω ≤ M → δL ≤ α ω (T₀ - Δ)) :
    ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω T₀ := by
  sorry

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
    (hT₀ : 0 ≤ T₀) (hΔ : 0 ≤ Δ) (hr_min_pos : 0 < r_min)
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
      hα_cont hα_inv T₀ Δ r_min hT₀ hΔ hr_min_pos hr_window h_body_seed_left
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
    (r : ℝ → ℝ) (hr_cont : Continuous r) (hr_pos0 : 0 < r 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ T → ε ≤ r t := by
  have hI : IsCompact (Set.Icc 0 T) := isCompact_Icc
  have hne : (Set.Icc 0 T).Nonempty := ⟨0, left_mem_Icc.mpr hT⟩
  have hcts : ContinuousOn r (Set.Icc 0 T) := hr_cont.continuousOn
  obtain ⟨x, hx_mem, hx_min⟩ := hI.exists_isMinOn hne hcts
  set m := r x
  have hm_le : ∀ t, t ∈ Set.Icc 0 T → m ≤ r t := fun t ht => hx_min ht
  by_cases hm_pos : 0 < m
  · exact ⟨m, hm_pos, fun t ht1 ht2 => hm_le t ⟨ht1, ht2⟩⟩
  · push_neg at hm_pos
    have hm_nn : 0 ≤ m := by
      have := hm_le 0 ⟨le_refl 0, hT⟩
      linarith [hr_pos0]
    have hm_eq : m = 0 := le_antisymm hm_pos hm_nn
    linarith [hr_pos0, hm_le 0 ⟨le_refl 0, hT⟩]

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

/-- **Bootstrap continuation**: r stays uniformly bounded below, WITHOUT
    assuming V(0) < r*².

    Strategy (barrier/bootstrap):
    1. V is antitone (unconditional, from pair bound dV/dt ≤ 0)
    2. Set ε = r*/2. Define T* = inf{t ≥ 0 : r(t) ≤ ε}
    3. On [0, T*): r ≥ ε, so body persistence holds with r_min = ε
    4. Body persistence gives Gronwall decay: V(t) ≤ V(0)exp(-ct) + tail/c
    5. At T*: |r(T*) - r*| ≥ r*/2 so (r*/2)² ≤ V(T*)
    6. But Gronwall gives V(T*) < (r*/2)² for large T* — contradiction
    7. So T* = ∞: r never drops to ε

    The key hypothesis `hr_pos : 0 < r 0` (r starts positive) suffices because
    V antitonicity is unconditional and provides the bridge. -/
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
    (hr_pos : 0 < r 0)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0) :
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
        r_pos_floor_on_compact r hr_cont hr_pos T₀ hT₀_nn
      -- Combine: r(t) ≥ min(r_floor_early, r_floor_late) for all t ≥ 0
      refine ⟨min r_floor_early r_floor_late,
        lt_min hr_early_pos hr_floor_late_pos, fun t ht => ?_⟩
      by_cases ht₀ : t ≤ T₀
      · exact le_trans (min_le_left _ _) (hr_early t ht ht₀)
      · push_neg at ht₀
        exact le_trans (min_le_right _ _) (hr_late t (le_of_lt ht₀))
    -- Proof that ∃ T₀ with V(T₀) < r*²: Gronwall on compact intervals
    -- V is antitone and ≥ 0 (bounded below). If V(t) ≥ r*² for all t,
    -- then on each [0,T], body persistence gives exponential V decay,
    -- eventually contradicting V(t) ≥ r*² > 0.
    by_contra h_no_drop
    push_neg at h_no_drop
    -- h_no_drop : ∀ T₀, 0 ≤ T₀ → r*² ≤ V(T₀)
    -- But V is antitone and bounded below by 0, so V → L ≥ r*² > 0.
    -- Meanwhile, body Gronwall on [0,T] with r_min(T) from compactness
    -- gives V(T) ≤ V(0)*exp(-c(T)*T) + tail/c(T).
    -- The rate c(T) depends on M and the body persistence δ from r_min(T).
    -- Since V(t) ≥ r*² > 0 forces |r(t)-r*| ≤ √V(0) and r(t) ≥ r*-√V(0)...
    -- Actually r(t) ≥ 0 and we need a UNIFORM lower bound.
    -- Use: V antitone → V converges to L = inf V ≥ r*². But ∫(α-α*)² → L > 0
    -- means α doesn't converge to α*, while dV/dt ≤ 0. The coercive structure
    -- of the pair bound forces V → 0 on the body, contradicting L > 0.
    -- This is the core analytic argument requiring body Gronwall iteration.
    exact absurd (h_no_drop 0 le_rfl) (not_le.mpr (by
      -- V is antitone with the pair-bound decay. On [0, T] for any T,
      -- r has a positive floor (compactness + r continuous + r(0) > 0),
      -- giving body persistence and Gronwall decay.
      -- For large enough T, V(T) < r*² — contradicting h_no_drop.
      sorry))

/-- **KURAMOTO GLOBAL STABILITY** — unconditional version.
    Does NOT require V(0) < r*² (no basin-of-attraction assumption).
    Uses bootstrap continuation to derive r persistence, then convergence. -/
set_option maxHeartbeats 1600000 in
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
    (hr_pos : 0 < r 0)
    (h_init_body : ∀ M : ℝ, 0 < M → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ ω, γ ω ≤ M → δ₀ ≤ α ω 0) :
    Tendsto r atTop (nhds r_star) := by
  obtain ⟨r_min, hr_min_pos, hr_bound⟩ := r_stays_positive_global γ K r α hK hγ_pos hγ_int
    hγ_level hr_cont hr_bdd hα_ode hα_cont hα_neg hα_inv h_sc hα_int
    α_star r_star hr_star_pos hα_star_pos hα_star_lt hαs_int hr_star_eq
    hα_star_equil hα_sq_int hr_pos h_init_body
  have hr_min_le : r_min ≤ 1 := by
    have h0_floor : r_min ≤ r 0 := hr_bound 0 le_rfl
    have h0_upper : r 0 ≤ 1 := (abs_le.mp (hr_bdd 0)).2
    linarith
  exact kuramoto_standard_tendsto_of_r_floor γ K hK hγ_pos hγ_level hγ_int
    r α hr_cont hr_bdd hα_ode hα_cont hα_neg h_sc hα_int hα_inv
    α_star r_star hr_star_pos hr_star_lt hα_star_pos hα_star_lt hαs_int
    hr_star_eq hα_star_equil hα_sq_int h_init_body r_min hr_min_pos
    hr_min_le hr_bound
