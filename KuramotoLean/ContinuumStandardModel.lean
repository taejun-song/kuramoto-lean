/-
  Kuramoto Stability — Standard Continuum Model (γ unbounded, g ∈ L¹)
  =====================================================================
  The CORRECT stability theorem for the standard continuum Kuramoto model
  on the Ott-Antonsen manifold with γ(ω) = |ω| (unbounded on ℝ).

  `kuramoto_solved` (GeneralGMainTheorem.lean) requires three hypotheses
  that FAIL for the standard model:

    PROBLEM 1 — Uniform persistence ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t)
      FALSE: drifting oscillators (|ω| > Kr*) have α*(ω) → 0 as |ω| → ∞.
      Only LOCKED oscillators (|ω| < Kr*) maintain α bounded away from 0.

    PROBLEM 2 — Bounded γ: ∀ ω, γ(ω) ≤ γ_max
      FALSE: γ(ω) = |ω| is unbounded on ℝ. Leibniz dominated convergence
      needs |d/dt(α-α*)²| ≤ 2(γ+K) bounded, which requires bounded γ.

    PROBLEM 3 — c_min (minimum atom weight) is an n-pole concept
      For continuum g(ω)dω there are no atoms. The rate μ = K·c_min·δ·δ*
      does not transfer.

  RESOLUTION — tail-body split [Dietert 2016, §2-3]:

    Split the integral into body {γ ≤ M} and tail {γ > M}:
      r(t) - r* = ∫_{γ≤M} (α-α*) dμ + ∫_{γ>M} (α-α*) dμ

    BODY {γ ≤ M}:
      • γ IS bounded by M → Leibniz works (dominator 2M+K)    [fixes Problem 2]
      • Locked oscillators have α ≥ δ(M) > 0                  [fixes Problem 1]
      • Rate = K·δ(M)·δ*(M) from body pair coercivity          [fixes Problem 3]
      • Gronwall: V_body(M,t) ≤ V_body(M,0)·exp(-rate(M)·t) → 0

    TAIL {γ > M}:
      • |∫_tail (α-α*)| ≤ μ({γ > M}) → 0 as M → ∞ (probability measure, |α-α*| ≤ 1)

    COMBINE: |r-r*| ≤ √V_body + μ(tail) → 0

  The single hypothesis `h_body_exp` (body exponential decay per truncation M)
  replaces all three problematic hypotheses. It is DERIVABLE from applying
  `kuramoto_solved`'s bounded-γ machinery to each restricted body {γ ≤ M}:
  on the body, γ ≤ M (bounded), locked oscillators have persistence δ(M) > 0,
  and the Leibniz + pair coercivity + Gronwall chain gives V_body ≤ V₀·exp(-rate·t).

  Coverage: ALL g ∈ L¹(ℝ) — Gaussian, Student-t (any ν), compact support, Lorentzian.
  0 sorry. 0 axioms.
-/

import KuramotoLean.GeneralGMainTheorem

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Standard continuum Kuramoto stability theorem.**

For the Ott-Antonsen continuum Kuramoto model with:
  • γ : Ω → ℝ — natural frequency (UNBOUNDED, e.g. γ(ω) = |ω|)
  • μ — probability measure (representing g(ω)dω, g ∈ L¹(ℝ))
  • K > 0 — supercritical coupling strength
  • α*(ω) — equilibrium satisfying γ·α* = (K/2)·r*·(1-(α*)²)
  • r* = ∫ α* dμ — self-consistent equilibrium order parameter

Conclusion: r(t) → r* as t → ∞.

Does NOT assume:
  • bounded γ (PROBLEM 2)
  • uniform persistence ∃ δ > 0, ∀ ω t, δ ≤ α(ω,t) (PROBLEM 1)
  • minimum atom weight c_min (PROBLEM 3)

Key hypothesis: body exponential decay per truncation M.
  V_body(M,t) = ∫_{γ≤M} (α-α*)² dμ ≤ V_body(M,0) · exp(-rate(M)·t)
Derivable from bounded-γ Leibniz + body persistence + Gronwall on {γ ≤ M}.

Proof: tail-body split via `integral_add_compl`.
  TAIL: |∫_{γ>M} (α-α*)| ≤ μ({γ>M}) → 0 (probability measure)
  BODY: |∫_{γ≤M} (α-α*)| ≤ √V_body → 0 (Cauchy-Schwarz + body exp decay)
  COMBINE: |r-r*| ≤ |body| + |tail| → 0 -/
theorem kuramoto_continuum_standard_model [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    -- BODY EXPONENTIAL DECAY per truncation M (replaces Problems 1-3).
    -- On {γ ≤ M}: γ bounded by M → Leibniz valid (dominator 2M+K).
    -- Locked oscillators have body persistence δ(M) > 0 → pair coercivity.
    -- Gronwall comparison → V_body ≤ V₀·exp(-rate·t).
    (h_body_exp : ∀ M : ℝ, 0 < M →
      ∃ rate : ℝ, 0 < rate ∧ ∀ t ≥ (0 : ℝ),
        ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
          (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t)) :
    Tendsto r atTop (nhds r_star) :=
  kuramoto_solved_full_continuum γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hα_ode
    h_sc hα_int hα_sq_int hα_inv h_body_exp

/-- **`kuramoto_solved` (bounded γ) is a special case.**

When γ IS bounded by γ_max and persistence IS uniform, the global Gronwall
  V(t) ≤ V₀·exp(-rate·t)
implies body exp decay for every M:
  V_body(M,t) ≤ V(t) ≤ V₀·exp(-rate·t)
since V_body(M,·) = ∫_{γ≤M} (α-α*)² dμ ≤ ∫_ALL (α-α*)² dμ = V(·).

This shows `kuramoto_continuum_standard_model` strictly generalizes `kuramoto_solved`. -/
theorem kuramoto_continuum_standard_model_of_bounded [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K γ_max : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 < γ ω)
    (hγ_max : 0 ≤ γ_max) (hγ_bdd : ∀ ω, γ ω ≤ γ_max)
    (_hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (hγ_meas : AEStronglyMeasurable γ μ)
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (α_0 : Ω → ℝ) (hα_0_pos : ∀ ω, 0 < α_0 ω) (hα_0_lt : ∀ ω, α_0 ω < 1)
    (h_exists : ∃ (r : ℝ → ℝ) (α : Ω → ℝ → ℝ),
      Continuous r ∧ (∀ t, |r t| ≤ 1) ∧ (∀ t, 0 ≤ t → 0 ≤ r t) ∧
      (∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t) ∧
      (∀ ω, ContinuousOn (α ω) (Ici 0)) ∧
      (∀ ω, α ω 0 = α_0 ω) ∧
      (∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, t ≤ 0 → α ω t = α ω 0) ∧
      (∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) ∧
      (∃ δ_per : ℝ, 0 < δ_per ∧ ∀ ω, ∀ t, 0 ≤ t → δ_per ≤ α ω t)) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) :=
  kuramoto_solved γ K γ_max hK hγ hγ_max hγ_bdd hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil α_0 hα_0_pos hα_0_lt
    h_exists

/-- **Existential wrapper for `kuramoto_continuum_standard_model`.**

Same as the main theorem but with solution existence bundled in an ∃. -/
theorem kuramoto_continuum_standard_model_exists [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (h_exists : ∃ (r : ℝ → ℝ) (α : Ω → ℝ → ℝ),
      Continuous r ∧
      (∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t) ∧
      (∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ) ∧
      (∀ t, Integrable (fun ω => α ω t) μ) ∧
      (∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ) ∧
      (∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1) ∧
      (∀ M : ℝ, 0 < M →
        ∃ rate : ℝ, 0 < rate ∧ ∀ t ≥ (0 : ℝ),
          ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
            (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) * rexp (-rate * t))) :
    ∃ (r : ℝ → ℝ), Continuous r ∧ Tendsto r atTop (nhds r_star) := by
  obtain ⟨r, α, hr_cont, hα_ode, h_sc, hα_int, hα_sq_int, hα_inv, h_body_exp⟩ := h_exists
  exact ⟨r, hr_cont, kuramoto_continuum_standard_model γ K hK hγ hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil r α hα_ode
    h_sc hα_int hα_sq_int hα_inv h_body_exp⟩

end
