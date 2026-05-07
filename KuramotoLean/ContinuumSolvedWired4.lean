/-
  ContinuumSolvedWired4.lean
  ==========================
  Eliminates `hr_star_pos` from `kuramoto_continuum_wired3`
  by deriving r_star > 0 internally from hα_star_pos + hαs_int + hr_star_eq.

  ELIMINATED (now proved internally):
    • hr_star_pos — r_star > 0 follows from:
        α_star > 0 everywhere (hα_star_pos) + IsProbabilityMeasure + hr_star_eq.
      Proof: if ∫ α_star = 0 then α_star = 0 a.e. (integral_eq_zero_iff_of_nonneg),
             ae μ ≠ ⊥ gives ∃ ω with α_star ω = 0, contradicting hα_star_pos.

  REMAINING OPEN (2 genuine analytic inputs):
    • hμ_body_pos — each body {γ ≤ M} has positive measure for M > 0
    • h_combined_vanish — C(M) + μ(tail) → 0 (depends on g's tail decay)

  C(M) is explicit:
    K · μ(tail M) / (K · min(δ₀_body M, bodyEquilibrium M K r_min) · ds(M) · μ(body M))
  where ds(M) = K · r* / (2M + K · r*).

  0 sorry. 0 axioms.
-/

import KuramotoLean.ContinuumSolvedWired3

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fully wired continuum theorem** — eliminates hr_star_pos.

  Compared to `kuramoto_continuum_wired3`, this removes the `hr_star_pos`
  hypothesis and derives r_star > 0 internally from:
  - `hα_star_pos : ∀ ω, 0 < α_star ω`
  - `hr_star_eq : r_star = ∫ ω, α_star ω ∂μ`
  - `[IsProbabilityMeasure μ]` (so ae μ ≠ ⊥)

  Remaining open hypotheses: hμ_body_pos and h_combined_vanish. -/
theorem kuramoto_continuum_wired4 [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
    (hγ_level : ∀ M : ℝ, MeasurableSet {ω | γ ω ≤ M})
    (α_star : Ω → ℝ) (r_star : ℝ)
    (hα_star_pos : ∀ ω, 0 < α_star ω) (hα_star_lt : ∀ ω, α_star ω < 1)
    (hαs_int : Integrable α_star μ)
    (hr_star_eq : r_star = ∫ ω, α_star ω ∂μ)
    (hα_star_equil : ∀ ω, γ ω * α_star ω = (K / 2) * r_star * (1 - (α_star ω) ^ 2))
    (r : ℝ → ℝ) (α : Ω → ℝ → ℝ)
    (hr_cont : Continuous r) (hr_bdd : ∀ t, |r t| ≤ 1)
    (hr_nn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hα_ode : ∀ ω, ∀ t ≥ 0, HasDerivAt (α ω) (oaScalarRHS (γ ω) K r t (α ω t)) t)
    (hα_cont : ∀ ω, ContinuousOn (α ω) (Ici 0))
    (h_sc : ∀ t ≥ 0, r t = ∫ ω, α ω t ∂μ)
    (hα_int : ∀ t, Integrable (fun ω => α ω t) μ)
    (hα_sq_int : ∀ t, Integrable (fun ω => (α ω t - α_star ω) ^ 2) μ)
    (hα_inv : ∀ ω t, 0 ≤ t → 0 < α ω t ∧ α ω t < 1)
    (r_min : ℝ) (hr_min_pos : 0 < r_min)
    (hr_bound : ∀ t, 0 ≤ t → r_min ≤ r t)
    (δ₀_body : ℝ → ℝ)
    (hδ₀_body_pos : ∀ M, 0 < M → 0 < δ₀_body M)
    (hα_0_body : ∀ M, 0 < M → ∀ ω, γ ω ≤ M → δ₀_body M ≤ α ω 0)
    (hμ_body_pos : ∀ M, 0 < M → 0 < (μ {ω | γ ω ≤ M}).toReal)
    (h_combined_vanish : Tendsto
        (fun M => K * (μ {ω | M < γ ω}).toReal /
              (K * min (δ₀_body M) (bodyEquilibrium M K r_min) *
               (K * r_star / (2 * M + K * r_star)) *
               (μ {ω | γ ω ≤ M}).toReal) +
              (μ {ω | M < γ ω}).toReal)
        atTop (nhds 0)) :
    Tendsto r atTop (nhds r_star) := by
  have hr_star_pos : 0 < r_star := by
    rw [hr_star_eq]
    have h_nn : (0 : ℝ) ≤ ∫ ω, α_star ω ∂μ :=
      integral_nonneg (fun ω => (hα_star_pos ω).le)
    rcases h_nn.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨ω, hω⟩ := ((integral_eq_zero_iff_of_nonneg
        (fun ω => (hα_star_pos ω).le) hαs_int).mp h.symm).exists
      simp at hω; linarith [hα_star_pos ω]
  exact kuramoto_continuum_wired3 γ K hK hγ hγ_meas hγ_level α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hr_star_pos hα_star_equil
    r α hr_cont hr_bdd hr_nn hα_ode hα_cont h_sc hα_int hα_sq_int hα_inv
    r_min hr_min_pos hr_bound δ₀_body hδ₀_body_pos hα_0_body hμ_body_pos h_combined_vanish

end
