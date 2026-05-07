/-
  BodyGronwallWired.lean
  ======================
  Wires body_gronwall_from_persistence with:
    - equil_lower_body (derives ds = K·r*/(2M+Kr*) on body {γ≤M})
    - V_body_continuousOn_prob (proves ContinuousOn of V_body)

  The resulting theorem `body_gronwall_wired` has a cleaner interface:
    inputs: δ (body persistence), hμ_body_pos, hr_star_pos
    output: let ds := K·r*/(2M+K·r*); let rate := K·δ·ds·μ(body);
            0 < rate ∧ V_body(t) ≤ V_body(0)·exp(-rate·t) + K·μ(tail)/rate

  The explicit `let`-based return avoids opaque Classical.choose witnesses,
  enabling callers to use the concrete rate formula directly.

  Used in `kuramoto_continuum_wired2` to eliminate `h_gronwall_from_persist`.

  0 sorry. 0 axioms.
-/

import KuramotoLean.BodyGronwallBound
import KuramotoLean.VBodyContinuous
import KuramotoLean.ContinuumSolvedComplete

open MeasureTheory Real Set Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Body Gronwall bound with ds derived from `equil_lower_body` and
    V_body continuity from `V_body_continuousOn_prob`. Returns explicit rate
    K · δ · ds(M) · μ(body M) where ds(M) = K · r* / (2M + K · r*). -/
theorem body_gronwall_wired [IsProbabilityMeasure μ]
    (γ : Ω → ℝ) (K : ℝ)
    (hK : 0 < K) (hγ_nn : ∀ ω, 0 ≤ γ ω)
    (hγ_meas : AEStronglyMeasurable γ μ)
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
    (M : ℝ) (hM : 0 < M)
    (hγ_level : MeasurableSet {ω | γ ω ≤ M})
    (δ : ℝ) (hδ : 0 < δ)
    (hα_lb : ∀ ω, γ ω ≤ M → ∀ t, 0 ≤ t → δ ≤ α ω t)
    (hμ_body_pos : 0 < (μ {ω | γ ω ≤ M}).toReal) :
    let ds := K * r_star / (2 * M + K * r_star)
    let rate := K * δ * ds * (μ {ω | γ ω ≤ M}).toReal
    0 < rate ∧ ∀ t ≥ (0 : ℝ),
      ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ ≤
        (∫ ω in {ω | γ ω ≤ M}, (α ω 0 - α_star ω) ^ 2 ∂μ) *
          rexp (-rate * t) + K * (μ {ω | M < γ ω}).toReal / rate := by
  intro ds rate
  have h_denom_pos : 0 < 2 * M + K * r_star := by positivity
  have hds_pos : 0 < ds := div_pos (mul_pos hK hr_star_pos) h_denom_pos
  have hds_lb : ∀ ω, γ ω ≤ M → ds ≤ α_star ω := fun ω hω =>
    equil_lower_body (γ ω) K r_star (α_star ω) M hK hr_star_pos
      (hα_star_pos ω) hω hM (hα_star_equil ω)
  have hV_body_cont : ContinuousOn
      (fun t => ∫ ω in {ω | γ ω ≤ M}, (α ω t - α_star ω) ^ 2 ∂μ) (Ici 0) :=
    V_body_continuousOn_prob γ M hγ_level α α_star hα_cont hα_inv
      hα_star_pos hα_star_lt hα_sq_int
  exact body_gronwall_from_persistence γ K hK hγ_nn hγ_meas α_star r_star
    hα_star_pos hα_star_lt hαs_int hr_star_eq hα_star_equil
    r α hr_bdd hα_ode hα_int hα_sq_int hα_inv h_sc
    M hM hγ_level δ hδ ds hds_pos hα_lb hds_lb hμ_body_pos hV_body_cont

end
