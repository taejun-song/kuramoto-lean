/-
  OAScalarMeasurableFlow.lean
  ============================
  Canonical measurable Lorentzian OA scalar flow.

  Given fixed Lorentzian parameters (K, γ₀, r₀) and initial condition α₀,
  define the canonical ODE solution lorentzian_oa_flow γ hγ as Classical.choose
  from lorentzian_scalar_ode_global. Key results:

  1. lorentzian_oa_flow_lipschitz_in_gamma: dist at time t ≤ gronwallBound 0 (γ₂+K) |γ₁-γ₂| t
  2. lorentzian_oa_flow_continuousAt_subtype: F : {γ // 0 < γ} → ℝ is continuous
  3. lorentzian_oa_flow_aemeasurable: ω ↦ lorentzian_oa_flow (γ ω) (hγ ω) t is AEMeasurable

  0 sorry.
-/

import KuramotoLean.LorentzianScalarODE
import KuramotoLean.OAScalarGammaLip

open MeasureTheory Real Set Filter Topology Metric

noncomputable section

variable {K γ₀ r₀ α₀ : ℝ}
  {hK : 0 < K} {hγ₀ : 0 < γ₀} {hKγ₀ : 2 * γ₀ < K}
  {hr₀_pos : 0 < r₀} {hr₀_lt : r₀ < 1}
  {hα₀_pos : 0 < α₀} {hα₀_lt : α₀ < 1}

/-- Canonical OA scalar solution for Lorentzian forcing and fixed initial condition α₀,
    defined by Classical.choose from lorentzian_scalar_ode_global. -/
noncomputable def lorentzian_oa_flow
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    (γ : ℝ) (hγ : 0 < γ) : ℝ → ℝ :=
  Classical.choose
    (lorentzian_scalar_ode_global γ K γ₀ r₀ α₀ hγ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt)

def lorentzian_oa_flow_spec_raw
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    (γ : ℝ) (hγ : 0 < γ) :
    let α := lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ hγ
    α 0 = α₀ ∧
    ContinuousOn α (Ici 0) ∧
    (∀ t, 0 ≤ t →
      HasDerivAt α (oaScalarRHS γ K (lorentzian_explicit K γ₀ r₀) t (α t)) t) ∧
    (∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) :=
  Classical.choose_spec
    (lorentzian_scalar_ode_global γ K γ₀ r₀ α₀ hγ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt)

/-- **Lipschitz bound in γ**: two canonical flows with the same IC and
    parameters γ₁, γ₂ satisfy a Gronwall distance bound at each t ∈ [0,T]. -/
theorem lorentzian_oa_flow_lipschitz_in_gamma
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    (γ₁ γ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (T : ℝ) (_hT : 0 < T)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    dist
      (lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₁ hγ₁ t)
      (lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₂ hγ₂ t) ≤
    gronwallBound 0 (γ₂ + K) |γ₁ - γ₂| t := by
  set α₁ := lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₁ hγ₁
  set α₂ := lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₂ hγ₂
  set r := lorentzian_explicit K γ₀ r₀
  obtain ⟨hinit₁, hcont₁, hode₁, hbdd₁⟩ :=
    lorentzian_oa_flow_spec_raw K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₁ hγ₁
  obtain ⟨hinit₂, hcont₂, hode₂, hbdd₂⟩ :=
    lorentzian_oa_flow_spec_raw K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₂ hγ₂
  exact oa_scalar_gamma_gronwall γ₁ γ₂ K r T (le_of_lt hγ₂) (le_of_lt hK)
    (fun s (hs : s ∈ Icc 0 T) => abs_le.mpr
      ⟨by linarith [lorentzian_explicit_pos K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt s hs.1],
       le_of_lt (lorentzian_explicit_lt_one K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt s hs.1)⟩)
    α₀ α₁ α₂ hinit₁ hinit₂
    (fun s (hs : s ∈ Ico 0 T) => (hode₁ s hs.1).hasDerivWithinAt)
    (fun s (hs : s ∈ Ico 0 T) => (hode₂ s hs.1).hasDerivWithinAt)
    (hcont₁.mono Icc_subset_Ici_self)
    (hcont₂.mono Icc_subset_Ici_self)
    (fun s (hs : s ∈ Ico 0 T) => ⟨le_of_lt (hbdd₁ s hs.1).1, le_of_lt (hbdd₁ s hs.1).2⟩)
    (fun s (hs : s ∈ Ico 0 T) => ⟨le_of_lt (hbdd₂ s hs.1).1, le_of_lt (hbdd₂ s hs.1).2⟩)
    t ht

/-- The map γ ↦ lorentzian_oa_flow γ hγ t is continuous on {γ > 0},
    viewed as a map on the subtype {γ : ℝ // 0 < γ}. -/
theorem lorentzian_oa_flow_continuous_subtype
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun (p : {γ : ℝ // 0 < γ}) =>
      lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt p.val p.prop t) := by
  rw [Metric.continuous_iff]
  intro ⟨γ₀', hγ₀'⟩ ε hε
  set C := gronwallBound 0 (γ₀' + K) 1 t
  have hC_nn : 0 ≤ C := by
    have h := (gronwallBound_mono le_rfl zero_le_one (by linarith : 0 ≤ γ₀' + K)) ht
    rwa [gronwallBound_x0] at h
  refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
  intro ⟨γ₁, hγ₁⟩ hdist
  simp only [Subtype.dist_eq] at hdist
  have ht' : t ∈ Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have hGronwall := lorentzian_oa_flow_lipschitz_in_gamma K γ₀ r₀ α₀ hK hγ₀ hKγ₀
    hr₀_pos hr₀_lt hα₀_pos hα₀_lt γ₁ γ₀' hγ₁ hγ₀' (t + 1) (by linarith) t ht'
  have hlinear : gronwallBound 0 (γ₀' + K) |γ₁ - γ₀'| t ≤ C * (ε / (C + 1)) := by
    have hKne : γ₀' + K ≠ 0 := by linarith
    have hC_linear : gronwallBound 0 (γ₀' + K) |γ₁ - γ₀'| t = C * |γ₁ - γ₀'| := by
      simp only [gronwallBound_of_K_ne_0 hKne, C]; ring
    rw [hC_linear]
    apply mul_le_mul_of_nonneg_left _ hC_nn
    rw [← Real.dist_eq]; exact le_of_lt hdist
  have hCε : C * (ε / (C + 1)) < ε := by
    have hC1 : 0 < C + 1 := by linarith
    have h : C * (ε / (C + 1)) = ε - ε / (C + 1) := by field_simp; ring
    linarith [div_pos hε hC1]
  exact lt_of_le_of_lt (hGronwall.trans hlinear) hCε

/-- **AE measurability of the canonical Lorentzian OA flow**.
    If γ : Ω → ℝ is measurable with γ ω > 0 everywhere, then
    ω ↦ lorentzian_oa_flow (γ ω) (hγ ω) t is AE strongly measurable. -/
theorem lorentzian_oa_flow_aestronglyMeasurable
    (K γ₀ r₀ α₀ : ℝ)
    (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (γ_fun : Ω → ℝ)
    (hγ_meas : Measurable γ_fun)
    (hγ_pos : ∀ ω, 0 < γ_fun ω)
    (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable
      (fun ω => lorentzian_oa_flow K γ₀ r₀ α₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt hα₀_pos hα₀_lt
        (γ_fun ω) (hγ_pos ω) t) μ := by
  have hcont := lorentzian_oa_flow_continuous_subtype K γ₀ r₀ α₀ hK hγ₀ hKγ₀
    hr₀_pos hr₀_lt hα₀_pos hα₀_lt t ht
  have hmeas_sub : Measurable (fun ω => (⟨γ_fun ω, hγ_pos ω⟩ : {γ : ℝ // 0 < γ})) :=
    hγ_meas.subtype_mk
  exact (hcont.measurable.comp hmeas_sub).aestronglyMeasurable

end
