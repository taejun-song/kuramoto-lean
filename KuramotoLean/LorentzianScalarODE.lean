/-
  LorentzianScalarODE.lean
  ========================
  Global existence for the per-ω OA scalar ODE with Lorentzian forcing:

      dα/dt = oaScalarRHS γ K (lorentzian_explicit K γ₀ r₀) t (α t)

  Strategy: extend r(t) = lorentzian_explicit K γ₀ r₀ (max 0 t) to all of ℝ,
  apply oa_solve_global_v2, then note r_ext = r for t ≥ 0.

  MAIN RESULT: lorentzian_scalar_ode_global
    For γ, K, γ₀ > 0 with K > 2γ₀, r₀ ∈ (0,1), α₀ ∈ (0,1):
    ∃ α global solution on [0,∞) with α ∈ (0,1) and HasDerivAt for t > 0.

  0 sorry.
-/

import KuramotoLean.OAGlobalExistence
import KuramotoLean.LorentzianExistence

open MeasureTheory Real Set Filter Topology

noncomputable section

/-- The Lorentzian r extended continuously to all of ℝ by clamping time to [0,∞). -/
private noncomputable def r_ext (K γ₀ r₀ : ℝ) (t : ℝ) : ℝ :=
  lorentzian_explicit K γ₀ r₀ (max 0 t)

private lemma r_ext_eq_of_nn {K γ₀ r₀ t : ℝ} (ht : 0 ≤ t) :
    r_ext K γ₀ r₀ t = lorentzian_explicit K γ₀ r₀ t := by
  unfold r_ext; rw [max_eq_right ht]

private lemma r_ext_continuous (K γ₀ r₀ : ℝ) (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    Continuous (r_ext K γ₀ r₀) :=
  (lorentzian_explicit_continuousOn K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt).comp_continuous
    (continuous_const.max continuous_id) (fun t => le_max_left 0 t)

private lemma r_ext_pos (K γ₀ r₀ : ℝ) (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) :
    0 < r_ext K γ₀ r₀ t :=
  lorentzian_explicit_pos K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt (max 0 t) (le_max_left 0 t)

private lemma r_ext_lt_one (K γ₀ r₀ : ℝ) (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) :
    r_ext K γ₀ r₀ t < 1 :=
  lorentzian_explicit_lt_one K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt (max 0 t) (le_max_left 0 t)

private lemma r_ext_bdd (K γ₀ r₀ : ℝ) (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) (t : ℝ) :
    |r_ext K γ₀ r₀ t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [r_ext_pos K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt t],
              le_of_lt (r_ext_lt_one K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt t)⟩

/-- **Per-ω OA scalar ODE global existence under Lorentzian forcing.**
    Given γ, K > 0 with K > 2γ₀, r₀ ∈ (0,1), and α₀ ∈ (0,1), there exists a
    global solution α : ℝ → ℝ on [0,∞) satisfying:
    - α(0) = α₀
    - ContinuousOn α (Ici 0)
    - HasDerivAt α (oaScalarRHS γ K (lorentzian_explicit K γ₀ r₀) t (α t)) t for t > 0
    - α(t) ∈ (0,1) for all t ≥ 0 -/
theorem lorentzian_scalar_ode_global
    (γ K γ₀ r₀ α₀ : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hγ₀ : 0 < γ₀) (hKγ₀ : 2 * γ₀ < K)
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1)
    (hα₀_pos : 0 < α₀) (hα₀_lt : α₀ < 1) :
    ∃ α : ℝ → ℝ,
      α 0 = α₀ ∧
      ContinuousOn α (Ici 0) ∧
      (∀ t, 0 < t → HasDerivAt α (oaScalarRHS γ K (lorentzian_explicit K γ₀ r₀) t (α t)) t) ∧
      (∀ t, 0 ≤ t → 0 < α t ∧ α t < 1) := by
  -- Apply global existence with r_ext (Lorentzian r clamped to [0,∞))
  obtain ⟨α, hα_init, hα_ode, hα_cont, hα_bdd⟩ :=
    oa_solve_global_v2 γ K (r_ext K γ₀ r₀) α₀ hγ hK
      (r_ext_continuous K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt)
      (r_ext_bdd K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt)
      (fun t ht => le_of_lt (r_ext_pos K γ₀ r₀ hK hγ₀ hKγ₀ hr₀_pos hr₀_lt t))
      hα₀_pos hα₀_lt
  -- For t ≥ 0: r_ext = lorentzian_explicit, so ODE agrees
  refine ⟨α, hα_init, hα_cont, ?_, hα_bdd⟩
  intro t ht
  have hrext : r_ext K γ₀ r₀ t = lorentzian_explicit K γ₀ r₀ t := r_ext_eq_of_nn (le_of_lt ht)
  have heq : oaScalarRHS γ K (r_ext K γ₀ r₀) t (α t) =
      oaScalarRHS γ K (lorentzian_explicit K γ₀ r₀) t (α t) := by
    simp only [oaScalarRHS, hrext]
  rw [← heq]; exact hα_ode t (le_of_lt ht)

end
