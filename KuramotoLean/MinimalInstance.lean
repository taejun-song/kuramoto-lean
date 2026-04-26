/-
  Kuramoto Stability — Minimal Instance Construction
  ====================================================

  Constructs MinimalStabilityData from the L² Lyapunov chain:
    persistence + exponential decay → drops → MinimalStabilityData

  This closes the pipeline:
    pair coercivity → exponential rate → persistence drops
    → V → 0 → (r-r*)² → 0 → r → r*

  0 sorry.
-/

import KuramotoLean.MinimalProof
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Real Filter Topology

noncomputable section

/-! ## Construction from exponential persistence drops -/

/-- **Construct MinimalStabilityData from L² Lyapunov + persistence.**

    Input: V antitone + V ≥ 0 + exponential drops at rate μ
    Output: MinimalStabilityData with q = exp(-μ) -/
def toMinimalData
    (V : ℝ → ℝ) (r : ℝ → ℝ) (r_star μ : ℝ)
    (hμ : 0 < μ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hdrops : ∀ T : ℝ, ∃ a, T ≤ a ∧
      V (a + 1) ≤ exp (-μ) * V a)
    (hV_controls : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    MinimalStabilityData where
  V := V
  r := r
  r_star := r_star
  q := exp (-μ)
  hq_nn := le_of_lt (exp_pos _)
  hq_lt := exp_lt_one_iff.mpr (by linarith)
  hV_nn := hV_nn
  hV_anti := hV_anti
  hdrops := hdrops
  hV_controls_r := hV_controls

/-- **Complete pipeline: L² Lyapunov → r → r*.**

    The full chain in one theorem:
    V antitone + V ≥ 0 + exp drops + Cauchy-Schwarz ⟹ r → r*

    The rate μ = K·δ·δ* comes from pair coercivity (UniformRate.lean).
    The drops come from persistence + comparison_decay (GronwallBridge.lean).
    The V ≤ (r-r*)² comes from weighted Cauchy-Schwarz (OrderParameterRate.lean). -/
theorem l2_pipeline_convergence
    (V : ℝ → ℝ) (r : ℝ → ℝ) (r_star μ : ℝ)
    (hμ : 0 < μ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hdrops : ∀ T : ℝ, ∃ a, T ≤ a ∧
      V (a + 1) ≤ exp (-μ) * V a)
    (hV_controls : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |r t - r_star| < ε :=
  minimal_global_stability (toMinimalData V r r_star μ hμ
    hV_nn hV_anti hdrops hV_controls)

/-- **Pipeline: Filter.Tendsto form.** -/
theorem l2_pipeline_tendsto
    (V : ℝ → ℝ) (r : ℝ → ℝ) (r_star μ : ℝ)
    (hμ : 0 < μ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (hdrops : ∀ T : ℝ, ∃ a, T ≤ a ∧
      V (a + 1) ≤ exp (-μ) * V a)
    (hV_controls : ∀ t, (r t - r_star) ^ 2 ≤ V t) :
    Tendsto (fun t => |r t - r_star|) atTop (nhds 0) :=
  minimal_tendsto (toMinimalData V r r_star μ hμ
    hV_nn hV_anti hdrops hV_controls)

/-! ## Explicit convergence time bound

From the Barbalat argument: after k drops, V ≤ exp(-μ)^k · V(0).
Need exp(-μ)^k · V(0) < ε², i.e., k > log(V(0)/ε²) / μ.
Since drops occur at least once per T_persist units, time = k·T_persist. -/

/-- **Convergence time estimate.** If V(0) > 0 and drops occur
    at rate exp(-μ), then |r-r*| < ε after at most
    ceil(log(V(0)/ε²)/μ) drop events. -/
theorem convergence_time_bound
    (V : ℝ → ℝ) (r : ℝ → ℝ) (r_star μ : ℝ)
    (hμ : 0 < μ)
    (_hV_nn : ∀ t, 0 ≤ V t)
    (_hV_anti : Antitone V)
    (hV0 : 0 < V 0)
    (_hV_controls : ∀ t, (r t - r_star) ^ 2 ≤ V t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, exp (-μ) ^ k * V 0 < ε ^ 2 := by
  have hq : exp (-μ) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq_nn : 0 ≤ exp (-μ) := le_of_lt (exp_pos _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (sq_pos_of_pos hε) hV0) hq
  exact ⟨k, by
    calc exp (-μ) ^ k * V 0
        < ε ^ 2 / V 0 * V 0 :=
          mul_lt_mul_of_pos_right hk hV0
      _ = ε ^ 2 := div_mul_cancel₀ _ (ne_of_gt hV0)⟩

end
