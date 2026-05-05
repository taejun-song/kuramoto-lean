/-
  Kuramoto Stability — Continuum Body Leibniz: ODE → V → 0
  =========================================================
  Proves V → 0 from ODE-level differentiability of V_body:

    V_body(M, t) - V_body(M, t+1) = K · ∫_t^{t+1} P_body(M, s) ds

  Chain:
  1. FTC on V_body (from HasDerivAt + IntervalIntegrable)
  2. Body coercivity: P_body(M,s) ≥ c(M)·V_body(M,s) eventually
  3. V_body antitone → ∫_t^{t+1} c·V_body(s) ds ≥ c·V_body(t+1)
  4. V_body(M,t+1) ≥ V(t+1) - tail_mass(M) (uniform tail bound)
  5. Monotone limit M' → ∞: V(t)-V(t+1) ≥ K·c(M)·(V(t+1)-tail_mass(M))
  6. EventualTAC → V → 0

  The Leibniz hypothesis h_Vb_hasDerivAt is provable from the ODE via
  hasDerivAt_integral_of_dominated_loc_of_deriv_le with bound 2(M+K).

  0 sorry.
-/

import KuramotoLean.BodyLeibnizInstantiation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Topology Set MeasureTheory

noncomputable section

namespace ContinuumBodyLeibniz

/-- **Body ODE Differentiability Data.**
    On bounded body {|ω| ≤ M}, the ODE gives V_body differentiable
    with V_body' = -K·P_body (from Leibniz + pair expansion). -/
structure BodyODEData where
  V : ℝ → ℝ
  V_body : ℝ → ℝ → ℝ
  P_body : ℝ → ℝ → ℝ
  K : ℝ
  hK : 0 < K
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hVb_nn : ∀ M t, 0 ≤ V_body M t
  hVb_le : ∀ M t, V_body M t ≤ V t
  hVb_mono : ∀ t, Monotone (fun M => V_body M t)
  hVb_lim : ∀ t, Tendsto (fun M => V_body M t) atTop (nhds (V t))
  hPb_nn : ∀ M t, 0 ≤ P_body M t
  hPb_mono : ∀ t, Monotone (fun M => P_body M t)
  tail_mass : ℝ → ℝ
  h_tail_mass_nn : ∀ M, 0 ≤ tail_mass M
  h_tail_vanish : Tendsto tail_mass atTop (nhds 0)
  h_tail_bound : ∀ M t, V t - V_body M t ≤ tail_mass M
  coercivity : ℝ → ℝ
  h_coer_pos : ∀ M, 0 < M → 0 < coercivity M
  h_body_coer : ∀ M, 0 < M → ∃ T₀ : ℝ, ∀ t, T₀ ≤ t →
    P_body M t ≥ coercivity M * V_body M t
  -- V_body(M,·) differentiable with derivative = -K·P_body(M,·)
  -- (Leibniz integral rule: |d/dt(α-α*)²| ≤ 2(M+K) on {|ω|≤M})
  h_Vb_hasDerivAt : ∀ M t, HasDerivAt (V_body M) (-(K * P_body M t)) t
  -- P_body(M,·) integrable on compact intervals
  h_Pb_intble : ∀ M a b, IntervalIntegrable (P_body M) volume a b
  -- V_body(M,·) integrable on compact intervals
  h_Vb_intble : ∀ M a b, IntervalIntegrable (V_body M) volume a b

/-! ## FTC: Body Leibniz identity -/

theorem BodyODEData.body_leibniz_id (D : BodyODEData) (M t : ℝ) :
    D.V_body M t - D.V_body M (t + 1) =
      D.K * ∫ s in t..(t + 1), D.P_body M s := by
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := D.V_body M) (f' := fun s => -(D.K * D.P_body M s))
    (a := t) (b := t + 1)
    (fun s _ => D.h_Vb_hasDerivAt M s)
    (IntervalIntegrable.neg (IntervalIntegrable.const_mul (D.h_Pb_intble M t (t + 1)) D.K))
  -- h_ftc : ∫ -(K·P) = V(t+1) - V(t), need V(t) - V(t+1) = K·∫P
  have h1 : ∫ s in t..(t + 1), (fun s => -(D.K * D.P_body M s)) s =
      -(∫ s in t..(t + 1), D.K * D.P_body M s) :=
    intervalIntegral.integral_neg
  have h2 : ∫ s in t..(t + 1), D.K * D.P_body M s =
      D.K * ∫ s in t..(t + 1), D.P_body M s :=
    intervalIntegral.integral_const_mul D.K (D.P_body M)
  linarith [h1, h2]

/-! ## V_body is antitone -/

theorem BodyODEData.Vb_antitone (D : BodyODEData) (M : ℝ) :
    Antitone (D.V_body M) := by
  intro a b hab
  have h_sub : ∫ u in a..b, (-(D.K * D.P_body M u)) = D.V_body M b - D.V_body M a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => D.h_Vb_hasDerivAt M x)
      (IntervalIntegrable.neg (IntervalIntegrable.const_mul (D.h_Pb_intble M a b) D.K))
  have h_neg : ∫ u in a..b, (-(D.K * D.P_body M u)) ≤ 0 := by
    rw [intervalIntegral.integral_neg]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hab
      (fun u _ => mul_nonneg (le_of_lt D.hK) (D.hPb_nn M u)))
  linarith

/-! ## Time-averaged coercivity -/

theorem BodyODEData.avg_coer (D : BodyODEData) (M : ℝ) (hM : 0 < M) :
    ∃ T₁ : ℝ, ∀ t, T₁ ≤ t →
      ∫ s in t..(t + 1), D.P_body M s ≥ D.coercivity M * D.V_body M (t + 1) := by
  obtain ⟨T₀, hT₀⟩ := D.h_body_coer M hM
  refine ⟨T₀, fun t ht => ?_⟩
  have h_le : t ≤ t + 1 := by linarith
  have hc_nn : (0 : ℝ) ≤ D.coercivity M := le_of_lt (D.h_coer_pos M hM)
  have h_bound : ∀ s, s ∈ Icc t (t + 1) →
      D.coercivity M * D.V_body M (t + 1) ≤ D.P_body M s := by
    intro s hs
    calc D.coercivity M * D.V_body M (t + 1)
        ≤ D.coercivity M * D.V_body M s :=
          mul_le_mul_of_nonneg_left (D.Vb_antitone M hs.2) hc_nn
      _ ≤ D.P_body M s := hT₀ s (by linarith [hs.1])
  calc ∫ s in t..(t + 1), D.P_body M s
      ≥ ∫ _s in t..(t + 1), D.coercivity M * D.V_body M (t + 1) :=
        intervalIntegral.integral_mono_on h_le
          intervalIntegrable_const (D.h_Pb_intble M t (t + 1)) h_bound
    _ = D.coercivity M * D.V_body M (t + 1) := by
        simp [intervalIntegral.integral_const, smul_eq_mul, show t + 1 - t = 1 from by ring]

/-! ## Main convergence -/

theorem BodyODEData.body_drop_bound (D : BodyODEData) (M : ℝ) (hM : 0 < M) :
    ∃ T : ℝ, ∀ M', M ≤ M' → ∀ t, T ≤ t →
      D.V_body M' t - D.V_body M' (t + 1) ≥
        D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by
  obtain ⟨T₁, hT₁⟩ := D.avg_coer M hM
  refine ⟨T₁, fun M' hM' t ht => ?_⟩
  have h_leibniz := D.body_leibniz_id M' t
  have h_le : t ≤ t + 1 := by linarith
  have h_Pb_mono_int : ∫ s in t..(t + 1), D.P_body M s ≤
      ∫ s in t..(t + 1), D.P_body M' s := by
    apply intervalIntegral.integral_mono_on h_le
      (D.h_Pb_intble M t (t + 1)) (D.h_Pb_intble M' t (t + 1))
    intro s _
    exact D.hPb_mono s hM'
  have h_avg := hT₁ t ht
  have h_Vb_bound : D.V_body M (t + 1) ≥ D.V (t + 1) - D.tail_mass M := by
    linarith [D.h_tail_bound M (t + 1)]
  calc D.V_body M' t - D.V_body M' (t + 1)
      = D.K * ∫ s in t..(t + 1), D.P_body M' s := h_leibniz
    _ ≥ D.K * ∫ s in t..(t + 1), D.P_body M s :=
        mul_le_mul_of_nonneg_left h_Pb_mono_int (le_of_lt D.hK)
    _ ≥ D.K * (D.coercivity M * D.V_body M (t + 1)) :=
        mul_le_mul_of_nonneg_left h_avg (le_of_lt D.hK)
    _ ≥ D.K * (D.coercivity M * (D.V (t + 1) - D.tail_mass M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_Vb_bound (le_of_lt (D.h_coer_pos M hM)))
          (le_of_lt D.hK)
    _ = D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by ring

theorem BodyODEData.full_drop_bound (D : BodyODEData) (M : ℝ) (hM : 0 < M) :
    ∃ T : ℝ, ∀ t, T ≤ t →
      D.V t - D.V (t + 1) ≥
        D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by
  obtain ⟨T, hT⟩ := D.body_drop_bound M hM
  refine ⟨T, fun t ht => ?_⟩
  set c := D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M)
  have h_all : ∀ M', M ≤ M' →
      D.V_body M' t - D.V_body M' (t + 1) ≥ c :=
    fun M' hM' => hT M' hM' t ht
  have h_lim : Tendsto (fun M' => D.V_body M' t - D.V_body M' (t + 1))
      atTop (nhds (D.V t - D.V (t + 1))) :=
    (D.hVb_lim t).sub (D.hVb_lim (t + 1))
  exact ge_of_tendsto h_lim (Eventually.mono (Ici_mem_atTop M) h_all)

/-- **V → 0 from Body ODE Data.** The main convergence theorem.
    No finite first moment needed. Works for Lorentzian. -/
theorem BodyODEData.convergence (D : BodyODEData) :
    Tendsto D.V atTop (nhds 0) := by
  apply TailBodyBarbalat.eventual_tac_tendsto D.V D.hV_nn D.hV_anti
  intro ε hε
  have h_tv := D.h_tail_vanish
  rw [Metric.tendsto_atTop] at h_tv
  obtain ⟨N, hN⟩ := h_tv (ε / 2) (by linarith)
  set M := max N 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_tail_small : D.tail_mass M < ε / 2 := by
    have h := hN M (le_max_left N 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.h_tail_mass_nn M)] at h; exact h
  obtain ⟨T, hT⟩ := D.full_drop_bound M hM_pos
  set δ := D.K * D.coercivity M * (ε / 2)
  have hKc : 0 < D.K * D.coercivity M := mul_pos D.hK (D.h_coer_pos M hM_pos)
  refine ⟨δ, mul_pos hKc (by linarith), T, fun t ht hVt => ?_⟩
  have h_diff : D.V (t + 1) - D.tail_mass M ≥ ε / 2 := by linarith
  calc D.V t - D.V (t + 1)
      ≥ D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := hT t ht
    _ ≥ D.K * D.coercivity M * (ε / 2) :=
        mul_le_mul_of_nonneg_left h_diff (le_of_lt hKc)
    _ = δ := by ring

/-! ## What remains to instantiate BodyODEData for the Kuramoto OA flow

PROVED (existing files, 0 sorry):
  • hV_nn, hV_anti: ContinuumLyapunov (pair bound → antitone)
  • hVb_nn, hVb_le, hVb_mono, hVb_lim: monotone convergence of ∫_{|ω|≤M}(α-α*)²g
  • hPb_nn, hPb_mono: pair integrand ≥ 0, monotone in integration domain
  • h_tail_bound, h_tail_vanish: (α-α*)² ≤ 1 and g ∈ L¹ → tail mass vanishes
  • h_body_coer: pair coercivity on body (PairCoercivity.lean)
  • h_Vb_intble, h_Pb_intble: bounded functions on compact intervals

TO PROVE (the single gap):
  • h_Vb_hasDerivAt: HasDerivAt (V_body M) (-(K * P_body M t)) t

  This follows from Mathlib's hasDerivAt_integral_of_dominated_loc_of_deriv_le:
  - F(t,ω) = (α(ω,t) - α*(ω))² for ω in body
  - F'(t,ω) = 2(α(ω,t) - α*(ω)) · α'(ω,t)
  - |F'(t,ω)| ≤ 2 · 1 · (M + K) = 2(M+K) [constant dominator]
  - bound = 2(M+K) ∈ L¹(μ|_body) since μ(body) < ∞
  - α(ω,·) differentiable at each t (ODE solution, ContinuumODEExistence)
  - Then: HasDerivAt (∫_body F(·,ω) dμ) (∫_body F'(t,ω) dμ) t
  - Pair expansion: ∫ F'(t,ω) dμ = -K · P_body(M,t) [ContinuumLyapunov algebra]

  The pair expansion step connects the raw derivative ∫2(α-α*)α' g to -K·P_body.
  This uses the ODE: α' = -γα + (K/2)r(1-α²), which after substitution and the
  symmetrized pair double-integral gives the identity dV_body/dt = -K·P_body. -/

end ContinuumBodyLeibniz

end
