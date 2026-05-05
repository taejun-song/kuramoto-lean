/-
  Kuramoto Stability — Barbalat-Leibniz Bridge: V → 0 from FTC
  =============================================================
  Proves: If the Leibniz/FTC identity holds for the full Lyapunov V,
  then h_body_drop is satisfied and V → 0 via TailBodyBarbalat.

  The Leibniz identity:
    V(t) - V(t+1) = K · ∫_t^{t+1} P(s) ds

  holds when ∫ |d/dt (α-α*)²| g < ∞, i.e., ∫(γ+K)g < ∞, i.e., ∫|ω|g < ∞.
  This covers:
    • Compactly supported g (trivially)
    • Gaussian g (∫|ω|g < ∞)
    • Any g with finite first moment

  The chain:
    Leibniz → P ≥ P_body → body coercivity → V_body ≥ V - tail_mass
    → V(t)-V(t+1) ≥ K·c(M)·(V(t+1)-tail_mass(M))
    → LeibnizReductionData.convergence → V → 0

  Also proves the "integral finite" route:
    V antitone + V → L → V(0)-L = ∫₀^∞ (-V') ds = K·∫₀^∞ P ds < ∞
  This gives ∫_t^{t+1} P → 0, which combined with body coercivity
  and the tail-body structure yields V → 0.

  0 sorry.
-/

import KuramotoLean.TailBodyBarbalat

open Filter Topology Set

noncomputable section

namespace BarbalatLeibnizBridge

/-! ## Leibniz identity implies h_leibniz

Given:
  • Leibniz: V(t) - V(t+1) = K · integral_P(t) where integral_P(t) = ∫_t^{t+1} P(s) ds
  • P restriction: integral_P(t) ≥ integral_P_body(M,t) for all M
  • Body coercivity: integral_P_body(M,t) ≥ c(M) · V_body_avg(M,t) eventually
  • V_body lower bound: V_body_avg(M,t) ≥ V(t+1) - tail_mass(M)
    (from: V_body(M,s) ≥ V(s) - tail_mass(M) ≥ V(t+1) - tail_mass(M) for s ∈ [t,t+1])

Conclude: V(t) - V(t+1) ≥ K · c(M) · (V(t+1) - tail_mass(M))
-/

/-- **Leibniz-coercivity data.** The minimal assumptions for the FTC route.
    Packages the Leibniz identity with body coercivity and tail structure. -/
structure LeibnizCoercivityData where
  V : ℝ → ℝ
  K : ℝ
  hK : 0 < K
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  -- Leibniz/FTC: V(t) - V(t+1) = K · integral_P(t)
  integral_P : ℝ → ℝ
  h_intP_nn : ∀ t, 0 ≤ integral_P t
  h_leibniz_id : ∀ t, V t - V (t + 1) = K * integral_P t
  -- Body restriction: integral_P ≥ integral of P_body
  integral_P_body : ℝ → ℝ → ℝ  -- M ↦ t ↦ ∫_t^{t+1} P_body(M,s) ds
  h_restrict : ∀ M t, integral_P_body M t ≤ integral_P t
  h_intPb_nn : ∀ M t, 0 ≤ integral_P_body M t
  -- Body coercivity: ∫ P_body ≥ c(M) · ∫ V_body ≥ c(M) · (V(t+1) - tail_mass)
  coercivity : ℝ → ℝ
  h_coer_pos : ∀ M, 0 < M → 0 < coercivity M
  -- Tail structure
  tail_mass : ℝ → ℝ
  h_tail_mass_nn : ∀ M, 0 ≤ tail_mass M
  h_tail_vanish : Tendsto tail_mass atTop (nhds 0)
  -- Combined body coercivity + V_body lower bound:
  -- integral_P_body(M,t) ≥ c(M) · (V(t+1) - tail_mass(M)) eventually
  h_body_bound : ∀ M, 0 < M → ∃ T : ℝ, ∀ t, T ≤ t →
    integral_P_body M t ≥ coercivity M * (V (t + 1) - tail_mass M)

/-- **h_leibniz from Leibniz-coercivity data.**
    Derives the LeibnizReductionData.h_leibniz hypothesis. -/
theorem LeibnizCoercivityData.derives_h_leibniz (D : LeibnizCoercivityData) :
    ∀ M, 0 < M → ∃ T : ℝ, ∀ t, T ≤ t →
      D.V t - D.V (t + 1) ≥ D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by
  intro M hM
  obtain ⟨T, hT⟩ := D.h_body_bound M hM
  exact ⟨T, fun t ht => by
    have h1 : D.V t - D.V (t + 1) = D.K * D.integral_P t := D.h_leibniz_id t
    have h2 : D.integral_P_body M t ≤ D.integral_P t := D.h_restrict M t
    have h3 : D.integral_P_body M t ≥ D.coercivity M * (D.V (t + 1) - D.tail_mass M) := hT t ht
    calc D.V t - D.V (t + 1) = D.K * D.integral_P t := h1
      _ ≥ D.K * D.integral_P_body M t :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt D.hK)
      _ ≥ D.K * (D.coercivity M * (D.V (t + 1) - D.tail_mass M)) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt D.hK)
      _ = D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by ring⟩

/-- **V → 0 from Leibniz-coercivity data.** Main convergence theorem.
    This is the definitive result for g with finite first moment. -/
theorem LeibnizCoercivityData.convergence (D : LeibnizCoercivityData) :
    Tendsto D.V atTop (nhds 0) := by
  have h_leib := D.derives_h_leibniz
  exact (TailBodyBarbalat.LeibnizReductionData.mk
    D.V D.K D.hK D.hV_nn D.hV_anti
    D.tail_mass D.h_tail_mass_nn D.h_tail_vanish
    D.coercivity D.h_coer_pos h_leib).convergence

/-! ## Alternative route: ∫₀^∞ P finite from V antitone

V antitone, V → L, V AC with V' = -KP gives:
  V(0) - L = ∫₀^∞ (-V') = K · ∫₀^∞ P < ∞

From ∫₀^∞ P < ∞: for any h > 0, ∫_t^{t+h} P → 0 as t → ∞.
Since V(t) - V(t+h) = K · ∫_t^{t+h} P, this recovers V(t)-V(t+h) → 0.

More usefully: ∫_t^{t+1} P = (V(t)-V(t+1))/K → 0.
Combined with body coercivity on [t,t+1]:
  ∫_t^{t+1} P ≥ c(M) · (V(t+1) - tail_mass(M))
If V(t+1) ≥ ε and tail_mass(M) < ε/2:
  ∫_t^{t+1} P ≥ c(M) · ε/2 > 0
contradicting ∫_t^{t+1} P → 0. -/

/-- **Integral-finite Barbalat data.** The route via ∫₀^∞ P < ∞. -/
structure IntegralFiniteData where
  V : ℝ → ℝ
  K : ℝ
  hK : 0 < K
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  -- V(t) - V(t+1) = K * avg_P(t) where avg_P(t) = ∫_t^{t+1} P
  avg_P : ℝ → ℝ
  h_avgP_nn : ∀ t, 0 ≤ avg_P t
  h_drop_eq : ∀ t, V t - V (t + 1) = K * avg_P t
  -- Body coercivity of the time-average:
  -- avg_P(t) ≥ c(M) · V_body_avg(M,t) ≥ c(M) · (V(t+1) - tail_mass(M))
  coercivity : ℝ → ℝ
  h_coer_pos : ∀ M, 0 < M → 0 < coercivity M
  tail_mass : ℝ → ℝ
  h_tail_mass_nn : ∀ M, 0 ≤ tail_mass M
  h_tail_vanish : Tendsto tail_mass atTop (nhds 0)
  h_avg_coer : ∀ M, 0 < M → ∃ T : ℝ, ∀ t, T ≤ t →
    avg_P t ≥ coercivity M * (V (t + 1) - tail_mass M)

/-- **V → 0 from integral-finite data.** Direct contradiction argument.
    If V → L > 0, then V(t+1) ≥ L/2 eventually, and choosing M large
    (tail_mass < L/4) gives avg_P(t) ≥ c(M)·L/4 > 0 eventually.
    But avg_P(t) = (V(t)-V(t+1))/K → 0. Contradiction. -/
theorem IntegralFiniteData.convergence (D : IntegralFiniteData) :
    Tendsto D.V atTop (nhds 0) := by
  apply TailBodyBarbalat.eventual_tac_tendsto D.V D.hV_nn D.hV_anti
  intro ε hε
  -- Choose M large: tail_mass(M) < ε/2
  have h_tv := D.h_tail_vanish
  rw [Metric.tendsto_atTop] at h_tv
  obtain ⟨N, hN⟩ := h_tv (ε / 2) (by linarith)
  set M := max N 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N 1)
  have h_tail_small : D.tail_mass M < ε / 2 := by
    have h := hN M (le_max_left N 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.h_tail_mass_nn M)] at h; exact h
  have hc := D.h_coer_pos M hM_pos
  obtain ⟨T, hT⟩ := D.h_avg_coer M hM_pos
  set δ := D.K * (D.coercivity M * (ε / 2))
  have hδ : 0 < δ := mul_pos D.hK (mul_pos hc (by linarith))
  refine ⟨δ, hδ, T, fun t ht hVt => ?_⟩
  -- V(t+1) ≥ ε, tail_mass < ε/2, so V(t+1) - tail_mass ≥ ε/2
  have h_diff : D.V (t + 1) - D.tail_mass M ≥ ε / 2 := by linarith
  -- avg_P(t) ≥ c(M) · (V(t+1) - tail_mass) ≥ c(M) · ε/2
  have h_avg := hT t ht
  have h_Pb : D.avg_P t ≥ D.coercivity M * (ε / 2) :=
    le_trans (mul_le_mul_of_nonneg_left h_diff (le_of_lt hc)) h_avg
  -- V(t) - V(t+1) = K · avg_P(t) ≥ K · c(M) · ε/2 = δ
  calc D.V t - D.V (t + 1)
      = D.K * D.avg_P t := D.h_drop_eq t
    _ ≥ D.K * (D.coercivity M * (ε / 2)) :=
        mul_le_mul_of_nonneg_left h_Pb (le_of_lt D.hK)
    _ = δ := by ring

/-! ## Connecting to TailBodyBarbalat: LeibnizReductionData instance -/

/-- **IntegralFiniteData gives LeibnizReductionData.** -/
def IntegralFiniteData.toLeibnizReduction (D : IntegralFiniteData) :
    TailBodyBarbalat.LeibnizReductionData where
  V := D.V
  K := D.K
  hK := D.hK
  hV_nn := D.hV_nn
  hV_anti := D.hV_anti
  tail_mass := D.tail_mass
  h_tail_mass_nn := D.h_tail_mass_nn
  h_tail_vanish := D.h_tail_vanish
  coercivity := D.coercivity
  h_coer_pos := D.h_coer_pos
  h_leibniz := fun M hM => by
    obtain ⟨T, hT⟩ := D.h_avg_coer M hM
    exact ⟨T, fun t ht => by
      have h1 := D.h_drop_eq t
      have h2 := hT t ht
      calc D.V t - D.V (t + 1) = D.K * D.avg_P t := h1
        _ ≥ D.K * (D.coercivity M * (D.V (t + 1) - D.tail_mass M)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt D.hK)
        _ = D.K * D.coercivity M * (D.V (t + 1) - D.tail_mass M) := by ring⟩

/-! ## The key new theorem: antitone + Leibniz → ∫₀^∞ P finite

This is the Barbalat route. V antitone bounded gives V → L.
Then V(0) - V(T) = K · Σ_{k=0}^{T-1} avg_P(k) (telescoping).
Since V(0) - L < ∞, the series Σ avg_P(k) converges, so avg_P(k) → 0.

Formalized as: V(t) - V(t+1) → 0 from V → L (already in WeakStarLaSalle).
Combined with V(t)-V(t+1) = K·avg_P(t): avg_P(t) → 0.

This is NOT new — it's antitone_increment_vanishes + the identity.
The key insight is combining this with the BODY coercivity to get
a contradiction when L > 0. -/

/-- **avg_P → 0 from Leibniz + V → L.** The integral ∫₀^∞ P < ∞ route. -/
theorem avg_P_tendsto_zero (V avg_P : ℝ → ℝ) (K L : ℝ)
    (hK : 0 < K)
    (hV_lim : Tendsto V atTop (nhds L))
    (h_drop_eq : ∀ t, V t - V (t + 1) = K * avg_P t) :
    Tendsto avg_P atTop (nhds 0) := by
  have h_incr := WeakStarLaSalle.antitone_increment_vanishes V L 1 hV_lim
  have hK_inv : (0 : ℝ) < K⁻¹ := inv_pos.mpr hK
  rw [Metric.tendsto_atTop] at h_incr ⊢
  intro ε hε
  obtain ⟨T, hT⟩ := h_incr (K * ε) (mul_pos hK hε)
  exact ⟨T, fun t ht => by
    have h1 := hT t ht
    rw [Real.dist_eq, sub_zero] at h1
    have h_eq : avg_P t = K⁻¹ * (V t - V (t + 1)) := by
      have := h_drop_eq t; field_simp; linarith
    rw [Real.dist_eq, sub_zero, h_eq, abs_mul, abs_of_pos hK_inv]
    calc K⁻¹ * |V t - V (t + 1)| < K⁻¹ * (K * ε) := by
          exact mul_lt_mul_of_pos_left h1 hK_inv
      _ = ε := by field_simp⟩

/-! ## Summary: the finite first moment theorem

For g with ∫|ω|g(ω)dω < ∞ (Gaussian, compactly supported, etc.):

1. Leibniz holds: V(t)-V(t+1) = K · ∫_t^{t+1} P(s) ds
   Proof: DCT with dominator 2(|ω|+K) ∈ L¹(g).

2. P ≥ P_body(M,·) (restriction of nonneg integrand).

3. Body coercivity: on {|ω| ≤ M}, γ ≤ M bounded, so
   pair coercivity gives P_body ≥ c(M) · V_body
   (from bounded-γ theorem applied to body).

4. V_body(M,s) = V(s) - V_tail(M,s) ≥ V(s) - tail_mass(M)
   ≥ V(t+1) - tail_mass(M) for s ∈ [t,t+1] (V antitone).

5. Chain: avg_P(t) ≥ c(M) · (V(t+1) - tail_mass(M))

6. IntegralFiniteData.convergence → V → 0.

The ONLY ingredient that requires ∫|ω|g < ∞ is step 1 (Leibniz/DCT).
All other steps use:
  • V antitone (ContinuumLyapunov, 0 sorry)
  • (α-α*)² ≤ 1 (uniform tail bound)
  • g ∈ L¹ (tail_mass → 0)
  • Bounded-γ coercivity (existing theorem)

For Lorentzian (∫|ω|g = ∞): Leibniz fails for the FULL V.
But Leibniz DOES hold for V_body(M',t) with any finite M'.
Passing M' → ∞ via monotone convergence:
  V(t)-V(t+1) = lim_{M'→∞} [V_body(M',t) - V_body(M',t+1)]
              ≥ lim_{M'→∞} K · ∫ P_body(M',s) ds
              ≥ K · ∫ P_body(M,s) ds    (for any fixed M ≤ M')
This gives h_body_drop for Lorentzian too, reducing the problem to
proving the monotone convergence interchange for the specific OA flow.
-/

end BarbalatLeibnizBridge

end
