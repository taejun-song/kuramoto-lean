/-
  Kuramoto Stability — Summability LaSalle: V → 0 via ∫|V'| < ∞
  ================================================================
  Alternative proof of V → 0 from the MonotoneLeibniz hypotheses using
  the summability/L¹ route rather than EventualTAC.

  The argument (formalizing the LaSalle principle for antitone Lyapunov):
  1. V antitone + h_body_drop: V(n)-V(n+1) ≥ K·c(M)·V_body(M,n) for n ≥ T
  2. Telescoping: Σ (V(n)-V(n+1)) = V(T) - L ≤ V(0) < ∞
  3. Comparison: Σ V_body(M,n) ≤ V(0)/(K·c(M)) < ∞ (summable)
  4. Summable.tendsto_atTop_zero: V_body(M,n) → 0
  5. V(n) ≤ V_body(M,n) + tail_mass(M), so V(n) → tail_mass(M)
  6. ∀ε: choose M with tail_mass < ε/2, get V(n) < ε eventually
  7. V antitone + V → 0 at integers ⟹ V → 0 (continuous time)

  This is a MORE DIRECT proof than EventualTAC. It explicitly constructs
  the summable series (= finite total dissipation ∫₀^∞ |V'| < ∞) and
  uses the Cauchy criterion to extract convergence.

  0 sorry.
-/

import KuramotoLean.MonotoneLeibnizBridge
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Topology Set

noncomputable section

namespace SummabilityLaSalle

/-! ## Summability from antitone telescoping -/

/-- Nonneg terms bounded by telescoping antitone sequence are summable. -/
theorem summable_of_le_antitone_telescope (a : ℕ → ℝ) (V : ℕ → ℝ)
    (ha_nn : ∀ n, 0 ≤ a n) (hV_anti : Antitone V) (hV_nn : ∀ n, 0 ≤ V n)
    (h_le : ∀ n, a n ≤ V n - V (n + 1)) : Summable a := by
  apply summable_of_sum_range_le ha_nn
  intro N
  calc ∑ i ∈ Finset.range N, a i
      ≤ ∑ i ∈ Finset.range N, (V i - V (i + 1)) :=
        Finset.sum_le_sum (fun i _ => h_le i)
    _ = V 0 - V N := Finset.sum_range_sub' V N
    _ ≤ V 0 := by linarith [hV_nn N]

/-- V_body is summable from body drop bound. -/
theorem summable_body_from_drop (V V_body : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hV_anti : Antitone V) (hV_nn : ∀ n, 0 ≤ V n)
    (hVb_nn : ∀ n, 0 ≤ V_body n)
    (h_drop : ∀ n, c * V_body n ≤ V n - V (n + 1)) :
    Summable V_body := by
  have h_scaled : Summable (fun n => c * V_body n) :=
    summable_of_le_antitone_telescope _ V
      (fun n => mul_nonneg (le_of_lt hc) (hVb_nn n))
      hV_anti hV_nn h_drop
  exact (summable_mul_left_iff hc.ne').mp h_scaled

/-! ## Antitone convergence from integer subsequence -/

/-- Antitone nonneg function that vanishes at integers vanishes everywhere. -/
theorem antitone_tendsto_zero_of_nat (V : ℝ → ℝ)
    (hV_anti : Antitone V) (hV_nn : ∀ t, 0 ≤ V t)
    (h_nat : Tendsto (fun n : ℕ => V ↑n) atTop (nhds 0)) :
    Tendsto V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at h_nat
  obtain ⟨N, hN⟩ := h_nat ε hε
  refine ⟨↑N + 1, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hV_nn t)]
  have ht_nn : (0 : ℝ) ≤ t := le_trans (by exact_mod_cast Nat.zero_le N : (0:ℝ) ≤ ↑N) (by linarith)
  have h_floor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht_nn
  have h_floor : V t ≤ V ↑⌊t⌋₊ := hV_anti h_floor_le
  have hn : N ≤ ⌊t⌋₊ := by
    have : (↑N : ℝ) < t := by linarith
    exact Nat.le_floor (le_of_lt this)
  have h_Vn := hN ⌊t⌋₊ hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hV_nn ↑⌊t⌋₊)] at h_Vn
  linarith

/-! ## Main theorem: Summability LaSalle convergence -/

/-- **Summability LaSalle data.** Minimal hypotheses for the L¹ route. -/
structure Data where
  V : ℝ → ℝ
  V_body : ℝ → ℝ → ℝ  -- M ↦ t ↦ V_body(M,t)
  K : ℝ
  hK : 0 < K
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hVb_nn : ∀ M t, 0 ≤ V_body M t
  hVb_le : ∀ M t, V_body M t ≤ V t
  -- Tail mass vanishes
  tail_mass : ℝ → ℝ
  h_tail_mass_nn : ∀ M, 0 ≤ tail_mass M
  h_tail_vanish : Tendsto tail_mass atTop (nhds 0)
  h_tail_bound : ∀ M t, V t - V_body M t ≤ tail_mass M
  -- Body coercivity constant
  coercivity : ℝ → ℝ
  h_coer_pos : ∀ M, 0 < M → 0 < coercivity M
  -- Body drop: V(t)-V(t+1) ≥ K·c(M)·V_body(M,t) eventually
  h_body_drop : ∀ M, 0 < M → ∃ T : ℝ, ∀ t, T ≤ t →
    V t - V (t + 1) ≥ K * coercivity M * V_body M t

/-- **V_body(M,·) summable at integers (shifted past threshold).** -/
theorem Data.body_summable_nat (D : Data) (M : ℝ) (hM : 0 < M)
    (T : ℕ) (hT : ∀ n : ℕ, T ≤ n → D.V ↑n - D.V (↑n + 1) ≥
      D.K * D.coercivity M * D.V_body M ↑n) :
    Summable (fun n : ℕ => D.V_body M ↑(n + T)) := by
  set c := D.K * D.coercivity M
  have hc : 0 < c := mul_pos D.hK (D.h_coer_pos M hM)
  apply summable_body_from_drop
    (fun n => D.V ↑(n + T)) (fun n => D.V_body M ↑(n + T)) c hc
  · intro n m hnm
    have : (↑(n + T) : ℝ) ≤ ↑(m + T) := by
      exact_mod_cast Nat.add_le_add_right hnm T
    exact D.hV_anti this
  · intro n; exact D.hV_nn _
  · intro n; exact D.hVb_nn M _
  · intro n
    have hn : T ≤ n + T := Nat.le_add_left T n
    have h := hT (n + T) hn
    have h_cast : (↑(n + 1 + T) : ℝ) = ↑(n + T) + 1 := by push_cast; ring
    rw [h_cast]
    linarith

/-- **V_body(M,n) → 0 at integers.** From summability. -/
theorem Data.body_tendsto_zero_nat (D : Data) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun n : ℕ => D.V_body M ↑n) atTop (nhds 0) := by
  obtain ⟨T_real, hT⟩ := D.h_body_drop M hM
  set T := ⌈T_real⌉₊
  have hT_nat : ∀ n : ℕ, T ≤ n → D.V ↑n - D.V (↑n + 1) ≥
      D.K * D.coercivity M * D.V_body M ↑n := by
    intro n hn
    apply hT
    exact le_trans (Nat.le_ceil T_real) (by exact_mod_cast hn)
  have h_sum := D.body_summable_nat M hM T hT_nat
  have h_tend := h_sum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at h_tend ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h_tend ε hε
  refine ⟨N + T, fun n hn => ?_⟩
  by_cases h_nT : T ≤ n
  · have h_idx : N ≤ n - T := by omega
    have h_spec := hN (n - T) h_idx
    have h_eq : n - T + T = n := Nat.sub_add_cancel h_nT
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.hVb_nn M _)]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.hVb_nn M _)] at h_spec
    rw [show (↑(n - T + T) : ℝ) = (↑n : ℝ) from by exact_mod_cast h_eq] at h_spec
    exact h_spec
  · omega

/-- **V(n) → 0 at integers.** From body convergence + tail vanishing. -/
theorem Data.V_tendsto_zero_nat (D : Data) :
    Tendsto (fun n : ℕ => D.V ↑n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_tv := D.h_tail_vanish
  rw [Metric.tendsto_atTop] at h_tv
  obtain ⟨N_tail, hN_tail⟩ := h_tv (ε / 2) (by linarith)
  set M := max N_tail 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right N_tail 1)
  have h_tail_small : D.tail_mass M < ε / 2 := by
    have h := hN_tail M (le_max_left N_tail 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.h_tail_mass_nn M)] at h; exact h
  have h_body := D.body_tendsto_zero_nat M hM_pos
  rw [Metric.tendsto_atTop] at h_body
  obtain ⟨N_body, hN_body⟩ := h_body (ε / 2) (by linarith)
  refine ⟨N_body, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.hV_nn ↑n)]
  have h_split : D.V ↑n ≤ D.V_body M ↑n + D.tail_mass M := by
    linarith [D.h_tail_bound M ↑n]
  have h_Vb := hN_body n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (D.hVb_nn M ↑n)] at h_Vb
  linarith

/-- **V → 0 (continuous time).** The main convergence theorem via summability. -/
theorem Data.convergence (D : Data) : Tendsto D.V atTop (nhds 0) :=
  antitone_tendsto_zero_of_nat D.V D.hV_anti D.hV_nn D.V_tendsto_zero_nat

/-! ## Connection: MonotoneLeibniz.Data gives SummabilityLaSalle.Data -/

/-- **MonotoneLeibniz.Data gives SummabilityLaSalle.Data.** -/
def fromMonotoneLeibniz (D : MonotoneLeibniz.Data) : Data where
  V := D.V
  V_body := D.V_body
  K := D.K
  hK := D.hK
  hV_nn := D.hV_nn
  hV_anti := D.hV_anti
  hVb_nn := D.hVb_nn
  hVb_le := D.hVb_le
  tail_mass := D.tail_mass
  h_tail_mass_nn := D.h_tail_mass_nn
  h_tail_vanish := D.h_tail_vanish
  h_tail_bound := D.h_tail_bound
  coercivity := D.coercivity
  h_coer_pos := D.h_coer_pos
  h_body_drop := D.full_body_drop

/-- **Alternative convergence proof for MonotoneLeibniz via summability.** -/
theorem monotone_leibniz_convergence_summability (D : MonotoneLeibniz.Data) :
    Tendsto D.V atTop (nhds 0) :=
  (fromMonotoneLeibniz D).convergence

end SummabilityLaSalle

end
