/-
  Kuramoto Stability — Component Barrier via Grönwall Multiplier
  ===============================================================

  For the n-pole OA ODE: dα_k/dt = -γ_k α_k + (K/2)r(1-α_k²),
  define F_k(t) = α_k(t)·exp(γ_k t). Then:

    dF_k/dt = (K/2)·r(t)·(1-α_k(t)²)·exp(γ_k t) ≥ 0

  when r ≥ 0 and α_k ∈ [0,1]. By monotoneOn_of_deriv_nonneg:
  F_k(t) ≥ F_k(0), giving α_k(t) ≥ α_k(0)·exp(-γ_k t).

  Consequences:
  - Component positivity: α_k(0) > 0 ⟹ α_k(t) > 0 for all t
  - Order parameter bound: r(t) ≥ r(0)·exp(-γ_max t)
  - Finite-time persistence: on [0,T], min_k α_k(t) > 0

  0 sorry.
-/

import KuramotoLean.RationalOA
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Real Set

noncomputable section

/-! ## Grönwall multiplier structure -/

structure NPoleBarrierData (n : ℕ) where
  γ : Fin n → ℝ
  c : Fin n → ℝ
  K : ℝ
  α : ℝ → Fin n → ℝ
  hK : 0 < K
  hγ : ∀ k, 0 < γ k
  hc : ∀ k, 0 < c k
  hα_nn : ∀ t, 0 ≤ t → ∀ k, 0 ≤ α t k
  hα_le : ∀ t, 0 ≤ t → ∀ k, α t k ≤ 1
  hα_ode : ∀ t, 0 < t → ∀ k,
    HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t
  hα_cont : ∀ k, ContinuousOn (fun t => α t k) (Ici 0)

/-! ## The order parameter -/

def NPoleBarrierData.r {n : ℕ} (D : NPoleBarrierData n) (t : ℝ) : ℝ :=
  ∑ k, D.c k * D.α t k

theorem NPoleBarrierData.r_nonneg {n : ℕ} (D : NPoleBarrierData n)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ D.r t :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (le_of_lt (D.hc k)) (D.hα_nn t ht k)

/-! ## Grönwall multiplier: F_k(t) = α_k(t) · exp(γ_k t) -/

private def gronwall_mul {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) : ℝ :=
  D.α t k * exp (D.γ k * t)

private theorem gronwall_mul_cont {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) : ContinuousOn (gronwall_mul D k) (Ici 0) :=
  (D.hα_cont k).mul
    (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

private theorem gronwall_mul_deriv {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (gronwall_mul D k)
      ((D.K / 2) * D.r t * (1 - D.α t k ^ 2) * exp (D.γ k * t)) t := by
  have hα_deriv := D.hα_ode t ht k
  have hexp_deriv : HasDerivAt (fun s => exp (D.γ k * s))
      (D.γ k * exp (D.γ k * t)) t := by
    have h1 : HasDerivAt (fun s => D.γ k * s) (D.γ k * 1) t :=
      (hasDerivAt_id t).const_mul (D.γ k)
    rw [mul_one] at h1
    have h2 := h1.exp
    convert h2 using 1; ring
  have h := hα_deriv.mul hexp_deriv
  convert h using 1
  unfold nPoleODE NPoleBarrierData.r
  ring

private theorem gronwall_deriv_nonneg {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) (ht : 0 < t) :
    0 ≤ (D.K / 2) * D.r t * (1 - D.α t k ^ 2) * exp (D.γ k * t) := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · linarith [D.hK]
      · exact D.r_nonneg t (le_of_lt ht)
    · have h_le := D.hα_le t (le_of_lt ht) k
      have h_nn := D.hα_nn t (le_of_lt ht) k
      nlinarith [sq_abs (D.α t k)]
  · exact exp_nonneg _

private theorem gronwall_mul_monotone {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) : MonotoneOn (gronwall_mul D k) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (gronwall_mul_cont D k)
  · rw [interior_Ici]
    intro s hs
    exact (gronwall_mul_deriv D k s (mem_Ioi.mp hs)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro s hs
    rw [(gronwall_mul_deriv D k s (mem_Ioi.mp hs)).deriv]
    exact gronwall_deriv_nonneg D k s (mem_Ioi.mp hs)

/-! ## Main barrier theorem -/

/-- **Component barrier.** α_k(t) ≥ α_k(0)·exp(-γ_k t) for t ≥ 0.
    Proof: F_k(t) = α_k(t)·exp(γ_k t) is monotone, so F_k(t) ≥ F_k(0).
    Multiplying by exp(-γ_k t) gives the bound. -/
theorem component_barrier {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    D.α 0 k * exp (-(D.γ k) * t) ≤ D.α t k := by
  have hF := gronwall_mul_monotone D k (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have h0 : gronwall_mul D k 0 = D.α 0 k := by simp [gronwall_mul]
  rw [h0] at hF
  calc D.α 0 k * exp (-(D.γ k) * t)
      ≤ gronwall_mul D k t * exp (-(D.γ k) * t) :=
        mul_le_mul_of_nonneg_right hF (exp_nonneg _)
    _ = D.α t k * (exp (D.γ k * t) * exp (-(D.γ k) * t)) := by
        unfold gronwall_mul; ring
    _ = D.α t k := by rw [← exp_add]; simp

/-- **Component positivity.** If α_k(0) > 0, then α_k(t) > 0 for all t ≥ 0. -/
theorem component_positive {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (hα0 : 0 < D.α 0 k) (t : ℝ) (ht : 0 ≤ t) :
    0 < D.α t k :=
  lt_of_lt_of_le (mul_pos hα0 (exp_pos _)) (component_barrier D k t ht)

/-! ## Order parameter lower bound -/

/-- **Finite-time order parameter bound.**
    r(t) ≥ r(0)·exp(-γ_max·t) for t ≥ 0. -/
theorem order_parameter_lower {n : ℕ} (D : NPoleBarrierData n)
    (γ_max : ℝ) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (t : ℝ) (ht : 0 ≤ t) :
    D.r 0 * exp (-γ_max * t) ≤ D.r t := by
  unfold NPoleBarrierData.r
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro k _
  calc D.c k * D.α 0 k * exp (-γ_max * t)
      ≤ D.c k * (D.α 0 k * exp (-(D.γ k) * t)) := by
        have h1 : exp (-γ_max * t) ≤ exp (-(D.γ k) * t) :=
          exp_le_exp.mpr (by nlinarith [hγ_max k])
        have h2 : 0 ≤ D.c k * D.α 0 k :=
          mul_nonneg (le_of_lt (D.hc k)) (D.hα_nn 0 le_rfl k)
        calc D.c k * D.α 0 k * exp (-γ_max * t)
            ≤ D.c k * D.α 0 k * exp (-(D.γ k) * t) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = D.c k * (D.α 0 k * exp (-(D.γ k) * t)) := by ring
    _ ≤ D.c k * D.α t k :=
        mul_le_mul_of_nonneg_left (component_barrier D k t ht) (le_of_lt (D.hc k))

/-- **Order parameter positive.**
    If r(0) > 0, then r(t) > 0 for all t ≥ 0. -/
theorem order_parameter_positive {n : ℕ} (D : NPoleBarrierData n)
    (γ_max : ℝ) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hr0 : 0 < D.r 0) (t : ℝ) (ht : 0 ≤ t) :
    0 < D.r t :=
  lt_of_lt_of_le (mul_pos hr0 (exp_pos _))
    (order_parameter_lower D γ_max hγ_max t ht)

/-! ## Quantitative persistence on finite intervals -/

/-- **Component lower bound on [0, T].**
    α_k(t) ≥ α_k(0)·exp(-γ_k T) on [0,T]. -/
theorem component_lower_on_interval {n : ℕ} (D : NPoleBarrierData n)
    (k : Fin n) (T : ℝ) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    D.α 0 k * exp (-(D.γ k) * T) ≤ D.α t k :=
  le_trans
    (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith [D.hγ k]))
      (D.hα_nn 0 le_rfl k))
    (component_barrier D k t ht)

end
