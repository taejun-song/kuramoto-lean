/-
  Kuramoto Stability — Gronwall Bridge
  =====================================
  Comparison principle: dV/dt ≤ -μV ⟹ V(t) ≤ V₀·exp(-μt).

  Uses the comparison function W(t) = V(t)·exp(μt), which has W'(t) ≤ 0,
  hence is antitone by Mathlib's mean value theorem.

  Combined with trajectory_lyapunov_bound, this completes the n-pole
  exponential convergence chain:

    l2_exponential_rate → trajectory_lyapunov_bound → comparison_decay
    → NPoleExponentialData → npole_exponential_convergence

  0 sorry target.
-/

import KuramotoLean.TrajectoryLyapunov
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Real Set

noncomputable section

/-! ## Comparison principle: V'(t) ≤ -μV(t) implies exponential decay

  Proof idea: W(t) = V(t)·exp(μt) satisfies W'(t) = (V'(t)+μV(t))·exp(μt) ≤ 0.
  By antitoneOn_of_deriv_nonpos: W antitone on [0,∞), so W(t) ≤ W(0) = V(0). -/

theorem comparison_decay (V : ℝ → ℝ) (V' : ℝ → ℝ) (μ : ℝ)
    (hV_cont : ContinuousOn V (Ici 0))
    (hV_hasderiv : ∀ t, 0 < t → HasDerivAt V (V' t) t)
    (hV_bound : ∀ t, 0 < t → V' t ≤ -μ * V t) :
    ∀ t, 0 ≤ t → V t ≤ V 0 * exp (-μ * t) := by
  intro t ht
  suffices h : V t * exp (μ * t) ≤ V 0 * exp (μ * 0) by
    have hexp : (0:ℝ) < exp (μ * t) := exp_pos _
    have : V t = V t * exp (μ * t) * exp (-μ * t) := by
      rw [mul_assoc, ← exp_add]; simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by rwa [mul_zero, exp_zero, mul_one] at h) (exp_nonneg _)
  set W : ℝ → ℝ := fun s => V s * exp (μ * s)
  have hexp_deriv : ∀ s, HasDerivAt (fun u => exp (μ * u)) (μ * exp (μ * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u => μ * u) (μ * 1) s :=
      (hasDerivAt_id s).const_mul μ
    rw [mul_one] at h1
    have h2 := h1.exp
    convert h2 using 1; ring
  have hexp_cont : Continuous (fun s => exp (μ * s)) :=
    continuous_exp.comp (continuous_const.mul continuous_id)
  have hW_cont : ContinuousOn W (Ici 0) :=
    hV_cont.mul hexp_cont.continuousOn
  have hW_diff : DifferentiableOn ℝ W (Ioi 0) := by
    intro s hs
    exact ((hV_hasderiv s (mem_Ioi.mp hs)).mul
      (hexp_deriv s)).differentiableAt.differentiableWithinAt
  have hW_nonpos : ∀ s ∈ Ioi (0:ℝ), deriv W s ≤ 0 := by
    intro s hs
    have hs_pos := mem_Ioi.mp hs
    have hW_has : HasDerivAt W (V' s * exp (μ * s) + V s * (μ * exp (μ * s))) s :=
      (hV_hasderiv s hs_pos).mul (hexp_deriv s)
    rw [hW_has.deriv]
    have : V' s * exp (μ * s) + V s * (μ * exp (μ * s)) =
           (V' s + μ * V s) * exp (μ * s) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hV_bound s hs_pos]) (exp_nonneg _)
  have hW_antitone : AntitoneOn W (Ici 0) := by
    exact antitoneOn_of_deriv_nonpos (convex_Ici (𝕜 := ℝ) 0) hW_cont
      (by rwa [interior_Ici]) (by rwa [interior_Ici])
  exact hW_antitone (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-! ## Shifted comparison: V'≤-μV on [a,a+Δ] ⟹ V(a+Δ)≤V(a)·exp(-μΔ) -/

/-- **Shifted comparison principle.** If dV/dt ≤ -μV on the interval
    (a, a+Δ), then V(a+Δ) ≤ V(a)·exp(-μΔ). -/
theorem comparison_decay_interval (V : ℝ → ℝ) (V' : ℝ → ℝ) (μ a Δ : ℝ)
    (hΔ : 0 ≤ Δ)
    (hV_cont : ContinuousOn V (Icc a (a + Δ)))
    (hV_hasderiv : ∀ t, a < t → t < a + Δ → HasDerivAt V (V' t) t)
    (hV_bound : ∀ t, a < t → t < a + Δ → V' t ≤ -μ * V t) :
    V (a + Δ) ≤ V a * exp (-μ * Δ) := by
  set W : ℝ → ℝ := fun t => V t * exp (μ * (t - a))
  have hexp_deriv : ∀ s, HasDerivAt (fun u => exp (μ * (u - a)))
      (μ * exp (μ * (s - a))) s := by
    intro s
    have h1 : HasDerivAt (fun u => μ * (u - a)) (μ * 1) s := by
      exact ((hasDerivAt_id s).sub_const a).const_mul μ
    rw [mul_one] at h1
    have h2 := h1.exp
    convert h2 using 1; ring
  have hexp_cont : Continuous (fun s => exp (μ * (s - a))) :=
    continuous_exp.comp ((continuous_const.mul (continuous_id.sub continuous_const)))
  have hW_cont : ContinuousOn W (Icc a (a + Δ)) :=
    hV_cont.mul hexp_cont.continuousOn
  have hW_nonpos : ∀ s ∈ Ioo a (a + Δ), deriv W s ≤ 0 := by
    intro s ⟨hs_lo, hs_hi⟩
    have hW_has : HasDerivAt W
        (V' s * exp (μ * (s - a)) + V s * (μ * exp (μ * (s - a)))) s :=
      (hV_hasderiv s hs_lo hs_hi).mul (hexp_deriv s)
    rw [hW_has.deriv]
    have : V' s * exp (μ * (s - a)) + V s * (μ * exp (μ * (s - a))) =
           (V' s + μ * V s) * exp (μ * (s - a)) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg
      (by linarith [hV_bound s hs_lo hs_hi]) (exp_nonneg _)
  have hW_diff : DifferentiableOn ℝ W (Ioo a (a + Δ)) := by
    intro s hs
    exact ((hV_hasderiv s (mem_Ioo.mp hs).1 (mem_Ioo.mp hs).2).mul
      (hexp_deriv s)).differentiableAt.differentiableWithinAt
  have hW_anti : AntitoneOn W (Icc a (a + Δ)) := by
    rcases eq_or_lt_of_le hΔ with rfl | _
    · simp [AntitoneOn]
    · exact antitoneOn_of_deriv_nonpos (convex_Icc a (a + Δ)) hW_cont
        (by rwa [interior_Icc]) (by rwa [interior_Icc])
  have hle : W (a + Δ) ≤ W a :=
    hW_anti (left_mem_Icc.mpr (by linarith))
      (right_mem_Icc.mpr (by linarith)) (by linarith)
  simp only [W, sub_self, mul_zero, exp_zero, mul_one] at hle
  calc V (a + Δ)
      = V (a + Δ) * exp (μ * Δ) * exp (-μ * Δ) := by
        rw [mul_assoc, ← exp_add]; simp
    _ ≤ V a * exp (-μ * Δ) := by
        apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
        have h : μ * ((a + Δ) - a) = μ * Δ := by ring
        rwa [h] at hle

/-! ## Assembled n-pole exponential decay

  Given an n-pole trajectory where:
  (a) the L² Lyapunov function V = Σ c_k(α_k-α*_k)² is continuous
  (b) the trajectory satisfies the ODE (giving HasDerivAt for V)
  (c) α_k ≥ δ > 0 uniformly (giving the exponential rate bound)

  Then V(t) ≤ V(0)·exp(-μt) where μ = K·c_min·δ·(δ+δ*). -/

structure NPoleTrajectoryData (n : ℕ) where
  γ : Fin n → ℝ
  c : Fin n → ℝ
  K : ℝ
  α : ℝ → Fin n → ℝ
  α_star : Fin n → ℝ
  δ : ℝ
  δ_star : ℝ
  c_min : ℝ
  hK : 0 < K
  hγ : ∀ k, 0 < γ k
  hc : ∀ k, 0 < c k
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  hδ : 0 < δ
  hδ_star : 0 < δ_star
  hc_min : 0 < c_min
  hα_lb : ∀ t, 0 ≤ t → ∀ k, δ ≤ α t k
  hα_lt : ∀ t, 0 ≤ t → ∀ k, α t k < 1
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  hc_lb : ∀ k, c_min ≤ c k
  hα_ode : ∀ t, 0 < t → ∀ k, HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t
  hV_cont : ContinuousOn (fun t => l2Distance c (α t) α_star) (Ici 0)

def NPoleTrajectoryData.rate (D : NPoleTrajectoryData n) : ℝ :=
  D.K * D.c_min * D.δ * (D.δ + D.δ_star)

theorem NPoleTrajectoryData.rate_pos (D : NPoleTrajectoryData n) : 0 < D.rate := by
  unfold rate
  exact mul_pos (mul_pos (mul_pos D.hK D.hc_min) D.hδ) (by linarith [D.hδ, D.hδ_star])

theorem npole_exponential_l2_decay (D : NPoleTrajectoryData n) :
    ∀ t, 0 ≤ t →
      l2Distance D.c (D.α t) D.α_star ≤
        l2Distance D.c (D.α 0) D.α_star * exp (-D.rate * t) := by
  apply comparison_decay
    (fun t => l2Distance D.c (D.α t) D.α_star)
    (fun t => ∑ k, D.c k * (2 * (D.α t k - D.α_star k) * nPoleODE D.γ D.c D.K (D.α t) k))
    D.rate
  · exact D.hV_cont
  · intro t ht
    exact hasDerivAt_l2Distance_along D.c D.α D.α_star
      (fun k => nPoleODE D.γ D.c D.K (D.α t) k) t (D.hα_ode t ht)
  · intro t ht
    have h := l2_exponential_rate D.γ D.c D.K (D.α t) D.α_star
      D.δ D.δ_star D.c_min
      D.hK D.hγ D.hc
      (fun k => lt_of_lt_of_le D.hδ (D.hα_lb t (le_of_lt ht) k))
      (D.hα_lt t (le_of_lt ht))
      D.hα_star_pos D.hα_star_lt
      D.h_equil D.hδ D.hδ_star D.hc_min
      (D.hα_lb t (le_of_lt ht)) D.hα_star_lb D.hc_lb
    have h_eq : ∑ k, D.c k * (2 * (D.α t k - D.α_star k) *
        nPoleODE D.γ D.c D.K (D.α t) k) =
      ∑ k, D.c k * 2 * (D.α t k - D.α_star k) *
        nPoleODE D.γ D.c D.K (D.α t) k := by
      congr 1; ext k; ring
    rw [h_eq]; unfold NPoleTrajectoryData.rate; linarith

/-- From L² exponential decay, construct NPoleExponentialData. -/
def NPoleTrajectoryData.toExponentialData (D : NPoleTrajectoryData n)
    (hV0 : 0 < l2Distance D.c (D.α 0) D.α_star) :
    NPoleExponentialData n where
  c := D.c
  α := D.α
  α_star := D.α_star
  hc := D.hc
  c_min := D.c_min
  hc_min := D.hc_lb
  hc_min_pos := D.hc_min
  rate := D.rate
  hrate := D.rate_pos
  V0 := l2Distance D.c (D.α 0) D.α_star
  hV0 := hV0
  hV_bound := npole_exponential_l2_decay D

/-- **N-pole global stability via L² Lyapunov + Gronwall.**
    For any n-pole OA trajectory with uniform lower bounds,
    α(t) → α* pointwise with explicit exponential rate. -/
theorem npole_l2_global_stability (D : NPoleTrajectoryData n)
    (hV0 : 0 < l2Distance D.c (D.α 0) D.α_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → ∀ k,
      |D.α t k - D.α_star k| < ε :=
  npole_exponential_convergence (D.toExponentialData hV0)

/-! ## Order parameter convergence from L² convergence -/

theorem order_parameter_from_pointwise {n : ℕ} (c : Fin n → ℝ)
    (α α_star : Fin n → ℝ) (ε : ℝ)
    (hc_nn : ∀ k, 0 ≤ c k)
    (h_close : ∀ k, |α k - α_star k| ≤ ε) :
    |∑ k : Fin n, c k * α k - ∑ k : Fin n, c k * α_star k| ≤
      (∑ k : Fin n, c k) * ε := by
  have h_diff : ∑ k : Fin n, c k * α k - ∑ k : Fin n, c k * α_star k =
      ∑ k : Fin n, c k * (α k - α_star k) := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
  rw [h_diff]
  calc |∑ k : Fin n, c k * (α k - α_star k)|
      ≤ ∑ k : Fin n, |c k * (α k - α_star k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, c k * |α k - α_star k| := by
        congr 1; ext k; rw [abs_mul, abs_of_nonneg (hc_nn k)]
    _ ≤ ∑ k : Fin n, c k * ε := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (h_close k) (hc_nn k)
    _ = (∑ k : Fin n, c k) * ε := by
        rw [← Finset.sum_mul]

end
