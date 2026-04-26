/-
  Kuramoto Stability — Chetaev Instability Escape
  =================================================

  Proves trajectories of the n-pole ODE with K > K_c cannot remain
  near the incoherent state α = 0. The instability Lyapunov function
  W = Σ c_k v_k α_k grows exponentially in the instability zone,
  forcing escape in finite time.

  Key theorems:
  - instability_W_growth: W grows exponentially along trajectories in ε-ball
  - instabilityW_le_in_ball: W ≤ (2/K)ε in the ε-ball
  - instability_escape: trajectory must leave ε-ball in finite time

  Building block for deriving persistence from instability.

  0 sorry target.
-/

import KuramotoLean.InstabilityLyapunov
import KuramotoLean.ComparisonGrowth
import KuramotoLean.ComponentBarrier

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Instability Lyapunov function along trajectory -/

/-- W(t) = Σ c_k v_k α_k(t), the instability Lyapunov function. -/
def instabilityW (c γ : Fin n → ℝ) (lam : ℝ)
    (α : ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, c k * unstableEigenvector γ lam k * α t k

/-- W is non-negative when α ≥ 0. -/
theorem instabilityW_nonneg (c γ : Fin n → ℝ) (lam : ℝ)
    (α : ℝ → Fin n → ℝ) (t : ℝ)
    (hc : ∀ k, 0 < c k) (hγ : ∀ k, 0 < γ k) (hlam : 0 < lam)
    (hα : ∀ k, 0 ≤ α t k) :
    0 ≤ instabilityW c γ lam α t := by
  unfold instabilityW
  apply Finset.sum_nonneg; intro k _
  exact mul_nonneg (mul_nonneg (le_of_lt (hc k))
    (le_of_lt (unstableEigenvector_pos γ lam hγ hlam k))) (hα k)

/-- W is continuous along the trajectory. -/
theorem instabilityW_cont (D : NPoleBarrierData n) (lam : ℝ) :
    ContinuousOn (instabilityW D.c D.γ lam D.α) (Ici 0) := by
  unfold instabilityW
  apply continuousOn_finset_sum; intro k _
  exact continuousOn_const.mul (D.hα_cont k)

/-- Chain rule: dW/dt = Σ c_k v_k · nPoleODE_k along the trajectory. -/
theorem hasDerivAt_instabilityW (c γ : Fin n → ℝ) (K lam : ℝ)
    (α : ℝ → Fin n → ℝ) (t : ℝ)
    (hα_ode : ∀ k, HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t) :
    HasDerivAt (instabilityW c γ lam α)
      (∑ k, c k * unstableEigenvector γ lam k * nPoleODE γ c K (α t) k) t := by
  unfold instabilityW
  exact HasDerivAt.fun_sum fun k _ => (hα_ode k).const_mul (c k * unstableEigenvector γ lam k)

/-! ## W growth bound in the instability zone -/

/-- **W growth along trajectory.** If the trajectory stays in the ε-ball
    (all α_k(t) ≤ ε) on [0,∞), then W(t) ≥ W(0)·exp((λ*/2)t). -/
theorem instability_W_growth (D : NPoleBarrierData n)
    (lam : ℝ) (hlam : 0 < lam)
    (hdisp : npoleDispersion D.γ D.c D.K lam = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (D.K / 2) * (∑ k, D.c k) * ε ^ 2 ≤ lam / 2)
    (hstay : ∀ t, 0 ≤ t → ∀ k, D.α t k ≤ ε) :
    ∀ t, 0 ≤ t →
      instabilityW D.c D.γ lam D.α 0 * exp (lam / 2 * t) ≤
      instabilityW D.c D.γ lam D.α t := by
  apply comparison_growth (instabilityW D.c D.γ lam D.α)
    (fun t => ∑ k, D.c k * unstableEigenvector D.γ lam k *
      nPoleODE D.γ D.c D.K (D.α t) k)
    (lam / 2)
  · exact instabilityW_cont D lam
  · intro t ht
    exact hasDerivAt_instabilityW D.c D.γ D.K lam D.α t (D.hα_ode t ht)
  · intro t ht
    have hα_nn := fun k => D.hα_nn t (le_of_lt ht) k
    have hα_le := hstay t (le_of_lt ht)
    have h_igr := instability_growth_rate D.γ D.c D.K lam (D.α t) ε
      D.hγ D.hc hlam D.hK hε hdisp hα_nn hα_le
    have hW_nn : 0 ≤ instabilityW D.c D.γ lam D.α t :=
      instabilityW_nonneg D.c D.γ lam D.α t D.hc D.hγ hlam hα_nn
    have hμ_le : lam / 2 ≤ lam - (D.K / 2) * (∑ k, D.c k) * ε ^ 2 := by linarith
    calc lam / 2 * instabilityW D.c D.γ lam D.α t
        ≤ (lam - (D.K / 2) * (∑ k, D.c k) * ε ^ 2) *
          (∑ k, D.c k * unstableEigenvector D.γ lam k * D.α t k) :=
          mul_le_mul_of_nonneg_right hμ_le hW_nn
      _ ≤ ∑ k, D.c k * unstableEigenvector D.γ lam k *
          nPoleODE D.γ D.c D.K (D.α t) k := h_igr

/-! ## W upper bound in the ε-ball -/

/-- W ≤ (2/K)·ε when all α_k ≤ ε. Uses Σ c_k v_k = 2/K (dispersion). -/
theorem instabilityW_le_in_ball (c γ : Fin n → ℝ) (K lam ε : ℝ)
    (α : Fin n → ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hlam : 0 < lam)
    (hdisp : npoleDispersion γ c K lam = 1)
    (_hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ ε) :
    ∑ k, c k * unstableEigenvector γ lam k * α k ≤
    2 / K * ε := by
  have hev := eigenvector_weight_sum γ c K lam hK hdisp
  calc ∑ k, c k * unstableEigenvector γ lam k * α k
      ≤ ∑ k, c k * unstableEigenvector γ lam k * ε := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hα_le k)
          (mul_nonneg (le_of_lt (hc k))
            (le_of_lt (unstableEigenvector_pos γ lam hγ hlam k)))
    _ = (∑ k, c k * unstableEigenvector γ lam k) * ε := by
        rw [Finset.sum_mul]
    _ = 2 / K * ε := by rw [hev]

/-! ## Instability escape theorem -/

/-- **Instability escape.** For the n-pole ODE with K > K_c:
    if W(0) > 0 (some component positive) and ε is in the instability zone,
    then the trajectory must leave the ε-ball. Some α_k(t) > ε at some t ≥ 0.

    Proof by contradiction: if the trajectory stays in the ball forever,
    W grows exponentially (comparison_growth) but W ≤ (2/K)ε (bounded).
    Since exp(μt) → ∞, this is impossible. -/
theorem instability_escape (D : NPoleBarrierData n)
    (lam : ℝ) (hlam : 0 < lam)
    (hdisp : npoleDispersion D.γ D.c D.K lam = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (D.K / 2) * (∑ k, D.c k) * ε ^ 2 ≤ lam / 2)
    (hW0 : 0 < instabilityW D.c D.γ lam D.α 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ k : Fin n, ε < D.α t k := by
  by_contra h_stay
  push Not at h_stay
  have hgrowth := instability_W_growth D lam hlam hdisp ε hε hε_small h_stay
  set C := 2 / D.K * ε with hC_def
  set W₀ := instabilityW D.c D.γ lam D.α 0 with hW₀_def
  have hC_pos : 0 < C :=
    mul_pos (div_pos (by norm_num : (0:ℝ) < 2) D.hK) hε
  have hW₀_pos : 0 < W₀ := hW0
  have hupper : ∀ t, 0 ≤ t →
      instabilityW D.c D.γ lam D.α t ≤ C := by
    intro t ht
    exact instabilityW_le_in_ball D.c D.γ D.K lam ε (D.α t)
      D.hK D.hγ D.hc hlam hdisp (D.hα_nn t ht) (h_stay t ht)
  have hbound : ∀ t, 0 ≤ t → W₀ * exp (lam / 2 * t) ≤ C :=
    fun t ht => le_trans (hgrowth t ht) (hupper t ht)
  have hμ : 0 < lam / 2 := by linarith
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp tendsto_exp_atTop) (C / W₀ + 1)
  set T := max 0 (N / (lam / 2)) with hT_def
  have hT_nn : (0:ℝ) ≤ T := le_max_left 0 _
  have hμT_ge : N ≤ lam / 2 * T := by
    by_cases hN_nn : 0 ≤ N
    · calc N = lam / 2 * (N / (lam / 2)) := by field_simp
        _ ≤ lam / 2 * T := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hμ)
            exact le_max_right 0 _
    · push Not at hN_nn
      calc N ≤ 0 := le_of_lt hN_nn
        _ ≤ lam / 2 * T := mul_nonneg (le_of_lt hμ) hT_nn
  have h_exp_large : C / W₀ + 1 ≤ exp (lam / 2 * T) := by
    calc C / W₀ + 1 ≤ exp N := hN N le_rfl
      _ ≤ exp (lam / 2 * T) := exp_le_exp.mpr hμT_ge
  have h_contradiction : C < W₀ * exp (lam / 2 * T) := by
    have : C / W₀ < C / W₀ + 1 := lt_add_one _
    calc C = W₀ * (C / W₀) := by field_simp
      _ < W₀ * (C / W₀ + 1) :=
          mul_lt_mul_of_pos_left this hW₀_pos
      _ ≤ W₀ * exp (lam / 2 * T) :=
          mul_le_mul_of_nonneg_left h_exp_large (le_of_lt hW₀_pos)
  linarith [hbound T hT_nn]

/-! ## Corollary: order parameter visits a positive value -/

/-- **Order parameter lower bound at escape.**
    When some α_k(t) > ε, the order parameter r(t) ≥ c_min · ε. -/
theorem r_pos_at_escape (D : NPoleBarrierData n)
    (ε : ℝ) (hε : 0 < ε) (c_min : ℝ) (hc_min : ∀ j, c_min ≤ D.c j)
    (_hc_min_pos : 0 < c_min)
    (t : ℝ) (ht : 0 ≤ t) (k : Fin n) (hk : ε < D.α t k) :
    c_min * ε < D.r t := by
  unfold NPoleBarrierData.r
  calc c_min * ε < D.c k * D.α t k := by
        calc c_min * ε ≤ D.c k * ε :=
              mul_le_mul_of_nonneg_right (hc_min k) (le_of_lt hε)
          _ < D.c k * D.α t k :=
              mul_lt_mul_of_pos_left hk (D.hc k)
    _ ≤ ∑ j, D.c j * D.α t j :=
        single_le_sum (fun j _ =>
          mul_nonneg (le_of_lt (D.hc j)) (D.hα_nn t ht j)) (mem_univ k)

end
