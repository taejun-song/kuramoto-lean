/-
  Kuramoto Stability — Instability Lyapunov Function
  ====================================================

  The Chetaev-type Lyapunov function W(α) = Σ c_k v_k α_k, where
  v_k = 1/(λ*+γ_k) is the unstable eigenvector at the incoherent state.

  Key identity: dW/dt = λ* W - (K/2) r · Σ c_k v_k α_k²

  Consequence: near α = 0 (all α_k small), dW/dt ≈ λ* W > 0,
  so W grows exponentially. Trajectories are repelled from incoherence.

  0 sorry target.
-/

import KuramotoLean.IncoherenceInstability

open Real Finset

noncomputable section

variable {n : ℕ}

/-! ## Eigenvector algebra -/

/-- v_k γ_k = 1 - λ v_k (from v_k = 1/(λ+γ_k), so v_k(λ+γ_k) = 1). -/
theorem eigenvector_gamma_rel (γ : Fin n → ℝ) (lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hlam : 0 < lam) (k : Fin n) :
    unstableEigenvector γ lam k * γ k =
    1 - lam * unstableEigenvector γ lam k := by
  unfold unstableEigenvector
  have hd : lam + γ k ≠ 0 := ne_of_gt (by linarith [hγ k])
  field_simp
  ring

/-- Σ c_k v_k = 2/K (from the dispersion relation). -/
theorem eigenvector_weight_sum (γ c : Fin n → ℝ) (K lam : ℝ)
    (hK : 0 < K) (hdisp : npoleDispersion γ c K lam = 1) :
    ∑ k, c k * unstableEigenvector γ lam k = 2 / K :=
  eigenvector_order_parameter γ c K lam hK hdisp

/-! ## The instability Lyapunov identity -/

/-- Per-component identity: c_k v_k (-γ_k α_k) = -(c_k α_k) + λ(c_k v_k α_k). -/
private theorem damp_component (γ : Fin n → ℝ) (c : Fin n → ℝ) (lam : ℝ) (α : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hlam : 0 < lam) (k : Fin n) :
    c k * unstableEigenvector γ lam k * (-γ k * α k) =
    -(c k * α k) + lam * (c k * unstableEigenvector γ lam k * α k) := by
  have hv := eigenvector_gamma_rel γ lam hγ hlam k
  have : c k * (unstableEigenvector γ lam k * γ k) * α k =
      c k * (1 - lam * unstableEigenvector γ lam k) * α k := by rw [hv]
  nlinarith

/-- **Instability Lyapunov identity.**
    dW/dt = λ* W - (K/2) r · Σ c_k v_k α_k²
    where W = Σ c_k v_k α_k and r = Σ c_k α_k. -/
theorem instability_lyapunov_identity (γ c : Fin n → ℝ) (K lam : ℝ)
    (α : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hlam : 0 < lam)
    (hdisp : npoleDispersion γ c K lam = 1) :
    ∑ k, c k * unstableEigenvector γ lam k * nPoleODE γ c K α k =
    lam * (∑ k, c k * unstableEigenvector γ lam k * α k) -
    (K / 2) * (∑ j, c j * α j) *
      ∑ k, c k * unstableEigenvector γ lam k * α k ^ 2 := by
  simp_rw [nPoleODE]
  -- Rewrite each term: c_k v_k (damping + coupling) = damping_part + coupling_part
  conv_lhs =>
    arg 2; ext k
    rw [show c k * unstableEigenvector γ lam k *
        (-γ k * α k + (K / 2) * (∑ j, c j * α j) * (1 - α k ^ 2)) =
      c k * unstableEigenvector γ lam k * (-γ k * α k) +
      (K / 2) * (∑ j, c j * α j) *
        (c k * unstableEigenvector γ lam k * (1 - α k ^ 2))
      from by ring]
  rw [Finset.sum_add_distrib]
  -- Damping sum: use per-component identity
  have h_damp : ∑ k, c k * unstableEigenvector γ lam k * (-γ k * α k) =
      -(∑ k, c k * α k) +
      lam * ∑ k, c k * unstableEigenvector γ lam k * α k := by
    simp_rw [damp_component γ c lam α hγ hlam]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  -- Coupling sum: factor out (K/2)r and use Σ c_k v_k = 2/K
  have h_coup : ∑ k, (K / 2) * (∑ j, c j * α j) *
      (c k * unstableEigenvector γ lam k * (1 - α k ^ 2)) =
      (K / 2) * (∑ j, c j * α j) *
        (∑ k, c k * unstableEigenvector γ lam k -
         ∑ k, c k * unstableEigenvector γ lam k * α k ^ 2) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [h_damp, h_coup, eigenvector_weight_sum γ c K lam hK hdisp]
  have hK_ne : K ≠ 0 := ne_of_gt hK
  field_simp
  ring

/-! ## Instability growth near incoherence -/

/-- **Instability correction bound.**
    When all α_k ≤ ε, the correction term satisfies:
    (K/2) r · Σ c_k v_k α_k² ≤ (K/2) Sc ε² · W
    where Sc = Σ c_k, W = Σ c_k v_k α_k. -/
theorem instability_correction_bound (γ c : Fin n → ℝ) (K lam : ℝ)
    (α : Fin n → ℝ) (ε : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hlam : 0 < lam) (hK : 0 < K) (hε : 0 < ε)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ ε) :
    (K / 2) * (∑ j, c j * α j) *
      (∑ k, c k * unstableEigenvector γ lam k * α k ^ 2) ≤
    (K / 2) * (∑ k, c k) * ε ^ 2 *
      (∑ k, c k * unstableEigenvector γ lam k * α k) := by
  have hr_bound : ∑ j, c j * α j ≤ (∑ j, c j) * ε := by
    calc ∑ j, c j * α j
        ≤ ∑ j, c j * ε := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hα_le j) (le_of_lt (hc j)))
      _ = (∑ j, c j) * ε := by rw [← Finset.sum_mul]
  have hαsq_bound : ∀ k : Fin n,
      c k * unstableEigenvector γ lam k * α k ^ 2 ≤
      c k * unstableEigenvector γ lam k * α k * ε := by
    intro k
    have hcv : 0 < c k * unstableEigenvector γ lam k :=
      mul_pos (hc k) (unstableEigenvector_pos γ lam hγ hlam k)
    have : α k ^ 2 ≤ α k * ε := by
      calc α k ^ 2 = α k * α k := sq (α k)
        _ ≤ α k * ε := mul_le_mul_of_nonneg_left (hα_le k) (hα_nn k)
    calc c k * unstableEigenvector γ lam k * α k ^ 2
        ≤ c k * unstableEigenvector γ lam k * (α k * ε) :=
          mul_le_mul_of_nonneg_left this (le_of_lt hcv)
      _ = c k * unstableEigenvector γ lam k * α k * ε := by ring
  have hsq_sum : ∑ k, c k * unstableEigenvector γ lam k * α k ^ 2 ≤
      (∑ k, c k * unstableEigenvector γ lam k * α k) * ε := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => hαsq_bound k)
  have hr_nn : 0 ≤ ∑ j, c j * α j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hc j)) (hα_nn j))
  have hW_nn : 0 ≤ ∑ k, c k * unstableEigenvector γ lam k * α k :=
    Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (le_of_lt (hc k))
        (le_of_lt (unstableEigenvector_pos γ lam hγ hlam k))) (hα_nn k))
  calc (K / 2) * (∑ j, c j * α j) *
        (∑ k, c k * unstableEigenvector γ lam k * α k ^ 2)
      ≤ (K / 2) * (∑ j, c j * α j) *
        ((∑ k, c k * unstableEigenvector γ lam k * α k) * ε) := by
        exact mul_le_mul_of_nonneg_left hsq_sum (mul_nonneg (by linarith) hr_nn)
    _ ≤ (K / 2) * ((∑ j, c j) * ε) *
        ((∑ k, c k * unstableEigenvector γ lam k * α k) * ε) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr_bound (by linarith))
          (mul_nonneg hW_nn (le_of_lt hε))
    _ = (K / 2) * (∑ k, c k) * ε ^ 2 *
        (∑ k, c k * unstableEigenvector γ lam k * α k) := by ring

/-- **Instability growth rate.**
    dW/dt ≥ (λ* - (K/2) Sc ε²) W when all α_k ∈ [0, ε].
    Combined with instability_lyapunov_identity, this gives exponential
    growth of W near the incoherent state when ε² < 2λ*/(K Sc). -/
theorem instability_growth_rate (γ c : Fin n → ℝ) (K lam : ℝ)
    (α : Fin n → ℝ) (ε : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hlam : 0 < lam) (hK : 0 < K) (hε : 0 < ε)
    (hdisp : npoleDispersion γ c K lam = 1)
    (hα_nn : ∀ k, 0 ≤ α k) (hα_le : ∀ k, α k ≤ ε) :
    (lam - (K / 2) * (∑ k, c k) * ε ^ 2) *
      (∑ k, c k * unstableEigenvector γ lam k * α k) ≤
    ∑ k, c k * unstableEigenvector γ lam k * nPoleODE γ c K α k := by
  rw [instability_lyapunov_identity γ c K lam α hγ hK hlam hdisp]
  have hcorr := instability_correction_bound γ c K lam α ε hγ hc hlam hK hε hα_nn hα_le
  linarith

end
