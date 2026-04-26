/-
  Kuramoto Stability — Uniform Exponential Rate
  ===============================================

  The existing l2_exponential_rate uses diagonal extraction, introducing
  a c_min factor that degenerates as n → ∞. This file uses the FULL
  double sum to get a rate independent of n.

  KEY IDENTITY: Σ_j Σ_k c_j c_k (p_j² + p_k²) = 2·(Σ c)·V

  Combined with pair_coercive (each pair ≥ δδ*(p²+p²)):
    r*Q - DS ≥ (1/2)·δδ*·2V = δδ*V
    ⟹ dV/dt ≤ -K·δ·δ*·V  (no c_min, uniform in n)

  0 sorry.
-/

import KuramotoLean.PairCoercivity

noncomputable section

/-! ## Full pair sum identity -/

/-- **Full pair sum identity.**
    Σ_j Σ_k c_j c_k (p_j² + p_k²) = 2·(Σ c)·(Σ c_k p_k²).
    No diagonal extraction — uses the full double sum. -/
theorem full_pair_sum_identity {n : ℕ} (c p : Fin n → ℝ) :
    ∑ j, ∑ k, c j * c k * (p j ^ 2 + p k ^ 2) =
    2 * (∑ i, c i) * (∑ i, c i * p i ^ 2) := by
  have h1 : ∑ j, ∑ k, c j * c k * p j ^ 2 =
      (∑ i, c i) * (∑ i, c i * p i ^ 2) := by
    have : ∀ j, ∑ k, c j * c k * p j ^ 2 = c j * p j ^ 2 * ∑ k, c k := by
      intro j; rw [Finset.mul_sum]; congr 1; ext k; ring
    simp_rw [this, ← Finset.sum_mul]; ring
  have h2 : ∑ j, ∑ k, c j * c k * p k ^ 2 =
      (∑ i, c i) * (∑ i, c i * p i ^ 2) := by
    have : ∀ j, ∑ k, c j * c k * p k ^ 2 = c j * ∑ k, c k * p k ^ 2 := by
      intro j; rw [Finset.mul_sum]; congr 1; ext k; ring
    simp_rw [this, ← Finset.sum_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  linarith

/-- **Corollary for probability weights (Σ c = 1).**
    The double sum of squared deviations equals 2V. -/
theorem full_pair_sum_prob {n : ℕ} (c p : Fin n → ℝ)
    (hc_sum : ∑ i, c i = 1) :
    ∑ j, ∑ k, c j * c k * (p j ^ 2 + p k ^ 2) =
    2 * (∑ i, c i * p i ^ 2) := by
  rw [full_pair_sum_identity, hc_sum, mul_one]

/-! ## Uniform rate from coercive pair bound

From pair_coercive: pair(j,k) ≥ δ·δ*·(p_j² + p_k²) when α_j, α_k ≥ δ
and α*_j, α*_k ≥ δ*.

Combined with full_pair_sum_prob:
  Σ_j Σ_k c_j c_k pair(j,k) ≥ δδ* · Σ_j Σ_k c_j c_k (p_j²+p_k²) = δδ* · 2V

The Lyapunov identity gives r*Q - DS = (1/2) Σ pair (by symmetrization).
So: r*Q - DS ≥ (1/2)·δδ*·2V = δδ*V.
Hence: dV/dt = K(DS - r*Q) ≤ -Kδδ*V.

The rate Kδδ* is independent of n and c_min. -/

/-- **Coercive double sum bound.** If each pair ≥ δδ*(p²+p²), then
    the full double sum ≥ δδ*·2V. -/
theorem coercive_double_sum {n : ℕ} (c : Fin n → ℝ)
    (α α_star : Fin n → ℝ) (δ δ_star : ℝ)
    (hδ : 0 < δ) (_hδ_star : 0 < δ_star)
    (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (_hα_star_lt : ∀ k, α_star k < 1)
    (hα_lb : ∀ k, δ ≤ α k) (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hc_sum : ∑ k, c k = 1) :
    2 * (δ * δ_star) * l2Distance c α α_star ≤
    ∑ j, ∑ k, c j * c k *
      pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
  have h_pw : ∀ j k : Fin n,
      δ * δ_star * ((α j - α_star j) ^ 2 + (α k - α_star k) ^ 2) ≤
      pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
    intro j k
    have h_pc := pair_coercive (α j) (α k) (α_star j) (α_star k) δ
      (hα j) (hα k) (hα_lt j) (hα_lt k) (hα_star j) (hα_star k)
      hδ (hα_lb j) (hα_lb k)
    have hmin : δ_star ≤ min (α_star j) (α_star k) :=
      le_min (hα_star_lb j) (hα_star_lb k)
    have hsum_nn : 0 ≤ (α j - α_star j) ^ 2 + (α k - α_star k) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    calc δ * δ_star * ((α j - α_star j) ^ 2 + (α k - α_star k) ^ 2)
        ≤ δ * min (α_star j) (α_star k) *
          ((α j - α_star j) ^ 2 + (α k - α_star k) ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (le_of_lt hδ)) hsum_nn
      _ ≤ pairIntegrand (α j) (α_star j) (α k) (α_star k) := h_pc
  calc 2 * (δ * δ_star) * l2Distance c α α_star
      = δ * δ_star * (2 * (∑ i, c i * (α i - α_star i) ^ 2)) := by
        unfold l2Distance; ring
    _ = δ * δ_star * ∑ j, ∑ k, c j * c k *
        ((α j - α_star j) ^ 2 + (α k - α_star k) ^ 2) := by
        rw [full_pair_sum_prob c (fun k => α k - α_star k) hc_sum]
    _ = ∑ j, ∑ k, c j * c k * (δ * δ_star *
        ((α j - α_star j) ^ 2 + (α k - α_star k) ^ 2)) := by
        rw [Finset.mul_sum]; congr 1; ext j
        rw [Finset.mul_sum]; congr 1; ext k; ring
    _ ≤ ∑ j, ∑ k, c j * c k *
        pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (h_pw j k)
          (mul_nonneg (le_of_lt (hc j)) (le_of_lt (hc k)))

/-! ## Pair expansion identity: 2(r*Q - DS) = Σ Σ c_j c_k pair(j,k) -/

/-- **Pair expansion identity.** Purely algebraic. -/
theorem pair_expansion_identity {n : ℕ} (c α α_star : Fin n → ℝ) :
    2 * ((∑ j, c j * α_star j) *
         (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
         (∑ j, c j * (α j - α_star j)) *
         (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2))) =
    ∑ j, ∑ k, c j * c k *
      (α_star j * (α k - α_star k) ^ 2 * (α k + 1 / α_star k) +
       α_star k * (α j - α_star j) ^ 2 * (α j + 1 / α_star j) -
       (α j - α_star j) * (α k - α_star k) * (2 - α j ^ 2 - α k ^ 2)) := by
  have h1 : (∑ j, c j * α_star j) * (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) =
      ∑ j, ∑ k, c j * α_star j * (c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) := by
    rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  have h2 : (∑ j, c j * (α j - α_star j)) * (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) =
      ∑ j, ∑ k, c j * (α j - α_star j) * (c k * (α k - α_star k) * (1 - α k ^ 2)) := by
    rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  rw [h1, h2, show (∑ j, ∑ k, c j * α_star j * (c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k))) -
      (∑ j, ∑ k, c j * (α j - α_star j) * (c k * (α k - α_star k) * (1 - α k ^ 2))) =
      ∑ j, ∑ k, (c j * α_star j * (c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
      c j * (α j - α_star j) * (c k * (α k - α_star k) * (1 - α k ^ 2))) from by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; rw [← Finset.sum_sub_distrib]]
  set S := ∑ j, ∑ k, (c j * α_star j * (c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
      c j * (α j - α_star j) * (c k * (α k - α_star k) * (1 - α k ^ 2)))
  have h_swap : (∑ j, ∑ k, (c k * α_star k * (c j * (α j - α_star j) ^ 2 * (α j + 1 / α_star j)) -
      c k * (α k - α_star k) * (c j * (α j - α_star j) * (1 - α j ^ 2)))) = S := Finset.sum_comm
  have h_sum : 2 * S = ∑ j, ∑ k,
      ((c j * α_star j * (c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
        c j * (α j - α_star j) * (c k * (α k - α_star k) * (1 - α k ^ 2))) +
       (c k * α_star k * (c j * (α j - α_star j) ^ 2 * (α j + 1 / α_star j)) -
        c k * (α k - α_star k) * (c j * (α j - α_star j) * (1 - α j ^ 2)))) := by
    have : 2 * S = S + (∑ j, ∑ k, (c k * α_star k * (c j * (α j - α_star j) ^ 2 * (α j + 1 / α_star j)) -
        c k * (α k - α_star k) * (c j * (α j - α_star j) * (1 - α j ^ 2)))) := by rw [h_swap]; ring
    rw [this]; simp only [S, ← Finset.sum_add_distrib]
  rw [h_sum]; congr 1; ext j; congr 1; ext k; ring

/-! ## Full uniform rate -/

/-- **Uniform exponential rate.** dV/dt ≤ -K·δ·δ*·V for probability weights. -/
theorem l2_uniform_rate {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ) (δ δ_star : ℝ)
    (hK : 0 < K) (_hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (hδ : 0 < δ) (hδ_star : 0 < δ_star)
    (hα_lb : ∀ k, δ ≤ α k) (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hc_sum : ∑ k, c k = 1) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k ≤
    -(K * δ * δ_star) * l2Distance c α α_star := by
  rw [l2_lyapunov_identity γ c K α α_star hα_star h_equil]
  have h_expand := pair_expansion_identity c α α_star
  have h_coercive := coercive_double_sum c α α_star δ δ_star hδ hδ_star hc hα hα_lt
    hα_star hα_star_lt hα_lb hα_star_lb hc_sum
  simp only [pairIntegrand] at h_coercive
  nlinarith

end
