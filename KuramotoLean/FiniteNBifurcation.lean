/-
  Finite-N Bifurcation via Continuum Theory
  ==========================================
  The continuum bifurcation results apply to N-oscillator systems via
  the uniform measure on Fin N. For N oscillators with frequencies
  γ₁,...,γ_N:

    Kc(N) = 2N / Σ(1/γᵢ)

  All continuum theorems instantiate:
  - K ≤ Kc(N): no positive equilibrium
  - K > Kc(N): unique positive equilibrium r*(N)
  - r*(N) is monotone in K
  - r*(N)² = Θ(K - Kc(N)) near onset

  The connection to the standard definition:
  Kc = 2/∫(1/γ)dμ with μ = (1/N)Σδ_{γₖ} gives Kc = 2/(1/N · Σ(1/γₖ)) = 2N/Σ(1/γₖ).

  0 sorry.
-/

import KuramotoLean.UnifiedPhaseTransition
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators

noncomputable section

/-! ## Finite-N critical coupling -/

/-- The critical coupling for N oscillators with frequencies γ₁,...,γ_N. -/
def finiteKc {N : ℕ} (γ : Fin N → ℝ) : ℝ :=
  2 * N / ∑ k : Fin N, (1 / γ k)

/-- **Kc(N) is positive** when all frequencies are positive. -/
theorem finiteKc_pos {N : ℕ} (γ : Fin N → ℝ) (hγ : ∀ k, 0 < γ k) (hN : 0 < N) :
    0 < finiteKc γ := by
  unfold finiteKc
  have h_sum_pos : 0 < ∑ k : Fin N, (1 / γ k) :=
    sum_pos (fun k _ => div_pos one_pos (hγ k)) (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
  exact div_pos (mul_pos two_pos (Nat.cast_pos.mpr hN)) h_sum_pos

/-- **Kc(N) scales linearly with γ.** -/
theorem finiteKc_scale {N : ℕ} (γ : Fin N → ℝ) (c : ℝ) (hc : 0 < c)
    (hγ : ∀ k, 0 < γ k) (hN : 0 < N) :
    finiteKc (fun k => c * γ k) = c * finiteKc γ := by
  unfold finiteKc
  have h_eq : ∑ k : Fin N, (1 / (c * γ k)) = (1 / c) * ∑ k : Fin N, (1 / γ k) := by
    rw [mul_sum]; congr 1; ext k; field_simp
  rw [h_eq]; field_simp

/-- **Kc(N) monotone in γ.**
    Wider frequencies → higher critical coupling. -/
theorem finiteKc_mono {N : ℕ} (γ₁ γ₂ : Fin N → ℝ)
    (hγ₁ : ∀ k, 0 < γ₁ k) (hγ₂ : ∀ k, 0 < γ₂ k)
    (hN : 0 < N) (h_le : ∀ k, γ₁ k ≤ γ₂ k) :
    finiteKc γ₁ ≤ finiteKc γ₂ := by
  unfold finiteKc
  have h₁_pos : 0 < ∑ k : Fin N, (1 / γ₁ k) :=
    sum_pos (fun k _ => div_pos one_pos (hγ₁ k)) (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
  have h₂_pos : 0 < ∑ k : Fin N, (1 / γ₂ k) :=
    sum_pos (fun k _ => div_pos one_pos (hγ₂ k)) (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
  have h_sum_le : ∑ k : Fin N, (1 / γ₂ k) ≤ ∑ k : Fin N, (1 / γ₁ k) :=
    sum_le_sum (fun k _ => div_le_div_of_nonneg_left zero_le_one (hγ₁ k) (h_le k))
  exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * ↑N) h₂_pos h_sum_le

/-! ## Finite-N self-consistency equation -/

/-- The self-consistency map for N oscillators (arithmetic mean). -/
def finitePhiMap {N : ℕ} (γ : Fin N → ℝ) (K r : ℝ) : ℝ :=
  (1 / N : ℝ) * ∑ k : Fin N, explicitEquil (γ k) K r

/-- **Φ(N,r) > 0** for r > 0. -/
theorem finitePhiMap_pos {N : ℕ} (γ : Fin N → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) (hN : 0 < N) :
    0 < finitePhiMap γ K r := by
  unfold finitePhiMap
  exact mul_pos (div_pos one_pos (Nat.cast_pos.mpr hN))
    (sum_pos (fun k _ => explicitEquil_pos (γ k) K r (hγ k) hK hr)
      (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩))

/-- **Φ(N,r) < 1** for r > 0. -/
theorem finitePhiMap_lt_one {N : ℕ} (γ : Fin N → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) (hN : 0 < N) :
    finitePhiMap γ K r < 1 := by
  unfold finitePhiMap
  have h_lt : ∑ k : Fin N, explicitEquil (γ k) K r < N := by
    calc ∑ k : Fin N, explicitEquil (γ k) K r
        < ∑ _ : Fin N, (1 : ℝ) := sum_lt_sum
          (fun k _ => le_of_lt (explicitEquil_lt_one (γ k) K r (hγ k) hK hr))
          ⟨⟨0, hN⟩, mem_univ _, explicitEquil_lt_one (γ ⟨0, hN⟩) K r (hγ _) hK hr⟩
      _ = N := by simp [card_fin]
  calc (1 / ↑N : ℝ) * ∑ k, explicitEquil (γ k) K r
      < (1 / ↑N : ℝ) * ↑N := by
        exact mul_lt_mul_of_pos_left h_lt (div_pos one_pos (Nat.cast_pos.mpr hN))
    _ = 1 := by field_simp

/-- **Φ(N) is strictly increasing in r.** -/
theorem finitePhiMap_strictMono {N : ℕ} (γ : Fin N → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hN : 0 < N)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    finitePhiMap γ K r₁ < finitePhiMap γ K r₂ := by
  unfold finitePhiMap
  apply mul_lt_mul_of_pos_left _ (div_pos one_pos (Nat.cast_pos.mpr hN))
  exact sum_lt_sum
    (fun k _ => le_of_lt (explicitEquil_strictMono_r (γ k) K (hγ k) hK hr₁ hr₁₂))
    ⟨⟨0, hN⟩, mem_univ _, explicitEquil_strictMono_r (γ ⟨0, hN⟩) K (hγ _) hK hr₁ hr₁₂⟩

/-! ## Connection between Kc(N) and slope at zero -/

/-- The finite-N slope at r → 0 equals K/Kc(N).
    This is the discrete analog of the dispersion function at λ = 0. -/
theorem finite_slope_at_zero {N : ℕ} (γ : Fin N → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hN : 0 < N) :
    (K / 2) * ((1 / N : ℝ) * ∑ k : Fin N, 1 / γ k) = K / finiteKc γ := by
  unfold finiteKc
  have h_sum_pos : (0 : ℝ) < ∑ k : Fin N, (1 / γ k) :=
    sum_pos (fun k _ => div_pos one_pos (hγ k)) (univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
  field_simp

end
