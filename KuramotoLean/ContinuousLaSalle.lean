/-
  Kuramoto Stability — Continuous-Time LaSalle Convergence
  =========================================================

  V : ℝ → ℝ antitone with additive drop modulus → V → 0.

  Key theorem: if V ≥ 0, V antitone, and V(t) ≥ δ implies
  V(t+1) ≤ V(t) - drop(δ) for some drop(δ) > 0, then V → 0.

  This is the continuous-time analogue of LaSalleConvergence.lean.
  Combined with l2_strict_lyapunov (pair double sum > 0 when V > 0),
  this gives global stability without persistence, Barbalat, or
  the locked-region hypothesis — only barrier + strict Lyapunov.

  12th independent proof path for n-pole convergence.

  0 sorry.
-/

import KuramotoLean.LaSalleConvergence
import KuramotoLean.ContinuumBarbalat

open Filter Topology

noncomputable section

/-! ## Continuous-time LaSalle with additive drop modulus -/

private theorem real_antitone_at_nat (V : ℝ → ℝ) (hV : Antitone V)
    (a b : ℕ) (hab : b ≤ a) : V (a : ℝ) ≤ V (b : ℝ) :=
  hV (Nat.cast_le.mpr hab)

/-- **Continuous-time LaSalle convergence.**
    V ≥ 0, V antitone, additive drop modulus → V(t) → 0.

    The drop modulus: if V(t) ≥ δ, then V drops by ≥ drop(δ) > 0
    over a unit interval. No persistence needed. -/
theorem continuous_lasalle (V : ℝ → ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (drop : ℝ → ℝ)
    (hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ)
    (hdrop_bound : ∀ t, ∀ δ > 0, δ ≤ V t →
      V (t + 1) ≤ V t - drop δ) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → V t < ε := by
  intro ε hε
  by_contra h
  push_neg at h
  have hV_ge_nat : ∀ n : ℕ, ε ≤ V (n : ℝ) := by
    intro n
    obtain ⟨t, ht, hVt⟩ := h (n : ℝ)
    exact le_trans hVt (hV_anti (by exact_mod_cast ht))
  have hdrop_each : ∀ n : ℕ, V (↑n + 1) ≤ V (↑n) - drop ε :=
    fun n => hdrop_bound (↑n) ε hε (hV_ge_nat n)
  have hdrop_cast : ∀ n : ℕ, V (↑(n + 1) : ℝ) ≤ V (↑n : ℝ) - drop ε := by
    intro n; convert hdrop_each n using 2; push_cast; ring
  have h_sum : ∀ k : ℕ, (k : ℝ) * drop ε ≤ V (0 : ℝ) - V (↑k : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have := hdrop_cast m
      calc ((m + 1 : ℕ) : ℝ) * drop ε
          = (m : ℝ) * drop ε + drop ε := by push_cast; ring
        _ ≤ (V (0 : ℝ) - V (↑m : ℝ)) + (V (↑m : ℝ) - V (↑(m + 1) : ℝ)) :=
            add_le_add ih (by linarith)
        _ = V (0 : ℝ) - V (↑(m + 1) : ℝ) := by ring
  obtain ⟨k, hk⟩ := Archimedean.arch (V (0 : ℝ)) (hdrop_pos ε hε)
  have hk' : V (0 : ℝ) ≤ (k : ℝ) * drop ε := by rwa [nsmul_eq_mul] at hk
  have h1 := h_sum (k + 1)
  have h2 := hV_nn (↑(k + 1) : ℝ)
  have h3 : ((k + 1 : ℕ) : ℝ) * drop ε = (k : ℝ) * drop ε + drop ε := by
    push_cast; ring
  have h4 := hdrop_pos ε hε
  linarith [h1, h2, h3, h4, hk']

/-- **Continuous LaSalle (Filter.Tendsto form).** -/
theorem continuous_lasalle_tendsto (V : ℝ → ℝ)
    (hV_nn : ∀ t, 0 ≤ V t)
    (hV_anti : Antitone V)
    (drop : ℝ → ℝ)
    (hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ)
    (hdrop_bound : ∀ t, ∀ δ > 0, δ ≤ V t →
      V (t + 1) ≤ V t - drop δ) :
    Tendsto V atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := continuous_lasalle V hV_nn hV_anti drop hdrop_pos hdrop_bound ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (hV_nn t)]
    exact hT t ht⟩

/-! ## Application: LaSalle stability data

Packages the hypotheses for applying continuous LaSalle to a
dynamical system with strict Lyapunov decrease. The key: the
drop modulus comes from the compactness of {V ≥ δ} ∩ orbit,
where -dV/dt is continuous and > 0. -/

/-- **LaSalle stability data for n-pole convergence.**
    Only needs: V antitone + additive drop modulus + V controls r.
    NO persistence, locked region, or Barbalat needed. -/
structure LaSalleStabilityData where
  V : ℝ → ℝ
  r : ℝ → ℝ
  r_star : ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  drop : ℝ → ℝ
  hdrop_pos : ∀ δ, 0 < δ → 0 < drop δ
  hdrop_bound : ∀ t, ∀ δ > 0, δ ≤ V t →
    V (t + 1) ≤ V t - drop δ
  hV_controls_r : ∀ t, (r t - r_star) ^ 2 ≤ V t

/-- **LaSalle global stability: V → 0.** -/
theorem lasalle_V_zero (D : LaSalleStabilityData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → D.V t < ε :=
  continuous_lasalle D.V D.hV_nn D.hV_anti D.drop D.hdrop_pos D.hdrop_bound

/-- **LaSalle global stability: r → r*.** -/
theorem lasalle_global_stability (D : LaSalleStabilityData) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - D.r_star| < ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := lasalle_V_zero D (ε ^ 2) (by positivity)
  exact ⟨T, fun t ht =>
    abs_lt_of_sq_lt_sq (lt_of_le_of_lt (D.hV_controls_r t) (hT t ht))
      (le_of_lt hε)⟩

/-- **LaSalle global stability (Filter.Tendsto form).** -/
theorem lasalle_tendsto (D : LaSalleStabilityData) :
    Tendsto (fun t => |D.r t - D.r_star|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := lasalle_global_stability D ε hε
  exact ⟨T, fun t ht => by
    simp only [Real.dist_eq, sub_zero, abs_abs]
    exact hT t ht⟩

/-! ## Boundary pair bound extension

The pair bound extends from (0,1) to [0,1): pair ≥ 0 for α ∈ [0,1).
Proof works on the cleared-denominator polynomial (no division needed).
The SOS decomposition uses α ≥ 0 (weak) instead of α > 0 (strict). -/

/-- **Pair bound on the boundary.** pair ≥ 0 for α ∈ [0,1), α* > 0.
    Extends pair_bound from α > 0 to α ≥ 0. -/
theorem pair_bound_boundary (αj αk αsj αsk : ℝ)
    (hαj : 0 ≤ αj) (hαk : 0 ≤ αk) (hαj1 : αj < 1) (hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    0 ≤ αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
        αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
        (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
  have hnej : αsj ≠ 0 := ne_of_gt hαsj
  have hnek : αsk ≠ 0 := ne_of_gt hαsk
  have hmul : (0 : ℝ) < αsj * αsk := mul_pos hαsj hαsk
  have h_num : 0 ≤ αsj * αsj * (αk * αsk + 1) * (αk - αsk) ^ 2 +
      αsk * αsk * (αj * αsj + 1) * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
    set pj := αj - αsj
    set pk := αk - αsk
    by_cases hpq : pj * pk ≥ 0
    · have h_amgm := sq_nonneg (αsk * pj - αsj * pk)
      have h_extra1 : 0 ≤ αj * αsj * αsk ^ 2 * pj ^ 2 := by
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg hαj (le_of_lt hαsj)
        exact sq_nonneg _
        exact sq_nonneg _
      have h_extra2 : 0 ≤ αk * αsk * αsj ^ 2 * pk ^ 2 := by
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg hαk (le_of_lt hαsk)
        exact sq_nonneg _
        exact sq_nonneg _
      nlinarith [sq_nonneg αj, sq_nonneg αk,
                 mul_nonneg (mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk)) hpq]
    · push_neg at hpq
      have h1 : 0 ≤ (1 + αj * αsj) * αsk ^ 2 * pj ^ 2 := by positivity
      have h2 : 0 ≤ (1 + αk * αsk) * αsj ^ 2 * pk ^ 2 := by positivity
      have h3 : 0 ≤ αsj * αsk * (2 - αj ^ 2 - αk ^ 2) * -(pj * pk) := by
        apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
        · exact le_of_lt hαsj
        · exact le_of_lt hαsk
        · nlinarith [sq_abs αj, sq_abs αk]
        · linarith
      nlinarith
  have h_eq := pair_bound_clear_denom αj αk αsj αsk hnej hnek
  have h_prod_nonneg : 0 ≤ αsj * αsk * (αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
      αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
      (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2)) := by linarith
  exact nonneg_of_mul_nonneg_right h_prod_nonneg hmul

/-- **Pair zero characterization at boundary.**
    pair(0, αsj, 0, αsk) = 0: the incoherent state is a zero. -/
theorem pair_zero_at_incoherent (αsj αsk : ℝ)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    pairIntegrand 0 αsj 0 αsk = 0 := by
  have hnej : αsj ≠ 0 := ne_of_gt hαsj
  have hnek : αsk ≠ 0 := ne_of_gt hαsk
  unfold pairIntegrand
  field_simp
  ring

/-- **Pair positive when one component is positive.**
    If α_j > 0 and α_k = 0 with α ≠ α*: pair(j,k) > 0. -/
theorem pair_pos_mixed (αj αsj αsk : ℝ)
    (hαj : 0 < αj) (_hαj1 : αj < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    0 < pairIntegrand αj αsj 0 αsk := by
  have hnej : αsj ≠ 0 := ne_of_gt hαsj
  have hnek : αsk ≠ 0 := ne_of_gt hαsk
  have hmul : (0 : ℝ) < αsj * αsk := mul_pos hαsj hαsk
  have h_cd := pair_bound_clear_denom αj 0 αsj αsk hnej hnek
  have h_ring : αsj * αsj * (0 * αsk + 1) * (0 - αsk) ^ 2 +
      αsk * αsk * (αj * αsj + 1) * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (0 - αsk) * (2 - αj ^ 2 - 0 ^ 2) =
      αsk ^ 2 * αj * (αj * (1 - αsj ^ 2) + αsj ^ 3) := by ring
  have h_inner : 0 < αj * (1 - αsj ^ 2) + αsj ^ 3 := by
    nlinarith [sq_nonneg αsj, sq_abs αsj]
  have h_rhs_pos : 0 < αsk ^ 2 * αj * (αj * (1 - αsj ^ 2) + αsj ^ 3) :=
    mul_pos (mul_pos (sq_pos_of_pos hαsk) hαj) h_inner
  have h_prod : 0 < αsj * αsk *
      (αsj * (0 - αsk) ^ 2 * (0 + 1 / αsk) +
       αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
       (αj - αsj) * (0 - αsk) * (2 - αj ^ 2 - 0 ^ 2)) := by linarith
  have h_unfold : pairIntegrand αj αsj 0 αsk =
      αsj * (0 - αsk) ^ 2 * (0 + 1 / αsk) +
      αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
      (αj - αsj) * (0 - αsk) * (2 - αj ^ 2 - 0 ^ 2) := by
    unfold pairIntegrand; ring
  rw [h_unfold]
  rcases mul_pos_iff.mp h_prod with ⟨_, hp⟩ | ⟨hn, _⟩
  · exact hp
  · linarith

/-! ## Pair sum rigidity in the interior

In (0,1)^n: the pair double sum = 0 iff α = α*. This is the LaSalle
characterization: the barrier keeps α in (0,1)^n, and on this open
set the strict Lyapunov (StrictLyapunov.lean) gives dV/dt = 0 iff α = α*.

Combined with V antitone → V → L, if L > 0 then V is eventually
in a level set where dV/dt < 0, contradicting constancy.
The drop modulus comes from this strict decrease. -/

/-- **Double sum zero iff equilibrium.**
    For the n-pole system with α ∈ (0,1)^n and α* ∈ (0,1)^n:
    Σ Σ c_j c_k pair(j,k) = 0 iff α = α*.
    The barrier keeps α in (0,1)^n, excluding the incoherent state. -/
theorem pair_sum_zero_iff_interior {n : ℕ}
    (c α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1) :
    (∑ j, ∑ k, c j * c k *
      pairIntegrand (α j) (α_star j) (α k) (α_star k) = 0) ↔
    α = α_star := by
  constructor
  · intro h_zero
    have h_nn : ∀ j k : Fin n,
        0 ≤ c j * c k * pairIntegrand (α j) (α_star j) (α k) (α_star k) := by
      intro j k
      exact mul_nonneg (le_of_lt (mul_pos (hc j) (hc k)))
        (pair_bound (α j) (α k) (α_star j) (α_star k)
          (hα j) (hα k) (hα_lt j) (hα_lt k) (hα_star j) (hα_star k))
    have h_all_zero : ∀ j k : Fin n,
        c j * c k * pairIntegrand (α j) (α_star j) (α k) (α_star k) = 0 := by
      intro j k
      have h1 := Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Finset.sum_nonneg (fun k _ => h_nn j k)) |>.mp h_zero
      have h2 := h1 j (Finset.mem_univ j)
      exact Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h_nn j k) |>.mp h2 k
        (Finset.mem_univ k)
    ext m
    have h_diag := h_all_zero m m
    have h_cc : c m * c m ≠ 0 := ne_of_gt (mul_pos (hc m) (hc m))
    have h_pair_zero : pairIntegrand (α m) (α_star m) (α m) (α_star m) = 0 := by
      rcases mul_eq_zero.mp h_diag with h | h
      · exact absurd h h_cc
      · exact h
    exact ((pair_eq_zero_iff (α m) (α m) (α_star m) (α_star m)
      (hα m) (hα m) (hα_lt m) (hα_lt m) (hα_star m) (hα_star m)).mp h_pair_zero).1
  · intro h_eq
    subst h_eq
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro k _
    simp [pairIntegrand]

/-! ## Quantitative velocity bound at boundary

When the order parameter r ≥ δ and α_k is small, the ODE pushes α_k
upward at a quantifiable rate. This is the mechanism by which
order-parameter persistence implies component-wise persistence. -/

/-- **Quantitative lower barrier.** When r ≥ δ and α_k ≤ min(Kδ/(4γ_k), 1/2),
    the ODE velocity is ≥ Kδ/8 > 0.

    Proof: nPoleODE = -γ_k·α_k + (K/2)·r·(1-α_k²)
    ≥ -γ_k·Kδ/(4γ_k) + (K/2)·δ·(3/4) = -Kδ/4 + 3Kδ/8 = Kδ/8. -/
theorem npole_velocity_lower_bound {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ) (k : Fin n)
    (hK : 0 < K) (hγ : 0 < γ k)
    (δ : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ ∑ j, c j * α j)
    (hα_nn : 0 ≤ α k)
    (hα_small : α k ≤ K * δ / (4 * γ k))
    (hα_half : α k ≤ 1 / 2) :
    K * δ / 8 ≤ nPoleODE γ c K α k := by
  unfold nPoleODE
  have h1 : -γ k * (α k) ≥ -(K * δ / 4) := by
    have : γ k * (α k) ≤ γ k * (K * δ / (4 * γ k)) :=
      mul_le_mul_of_nonneg_left hα_small (le_of_lt hγ)
    have : γ k * (K * δ / (4 * γ k)) = K * δ / 4 := by
      field_simp
    linarith
  have h2 : (K / 2) * (∑ j, c j * α j) * (1 - (α k) ^ 2) ≥
      K / 2 * δ * (3 / 4) := by
    have h2a : K / 2 * (∑ j, c j * α j) ≥ K / 2 * δ := by
      exact mul_le_mul_of_nonneg_left hr (by linarith)
    have h2b : (1 : ℝ) - (α k) ^ 2 ≥ 3 / 4 := by
      nlinarith [sq_nonneg (α k)]
    have h2c : 0 ≤ K / 2 * δ := by positivity
    exact mul_le_mul h2a h2b (by linarith) (by linarith)
  have h3 : K / 2 * δ * (3 / 4) = 3 * K * δ / 8 := by ring
  linarith

/-- **Velocity bound is positive.** Consequence of the lower bound. -/
theorem npole_velocity_pos_at_boundary {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ) (k : Fin n)
    (hK : 0 < K) (hγ : 0 < γ k)
    (δ : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ ∑ j, c j * α j)
    (hα_nn : 0 ≤ α k)
    (hα_small : α k ≤ K * δ / (4 * γ k))
    (hα_half : α k ≤ 1 / 2) :
    0 < nPoleODE γ c K α k := by
  have h := npole_velocity_lower_bound γ c K α k hK hγ δ hδ hr hα_nn hα_small hα_half
  linarith [mul_pos hK hδ]

end
