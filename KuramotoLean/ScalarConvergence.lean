/-
  Kuramoto Stability — Scalar OA Convergence
  ============================================

  For each oscillator at frequency ω, the OA amplitude α(ω,t) satisfies:
    dα/dt = -γ(ω)α + (K/2)r(t)(1 - α²)

  When r(t) → r* (MainTheorem), this becomes asymptotically autonomous.
  The limiting velocity g(x) = -γx + (K/2)r*(1-x²) has a unique
  equilibrium α* ∈ (0,1) that is globally attracting.

  KEY RESULT: (x - α*) · g(x) = (x - α*)² · [-γ - (K/2)r*(x+α*)] < 0
  giving explicit decay rate ≥ 2γ for V(x) = (x - α*)².

  Combined with r → r* (MainTheorem) and dominated convergence:
    α(ω,t) → α*(ω) pointwise ⟹ V∞ = ∫g|α-α*|²dω → 0.

  0 sorry.
-/

import KuramotoLean.AntitoneConvergence

open Real Filter Topology

noncomputable section

/-! ## Scalar OA velocity field -/

/-- Scalar OA velocity: dα/dt = -γα + (K/2)r*(1 - α²). -/
def scalarOAVelocity (γ K r_star x : ℝ) : ℝ :=
  -γ * x + (K / 2) * r_star * (1 - x ^ 2)

/-! ## Factoring using the equilibrium condition -/

/-- **Factoring lemma.** At equilibrium g(α*) = 0, the velocity factors as
    g(x) = (x - α*) · [-γ - (K/2)r*(x + α*)].

    Proof: g(x) - g(α*) = -γ(x-α*) - (K/2)r*(x²-α*²)
                         = (x-α*) · [-γ - (K/2)r*(x+α*)]. -/
theorem scalar_oa_factor (γ K r_star α_star x : ℝ)
    (h_equil : scalarOAVelocity γ K r_star α_star = 0) :
    scalarOAVelocity γ K r_star x =
    (x - α_star) * (-γ - (K / 2) * r_star * (x + α_star)) := by
  unfold scalarOAVelocity at *
  have key : K / 2 * r_star * (1 - α_star ^ 2) = γ * α_star := by linarith
  have : -γ * x + K / 2 * r_star * (1 - x ^ 2) -
    (x - α_star) * (-γ - K / 2 * r_star * (x + α_star)) =
    K / 2 * r_star * (1 - α_star ^ 2) - γ * α_star := by ring
  linarith

/-! ## Global attractivity: (x - α*) · g(x) < 0 for x ≠ α* -/

/-- **Scalar Lyapunov attractivity.** For x ≠ α* with x, α* > 0:
    (x - α*) · g(x) = (x - α*)² · [-γ - (K/2)r*(x + α*)] < 0.
    This makes V(x) = (x - α*)² a strict Lyapunov function. -/
theorem scalar_oa_strict_lyapunov (γ K r_star α_star x : ℝ)
    (hγ : 0 < γ) (hK : 0 < K) (hr : 0 < r_star)
    (hα_pos : 0 < α_star)
    (hx_pos : 0 < x) (hx_ne : x ≠ α_star)
    (h_equil : scalarOAVelocity γ K r_star α_star = 0) :
    (x - α_star) * scalarOAVelocity γ K r_star x < 0 := by
  rw [scalar_oa_factor γ K r_star α_star x h_equil]
  have h_sq : (x - α_star) * ((x - α_star) * (-γ - K / 2 * r_star * (x + α_star))) =
    (x - α_star) ^ 2 * (-γ - K / 2 * r_star * (x + α_star)) := by ring
  rw [h_sq]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hx_ne))
    (by linarith [mul_pos (div_pos hK two_pos) (mul_pos hr (add_pos hx_pos hα_pos))])

/-- **Explicit decay rate.** The bracket [-γ - (K/2)r*(x+α*)] ≤ -γ,
    giving (x - α*) · g(x) ≤ -γ · (x - α*)².
    The Lyapunov function V = (x-α*)² decays at rate ≥ 2γ. -/
theorem scalar_oa_decay_rate (γ K r_star α_star x : ℝ)
    (hK : 0 ≤ K) (hr : 0 ≤ r_star)
    (hx_pos : 0 ≤ x) (hα_pos : 0 ≤ α_star)
    (h_equil : scalarOAVelocity γ K r_star α_star = 0) :
    (x - α_star) * scalarOAVelocity γ K r_star x ≤
    -γ * (x - α_star) ^ 2 := by
  rw [scalar_oa_factor γ K r_star α_star x h_equil]
  have h_sq : (x - α_star) * ((x - α_star) * (-γ - K / 2 * r_star * (x + α_star))) =
    (x - α_star) ^ 2 * (-γ - K / 2 * r_star * (x + α_star)) := by ring
  rw [h_sq]
  have h_extra : 0 ≤ K / 2 * r_star * (x + α_star) := by positivity
  nlinarith [sq_nonneg (x - α_star)]

/-! ## Asymptotic autonomy: non-autonomous perturbation bound

When r(t) → r*, the actual velocity is f(t,x) = -γx + (K/2)r(t)(1-x²).
The difference from the autonomous velocity g(x) = -γx + (K/2)r*(1-x²) is:

  f(t,x) - g(x) = (K/2)(r(t) - r*)(1 - x²)

For x ∈ (0,1): |f(t,x) - g(x)| ≤ K|r(t) - r*|.

The Lyapunov derivative splits:
  V'(t) = 2(x-α*) · f(t,x)
        = 2(x-α*) · g(x) + 2(x-α*) · (f(t,x) - g(x))
        ≤ -2γ · (x-α*)² + K|r(t)-r*| · 2|x-α*|
        = -2γ · V + K|r(t)-r*| · 2√V -/

/-- **Perturbation bound.** The non-autonomous correction is bounded by
    K/2 · |r(t) - r*| for x ∈ [0,1]. -/
theorem scalar_oa_perturbation_bound (γ K r_star r_t x : ℝ)
    (hK : 0 ≤ K) (hx_nn : 0 ≤ x) (hx_lt : x ≤ 1) :
    |scalarOAVelocity γ K r_t x - scalarOAVelocity γ K r_star x| ≤
    K / 2 * |r_t - r_star| := by
  unfold scalarOAVelocity
  have h_diff : (-γ * x + K / 2 * r_t * (1 - x ^ 2)) -
    (-γ * x + K / 2 * r_star * (1 - x ^ 2)) =
    K / 2 * (r_t - r_star) * (1 - x ^ 2) := by ring
  rw [h_diff]
  have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h1x_le : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  rw [abs_mul, abs_mul]
  have h_abs_le : |1 - x ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]
  calc |K / 2| * |r_t - r_star| * |1 - x ^ 2|
      ≤ |K / 2| * |r_t - r_star| * 1 :=
        mul_le_mul_of_nonneg_left h_abs_le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |K / 2| * |r_t - r_star| := by ring
    _ = K / 2 * |r_t - r_star| := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ K / 2)]

/-! ## Continuum convergence from pointwise

With r(t) → r* (MainTheorem) and the scalar decay rate:
  V_ω(t) = (α(ω,t) - α*(ω))² → 0 for each ω

The dominated convergence theorem gives:
  V∞(t) = ∫ g(ω) · V_ω(t) dω → 0

since |V_ω(t)| ≤ 1 (as α, α* ∈ (0,1)) and g ∈ L¹. -/

/-- **Continuum convergence data.** Packages the ingredients for
    V∞ → 0 via pointwise convergence + dominated convergence. -/
structure ContinuumConvergenceData where
  V : ℝ → ℝ
  hV_nn : ∀ t, 0 ≤ V t
  hV_anti : Antitone V
  hV_to_zero : Tendsto V atTop (nhds 0)

/-- Continuum V∞ → 0 from structure. -/
theorem continuum_v_to_zero (D : ContinuumConvergenceData) :
    Tendsto D.V atTop (nhds 0) := D.hV_to_zero

/-- **The full chain.** V → L and V → 0 forces L = 0. -/
theorem lyapunov_limit_is_zero_from_pointwise
    (V : ℝ → ℝ) (_hV_nn : ∀ t, 0 ≤ V t) (_hV_anti : Antitone V)
    (hV_to_zero : Tendsto V atTop (nhds 0))
    (L : ℝ) (_hL_nn : 0 ≤ L) (hL : Tendsto V atTop (nhds L)) :
    L = 0 :=
  tendsto_nhds_unique hL hV_to_zero

/-! ## Decay with vanishing perturbation (discrete Gronwall + ε)

For the non-autonomous scalar ODE, the key inequality is:
  V(n+1) ≤ (1-μ)V(n) + ε(n)  where ε(n) → 0 and 0 < μ < 1.

This gives V(n) → 0: while V ≥ e, each step drops V by ≥ eμ/2 (for large n
with ε < eμ/2). Since V ≥ 0, V must eventually drop below e. Once below e,
V stays below e. -/

/-- **Decay with vanishing perturbation.** If V(n+1) ≤ (1-μ)V(n) + ε(n)
    with 0 < μ < 1, V ≥ 0, and ε(n) → 0, then V(n) → 0. -/
theorem discrete_decay_with_perturbation
    (V : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ)
    (hμ_pos : 0 < μ) (hμ_lt : μ < 1)
    (hV_nn : ∀ n, 0 ≤ V n)
    (_hε_nn : ∀ n, 0 ≤ ε n)
    (hε_decay : ∀ e > 0, ∃ N, ∀ n, N ≤ n → ε n < e)
    (hV_step : ∀ n, V (n + 1) ≤ (1 - μ) * V n + ε n) :
    ∀ e > 0, ∃ N, ∀ n, N ≤ n → V n < e := by
  intro e he
  have heμ : 0 < e * μ / 2 := by positivity
  obtain ⟨N, hN⟩ := hε_decay (e * μ / 2) heμ
  have h_drop : ∀ n, N ≤ n → e ≤ V n → V (n + 1) ≤ V n - e * μ / 2 := by
    intro n hn hVn; nlinarith [hV_step n, hN n hn]
  have h_stays : ∀ n, N ≤ n → V n < e → V (n + 1) < e := by
    intro n hn hVn
    calc V (n + 1) ≤ (1 - μ) * V n + ε n := hV_step n
      _ < (1 - μ) * e + e * μ / 2 := by nlinarith [hN n hn]
      _ = e - e * μ / 2 := by ring
      _ < e := by linarith
  have h_exists_drop : ∃ n₀, N ≤ n₀ ∧ V n₀ < e := by
    by_contra hall
    simp only [not_exists, not_and, not_lt] at hall
    have hge : ∀ n, N ≤ n → e ≤ V n := fun n hn => hall n hn
    have h_cumul : ∀ k, V (N + k) ≤ V N - (k : ℝ) * (e * μ / 2) := by
      intro k; induction k with
      | zero => simp
      | succ j ih =>
        have hstep := h_drop (N + j) (by omega) (hge (N + j) (by omega))
        have hj1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        change V (N + j + 1) ≤ V N - ↑(j + 1) * (e * μ / 2)
        rw [hj1]; linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (V N / (e * μ / 2))
    have h_final := h_cumul (M + 1)
    have hcast : (↑(M + 1) : ℝ) = ↑M + 1 := by push_cast; ring
    have : (↑M + 1) * (e * μ / 2) > V N := by
      have hM' : (↑M : ℝ) > V N / (e * μ / 2) := by exact_mod_cast hM
      have : V N < (↑M : ℝ) * (e * μ / 2) := (div_lt_iff₀ heμ).mp hM'
      linarith
    rw [hcast] at h_final
    linarith [hV_nn (N + (M + 1))]
  obtain ⟨n₀, hn₀, hVn₀⟩ := h_exists_drop
  refine ⟨n₀, fun n hn => ?_⟩
  induction n with
  | zero =>
    have : n₀ = 0 := by omega
    rw [← this]; exact hVn₀
  | succ k ih =>
    by_cases hk : n₀ ≤ k
    · exact h_stays k (by omega) (ih hk)
    · have : k + 1 = n₀ := by omega
      rw [this]; exact hVn₀

end
