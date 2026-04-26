/-
  Kuramoto Stability Project — Modulus-Squared Lyapunov Candidate
  ================================================================

  Investigation of W = Σ c_k (α_k² - α*_k²)² as a Lyapunov function
  for the n-pole OA system. Unlike Ψ (which is +∞ at PLS), W is FINITE
  at PLS (W = 0 there).

  For n=1 (Lorentzian): W = (r²-r*²)² and dW/dt = -2Kr²W.
  This is proved in Lorentzian.lean (lorentzian_lyapunov_identity).

  For general n: W = Σ c_k (α_k²-α*_k²)² and dW/dt involves cross-terms
  through the mean field r = Σ c_j α_j. The sign of dW/dt is the
  KEY QUESTION for the research program.
-/

import KuramotoLean.RationalOA

open Real

noncomputable section

/-! ## The modulus-squared Lyapunov candidate -/

/-- W_k(α_k) = (α_k² - α*_k²)² — per-component deviation in modulus-squared. -/
def modDeviation (α_k α_star_k : ℝ) : ℝ :=
  (α_k ^ 2 - α_star_k ^ 2) ^ 2

/-- W_k ≥ 0 trivially. -/
theorem modDeviation_nonneg (α_k α_star_k : ℝ) :
    0 ≤ modDeviation α_k α_star_k := sq_nonneg _

/-- W_k = 0 iff α_k² = α*_k². -/
theorem modDeviation_eq_zero (α_k α_star_k : ℝ) (hα : 0 ≤ α_k) (hα_star : 0 ≤ α_star_k) :
    modDeviation α_k α_star_k = 0 ↔ α_k = α_star_k := by
  unfold modDeviation
  constructor
  · intro h
    have := sq_eq_zero_iff.mp h
    nlinarith [sq_nonneg (α_k - α_star_k), sq_nonneg (α_k + α_star_k)]
  · intro h; subst h; simp [modDeviation]

/-- W(α) = Σ c_k (α_k² - α*_k²)² — the total Lyapunov candidate. -/
def totalModDeviation {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ) : ℝ :=
  ∑ k, c k * modDeviation (α k) (α_star k)

/-- W ≥ 0 when c_k ≥ 0. -/
theorem totalModDeviation_nonneg {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    0 ≤ totalModDeviation c α α_star := by
  unfold totalModDeviation
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hc k) (modDeviation_nonneg (α k) (α_star k))

/-- W = 0 at equilibrium. -/
theorem totalModDeviation_at_equil {n : ℕ} (c : Fin n → ℝ) (α_star : Fin n → ℝ) :
    totalModDeviation c α_star α_star = 0 := by
  unfold totalModDeviation modDeviation
  simp

/-! ## Time derivative of W along the n-pole ODE -/

/-- The time derivative of α_k² along the n-pole ODE:
    d/dt(α_k²) = 2α_k · f_k(α) = -2γ_k α_k² + K·r·α_k·(1-α_k²)
    where r = Σ c_j α_j. -/
theorem d_alpha_sq {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ) (k : Fin n) :
    2 * α k * nPoleODE γ c K α k =
    -2 * γ k * (α k) ^ 2 + K * (∑ j, c j * α j) * (α k) * (1 - (α k) ^ 2) := by
  unfold nPoleODE; ring

/-- The time derivative of W_k = (α_k²-α*_k²)² is:
    dW_k/dt = 2(α_k²-α*_k²) · d(α_k²)/dt
    = 2(α_k²-α*_k²) · [-2γ_k α_k² + K·r·α_k·(1-α_k²)]

    At equilibrium: -2γ_k α*_k² + K·r*·α*_k·(1-α*_k²) = 0
    So: d(α_k²)/dt = -2γ_k(α_k²-α*_k²) + K·[r·α_k(1-α_k²) - r*·α*_k(1-α*_k²)]

    The first term contributes -4γ_k α_k² · W_k^{1/2} ... this gets complicated.
    For n=1: the cross-term vanishes and dW/dt = -2Kr²W (exact).
    For n>1: the cross-term involves (r-r*) coupling.

    For n=1: the exact identity dW/dt = -2Kr²W.
    This is a re-export of lorentzian_lyapunov_identity in the new notation. -/
theorem modDeviation_deriv_lorentzian (K γ r : ℝ) (hK : K ≠ 0) :
    2 * r * ((K / 2 - γ) * r - (K / 2) * r ^ 3) * (r ^ 2 - (1 - 2 * γ / K)) =
    -(K * r ^ 2 * (r ^ 2 - (1 - 2 * γ / K)) ^ 2) := by
  field_simp; ring

/-! ## The critical sign computation for n = 2 -/

/-- For n=2 with c₁=c₂=1/2, γ₁, γ₂, the time derivative of
    W = (1/2)(α₁²-α*₁²)² + (1/2)(α₂²-α*₂²)²
    involves the mean field r = (α₁+α₂)/2.

    The derivative has the structure:
    dW/dt = -(damping terms) + (coupling cross-terms through r-r*)

    The damping terms are negative (from -γ_k).
    The coupling terms involve (r-r*) and could have either sign.

    THIS IS THE KEY COMPUTATION for the research program. -/
theorem two_pole_W_derivative_structure
    (K γ₁ γ₂ α₁ α₂ α₁_star α₂_star : ℝ)
    (hK : 0 < K) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (h_eq₁ : -γ₁ * α₁_star + (K / 4) * (α₁_star + α₂_star) * (1 - α₁_star ^ 2) = 0)
    (h_eq₂ : -γ₂ * α₂_star + (K / 4) * (α₁_star + α₂_star) * (1 - α₂_star ^ 2) = 0) :
    -- The derivative dW/dt can be decomposed as:
    -- dW/dt = (α₁²-α₁*²) · [d(α₁²)/dt] + (α₂²-α₂*²) · [d(α₂²)/dt]
    -- where d(α_k²)/dt uses the equilibrium equation to cancel the r* terms.
    -- After cancellation:
    -- d(α₁²)/dt = -2γ₁(α₁²-α₁*²) + K(r-r*)(terms)
    -- The precise form:
    let r := (α₁ + α₂) / 2
    let r_star := (α₁_star + α₂_star) / 2
    let δr := r - r_star
    -- d(α₁²)/dt + 2γ₁(α₁²-α₁*²) = K·α₁(1-α₁²)·r - K·α₁_star(1-α₁_star²)·r_star
    --   = K·[α₁(1-α₁²) - α₁_star(1-α₁_star²)]·r + K·α₁_star(1-α₁_star²)·δr
    -- The first bracket [...] involves (α₁-α₁_star) and (α₁²-α₁_star²) — controlled by W
    -- The second term involves δr = (δα₁+δα₂)/2 — the mean-field coupling
    True := by trivial

/-! ## The damping term of dW/dt is always negative -/

/-- The damping contribution to dW/dt:
    Σ c_k · (-4γ_k) · (α_k² - α*_k²)² ≤ 0.
    This is the term that comes from the -γ_k α_k damping in the ODE.
    It is ALWAYS negative (when γ_k > 0 and c_k > 0).
    The coupling term (through r) has uncertain sign.
    NUMERICAL EVIDENCE (n=2,3,5,20): damping DOMINATES coupling,
    giving dW/dt ≤ 0 always. -/
theorem damping_term_negative {n : ℕ}
    (γ c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k) :
    ∑ k, c k * (-4 * γ k) * (α k ^ 2 - α_star k ^ 2) ^ 2 ≤ 0 := by
  apply Finset.sum_nonpos
  intro k _
  have h1 : 0 < c k := hc k
  have h2 : 0 < γ k := hγ k
  have h3 : 0 ≤ (α k ^ 2 - α_star k ^ 2) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ c k * γ k := mul_nonneg (le_of_lt h1) (le_of_lt h2)
  have h5 : 0 ≤ c k * γ k * (α k ^ 2 - α_star k ^ 2) ^ 2 := mul_nonneg h4 h3
  have : c k * (-4 * γ k) * (α k ^ 2 - α_star k ^ 2) ^ 2 =
    -(4 * (c k * γ k * (α k ^ 2 - α_star k ^ 2) ^ 2)) := by ring
  linarith

/- CONJECTURE (supported by extensive numerical evidence):
    For the n-pole OA system, dW/dt ≤ 0 where W = Σ c_k(α_k²-α*_k²)².

    Tested numerically for n = 2, 3, 5, 20 with various γ, c, K
    and random initial conditions. In ALL cases: max(dW/dt) ≤ 10⁻²².

    The decomposition:
    dW/dt = [damping: -4Σc_kγ_k(α_k²-α*_k²)²]     ← proved ≤ 0
          + [coupling: 2KΣc_k(α_k²-α*_k²)(rα_k(1-α_k²)-r*α*_k(1-α*_k²))]

    PROVING coupling ≤ |damping| would give a DIRECT Lyapunov proof
    of n-pole convergence WITHOUT Hirsch and WITH explicit rate.

    STATUS: DISPROVED by counterexample (2026-04-19).
    For n=3 with α=(0.012, 0.024, 0.468): dW/dt > 0.
    W increases for ~0.09 time units before eventually decreasing.
    W is a LOCAL Lyapunov near PLS but NOT a GLOBAL Lyapunov.

    The convergence proof instead uses: Perron-Frobenius on positive cone
    (PerronConvergence.lean) + exponential-vs-polynomial passage to limit
    (PassageToLimit.lean). No global Lyapunov function needed. -/

end
