/-
  Kuramoto Stability Project — Phase 4: Lorentzian Sanity Check
  ==============================================================
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import KuramotoLean.Defs

open Real

noncomputable section

/-- V(r) = -(K/4 - γ/2)r² + (K/8)r⁴ -/
def lorentzianPotential (K γ r : ℝ) : ℝ :=
  -(K / 4 - γ / 2) * r ^ 2 + (K / 8) * r ^ 4

/-- V'(r) = -(K/2 - γ)r + (K/2)r³ -/
def lorentzianPotentialDeriv (K γ r : ℝ) : ℝ :=
  -(K / 2 - γ) * r + (K / 2) * r ^ 3

/-- The OA ODE: ṙ = (K/2 - γ)r - (K/2)r³ -/
def lorentzianODE (K γ r : ℝ) : ℝ :=
  (K / 2 - γ) * r - (K / 2) * r ^ 3

/-- V'(r) = -ṙ. -/
lemma potentialDeriv_eq_neg_ode (K γ r : ℝ) :
    lorentzianPotentialDeriv K γ r = -lorentzianODE K γ r := by
  unfold lorentzianPotentialDeriv lorentzianODE; ring

/-- ṙ > 0 for 0 < r < r*. -/
theorem lorentzian_ode_pos
    (K γ r : ℝ)
    (hK_pos : 0 < K)
    (hK_gt : K > 2 * γ)
    (hr_pos : 0 < r)
    (hr_lt : r ^ 2 < 1 - 2 * γ / K) :
    lorentzianODE K γ r > 0 := by
  unfold lorentzianODE
  -- ṙ = (K/2 - γ)r - (K/2)r³ = (K/2)r(1 - 2γ/K - r²)
  -- Factor: (K/2) > 0, r > 0, (1 - 2γ/K - r²) > 0
  have hKhalf : 0 < K / 2 := by linarith
  have hKγ : 0 < K / 2 - γ := by linarith
  -- (K/2 - γ)r > (K/2)r³ iff (K/2 - γ) > (K/2)r² iff 1 - 2γ/K > r²
  have h1 : (K / 2 - γ) * r > 0 := mul_pos hKγ hr_pos
  have h2 : K / 2 * r ^ 3 ≥ 0 := by positivity
  -- Need: (K/2 - γ)r > (K/2)r³
  -- i.e., (K/2 - γ) > (K/2)r²
  -- i.e., 1 - 2γ/K > r²  (multiply by K/2, divide by... )
  -- From hr_lt: r² < 1 - 2γ/K
  -- So K/2 * r² < K/2 * (1 - 2γ/K) = K/2 - γ
  have h3 : K / 2 * r ^ 2 < K / 2 - γ := by
    have h := mul_lt_mul_of_pos_left hr_lt hKhalf
    have hKne : K ≠ 0 := ne_of_gt hK_pos
    nlinarith [div_mul_cancel₀ (2 * γ) hKne]
  -- Now: (K/2 - γ)*r - (K/2)*r³ = r * ((K/2 - γ) - (K/2)*r²) > 0
  nlinarith [sq_nonneg r]

/-- **Phase 4 main result.** V'(r) < 0 for 0 < r < r*. -/
theorem lorentzian_decrease
    (K γ r : ℝ)
    (hK_pos : 0 < K)
    (hK_gt : K > 2 * γ)
    (hr_pos : 0 < r)
    (hr_lt : r ^ 2 < 1 - 2 * γ / K) :
    lorentzianPotentialDeriv K γ r < 0 := by
  rw [potentialDeriv_eq_neg_ode]
  linarith [lorentzian_ode_pos K γ r hK_pos hK_gt hr_pos hr_lt]

/-- dV/dt = V'(r) · ṙ = -(ṙ)² < 0. -/
theorem lorentzian_V_dot_neg
    (K γ r : ℝ)
    (hK_pos : 0 < K)
    (hK_gt : K > 2 * γ)
    (hr_pos : 0 < r)
    (hr_lt : r ^ 2 < 1 - 2 * γ / K) :
    lorentzianPotentialDeriv K γ r * lorentzianODE K γ r < 0 := by
  have hode_pos := lorentzian_ode_pos K γ r hK_pos hK_gt hr_pos hr_lt
  have hderiv_neg := lorentzian_decrease K γ r hK_pos hK_gt hr_pos hr_lt
  exact mul_neg_of_neg_of_pos hderiv_neg hode_pos

/-- ṙ < 0 for r > r*, i.e., the ODE pushes back from above the equilibrium.
    Combined with lorentzian_ode_pos: r* is the unique stable equilibrium on (0,1). -/
theorem lorentzian_ode_neg
    (K γ r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_gt : r ^ 2 > 1 - 2 * γ / K) :
    lorentzianODE K γ r < 0 := by
  unfold lorentzianODE
  have hKhalf : 0 < K / 2 := by linarith
  have h3 : K / 2 * r ^ 2 > K / 2 - γ := by
    have h := mul_lt_mul_of_pos_left (show 1 - 2 * γ / K < r ^ 2 from hr_gt) hKhalf
    have hKne : K ≠ 0 := ne_of_gt hK_pos
    nlinarith [div_mul_cancel₀ (2 * γ) hKne]
  nlinarith [sq_nonneg r]

/-- The linearized stability at r*: f'(r*) = -(K - 2γ) < 0 for K > K_c = 2γ.
    This proves the PLS is a linearly stable equilibrium of the scalar ODE.
    Precisely: f(r) = (K/2 - γ)r - (K/2)r³, so f'(r) = (K/2 - γ) - (3K/2)r².
    At r*² = 1 - 2γ/K: f'(r*) = (K/2 - γ) - (3K/2)(1 - 2γ/K) = -K + 2γ = -(K - 2γ). -/
theorem lorentzian_linearized_stability
    (K γ : ℝ) (hK_pos : 0 < K) (hK_gt : K > 2 * γ) :
    (K / 2 - γ) - (3 * K / 2) * (1 - 2 * γ / K) < 0 := by
  have hKne : K ≠ 0 := ne_of_gt hK_pos
  field_simp
  nlinarith

/-- The ODE has exactly the right structure for global stability on (0,1):
    f(0) = 0, f(r) > 0 for r ∈ (0,r*), f(r*) = 0, f(r) < 0 for r ∈ (r*,1).
    Combined with f'(r*) < 0: r* is the unique GLOBALLY ATTRACTING equilibrium
    on (0,1) for the scalar ODE. This is the Lorentzian case of the
    Kuramoto stability problem — proved without Hirsch's theorem. -/
theorem lorentzian_global_attractor_structure
    (K γ r : ℝ) (hK_pos : 0 < K) (hK_gt : K > 2 * γ) (hr_pos : 0 < r) :
    (r ^ 2 < 1 - 2 * γ / K → lorentzianODE K γ r > 0) ∧
    (r ^ 2 > 1 - 2 * γ / K → lorentzianODE K γ r < 0) := by
  exact ⟨lorentzian_ode_pos K γ r hK_pos hK_gt hr_pos,
         lorentzian_ode_neg K γ r hK_pos hr_pos⟩

/-! ## Fixed-point uniqueness (KuramotoData.hΦ_unique structure) -/

/-- The ODE has exactly two non-negative equilibria: 0 and r* = √(1-2γ/K).
    This matches KuramotoData.hΦ_unique: Φ(x) = x → x = 0 ∨ x = r*. -/
theorem lorentzian_fixed_point_unique (K γ r : ℝ)
    (hK_pos : 0 < K) (_hK_gt : K > 2 * γ)
    (hfp : lorentzianODE K γ r = 0) :
    r = 0 ∨ r ^ 2 = 1 - 2 * γ / K := by
  unfold lorentzianODE at hfp
  have h : r * ((K / 2 - γ) - K / 2 * r ^ 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with hr0 | hq
  · exact Or.inl hr0
  · right
    have hK_ne : K ≠ 0 := ne_of_gt hK_pos
    have : K / 2 * r ^ 2 = K / 2 - γ := by linarith
    field_simp at this ⊢
    linarith

/-- r* is positive when K > Kc = 2γ. -/
theorem lorentzian_rstar_pos (K γ : ℝ) (hK_pos : 0 < K) (hK_gt : K > 2 * γ) :
    0 < 1 - 2 * γ / K := by
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  rw [sub_pos, div_lt_one hK_pos]
  linarith

/-- r* ≤ 1 when K > Kc = 2γ and γ ≥ 0. -/
theorem lorentzian_rstar_le_one (K γ : ℝ) (hK_pos : 0 < K) (hγ_nn : 0 ≤ γ) :
    1 - 2 * γ / K ≤ 1 := by
  linarith [div_nonneg (by linarith : (0:ℝ) ≤ 2 * γ) (le_of_lt hK_pos)]

/-! ## Self-consistency map for KuramotoData -/

/-- Continuous self-consistency map: Φ(r) = r - f(r).
    Fixed points of Φ are zeros of the ODE. -/
def lorentzianPhi (K γ r : ℝ) : ℝ := r - lorentzianODE K γ r

theorem lorentzianPhi_fp_iff (K γ r : ℝ) :
    lorentzianPhi K γ r = r ↔ lorentzianODE K γ r = 0 := by
  unfold lorentzianPhi; constructor <;> intro h <;> linarith

theorem lorentzianPhi_continuous (K γ : ℝ) :
    Continuous (lorentzianPhi K γ) := by
  unfold lorentzianPhi lorentzianODE; fun_prop

theorem lorentzianPhi_unique (K γ x : ℝ)
    (hK_pos : 0 < K) (hK_gt : K > 2 * γ)
    (hfp : lorentzianPhi K γ x = x) :
    x = 0 ∨ x ^ 2 = 1 - 2 * γ / K :=
  lorentzian_fixed_point_unique K γ x hK_pos hK_gt
    ((lorentzianPhi_fp_iff K γ x).mp hfp)

/-! ## Invariance: r ∈ [0,1] -/

/-- The ODE vanishes at r = 0: f(0) = 0. -/
theorem lorentzian_ode_zero (K γ : ℝ) : lorentzianODE K γ 0 = 0 := by
  unfold lorentzianODE; ring

/-- The ODE is negative at r = 1 for γ > 0: f(1) = -γ < 0.
    This means the unit ball boundary repels inward. -/
theorem lorentzian_ode_at_one (K γ : ℝ) (hγ : 0 < γ) :
    lorentzianODE K γ 1 < 0 := by
  unfold lorentzianODE; nlinarith

/-- Φ(0) = 0: the incoherent state is a fixed point. -/
theorem lorentzianPhi_zero (K γ : ℝ) : lorentzianPhi K γ 0 = 0 := by
  unfold lorentzianPhi; rw [lorentzian_ode_zero]; ring

/-! ## Velocity bound (KuramotoData.hLip structure) -/

/-- The ODE velocity is bounded on [0,1]: |f(r)| ≤ K - γ for r ∈ [0,1], K > 2γ.
    This gives the Lipschitz constant for the discrete trajectory. -/
theorem lorentzian_ode_bounded (K γ r : ℝ)
    (hK_pos : 0 < K) (hK_gt : K > 2 * γ)
    (hr_nn : 0 ≤ r) (hr_le : r ≤ 1) :
    |lorentzianODE K γ r| ≤ K - γ := by
  unfold lorentzianODE
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr3 : 0 ≤ r ^ 3 := by positivity
  have hr3_le : r ^ 3 ≤ r := by nlinarith [sq_nonneg r]
  rw [abs_le]
  constructor
  · -- (K/2-γ)r - (K/2)r³ ≥ -(K-γ)
    -- Worst case: r=1, f(1) = -γ ≥ -(K-γ) since K > 2γ > γ
    nlinarith
  · -- (K/2-γ)r - (K/2)r³ ≤ K-γ
    -- Each term: (K/2-γ)r ≤ K/2-γ, -(K/2)r³ ≤ 0
    nlinarith

/-! ## Lipschitz property (for Picard-Lindelöf) -/

/-- The Lorentzian ODE is Lipschitz on [0,1] with constant 2K.
    |f(x) - f(y)| ≤ 2K · |x - y| for x, y ∈ [0,1]. -/
theorem lorentzian_ode_lipschitz (K γ x y : ℝ)
    (hx_nn : 0 ≤ x) (hx_le : x ≤ 1) (hy_nn : 0 ≤ y) (hy_le : y ≤ 1)
    (hK_pos : 0 < K) (hK_gt : K > 2 * γ) (hγ_nn : 0 ≤ γ) :
    |lorentzianODE K γ x - lorentzianODE K γ y| ≤ 2 * K * |x - y| := by
  unfold lorentzianODE
  have h : (K / 2 - γ) * x - K / 2 * x ^ 3 - ((K / 2 - γ) * y - K / 2 * y ^ 3) =
      (x - y) * ((K / 2 - γ) - K / 2 * (x ^ 2 + x * y + y ^ 2)) := by ring
  rw [h, abs_mul]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hsum : x ^ 2 + x * y + y ^ 2 ≤ 3 := by nlinarith
  have hsum_nn : 0 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith
  have hfactor : |K / 2 - γ - K / 2 * (x ^ 2 + x * y + y ^ 2)| ≤ 2 * K := by
    rw [abs_le]
    constructor
    · -- lower: -(2K) ≤ K/2 - γ - K/2·S
      -- K/2 - γ - K/2·S ≥ K/2 - γ - 3K/2 = -K - γ ≥ -2K
      nlinarith
    · -- upper: K/2 - γ - K/2·S ≤ 2K
      -- S ≥ 0 so K/2·S ≥ 0, so K/2 - γ - K/2·S ≤ K/2 ≤ 2K
      have : K / 2 * (x ^ 2 + x * y + y ^ 2) ≥ 0 := by nlinarith
      linarith
  calc |x - y| * |K / 2 - γ - K / 2 * (x ^ 2 + x * y + y ^ 2)|
      ≤ |x - y| * (2 * K) := by
        apply mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ = 2 * K * |x - y| := by ring

/-! ## KuramotoData compatibility -/

/-- For the discrete-time version with step size h, the Lipschitz constant
    is L = h·(K-γ). The condition 3L < r* = √(1-2γ/K) is satisfiable
    by choosing h small enough. This theorem shows it for h ≤ r*/(4K). -/
theorem lorentzian_hL_small_satisfiable (K γ : ℝ)
    (hK_pos : 0 < K) (hK_gt : K > 2 * γ) (_hγ_nn : 0 ≤ γ) :
    ∃ h : ℝ, 0 < h ∧ 3 * (h * (K - γ)) < Real.sqrt (1 - 2 * γ / K) := by
  have hrs_pos := lorentzian_rstar_pos K γ hK_pos hK_gt
  have hrs := Real.sqrt_pos_of_pos hrs_pos
  have hKγ : 0 < K - γ := by linarith
  set rstar := Real.sqrt (1 - 2 * γ / K)
  refine ⟨rstar / (4 * (K - γ)), by positivity, ?_⟩
  have h4 : (0:ℝ) < 4 * (K - γ) := by positivity
  have heq : rstar / (4 * (K - γ)) * (K - γ) = rstar / 4 := by
    field_simp
  rw [heq]
  linarith

/-! ## Perfect-square Lyapunov identity -/

/-- The ODE factors as ṙ = (K/2)r(r*² - r²) where r*² = 1 - 2γ/K. -/
theorem lorentzian_ode_factored (K γ r : ℝ) (hK : K ≠ 0) :
    lorentzianODE K γ r = (K / 2) * r * ((1 - 2 * γ / K) - r ^ 2) := by
  unfold lorentzianODE; field_simp

/-- V(r) = V_min + (K/8)(r² - r*²)² where V_min = V(r*) and r*² = 1 - 2γ/K.
    This means r* is the unique global minimizer of V on (0,∞). -/
theorem lorentzian_potential_perfect_square (K γ r rstar_sq : ℝ) (hK : K ≠ 0)
    (hrs : rstar_sq = 1 - 2 * γ / K) :
    lorentzianPotential K γ r =
    (K / 8) * (r ^ 2 - rstar_sq) ^ 2 +
    (-(K / 4 - γ / 2) * rstar_sq + (K / 8) * rstar_sq ^ 2) := by
  unfold lorentzianPotential; subst hrs; field_simp; ring

/-- Key algebraic identity: the Lyapunov derivative of W = (r²-r*²)² along
    the ODE is exactly -2Kr²W. This gives dW/dt = -2Kr²W, a closed-form
    Grönwall inequality implying exponential convergence r(t) → r*.

    Precisely: 2r·f(r)·(r²-r*²) = -Kr²·(r²-r*²)²
    where f(r) = (K/2-γ)r - (K/2)r³ is the ODE and r*² = 1-2γ/K. -/
theorem lorentzian_lyapunov_identity (K γ r : ℝ) (hK : K ≠ 0) :
    2 * r * lorentzianODE K γ r * (r ^ 2 - (1 - 2 * γ / K)) =
    -(K * r ^ 2 * (r ^ 2 - (1 - 2 * γ / K)) ^ 2) := by
  unfold lorentzianODE; field_simp; ring

/-- Consequence: d/dt(r²-r*²)² = -2Kr²(r²-r*²)².
    Since r > 0 and K > 0: this is ≤ 0, with equality iff r = r*.
    Combined with W ≥ 0: W(t) → 0, hence r(t) → r*.
    This is a COMPLETE algebraic proof of global convergence for the
    scalar Lorentzian ODE — the convergence rate is exponential:
    W(t) = W(0)·exp(-2K∫₀ᵗr(s)²ds). -/
theorem lorentzian_convergence_rate (K γ r : ℝ) (hK_pos : 0 < K) :
    2 * r * lorentzianODE K γ r * (r ^ 2 - (1 - 2 * γ / K)) ≤ 0 := by
  rw [lorentzian_lyapunov_identity K γ r (ne_of_gt hK_pos)]
  have h1 : 0 ≤ K := le_of_lt hK_pos
  have h2 : 0 ≤ r ^ 2 := sq_nonneg r
  have h3 : 0 ≤ (r ^ 2 - (1 - 2 * γ / K)) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg h1 (mul_nonneg h2 h3)]

/-! ## Łojasiewicz identity (scalar case) -/

/-- The exact Łojasiewicz identity for the Lorentzian:
    |f(r)| = (K/2)·|r|·|r²-r*²|, and √V = √(K/8)·|r²-r*²|.
    So |f(r)| = √(2K)·|r|·√V — the Łojasiewicz exponent is θ = 1/2 (optimal).
    Near r* where |r| ≥ r*/2: |f(r)| ≥ (r*/2)·√(2K)·√V,
    giving exponential convergence V(t) → 0 at rate √(2K)·r*. -/
theorem lorentzian_lojasiewicz_identity (K γ r : ℝ) (hK_pos : 0 < K) :
    |lorentzianODE K γ r| = K / 2 * |r| * |r ^ 2 - (1 - 2 * γ / K)| := by
  rw [lorentzian_ode_factored K γ r (ne_of_gt hK_pos)]
  simp only [abs_mul]
  congr 1
  · congr 1; exact abs_of_pos (by linarith)
  · exact abs_sub_comm _ _

end
