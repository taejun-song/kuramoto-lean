/-
  Kuramoto Stability Project — L² Lyapunov Function
  ====================================================

  PROVED: V = Σ c_k (α_k - α*_k)² satisfies dV/dt ≤ 0
  along trajectories of the n-pole OA system (0 sorry).

  Key results (all 0 sorry):
    l2_lyapunov_theorem:      dV/dt ≤ 0 for general n
    l2_diagonal_lower_bound:  r*Q - DS ≥ diagonal (quantitative)
    l2_exponential_rate:      dV/dt ≤ -K·c_min·δ·(δ+δ*)·V

  Gives DIRECT global Lyapunov convergence WITHOUT Hirsch, Kamke,
  Perron, or passage to limit. V is FINITE at PLS (unlike Ψ).
-/

import KuramotoLean.RationalOA

open Real

noncomputable section

/-! ## The L² Lyapunov function -/

/-- V(α) = Σ c_k (α_k - α*_k)² — the weighted L² distance from PLS. -/
def l2Distance {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ) : ℝ :=
  ∑ k, c k * (α k - α_star k) ^ 2

/-- V ≥ 0 when c_k ≥ 0. -/
theorem l2Distance_nonneg {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    0 ≤ l2Distance c α α_star := by
  unfold l2Distance
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hc k) (sq_nonneg _)

/-- V = 0 iff α = α* (when c_k > 0). -/
theorem l2Distance_eq_zero {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) :
    l2Distance c α α_star = 0 ↔ α = α_star := by
  unfold l2Distance
  constructor
  · intro h
    ext k
    have := Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (le_of_lt (hc k)) (sq_nonneg (α k - α_star k))) |>.mp h k (Finset.mem_univ _)
    have := (mul_eq_zero.mp this).resolve_left (ne_of_gt (hc k))
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this)
  · intro h; subst h; simp [l2Distance]

/-! ## n = 1: Exact Lyapunov identity -/

/-- For n=1 (Lorentzian): dV/dt = -Kα(α+α*)(α-α*)².
    This is ≤ 0 for α ∈ (0,1), giving a DIRECT Lyapunov proof. -/
theorem l2_lyapunov_lorentzian (K γ α α_star : ℝ)
    (hK : 0 < K)
    (h_equil : γ = (K / 2) * (1 - α_star ^ 2)) :
    2 * (α - α_star) * lorentzianODE K γ α =
    -K * α * (α + α_star) * (α - α_star) ^ 2 := by
  unfold lorentzianODE; rw [h_equil]; ring

/-- The Lorentzian L² Lyapunov derivative is ≤ 0 for α, α* > 0. -/
theorem l2_lyapunov_lorentzian_nonpos (K γ α α_star : ℝ)
    (hK : 0 < K) (hα : 0 < α) (hα_star : 0 < α_star)
    (h_equil : γ = (K / 2) * (1 - α_star ^ 2)) :
    2 * (α - α_star) * lorentzianODE K γ α ≤ 0 := by
  rw [l2_lyapunov_lorentzian K γ α α_star hK h_equil]
  nlinarith [sq_nonneg (α - α_star), mul_pos hK (mul_pos hα (by linarith : 0 < α + α_star))]

/-! ## Key algebraic identity: factoring f_k at fixed r = r* -/

/-- The velocity f_k at fixed r = r* factors as:
    g_k(α_k) = -γ_k α_k + (K/2)r*(1-α_k²) = (K/2)r*(α*_k - α_k)(α_k + 1/α*_k)
    This uses the fact that α*_k and -1/α*_k are roots of the quadratic g_k.
    Product of roots = -1 (from the coefficient structure). -/
theorem velocity_factoring (K r_star α_k α_star_k γ_k : ℝ)
    (hα_star : α_star_k ≠ 0)
    (h_equil : γ_k * α_star_k = (K / 2) * r_star * (1 - α_star_k ^ 2)) :
    -γ_k * α_k + (K / 2) * r_star * (1 - α_k ^ 2) =
    (K / 2) * r_star * (α_star_k - α_k) * (α_k + 1 / α_star_k) := by
  have h_γ : γ_k = (K / 2) * r_star * (1 - α_star_k ^ 2) / α_star_k := by
    field_simp at h_equil ⊢; linarith
  rw [h_γ]; field_simp; ring

/-- Consequence: p_k · g_k(α_k) = -(K/2)r* · p_k² · (α_k + 1/α*_k) ≤ 0.
    Each component's contribution to dV/dt (at fixed r = r*) is non-positive. -/
theorem component_lyapunov_nonpos (K r_star α_k α_star_k γ_k : ℝ)
    (hα_star : α_star_k ≠ 0)
    (h_equil : γ_k * α_star_k = (K / 2) * r_star * (1 - α_star_k ^ 2)) :
    (α_k - α_star_k) * (-γ_k * α_k + (K / 2) * r_star * (1 - α_k ^ 2)) =
    -(K / 2) * r_star * (α_k - α_star_k) ^ 2 * (α_k + 1 / α_star_k) := by
  rw [velocity_factoring K r_star α_k α_star_k γ_k hα_star h_equil]; ring

/-! ## General n: The dV/dt decomposition -/

/-! The time derivative of V decomposes as:
    dV/dt = 2 Σ c_k (α_k - α*_k) · f_k(α)
          = [coupling: K(r-r*)Σc_k(α_k-α*_k)(1-α_k²)]
          + [weighted damping: -Kr*Σc_k(α_k-α*_k)²(α_k+α*_k)]
          + [damping: -2Σc_kγ_k(α_k-α*_k)²]

    The last two terms are ALWAYS ≤ 0.
    The coupling term has uncertain sign.
    CONJECTURE: the sum is ≤ 0. -/

/-- The damping terms are ≤ 0. -/
theorem l2_damping_nonpos {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_star : ∀ k, 0 < α_star k)
    (hr : 0 < ∑ j, c j * α_star j) :
    0 ≤ ∑ k, c k * (α k - α_star k) ^ 2 * (K * (∑ j, c j * α_star j) * (α k + α_star k) +
      2 * γ k) := by
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
  · exact mul_nonneg (le_of_lt (hc k)) (sq_nonneg _)
  · have : 0 < K * (∑ j, c j * α_star j) := mul_pos hK hr
    nlinarith [hα k, hα_star k, hγ k]

/-! ## L² Lyapunov Theorem

**PROVED**: dV/dt ≤ 0 for the n-pole OA system.
The proof uses three elementary ingredients:
1. AM-GM: |xy| ≤ (x²+y²)/2
2. Constraint: α_k ∈ (0,1) implies 1-α_k² < 1
3. Key identity: α*_k·A_k - (r*-c_k·α*_k) = α*_k·α_k·(r*+c_k·α_k) ≥ 0 -/

/-- The per-component Lyapunov identity, expanded for the full ODE:
    p_k · f_k(α) = -(K/2)r* p_k²(α_k+1/α*_k) + (K/2)(r-r*) p_k(1-α_k²) -/
theorem l2_component_identity {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (α α_star : Fin n → ℝ) (k : Fin n)
    (hα_star_pos : 0 < α_star k)
    (h_equil : nPoleODE γ c K α_star k = 0) :
    (α k - α_star k) * nPoleODE γ c K α k =
    -(K / 2) * (∑ j, c j * α_star j) * (α k - α_star k) ^ 2 *
      (α k + 1 / α_star k) +
    (K / 2) * (∑ j, c j * α j - ∑ j, c j * α_star j) *
      (α k - α_star k) * (1 - α k ^ 2) := by
  unfold nPoleODE
  have hne : α_star k ≠ 0 := ne_of_gt hα_star_pos
  have h_eq : γ k * α_star k = (K / 2) * (∑ j, c j * α_star j) * (1 - α_star k ^ 2) := by
    have := h_equil; unfold nPoleODE at this; linarith
  have h_γ : γ k = (K / 2) * (∑ j, c j * α_star j) * (1 - α_star k ^ 2) / α_star k := by
    field_simp at h_eq ⊢; linarith
  rw [h_γ]; field_simp; ring

/-- dV/dt = K(DS - r*Q): the Lyapunov derivative identity.
    Uses l2_component_identity for each component. -/
theorem l2_lyapunov_identity {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k =
    K * ((∑ j, c j * (α j - α_star j)) *
         (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) -
         (∑ j, c j * α_star j) *
         (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k))) := by
  have h_comp : ∀ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k =
      c k * 2 * (-(K / 2) * (∑ j, c j * α_star j) * (α k - α_star k) ^ 2 *
        (α k + 1 / α_star k) +
      (K / 2) * (∑ j, c j * α j - ∑ j, c j * α_star j) *
        (α k - α_star k) * (1 - α k ^ 2)) := by
    intro k
    rw [show c k * 2 * (α k - α_star k) * nPoleODE γ c K α k =
      c k * (2 * ((α k - α_star k) * nPoleODE γ c K α k)) from by ring,
      l2_component_identity γ c K α α_star k (hα_star_pos k) (h_equil k)]
    ring
  -- Each summand has been rewritten. Now combine into the K(DS-r*Q) form.
  have h_final : ∀ x : Fin n,
    c x * 2 * (-(K / 2) * (∑ j, c j * α_star j) * (α x - α_star x) ^ 2 *
      (α x + 1 / α_star x) +
    (K / 2) * (∑ j, c j * α j - ∑ j, c j * α_star j) *
      (α x - α_star x) * (1 - α x ^ 2)) =
    K * (∑ j, c j * α j - ∑ j, c j * α_star j) *
      (c x * (α x - α_star x) * (1 - α x ^ 2)) -
    K * (∑ j, c j * α_star j) *
      (c x * (α x - α_star x) ^ 2 * (α x + 1 / α_star x)) := fun x => by ring
  simp_rw [h_comp, h_final, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h_D : ∑ j, c j * α j - ∑ j, c j * α_star j = ∑ j, c j * (α j - α_star j) := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
  rw [h_D]; ring

/-- Clearing denominators for pair_bound. Isolated to prevent field_simp leakage. -/
theorem pair_bound_clear_denom (αj αk αsj αsk : ℝ) (hαsj : αsj ≠ 0) (hαsk : αsk ≠ 0) :
    αsj * αsk * (αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
    αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
    (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2)) =
    αsj * αsj * (αk * αsk + 1) * (αk - αsk) ^ 2 +
    αsk * αsk * (αj * αsj + 1) * (αj - αsj) ^ 2 -
    αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
  field_simp

/-- Per-pair bound: the symmetrized off-diagonal integrand is ≥ 0. -/
theorem pair_bound (αj αk αsj αsk : ℝ)
    (hαj : 0 < αj) (hαk : 0 < αk) (hαj1 : αj < 1) (hαk1 : αk < 1)
    (hαsj : 0 < αsj) (hαsk : 0 < αsk) :
    0 ≤ αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
        αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
        (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
  have hnej : αsj ≠ 0 := ne_of_gt hαsj
  have hnek : αsk ≠ 0 := ne_of_gt hαsk
  have hmul : (0 : ℝ) < αsj * αsk := mul_pos hαsj hαsk
  -- Polynomial numerator ≥ 0 (SOS decomposition)
  have h_num : 0 ≤ αsj * αsj * (αk * αsk + 1) * (αk - αsk) ^ 2 +
      αsk * αsk * (αj * αsj + 1) * (αj - αsj) ^ 2 -
      αsj * αsk * (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2) := by
    -- N = (αsk·p - αsj·q)² + αsj·αsk·(αj·αsk·p² + αk·αsj·q² + (αj²+αk²)·p·q)
    -- where p = αj-αsj, q = αk-αsk.
    -- First term ≥ 0. For the second: split into cases pq ≥ 0 and pq < 0.
    -- When pq ≥ 0: all terms nonneg. When pq < 0: |(αj²+αk²)pq| < 2|pq| ≤ p²+q²
    -- and αj·αsk·p² + αk·αsj·q² absorbs this since the cross is bounded.
    -- Provide explicit nlinarith witnesses:
    -- N = (1+αj·αsj)·αsk²·(αj-αsj)² + (1+αk·αsk)·αsj²·(αk-αsk)²
    --   + αsj·αsk·(αj²+αk²-2)·(αj-αsj)·(αk-αsk)
    -- Case split on sign of (αj-αsj)·(αk-αsk)
    set pj := αj - αsj
    set pk := αk - αsk
    by_cases hpq : pj * pk ≥ 0
    · -- Case pq ≥ 0: AM-GM gives αsk²pj² + αsj²pk² ≥ 2αsjαskpjpk,
      -- and (2-αj²-αk²) ≤ 2, so the negative part -(2-αj²-αk²)pjpk ≥ -2pjpk
      -- is absorbed by the AM-GM bound.
      have h_amgm := sq_nonneg (αsk * pj - αsj * pk)
      -- h_amgm: αsk²pj² - 2αsjαskpjpk + αsj²pk² ≥ 0
      -- i.e. αsk²pj² + αsj²pk² ≥ 2αsjαskpjpk
      -- Extra positive terms: αj·αsj·αsk²·pj² and αk·αsk·αsj²·pk²
      have h_extra1 : 0 ≤ αj * αsj * αsk ^ 2 * pj ^ 2 := by positivity
      have h_extra2 : 0 ≤ αk * αsk * αsj ^ 2 * pk ^ 2 := by positivity
      -- The negative term: αsj·αsk·(αj²+αk²-2)·pjpk. Since αj²+αk²<2 and pjpk≥0:
      -- this equals -αsj·αsk·(2-αj²-αk²)·pjpk ≤ 0.
      -- Bound: αsj·αsk·(2-αj²-αk²)·pjpk ≤ αsj·αsk·2·pjpk = 2αsjαskpjpk
      -- ≤ αsk²pj² + αsj²pk² (by AM-GM = h_amgm)
      -- The key: αsj*αsk*(αj²+αk²-2)*pj*pk = -αsj*αsk*(2-αj²-αk²)*pj*pk
      -- Since 2-αj²-αk² > 0 and pj*pk ≥ 0: this is ≤ 0.
      -- And |αsj*αsk*(2-αj²-αk²)*pj*pk| ≤ 2*αsj*αsk*pj*pk ≤ αsk²pj²+αsj²pk² [AM-GM]
      -- So the negative part is absorbed.
      nlinarith [sq_nonneg αj, sq_nonneg αk, sq_nonneg (αsj * pk - αsk * pj),
                 mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk),
                 mul_nonneg (mul_nonneg (le_of_lt hαsj) (le_of_lt hαsk)) hpq]
    · -- Case pq < 0: all three terms are non-negative
      push Not at hpq
      have h1 : 0 ≤ (1 + αj * αsj) * αsk ^ 2 * pj ^ 2 := by positivity
      have h2 : 0 ≤ (1 + αk * αsk) * αsj ^ 2 * pk ^ 2 := by positivity
      have h3 : 0 ≤ αsj * αsk * (2 - αj ^ 2 - αk ^ 2) * -(pj * pk) := by
        apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
        · exact le_of_lt hαsj
        · exact le_of_lt hαsk
        · nlinarith [sq_abs αj, sq_abs αk]
        · linarith
      nlinarith
  -- Use isolated clearing lemma
  have h_eq := pair_bound_clear_denom αj αk αsj αsk hnej hnek
  -- From h_eq: αsj*αsk * expr = polynomial ≥ 0, and αsj*αsk > 0, so expr ≥ 0
  have h_prod_nonneg : 0 ≤ αsj * αsk * (αsj * (αk - αsk) ^ 2 * (αk + 1 / αsk) +
      αsk * (αj - αsj) ^ 2 * (αj + 1 / αsj) -
      (αj - αsj) * (αk - αsk) * (2 - αj ^ 2 - αk ^ 2)) := by linarith
  exact nonneg_of_mul_nonneg_right h_prod_nonneg hmul

/-- DS ≤ r*Q: the core inequality.
    Proof: expand as double sum, split diagonal/off-diagonal, apply pair_bound. -/
theorem ds_le_rstarQ {n : ℕ} (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1) :
    (∑ j, c j * (α j - α_star j)) *
    (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) ≤
    (∑ j, c j * α_star j) *
    (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) := by
  -- Suffices: r*Q - DS ≥ 0
  suffices h : 0 ≤ (∑ j, c j * α_star j) *
    (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
    (∑ j, c j * (α j - α_star j)) *
    (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) by linarith
  -- Rewrite r*Q - DS = Σ_k c_k p_k [r* p_k q_k - D(1-α_k²)]
  -- where D = Σ c_j p_j, q_k = α_k + 1/α*_k
  set p := fun k => α k - α_star k
  set q := fun k => α k + 1 / α_star k
  set D := ∑ j, c j * p j
  set r_star := ∑ j, c j * α_star j
  -- Expand both sides as double sums
  -- LHS: D·S = (Σ_j c_j p_j)(Σ_k c_k p_k(1-α_k²)) = Σ_{(j,k)} c_j p_j · c_k p_k(1-α_k²)
  -- RHS: r*·Q = (Σ_j c_j α*_j)(Σ_k c_k p_k² q_k) = Σ_{(j,k)} c_j α*_j · c_k p_k² q_k
  -- Need: Σ_{(j,k)} c_j c_k [α*_j p_k² q_k - p_j p_k(1-α_k²)] ≥ 0
  -- Split into diagonal (j=k) + off-diagonal (j≠k) using Finset.diag_union_offDiag.
  -- Diagonal: Σ_k c_k²[α*_k p_k² q_k - p_k²(1-α_k²)] = Σ c_k² p_k²(α*_k q_k - 1 + α_k²)
  --         = Σ c_k² p_k²(α*_k α_k + α_k²) ≥ 0  [positivity]
  -- Off-diagonal: symmetrize (j,k)↔(k,j):
  --   (1/2)Σ_{j≠k} c_jc_k [α*_j p_k² q_k + α*_k p_j² q_j - p_jp_k((1-α_k²)+(1-α_j²))]
  -- By AM-GM: p_jp_k ≤ (p_j²+p_k²)/2 (when same sign)
  --           and (1-α_j²)+(1-α_k²) < 2
  -- So cross ≤ p_j²+p_k², absorbed by α*_j p_k² q_k + α*_k p_j² q_j
  --   via the identity α*_k(α_k+1/α*_k) = α*_kα_k+1 ≥ 1.
  -- Rewrite as double sum: r*Q - DS = Σ_j Σ_k c_j c_k [α*_j p_k² q_k - p_j p_k(1-α_k²)]
  -- Pair (j,k) with (k,j): symmetric sum = c_j c_k · pair_bound ≥ 0
  -- Strategy: show r*Q - DS = (1/2) Σ_j Σ_k c_j c_k · symmetric_term(j,k) ≥ 0

  -- Step 1: Expand r*Q and DS as double sums
  have h1 : r_star * (∑ k, c k * p k ^ 2 * q k) =
      ∑ j, ∑ k, c j * α_star j * (c k * p k ^ 2 * q k) := by
    simp only [r_star]; rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  have h2 : D * (∑ k, c k * p k * (1 - α k ^ 2)) =
      ∑ j, ∑ k, c j * p j * (c k * p k * (1 - α k ^ 2)) := by
    simp only [D]; rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  -- Step 2: r*Q - DS as single double sum
  rw [h1, h2]
  rw [show (∑ j, ∑ k, c j * α_star j * (c k * p k ^ 2 * q k)) -
      (∑ j, ∑ k, c j * p j * (c k * p k * (1 - α k ^ 2))) =
      ∑ j, ∑ k, (c j * α_star j * (c k * p k ^ 2 * q k) -
      c j * p j * (c k * p k * (1 - α k ^ 2))) from by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; rw [← Finset.sum_sub_distrib]]
  -- Step 3: Symmetrize: S = (S + S')/2 where S' = S (by sum_comm)
  -- Then S = (1/2) Σ_j Σ_k [term(j,k) + term(k,j)] and each pair ≥ 0.
  set S := ∑ j, ∑ k, (c j * α_star j * (c k * p k ^ 2 * q k) -
      c j * p j * (c k * p k * (1 - α k ^ 2)))
  -- S' (transposed) = S
  have h_swap : (∑ j, ∑ k, (c k * α_star k * (c j * p j ^ 2 * q j) -
      c k * p k * (c j * p j * (1 - α j ^ 2)))) = S := Finset.sum_comm
  -- 2S = S + S' = Σ_j Σ_k [term(j,k) + term'(j,k)]
  -- where term'(j,k) = term(k,j) after relabeling
  suffices h_2S : 0 ≤ 2 * S by linarith
  -- 2S = S + S = S + S' (where S'=S by h_swap)
  -- = Σ_j Σ_k [term(j,k) + term'(j,k)]
  have h_sum : 2 * S = ∑ j, ∑ k,
      ((c j * α_star j * (c k * p k ^ 2 * q k) -
        c j * p j * (c k * p k * (1 - α k ^ 2))) +
       (c k * α_star k * (c j * p j ^ 2 * q j) -
        c k * p k * (c j * p j * (1 - α j ^ 2)))) := by
    have : 2 * S = S + (∑ j, ∑ k, (c k * α_star k * (c j * p j ^ 2 * q j) -
        c k * p k * (c j * p j * (1 - α j ^ 2)))) := by rw [h_swap]; ring
    rw [this]; simp only [S, ← Finset.sum_add_distrib]
  rw [h_sum]
  -- Each (j,k) summand = c_j c_k · [pair_bound terms]
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  have : (c j * α_star j * (c k * p k ^ 2 * q k) -
      c j * p j * (c k * p k * (1 - α k ^ 2))) +
      (c k * α_star k * (c j * p j ^ 2 * q j) -
       c k * p k * (c j * p j * (1 - α j ^ 2))) =
    c j * c k * (α_star j * (p k) ^ 2 * q k +
      α_star k * (p j) ^ 2 * q j -
      p j * p k * ((1 - α k ^ 2) + (1 - α j ^ 2))) := by ring
  rw [this]
  apply mul_nonneg (le_of_lt (mul_pos (hc j) (hc k)))
  simp only [p, q]
  convert pair_bound (α j) (α k) (α_star j) (α_star k) (hα j) (hα k) (hα_lt j) (hα_lt k)
    (hα_star j) (hα_star k) using 2
  ring

/-- **L² LYAPUNOV THEOREM**: dV/dt ≤ 0 for the n-pole OA system. -/
theorem l2_lyapunov_theorem {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (hK : 0 < K) (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k ≤ 0 := by
  rw [l2_lyapunov_identity γ c K α α_star hα_star h_equil]
  have h_ineq := ds_le_rstarQ c α α_star hc hα hα_lt hα_star hα_star_lt
  have h_sub : 0 ≤ (∑ j, c j * α_star j) *
    (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
    (∑ j, c j * (α j - α_star j)) *
    (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) := by linarith
  nlinarith

/-! ## Exponential Lyapunov Rate

The diagonal of the double-sum bound gives a quantitative decay rate.
At (j,k) = (k,k): the symmetrized pair term equals
  2·(α_k-α*_k)²·α_k·(α*_k+α_k)
Since off-diagonal terms ≥ 0 (pair_bound), we get:
  r*Q - DS ≥ Σ c_k²·(α_k-α*_k)²·α_k·(α*_k+α_k) ≥ c_min·δ·(δ+δ*)·V
Hence: dV/dt ≤ -K·c_min·δ·(δ+δ*)·V. -/

/-- The self-pair term: pair_bound at (k,k) gives
    2(α-α*)²·α·(α*+α) (always ≥ 0). -/
theorem self_pair_identity (α α_star : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hα_star : 0 < α_star) :
    α_star * (α - α_star) ^ 2 * (α + 1 / α_star) +
    α_star * (α - α_star) ^ 2 * (α + 1 / α_star) -
    (α - α_star) * (α - α_star) * (2 - α ^ 2 - α ^ 2) =
    2 * (α - α_star) ^ 2 * α * (α_star + α) := by
  have hne : α_star ≠ 0 := ne_of_gt hα_star
  field_simp; ring

/-- Double sum ≥ diagonal when all terms are non-negative. -/
private theorem double_sum_ge_diagonal {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ j k, 0 ≤ f j k) :
    ∑ k, f k k ≤ ∑ j, ∑ k, f j k := by
  apply Finset.sum_le_sum
  intro j _
  exact Finset.single_le_sum (fun k _ => hf j k) (Finset.mem_univ j)

/-- The diagonal of the symmetrized double sum bounds r*Q - DS from below.
    This is the key quantitative step for the exponential rate.
    PROVED: symmetrize, apply double_sum_ge_diagonal, simplify via self_pair_identity. -/
theorem l2_diagonal_lower_bound {n : ℕ}
    (c : Fin n → ℝ) (α α_star : Fin n → ℝ)
    (hc : ∀ k, 0 < c k) (_hα : ∀ k, 0 < α k) (_hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (_hα_star_lt : ∀ k, α_star k < 1) :
    ∑ k, c k ^ 2 * (α k - α_star k) ^ 2 * (α k * (α_star k + α k)) ≤
    (∑ j, c j * α_star j) *
      (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
    (∑ j, c j * (α j - α_star j)) *
      (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) := by
  suffices h_main :
      2 * ∑ k, c k ^ 2 * (α k - α_star k) ^ 2 * (α k * (α_star k + α k)) ≤
      2 * ((∑ j, c j * α_star j) *
        (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
      (∑ j, c j * (α j - α_star j)) *
        (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2))) by linarith
  set p := fun k => α k - α_star k
  set q := fun k => α k + 1 / α_star k
  set f : Fin n → Fin n → ℝ := fun j k =>
    c j * c k * (α_star j * p k ^ 2 * q k +
      α_star k * p j ^ 2 * q j -
      p j * p k * (2 - α j ^ 2 - α k ^ 2))
  have hf_nn : ∀ j k, 0 ≤ f j k := by
    intro j k; simp only [f]
    apply mul_nonneg (le_of_lt (mul_pos (hc j) (hc k)))
    simp only [p, q]
    exact pair_bound (α j) (α k) (α_star j) (α_star k)
      (_hα j) (_hα k) (_hα_lt j) (_hα_lt k) (hα_star j) (hα_star k)
  have h1 : (∑ j, c j * α_star j) * (∑ k, c k * p k ^ 2 * q k) =
      ∑ j, ∑ k, c j * α_star j * (c k * p k ^ 2 * q k) := by
    rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  have h2 : (∑ j, c j * p j) * (∑ k, c k * p k * (1 - α k ^ 2)) =
      ∑ j, ∑ k, c j * p j * (c k * p k * (1 - α k ^ 2)) := by
    rw [Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
  set S := ∑ j, ∑ k, (c j * α_star j * (c k * p k ^ 2 * q k) -
    c j * p j * (c k * p k * (1 - α k ^ 2)))
  have h_diff : (∑ j, c j * α_star j) * (∑ k, c k * p k ^ 2 * q k) -
      (∑ j, c j * p j) * (∑ k, c k * p k * (1 - α k ^ 2)) = S := by
    simp only [S]; rw [h1, h2, ← Finset.sum_sub_distrib]
    congr 1; ext j; rw [← Finset.sum_sub_distrib]
  have h_swap : (∑ j, ∑ k, (c k * α_star k * (c j * p j ^ 2 * q j) -
      c k * p k * (c j * p j * (1 - α j ^ 2)))) = S := Finset.sum_comm
  have h_2S : 2 * S = ∑ j, ∑ k,
      ((c j * α_star j * (c k * p k ^ 2 * q k) -
        c j * p j * (c k * p k * (1 - α k ^ 2))) +
       (c k * α_star k * (c j * p j ^ 2 * q j) -
        c k * p k * (c j * p j * (1 - α j ^ 2)))) := by
    have : 2 * S = S + (∑ j, ∑ k, (c k * α_star k * (c j * p j ^ 2 * q j) -
        c k * p k * (c j * p j * (1 - α j ^ 2)))) := by rw [h_swap]; ring
    rw [this]; simp only [S, ← Finset.sum_add_distrib]
  have h_2S_eq : 2 * S = ∑ j, ∑ k, f j k := by
    rw [h_2S]; congr 1; ext j; congr 1; ext k; simp only [f]; ring
  have h_diag : ∀ k : Fin n, f k k =
      2 * (c k ^ 2 * p k ^ 2 * (α k * (α_star k + α k))) := by
    intro k; simp only [f, p, q]
    have hne : α_star k ≠ 0 := ne_of_gt (hα_star k)
    field_simp; ring
  have h_diag_sum : ∑ k : Fin n, f k k =
      2 * ∑ k, c k ^ 2 * p k ^ 2 * (α k * (α_star k + α k)) := by
    simp_rw [h_diag, ← Finset.mul_sum]
  have h_ge := double_sum_ge_diagonal f hf_nn
  linarith [h_diag_sum, h_ge, h_2S_eq, h_diff]

/-- **L² EXPONENTIAL RATE**: dV/dt ≤ -K·μ·V where
    μ = c_min·δ·(δ+δ*), given α_k ≥ δ, α*_k ≥ δ*, c_k ≥ c_min.
    PROVED (0 sorry). -/
theorem l2_exponential_rate {n : ℕ}
    (γ c : Fin n → ℝ) (K : ℝ) (α α_star : Fin n → ℝ)
    (δ δ_star c_min : ℝ)
    (hK : 0 < K) (_hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hα : ∀ k, 0 < α k) (hα_lt : ∀ k, α k < 1)
    (hα_star : ∀ k, 0 < α_star k) (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE γ c K α_star k = 0)
    (_hδ : 0 < δ) (_hδ_star : 0 < δ_star) (_hc_min : 0 < c_min)
    (hα_lb : ∀ k, δ ≤ α k) (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (hc_lb : ∀ k, c_min ≤ c k) :
    ∑ k, c k * 2 * (α k - α_star k) * nPoleODE γ c K α k ≤
    -(K * c_min * δ * (δ + δ_star)) * l2Distance c α α_star := by
  rw [l2_lyapunov_identity γ c K α α_star hα_star h_equil]
  have h_diag := l2_diagonal_lower_bound c α α_star hc hα hα_lt hα_star hα_star_lt
  have h_lb : c_min * δ * (δ + δ_star) * l2Distance c α α_star ≤
      ∑ k, c k ^ 2 * (α k - α_star k) ^ 2 * (α k * (α_star k + α k)) := by
    unfold l2Distance; rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hck := hc_lb k; have hαk := hα_lb k; have hαsk := hα_star_lb k
    have h1 : c_min * δ ≤ c k * α k := by nlinarith [hc k]
    have h2 : δ + δ_star ≤ α_star k + α k := by linarith
    have h3 : c_min * δ * (δ + δ_star) ≤ c k * α k * (α_star k + α k) := by
      calc c_min * δ * (δ + δ_star)
          ≤ (c k * α k) * (α_star k + α k) :=
            mul_le_mul h1 h2 (by linarith) (by nlinarith [hc k])
        _ = c k * α k * (α_star k + α k) := by ring
    have h4 : c_min * δ * (δ + δ_star) * c k ≤ c k ^ 2 * (α k * (α_star k + α k)) := by
      nlinarith [hc k]
    nlinarith [sq_nonneg (α k - α_star k)]
  have h_chain : c_min * δ * (δ + δ_star) * l2Distance c α α_star ≤
      (∑ j, c j * α_star j) *
        (∑ k, c k * (α k - α_star k) ^ 2 * (α k + 1 / α_star k)) -
      (∑ j, c j * (α j - α_star j)) *
        (∑ k, c k * (α k - α_star k) * (1 - α k ^ 2)) :=
    le_trans h_lb h_diag
  nlinarith

end
