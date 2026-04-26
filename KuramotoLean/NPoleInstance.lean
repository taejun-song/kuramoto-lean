/-
  Kuramoto Stability — N-Pole ODE Instance
  ==========================================
  Constructs NPoleTrajectoryData from an abstract n-pole ODE solution.
  This is the general analogue of LorentzianInstance.lean for n ≥ 2.

  Given an n-pole ODE solution (trajectory + equilibrium + bounds),
  applies the L² Lyapunov chain to prove:
    α_k(t) → α*_k for all k (exponential rate)
    r(t) → r* (order parameter convergence)

  0 sorry.
-/

import KuramotoLean.GronwallBridge
import KuramotoLean.OrderParameterRate

open Real Set

noncomputable section

variable {n : ℕ}

/-- An n-pole OA ODE solution with the structural properties
    needed for the L² Lyapunov convergence chain. -/
structure NPoleODESolution (n : ℕ) where
  γ : Fin n → ℝ
  c : Fin n → ℝ
  K : ℝ
  α : ℝ → Fin n → ℝ
  α_star : Fin n → ℝ
  hK : 0 < K
  hγ : ∀ k, 0 < γ k
  hc : ∀ k, 0 < c k
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  δ : ℝ
  δ_star : ℝ
  c_min : ℝ
  hδ : 0 < δ
  hδ_star : 0 < δ_star
  hc_min : 0 < c_min
  hα_lb : ∀ t, 0 ≤ t → ∀ k, δ ≤ α t k
  hα_lt : ∀ t, 0 ≤ t → ∀ k, α t k < 1
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  hc_lb : ∀ k, c_min ≤ c k
  hα_ode : ∀ t, 0 < t → ∀ k,
    HasDerivAt (fun s => α s k) (nPoleODE γ c K (α t) k) t
  hV_cont : ContinuousOn
    (fun t => l2Distance c (α t) α_star) (Ici 0)

def NPoleODESolution.r (S : NPoleODESolution n) (t : ℝ) : ℝ :=
  ∑ k, S.c k * S.α t k

def NPoleODESolution.r_star (S : NPoleODESolution n) : ℝ :=
  ∑ k, S.c k * S.α_star k

/-- Construct NPoleTrajectoryData from an n-pole ODE solution. -/
def NPoleODESolution.toTrajectoryData
    (S : NPoleODESolution n) : NPoleTrajectoryData n where
  γ := S.γ
  c := S.c
  K := S.K
  α := S.α
  α_star := S.α_star
  δ := S.δ
  δ_star := S.δ_star
  c_min := S.c_min
  hK := S.hK
  hγ := S.hγ
  hc := S.hc
  h_equil := S.h_equil
  hα_star_pos := S.hα_star_pos
  hα_star_lt := S.hα_star_lt
  hδ := S.hδ
  hδ_star := S.hδ_star
  hc_min := S.hc_min
  hα_lb := S.hα_lb
  hα_lt := S.hα_lt
  hα_star_lb := S.hα_star_lb
  hc_lb := S.hc_lb
  hα_ode := S.hα_ode
  hV_cont := S.hV_cont

/-- The exponential convergence rate for the n-pole system. -/
def NPoleODESolution.rate (S : NPoleODESolution n) : ℝ :=
  S.K * S.c_min * S.δ * (S.δ + S.δ_star)

/-- **N-pole L² exponential decay.**
    V(t) ≤ V(0)·exp(-μt) where μ = K·c_min·δ·(δ+δ*). -/
theorem npole_ode_l2_decay (S : NPoleODESolution n) :
    ∀ t, 0 ≤ t →
      l2Distance S.c (S.α t) S.α_star ≤
        l2Distance S.c (S.α 0) S.α_star *
        exp (-S.rate * t) :=
  npole_exponential_l2_decay S.toTrajectoryData

/-- **N-pole pointwise convergence.**
    Each α_k(t) → α*_k with exponential rate. -/
theorem npole_ode_convergence (S : NPoleODESolution n)
    (hV0 : 0 < l2Distance S.c (S.α 0) S.α_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → ∀ k,
      |S.α t k - S.α_star k| < ε :=
  npole_l2_global_stability S.toTrajectoryData hV0

/-- **N-pole order parameter convergence.**
    r(t) = Σ c_k α_k(t) → r* = Σ c_k α*_k. -/
theorem npole_r_convergence (S : NPoleODESolution n)
    (hV0 : 0 < l2Distance S.c (S.α 0) S.α_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |S.r t - S.r_star| ≤ (∑ k : Fin n, S.c k) * ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := npole_ode_convergence S hV0 ε hε
  exact ⟨T, fun t ht =>
    order_parameter_from_pointwise S.c (S.α t) S.α_star ε
      (fun k => le_of_lt (S.hc k))
      (fun k => le_of_lt (hT t ht k))⟩

/-! ## Order parameter exponential convergence via Cauchy-Schwarz

For probability weights (Σ c_k = 1), Cauchy-Schwarz gives (r-r*)² ≤ V directly.
Combined with exponential L² decay V(t) ≤ V₀·exp(-μt), this yields:
  |r(t) - r*| ≤ √V₀ · exp(-μt/2)

This is TIGHTER than the pointwise route (npole_r_convergence), which loses
a factor through c_min extraction. The rate μ = K·c_min·δ·(δ+δ*) is
inherited at full strength. -/

theorem NPoleODESolution.r_diff_eq (S : NPoleODESolution n) (t : ℝ) :
    S.r t - S.r_star = ∑ k, S.c k * (S.α t k - S.α_star k) := by
  simp only [NPoleODESolution.r, NPoleODESolution.r_star, ← Finset.sum_sub_distrib]
  congr 1; ext k; ring

/-- **(r(t) - r*)² ≤ V(t) for probability weights.** -/
theorem NPoleODESolution.r_sq_le_V (S : NPoleODESolution n)
    (hc_prob : ∑ k, S.c k = 1) (t : ℝ) :
    (S.r t - S.r_star) ^ 2 ≤ l2Distance S.c (S.α t) S.α_star := by
  rw [S.r_diff_eq t]
  exact order_parameter_sq_le_l2 S.c (S.α t) S.α_star
    (fun k => le_of_lt (S.hc k)) hc_prob

/-- **Order parameter exponential bound.**
    |r(t) - r*|² ≤ V₀ · exp(-μt) where μ = K·c_min·δ·(δ+δ*). -/
theorem NPoleODESolution.r_exponential_bound (S : NPoleODESolution n)
    (hc_prob : ∑ k, S.c k = 1) :
    ∀ t, 0 ≤ t →
      (S.r t - S.r_star) ^ 2 ≤
        l2Distance S.c (S.α 0) S.α_star * exp (-S.rate * t) :=
  fun t ht => le_trans (S.r_sq_le_V hc_prob t) (npole_ode_l2_decay S t ht)

/-- **Order parameter exponential convergence (Cauchy-Schwarz).**
    For probability weights: r(t) → r* without c_min loss. -/
theorem npole_r_cauchy_schwarz (S : NPoleODESolution n)
    (hc_prob : ∑ k, S.c k = 1) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |S.r t - S.r_star| < ε := by
  intro ε hε
  set V₀ := l2Distance S.c (S.α 0) S.α_star
  by_cases hV : V₀ = 0
  · exact ⟨0, fun t ht => by
      have h_nn := l2Distance_nonneg S.c (S.α t) S.α_star
        (fun k => le_of_lt (S.hc k))
      have h_le : l2Distance S.c (S.α t) S.α_star ≤ 0 :=
        calc l2Distance S.c (S.α t) S.α_star
            ≤ V₀ * exp (-S.rate * t) := npole_ode_l2_decay S t ht
          _ = 0 := by rw [hV, zero_mul]
      have h_sq := le_trans (S.r_sq_le_V hc_prob t) (le_antisymm h_le h_nn ▸ le_refl 0)
      have := sq_nonneg (S.r t - S.r_star)
      rw [show S.r t - S.r_star = 0 from by nlinarith] at *
      simpa using hε⟩
  · have hV_pos : 0 < V₀ := lt_of_le_of_ne
      (l2Distance_nonneg S.c (S.α 0) S.α_star (fun k => le_of_lt (S.hc k)))
      (Ne.symm hV)
    have hrate : 0 < S.rate := S.toTrajectoryData.rate_pos
    obtain ⟨T, hT⟩ := exponential_decay_convergence
      (fun t => l2Distance S.c (S.α t) S.α_star) V₀ S.rate
      hrate hV_pos (npole_ode_l2_decay S) (ε ^ 2) (by positivity)
    exact ⟨T, fun t ht =>
      abs_lt_of_sq_lt_sq
        (lt_of_le_of_lt (S.r_sq_le_V hc_prob t) (hT t ht))
        (le_of_lt hε)⟩

end
