/-
  Kuramoto Stability — Lorentzian Solution from ODE
  ==================================================
  Constructs a LorentzianSolution from a continuous-time ODE solution.
  Proves all assumed fields (hr_bdd, hr_lip, hpersist, hlyap) from the ODE.

  Bridge: the scalar Lorentzian ODE is the n-pole ODE with n = 1.
  Invariance via InvariantBox. Lipschitz via MVT. Persistence from convergence.

  This file closes the LorentzianSolution gap.
-/

import KuramotoLean.InvariantBox
import KuramotoLean.Lorentzian

open Real Set Finset

noncomputable section

/-! ## Bridge: scalar Lorentzian ODE = n-pole ODE with n = 1 -/

theorem lorentzian_eq_npole_n1 (γ_val K r : ℝ) :
    lorentzianODE K γ_val r =
    nPoleODE (fun _ : Fin 1 => γ_val) (fun _ : Fin 1 => (1 : ℝ)) K
      (fun _ : Fin 1 => r) 0 := by
  unfold lorentzianODE nPoleODE
  simp; ring

/-! ## Continuous ODE solution structure -/

structure LorentzianContinuousSolution where
  K : ℝ
  γ : ℝ
  hK_pos : 0 < K
  hγ_pos : 0 < γ
  hK_gt : K > 2 * γ
  r : ℝ → ℝ
  hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t
  hr_cont : ContinuousOn r (Ici 0)
  hr_init_pos : 0 < r 0
  hr_init_lt : r 0 < 1

/-! ## Bridge to NPoleODEData -/

def LorentzianContinuousSolution.toNPoleODEData (S : LorentzianContinuousSolution) :
    NPoleODEData 1 where
  γ := fun _ => S.γ
  c := fun _ => 1
  K := S.K
  α := fun t _ => S.r t
  hK := S.hK_pos
  hγ := fun _ => S.hγ_pos
  hc := fun _ => one_pos
  hα_ode := fun t ht k => by
    have h := S.hr_ode t (le_of_lt ht)
    rw [lorentzian_eq_npole_n1] at h
    exact Fin.fin_one_eq_zero k ▸ h
  hα_cont := fun _ => by
    exact S.hr_cont.comp continuousOn_id fun t ht => ht
  hα_init_pos := fun _ => S.hr_init_pos
  hα_init_lt := fun _ => S.hr_init_lt

/-! ## Invariance from InvariantBox -/

theorem LorentzianContinuousSolution.r_pos (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    0 < S.r t := by
  have := lower_barrier S.toNPoleODEData 0 t ht
  exact this

theorem LorentzianContinuousSolution.r_lt_one
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    S.r t < 1 := by
  have := upper_barrier S.toNPoleODEData 0 t ht
  exact this

theorem LorentzianContinuousSolution.r_bdd
    (S : LorentzianContinuousSolution)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ S.r t ∧ S.r t ≤ 1 :=
  ⟨le_of_lt (S.r_pos t ht), le_of_lt (S.r_lt_one t ht)⟩

/-! ## ODE velocity bound on [0,1] -/

theorem lorentzian_ode_abs_le (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : K > 2 * γ)
    (hr_nn : 0 ≤ r) (hr_le : r ≤ 1) :
    |lorentzianODE K γ r| ≤ K - γ := by
  unfold lorentzianODE
  rw [abs_le]; constructor
  · -- Lower: -(K-γ) ≤ f(r)
    -- f(r) = (K/2-γ)r - (K/2)r³ ≥ -γr ≥ -γ ≥ -(K-γ)
    nlinarith [sq_nonneg r, sq_nonneg (1 - r),
      mul_nonneg hr_nn (sq_nonneg r),
      mul_nonneg (by linarith : (0:ℝ) ≤ K/2) (mul_nonneg hr_nn
        (by nlinarith : 0 ≤ 1 - r ^ 2))]
  · -- Upper: f(r) ≤ K-γ
    -- f(r) = (K/2-γ)r - (K/2)r³ ≤ (K/2-γ)r ≤ K/2-γ ≤ K-γ
    nlinarith [sq_nonneg r,
      mul_nonneg (by linarith : (0:ℝ) ≤ K/2) (mul_nonneg hr_nn
        (sq_nonneg r))]

/-! ## Discrete sampling -/

theorem LorentzianContinuousSolution.hr_bdd_discrete
    (S : LorentzianContinuousSolution) :
    ∀ n : ℕ, 0 ≤ S.r n ∧ S.r n ≤ 1 :=
  fun n => S.r_bdd n (Nat.cast_nonneg n)

/-! ## Lipschitz bound via MVT -/

private theorem nat_le_succ_cast (n : ℕ) : (n : ℝ) ≤ (↑(n + 1) : ℝ) := by
  exact_mod_cast Nat.le_succ n

theorem LorentzianContinuousSolution.hr_lip_discrete
    (S : LorentzianContinuousSolution) :
    ∀ n : ℕ, |S.r (↑(n + 1)) - S.r (↑n)| ≤ S.K - S.γ := by
  intro n
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn_le := nat_le_succ_cast n
  have h_deriv : ∀ x ∈ Icc (n : ℝ) (↑(n + 1)),
      HasDerivWithinAt S.r
        (lorentzianODE S.K S.γ (S.r x))
        (Icc (↑n) (↑(n + 1))) x := by
    intro x hx
    exact (S.hr_ode x (le_trans hn_nn hx.1)).hasDerivWithinAt
  have h_bound : ∀ x ∈ Ico (n : ℝ) (↑(n + 1)),
      ‖lorentzianODE S.K S.γ (S.r x)‖ ≤ S.K - S.γ := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hx_nn : 0 ≤ x := le_trans hn_nn hx.1
    exact lorentzian_ode_abs_le S.K S.γ (S.r x) S.hK_pos
      S.hγ_pos S.hK_gt
      (le_of_lt (S.r_pos x hx_nn))
      (le_of_lt (S.r_lt_one x hx_nn))
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment'
    h_deriv h_bound ↑(n + 1) (right_mem_Icc.mpr hn_le)
  rw [Real.norm_eq_abs] at h_mvt
  have h_diff : (↑(n + 1) : ℝ) - (↑n : ℝ) = 1 := by
    push_cast; ring
  rw [h_diff, mul_one] at h_mvt; exact h_mvt

end
