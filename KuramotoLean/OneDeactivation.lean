/-
  Kuramoto Stability — One Component Deactivation
  =================================================

  Proves α_k(t) < 1 for all t > 0 when α_k(0) = 1, from the n-pole ODE.
  At α_k = 1, dα_k/dt = -γ_k < 0, so the component drops immediately.
  Combined with ZeroActivation, this handles all initial data in [0,1]^n.

  0 sorry target.
-/

import KuramotoLean.UpperBarrier

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-- Components at the upper boundary α_k = 1 immediately drop below 1. -/
theorem one_component_deactivation (D : NPoleBarrierData n)
    (k : Fin n) (h1 : D.α 0 k = 1) :
    ∀ t, 0 < t → D.α t k < 1 := by
  intro t ht
  by_contra h_neg
  push Not at h_neg
  have ht_eq : D.α t k = 1 := le_antisymm (D.hα_le t (le_of_lt ht) k) h_neg
  have h_const : ∀ s, 0 ≤ s → s ≤ t → D.α s k = 1 :=
    alpha_one_backward D k t (le_of_lt ht) ht_eq
  have hf_cont : ContinuousOn (fun s => D.α s k) (Icc 0 t) :=
    (D.hα_cont k).mono Icc_subset_Ici_self
  have hf_deriv : ∀ s ∈ interior (Icc 0 t), deriv (fun s => D.α s k) s < 0 := by
    rw [interior_Icc]
    intro s ⟨hs_lo, hs_hi⟩
    have hs_eq : D.α s k = 1 := h_const s (le_of_lt hs_lo) (le_of_lt hs_hi)
    have h_ode : HasDerivAt (fun s => D.α s k) (nPoleODE D.γ D.c D.K (D.α s) k) s :=
      D.hα_ode s hs_lo k
    rw [h_ode.deriv]
    unfold nPoleODE
    rw [hs_eq]
    nlinarith [D.hγ k, D.r_nonneg s (le_of_lt hs_lo)]
  have hf_anti := strictAntiOn_of_deriv_neg (convex_Icc 0 t) hf_cont hf_deriv
  have := hf_anti (left_mem_Icc.mpr (le_of_lt ht)) (right_mem_Icc.mpr (le_of_lt ht)) ht
  linarith [h1, ht_eq]

end
