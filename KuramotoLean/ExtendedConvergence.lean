import KuramotoLean.GlobalStabilitySupercritical
import KuramotoLean.ZeroActivation
import KuramotoLean.UpperBarrier
import KuramotoLean.OneDeactivation

set_option linter.style.longLine false

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

def NPoleBarrierData.shift (ε : ℝ) (hε : 0 < ε) (D : NPoleBarrierData n) : NPoleBarrierData n where
  γ := D.γ
  c := D.c
  K := D.K
  α := fun t k => D.α (t + ε) k
  hK := D.hK
  hγ := D.hγ
  hc := D.hc
  hα_nn := fun t ht k => D.hα_nn (t + ε) (by linarith) k
  hα_le := fun t ht k => D.hα_le (t + ε) (by linarith) k
  hα_ode := fun t ht k => by
    have h := D.hα_ode (t + ε) (by linarith) k
    have hshift : HasDerivAt (fun s => s + ε) 1 t :=
      (hasDerivAt_id t).add_const ε
    have hcomp := h.comp t hshift
    simp only [mul_one] at hcomp
    exact hcomp
  hα_cont := fun k => by
    have hc := D.hα_cont k
    apply ContinuousOn.comp hc ((continuous_id.add continuous_const).continuousOn)
    intro t ht
    simp only [Set.mem_Ici, Pi.add_apply, id] at ht ⊢; linarith [hε]

theorem shift_r (ε : ℝ) (hε : 0 < ε) (D : NPoleBarrierData n) (t : ℝ) :
    (D.shift ε hε).r t = D.r (t + ε) := by
  unfold NPoleBarrierData.r NPoleBarrierData.shift; rfl

theorem parametric_convergence_general (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K)
    (hα_init_lt : ∀ k, D.α 0 k < 1)
    (hα_some_pos : ∃ j, 0 < D.α 0 j) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.r t - r_star| < ε := by
  obtain ⟨j, hj⟩ := hα_some_pos
  set ε₀ : ℝ := 1
  have hε₀ : (0 : ℝ) < ε₀ := one_pos
  set D' := D.shift ε₀ hε₀
  have h_init_pos : ∀ k, 0 < D'.α 0 k := by
    intro k
    show 0 < D.α (0 + ε₀) k
    exact zero_component_activation D k j hj (0 + ε₀) (by linarith)
  have h_init_lt : ∀ k, D'.α 0 k < 1 := by
    intro k
    show D.α (0 + ε₀) k < 1
    exact component_strict_lt_one D hα_init_lt (0 + ε₀) (by linarith) k
  obtain ⟨r_star, hr_pos, hr_lt, hconv⟩ :=
    parametric_convergence D' hn hc_sum hK_super h_init_pos h_init_lt
  refine ⟨r_star, hr_pos, hr_lt, ?_⟩
  intro ε hε
  obtain ⟨T, hT⟩ := hconv ε hε
  refine ⟨T + ε₀, fun t ht => ?_⟩
  have h_shifted := hT (t - ε₀) (by linarith)
  rw [shift_r] at h_shifted
  rwa [show t - ε₀ + ε₀ = t from by ring] at h_shifted

private theorem alpha_lt_one_at_pos (D : NPoleBarrierData n)
    (k : Fin n) (t : ℝ) (ht : 0 < t) :
    D.α t k < 1 := by
  by_cases hlt : D.α 0 k < 1
  · exact component_lt_one_uniform D k (∑ j, D.c j) le_rfl hlt t (le_of_lt ht)
  · have h1 : D.α 0 k = 1 := le_antisymm (D.hα_le 0 le_rfl k) (not_lt.mp hlt)
    exact one_component_deactivation D k h1 t ht

/-- **Maximal convergence**: α(0) ∈ [0,1]^n with ∃j, α_j(0) > 0 suffices.
    This covers ALL initial data except the incoherent equilibrium α = 0. -/
theorem maximal_convergence (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K)
    (hα_some_pos : ∃ j, 0 < D.α 0 j) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.r t - r_star| < ε := by
  obtain ⟨j, hj⟩ := hα_some_pos
  set ε₀ : ℝ := 1
  have hε₀ : (0 : ℝ) < ε₀ := one_pos
  set D' := D.shift ε₀ hε₀
  have h_init_pos : ∀ k, 0 < D'.α 0 k := by
    intro k
    show 0 < D.α (0 + ε₀) k
    exact zero_component_activation D k j hj (0 + ε₀) (by linarith)
  have h_init_lt : ∀ k, D'.α 0 k < 1 := by
    intro k
    show D.α (0 + ε₀) k < 1
    exact alpha_lt_one_at_pos D k (0 + ε₀) (by linarith)
  obtain ⟨r_star, hr_pos, hr_lt, hconv⟩ :=
    parametric_convergence D' hn hc_sum hK_super h_init_pos h_init_lt
  refine ⟨r_star, hr_pos, hr_lt, ?_⟩
  intro ε hε
  obtain ⟨T, hT⟩ := hconv ε hε
  refine ⟨T + ε₀, fun t ht => ?_⟩
  have h_shifted := hT (t - ε₀) (by linarith)
  rw [shift_r] at h_shifted
  rwa [show t - ε₀ + ε₀ = t from by ring] at h_shifted

end
