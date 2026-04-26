/-
  Kuramoto Stability — Equilibrium Uniqueness
  ==============================================

  For the n-pole ODE dα_k/dt = -γ_k α_k + (K/2)r(1-α_k²),
  the equilibrium equation f(α) = -γα + (K/2)r(1-α²) = 0 has
  exactly one root in (0,1) when r > 0.

  Proof:
    f(0) = (K/2)r > 0
    f(1) = -γ < 0
    f'(α) = -γ - Krα < 0 on (0,1)
    → IVT gives existence, strict monotonicity gives uniqueness.

  This grounds the α* hypotheses in EndToEndData and KuramotoData.

  0 sorry target.
-/

import KuramotoLean.RationalOA
import Mathlib.Topology.Order.IntermediateValue

open Real Set

noncomputable section

variable {n : ℕ}

def componentEquil (γ_k K r : ℝ) (α : ℝ) : ℝ :=
  -γ_k * α + (K / 2) * r * (1 - α ^ 2)

theorem componentEquil_eq_nPoleODE (γ c : Fin n → ℝ) (K : ℝ) (α : Fin n → ℝ)
    (k : Fin n) (r : ℝ) (hr : r = ∑ j, c j * α j) :
    componentEquil (γ k) K r (α k) = nPoleODE γ c K α k := by
  unfold componentEquil nPoleODE; rw [hr]

theorem componentEquil_at_zero (γ_k K r : ℝ) :
    componentEquil γ_k K r 0 = (K / 2) * r := by
  unfold componentEquil; ring

theorem componentEquil_at_one (γ_k K r : ℝ) :
    componentEquil γ_k K r 1 = -γ_k := by
  unfold componentEquil; ring

theorem componentEquil_continuous (γ_k K r : ℝ) :
    Continuous (componentEquil γ_k K r) := by
  unfold componentEquil
  exact ((continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))))

theorem componentEquil_strictAntiOn (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    StrictAntiOn (componentEquil γ_k K r) (Icc 0 1) := by
  intro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩ hab
  unfold componentEquil
  have h_factor : -γ_k * b + (K / 2) * r * (1 - b ^ 2) -
      (-γ_k * a + (K / 2) * r * (1 - a ^ 2)) =
      (a - b) * (γ_k + (K / 2) * r * (a + b)) := by ring
  have h_neg : (a - b) * (γ_k + (K / 2) * r * (a + b)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

theorem equilibrium_exists (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    ∃ α_star, 0 < α_star ∧ α_star < 1 ∧ componentEquil γ_k K r α_star = 0 := by
  have hf0 : 0 < componentEquil γ_k K r 0 := by
    rw [componentEquil_at_zero]; positivity
  have hf1 : componentEquil γ_k K r 1 < 0 := by
    rw [componentEquil_at_one]; linarith
  obtain ⟨α_star, hα_mem, hα_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr zero_le_one)
      (right_mem_Icc.mpr zero_le_one)
      continuousOn_const
      ((componentEquil_continuous γ_k K r).continuousOn)
      (le_of_lt hf0)
      (le_of_lt hf1)
  obtain ⟨hα0, hα1⟩ := mem_Icc.mp hα_mem
  exact ⟨α_star,
    lt_of_le_of_ne hα0 (fun h => by rw [← h] at hα_eq; linarith),
    lt_of_le_of_ne hα1 (fun h => by rw [h] at hα_eq; linarith),
    hα_eq.symm⟩

theorem equilibrium_unique (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hfa : componentEquil γ_k K r a = 0) (hfb : componentEquil γ_k K r b = 0) :
    a = b := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exfalso
    have := componentEquil_strictAntiOn γ_k K r hγ hK hr ⟨ha, ha1⟩ ⟨hb, hb1⟩ hab
    linarith
  · rfl
  · exfalso
    have := componentEquil_strictAntiOn γ_k K r hγ hK hr ⟨hb, hb1⟩ ⟨ha, ha1⟩ hab
    linarith

theorem equilibrium_unique_in_open (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    ∃! α_star, 0 < α_star ∧ α_star < 1 ∧ componentEquil γ_k K r α_star = 0 := by
  obtain ⟨α, hα_pos, hα_lt, hα_eq⟩ := equilibrium_exists γ_k K r hγ hK hr
  exact ⟨α, ⟨hα_pos, hα_lt, hα_eq⟩, fun b ⟨hb_pos, hb_lt, hb_eq⟩ =>
    equilibrium_unique γ_k K r hγ hK hr b α (le_of_lt hb_pos) (le_of_lt hb_lt)
      (le_of_lt hα_pos) (le_of_lt hα_lt) hb_eq hα_eq⟩

/-! ## Vector equilibrium construction

For each component k with damping γ_k > 0 and coupling K > 0
at order parameter r > 0, construct the unique equilibrium α*_k ∈ (0,1). -/

noncomputable def equilibriumComponent (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) : ℝ :=
  (equilibrium_exists γ_k K r hγ hK hr).choose

theorem equilibriumComponent_pos (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    0 < equilibriumComponent γ_k K r hγ hK hr :=
  (equilibrium_exists γ_k K r hγ hK hr).choose_spec.1

theorem equilibriumComponent_lt_one (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    equilibriumComponent γ_k K r hγ hK hr < 1 :=
  (equilibrium_exists γ_k K r hγ hK hr).choose_spec.2.1

theorem equilibriumComponent_equil (γ_k K r : ℝ) (hγ : 0 < γ_k) (hK : 0 < K) (hr : 0 < r) :
    componentEquil γ_k K r (equilibriumComponent γ_k K r hγ hK hr) = 0 :=
  (equilibrium_exists γ_k K r hγ hK hr).choose_spec.2.2

/-- **The equilibrium vector α* for the n-pole system.** -/
noncomputable def equilibriumVector {n : ℕ} (γ : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) : Fin n → ℝ :=
  fun k => equilibriumComponent (γ k) K r (hγ k) hK hr

theorem equilibriumVector_pos {n : ℕ} (γ : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) (k : Fin n) :
    0 < equilibriumVector γ K r hγ hK hr k :=
  equilibriumComponent_pos (γ k) K r (hγ k) hK hr

theorem equilibriumVector_lt_one {n : ℕ} (γ : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) (k : Fin n) :
    equilibriumVector γ K r hγ hK hr k < 1 :=
  equilibriumComponent_lt_one (γ k) K r (hγ k) hK hr

theorem equilibriumVector_equil {n : ℕ} (γ : Fin n → ℝ) (K r : ℝ)
    (hγ : ∀ k, 0 < γ k) (hK : 0 < K) (hr : 0 < r) (k : Fin n) :
    componentEquil (γ k) K r (equilibriumVector γ K r hγ hK hr k) = 0 :=
  equilibriumComponent_equil (γ k) K r (hγ k) hK hr

end
