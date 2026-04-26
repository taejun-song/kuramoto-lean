/-
  Kuramoto Stability — Instability of Incoherence
  =================================================

  For the n-pole OA ODE, the incoherent state α = 0 has Jacobian
  J = -diag(γ) + (K/2) c ⊗ 1, a rank-1 perturbation of a diagonal.

  The dispersion relation: h(lam) = (K/2) Σ c_k/(lam + γ_k) = 1.
  The critical coupling: K_c = 2 / (Σ c_k/γ_k).
  When K > K_c: h(0) > 1, h(Λ) < 1, so by IVT ∃ lam* > 0 (unstable eigenvalue).

  0 sorry.
-/

import KuramotoLean.RationalOA
import Mathlib.Topology.Order.IntermediateValue

open Real Finset

noncomputable section

/-! ## The dispersion function -/

def npoleDispersion {n : ℕ} (γ c : Fin n → ℝ) (K lam : ℝ) : ℝ :=
  (K / 2) * ∑ k : Fin n, c k / (lam + γ k)

def npoleCriticalK {n : ℕ} (γ c : Fin n → ℝ) : ℝ :=
  2 / (∑ k : Fin n, c k / γ k)

theorem npoleDispersion_at_zero {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ) :
    npoleDispersion γ c K 0 = (K / 2) * ∑ k, c k / γ k := by
  simp [npoleDispersion, zero_add]

theorem npoleDispersion_supercritical {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n))
    (hK : npoleCriticalK γ c < K) :
    1 < npoleDispersion γ c K 0 := by
  rw [npoleDispersion_at_zero]
  have hsum_pos : 0 < ∑ k : Fin n, c k / γ k :=
    Finset.sum_pos (fun k _ => div_pos (hc k) (hγ k))
      (Finset.univ_nonempty (α := Fin n))
  unfold npoleCriticalK at hK
  rw [div_lt_iff₀ hsum_pos] at hK
  linarith

theorem npoleDispersion_eventually_small {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n))
    (hK : 0 < K) :
    ∃ big : ℝ, 0 < big ∧ npoleDispersion γ c K big < 1 := by
  set Sc := ∑ k : Fin n, c k
  have hSc_pos : 0 < Sc :=
    Finset.sum_pos (fun k _ => hc k) (Finset.univ_nonempty (α := Fin n))
  refine ⟨K * Sc, mul_pos hK hSc_pos, ?_⟩
  unfold npoleDispersion
  have hKSc_pos : 0 < K * Sc := mul_pos hK hSc_pos
  have h_upper : ∀ k : Fin n, c k / (K * Sc + γ k) ≤ c k / (K * Sc) := by
    intro k
    exact div_le_div_of_nonneg_left (le_of_lt (hc k)) hKSc_pos (by linarith [hγ k])
  have h_sum_bound : (∑ k, c k / (K * Sc + γ k)) ≤ Sc / (K * Sc) := by
    calc ∑ k, c k / (K * Sc + γ k)
        ≤ ∑ k, c k / (K * Sc) := Finset.sum_le_sum (fun k _ => h_upper k)
      _ = (∑ k, c k) / (K * Sc) := by rw [Finset.sum_div]
      _ = Sc / (K * Sc) := by rfl
  have h_cancel : Sc / (K * Sc) = 1 / K := by field_simp
  calc (K / 2) * ∑ k, c k / (K * Sc + γ k)
      ≤ (K / 2) * (Sc / (K * Sc)) := by
        exact mul_le_mul_of_nonneg_left h_sum_bound (by linarith)
    _ = (K / 2) * (1 / K) := by rw [h_cancel]
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

theorem npoleDispersion_continuous {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) :
    ContinuousOn (npoleDispersion γ c K) (Set.Ici 0) := by
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.div continuousOn_const
    ((continuous_id.add continuous_const).continuousOn)
  intro x hx
  have : 0 ≤ x := Set.mem_Ici.mp hx
  change x + γ k ≠ 0
  linarith [hγ k]

/-! ## Main theorem: existence of unstable eigenvalue -/

/-- **Instability of incoherence.** When K > K_c, the dispersion relation
    h(lam) = 1 has a positive root. This is the unstable eigenvalue of
    the rank-1 Jacobian at the incoherent state α = 0. -/
theorem incoherence_unstable {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (hγ : ∀ k, 0 < γ k) (hc : ∀ k, 0 < c k)
    (hn : Nonempty (Fin n)) (hK_pos : 0 < K)
    (hK : npoleCriticalK γ c < K) :
    ∃ lam_star : ℝ, 0 < lam_star ∧ npoleDispersion γ c K lam_star = 1 := by
  obtain ⟨big, hbig_pos, hbig_small⟩ := npoleDispersion_eventually_small γ c K hγ hc hn hK_pos
  have h0_big := npoleDispersion_supercritical γ c K hγ hc hn hK
  have hcont := npoleDispersion_continuous γ c K hγ
  have h_ivt := IsPreconnected.intermediate_value₂
    (isPreconnected_Icc (a := (0 : ℝ)) (b := big))
    (Set.right_mem_Icc.mpr (le_of_lt hbig_pos))
    (Set.left_mem_Icc.mpr (le_of_lt hbig_pos))
    (hcont.mono (fun x hx => Set.mem_Ici.mpr (Set.mem_Icc.mp hx).1))
    continuousOn_const
    (le_of_lt hbig_small)
    (le_of_lt h0_big)
  obtain ⟨lam_star, hlam_mem, hlam_eq⟩ := h_ivt
  have hlam_nn : 0 ≤ lam_star := (Set.mem_Icc.mp hlam_mem).1
  have hlam_ne : lam_star ≠ 0 := by
    intro heq; subst heq; linarith
  exact ⟨lam_star, lt_of_le_of_ne hlam_nn (Ne.symm hlam_ne), hlam_eq⟩

/-! ## The Jacobian at incoherence -/

/-- The Jacobian of the n-pole ODE at α = 0:
    J_{kj} = -γ_k δ_{kj} + (K/2) c_j. -/
def jacobianAtZero {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ) (k j : Fin n) : ℝ :=
  (if k = j then -γ k else 0) + (K / 2) * c j

/-- The Jacobian action matches the linearized ODE at α = 0:
    Σ_j J_{kj} v_j = -γ_k v_k + (K/2)(Σ c_j v_j). -/
theorem jacobian_action {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (v : Fin n → ℝ) (k : Fin n) :
    ∑ j, jacobianAtZero γ c K k j * v j =
    -γ k * v k + (K / 2) * ∑ j, c j * v j := by
  unfold jacobianAtZero
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · conv_lhs => arg 2; ext j; rw [show (if k = j then -γ k else (0 : ℝ)) * v j =
      if k = j then -γ k * v j else 0 by split <;> simp [*]]
    simp
  · conv_lhs => arg 2; ext j; rw [show (K / 2) * c j * v j = (K / 2) * (c j * v j) by ring]
    rw [← Finset.mul_sum]

/-- The linearization of nPoleODE at α = 0:
    to first order in v, f_k(v) = -γ_k v_k + (K/2)(Σ c_j v_j). -/
theorem linearization_at_zero {n : ℕ} (γ c : Fin n → ℝ) (K : ℝ)
    (v : Fin n → ℝ) (k : Fin n) :
    nPoleODE γ c K v k =
    -γ k * v k + (K / 2) * (∑ j, c j * v j) - (K / 2) * (∑ j, c j * v j) * v k ^ 2 := by
  unfold nPoleODE; ring

/-! ## The unstable eigenvector is positive

When λ* > 0 solves h(λ*) = 1, the eigenvector v_k = c_k/(λ* + γ_k) > 0
for all k (since c_k > 0, λ* > 0, γ_k > 0). The order parameter
r = Σ c_k v_k > 0 along this direction. This means:
1. The instability direction points INTO the positive orthant (0,∞)^n
2. The order parameter grows exponentially in the unstable direction -/

/-- The eigenvector at the unstable eigenvalue: v_k = 1/(lam + γ_k). -/
def unstableEigenvector {n : ℕ} (γ : Fin n → ℝ) (lam : ℝ) (k : Fin n) : ℝ :=
  1 / (lam + γ k)

/-- The eigenvector is strictly positive when lam > 0. -/
theorem unstableEigenvector_pos {n : ℕ} (γ : Fin n → ℝ) (lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hlam : 0 < lam) (k : Fin n) :
    0 < unstableEigenvector γ lam k :=
  div_pos one_pos (by linarith [hγ k])

/-- The eigenvector satisfies the eigenvalue equation: Σ_j J_{kj} v_j = λ* v_k.
    With v_j = 1/(λ*+γ_j): LHS = -γ_k/(λ*+γ_k) + (K/2)Σc_j/(λ*+γ_j)
    = -γ_k/(λ*+γ_k) + 1 (dispersion) = λ*/(λ*+γ_k) = λ* v_k. -/
theorem eigenvector_equation {n : ℕ} (γ c : Fin n → ℝ) (K lam : ℝ)
    (hγ : ∀ k, 0 < γ k) (hlam : 0 < lam)
    (hdisp : npoleDispersion γ c K lam = 1) (k : Fin n) :
    ∑ j, jacobianAtZero γ c K k j * unstableEigenvector γ lam j =
    lam * unstableEigenvector γ lam k := by
  rw [jacobian_action]
  unfold unstableEigenvector
  have hden : (0 : ℝ) < lam + γ k := by linarith [hγ k]
  have hden_ne : lam + γ k ≠ 0 := ne_of_gt hden
  unfold npoleDispersion at hdisp
  have hR : (K / 2) * ∑ j, c j * (1 / (lam + γ j)) = 1 := by
    have : ∀ j : Fin n, c j * (1 / (lam + γ j)) = c j / (lam + γ j) := by
      intro j; ring
    simp_rw [this]; exact hdisp
  rw [hR]
  field_simp
  ring

/-- The order parameter Σ c_k v_k = 2/K along the eigenvector (by dispersion). -/
theorem eigenvector_order_parameter {n : ℕ} (γ c : Fin n → ℝ) (K lam : ℝ)
    (hK : 0 < K) (hdisp : npoleDispersion γ c K lam = 1) :
    ∑ k, c k * unstableEigenvector γ lam k = 2 / K := by
  unfold unstableEigenvector npoleDispersion at *
  have hK_ne : K ≠ 0 := ne_of_gt hK
  have : K / 2 * ∑ k, c k / (lam + γ k) = 1 := hdisp
  have hsum : ∑ k, c k / (lam + γ k) = 2 / K := by
    field_simp at this ⊢; linarith
  simp_rw [show ∀ k : Fin n, c k * (1 / (lam + γ k)) = c k / (lam + γ k) from fun k => by ring]
  exact hsum

/-- The order parameter is positive along the unstable eigenvector. -/
theorem eigenvector_r_pos {n : ℕ} (γ c : Fin n → ℝ) (K lam : ℝ)
    (hK : 0 < K) (hdisp : npoleDispersion γ c K lam = 1) :
    0 < ∑ k, c k * unstableEigenvector γ lam k := by
  rw [eigenvector_order_parameter γ c K lam hK hdisp]
  exact div_pos (by norm_num) hK

/-! ## Lorentzian specialization: K_c = 2γ -/

/-- For the Lorentzian (n=1, c₀=1): K_c = 2γ. -/
theorem lorentzian_critical_coupling (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    npoleCriticalK (n := 1) (fun _ => γ₀) (fun _ => 1) = 2 * γ₀ := by
  unfold npoleCriticalK
  simp [Finset.sum_singleton, Finset.univ_unique]

/-- For the Lorentzian, K > 2γ implies instability of incoherence. -/
theorem lorentzian_incoherence_unstable (γ₀ K : ℝ) (hγ₀ : 0 < γ₀) (hK : 0 < K) (hKγ : 2 * γ₀ < K) :
    ∃ lam_star : ℝ, 0 < lam_star ∧
    npoleDispersion (n := 1) (fun _ => γ₀) (fun _ => 1) K lam_star = 1 := by
  apply incoherence_unstable (fun _ => γ₀) (fun _ => 1) K (fun _ => hγ₀) (fun _ => one_pos)
    ⟨0⟩ hK
  rw [lorentzian_critical_coupling γ₀ hγ₀]
  exact hKγ

end
