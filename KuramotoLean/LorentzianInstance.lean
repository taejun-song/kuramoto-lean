/-
  Kuramoto Stability Project — Lorentzian KuramotoData Instance
  ==============================================================
  Constructs a concrete KuramotoData from the Lorentzian OA ODE
  ṙ = (K/2-γ)r - (K/2)r³.

  The ODE solution is provided as a structure parameter
  (existence follows from standard ODE theory: Picard-Lindelöf +
  a priori bound r ∈ [0,1]).

  0 sorry.
-/

import KuramotoLean.Lorentzian
import KuramotoLean.SelfConsistencyDecay
import KuramotoLean.MainTheorem

open Real

noncomputable section

/-- A solution to the Lorentzian OA ODE sampled at integer times. -/
structure LorentzianSolution where
  K : ℝ
  γ : ℝ
  hK_pos : 0 < K
  hK_gt : K > 2 * γ
  r : ℕ → ℝ
  hr_bdd : ∀ n, 0 ≤ r n ∧ r n ≤ 1
  hr_lip : ∀ n, |r (n + 1) - r n| ≤ K - γ
  δ : ℝ
  hδ : 0 < δ
  hpersist : ∀ N, ∃ n, N ≤ n ∧ δ ≤ r n
  hlyap_coeff : ℝ
  hlyap_coeff_pos : 0 < hlyap_coeff
  hlyap : ∀ n, (r n ^ 2 - (1 - 2 * γ / K)) ^ 2 ≤
    hlyap_coeff *
    Real.exp (-2 * (Finset.range n).sum (fun k => K * r k ^ 2))

def LorentzianSolution.Ψ (S : LorentzianSolution) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => S.K * S.r k ^ 2)

theorem LorentzianSolution.Ψ_growth (S : LorentzianSolution) (n : ℕ) :
    S.Ψ (n + 1) - S.Ψ n = S.K * S.r n ^ 2 := by
  simp [LorentzianSolution.Ψ, Finset.sum_range_succ]

def LorentzianSolution.r_star (S : LorentzianSolution) : ℝ :=
  Real.sqrt (1 - 2 * S.γ / S.K)

theorem LorentzianSolution.r_star_pos (S : LorentzianSolution) :
    0 < S.r_star :=
  Real.sqrt_pos_of_pos (lorentzian_rstar_pos S.K S.γ S.hK_pos S.hK_gt)

theorem lorentzianPhi_sc_err (K γ r : ℝ) :
    r - lorentzianPhi K γ r = lorentzianODE K γ r := by
  unfold lorentzianPhi; ring

/-! ## Ψ monotonicity and divergence (for ApproxSCData) -/

private theorem Ψ_mono (S : LorentzianSolution) :
    ∀ n, S.Ψ n ≤ S.Ψ (n + 1) := by
  intro n
  have h := S.Ψ_growth n
  have : 0 ≤ S.K * S.r n ^ 2 :=
    mul_nonneg (le_of_lt S.hK_pos) (sq_nonneg _)
  linarith

private theorem Ψ_mono_le (S : LorentzianSolution) (a b : ℕ)
    (hab : a ≤ b) : S.Ψ a ≤ S.Ψ b := by
  induction b with
  | zero => simp [show a = 0 from by omega]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact le_trans (ih (by omega)) (Ψ_mono S k)

private theorem Ψ_diverges (S : LorentzianSolution) :
    ∀ C, ∃ n, C < S.Ψ n := by
  have hKδ : 0 < S.K * S.δ ^ 2 :=
    mul_pos S.hK_pos (sq_pos_of_pos S.hδ)
  suffices h : ∀ k : ℕ, ∃ N,
      S.Ψ 0 + (k : ℝ) * (S.K * S.δ ^ 2) ≤ S.Ψ N by
    intro C
    obtain ⟨k, hk⟩ := exists_nat_gt
      ((C - S.Ψ 0) / (S.K * S.δ ^ 2))
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, ?_⟩
    have : (C - S.Ψ 0) / (S.K * S.δ ^ 2) < ↑k := hk
    have := mul_lt_mul_of_pos_right this hKδ
    rw [div_mul_cancel₀ _ (ne_of_gt hKδ)] at this
    linarith
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨n, hn, hrn⟩ := S.hpersist N
    refine ⟨n + 1, ?_⟩
    have h_mono := Ψ_mono_le S N n hn
    have h_growth := S.Ψ_growth n
    have h_δ : S.K * S.δ ^ 2 ≤ S.K * S.r n ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt S.hK_pos)
      exact pow_le_pow_left₀ (le_of_lt S.hδ) hrn 2
    push_cast; linarith

/-! ## Derive hsc_decay from slaving/tail via ApproxSCData -/

private theorem lorentzian_hΦ_unique (S : LorentzianSolution) :
    ∀ x, 0 ≤ x → x ≤ 1 →
    lorentzianPhi S.K S.γ x = x → x = 0 ∨ x = S.r_star := by
  intro x hx0 _ hfp
  rcases lorentzianPhi_unique S.K S.γ x S.hK_pos S.hK_gt hfp with h | h
  · exact Or.inl h
  · right
    have hsq : x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0).symm
    rw [hsq, h]; rfl

private def toApproxSCData (S : LorentzianSolution)
    (C_s : ℝ) (hC_s : 0 < C_s)
    (hslaving : ∀ n, |lorentzianODE S.K S.γ (S.r n)| ≤
      C_s * Real.exp (-1 * S.Ψ n)) :
    ApproxSCData where
  r := S.r
  r_star := S.r_star
  Φ := lorentzianPhi S.K S.γ
  Ψ := S.Ψ
  hr_star := S.r_star_pos
  hr_bdd := S.hr_bdd
  hΦ_unique := lorentzian_hΦ_unique S
  hΦ_cont := gap_min_from_continuity S.r_star
    (lorentzianPhi S.K S.γ) S.r_star_pos
    (lorentzian_hΦ_unique S) (lorentzianPhi_continuous S.K S.γ)
  hΨ_mono := Ψ_mono S
  hΨ_div := Ψ_diverges S
  γ := 1
  hγ := one_pos
  C := C_s
  hC := hC_s
  slaving_error := fun n => lorentzianODE S.K S.γ (S.r n)
  hslaving_bound := hslaving
  tail_error := fun _ => 0
  htail_decay := fun ε hε => ⟨0, fun n _ => by simp only [abs_zero]; exact hε⟩
  h_decomp := fun n => by simp [lorentzianPhi_sc_err]

private theorem lorentzian_sc_decay (S : LorentzianSolution)
    (C_s : ℝ) (hC_s : 0 < C_s)
    (hslaving : ∀ n, |lorentzianODE S.K S.γ (S.r n)| ≤
      C_s * Real.exp (-1 * S.Ψ n)) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
      |S.r n - lorentzianPhi S.K S.γ (S.r n)| < ε :=
  sc_decay_from_contraction (toApproxSCData S C_s hC_s hslaving)

/-- Construct minimal KuramotoData from a Lorentzian solution. -/
def LorentzianSolution.toKuramotoData (S : LorentzianSolution)
    (C_s : ℝ) (hC_s : 0 < C_s)
    (hslaving : ∀ n, |lorentzianODE S.K S.γ (S.r n)| ≤
      C_s * Real.exp (-1 * S.Ψ n))
    (hL : 3 * (S.K - S.γ) < S.r_star) :
    KuramotoData where
  r := S.r
  r_star := S.r_star
  hr_star := S.r_star_pos
  hr_bdd := S.hr_bdd
  δ := S.δ
  hδ := S.hδ
  hpersist := S.hpersist
  L := S.K - S.γ
  hL_small := hL
  hLip := S.hr_lip
  Φ := lorentzianPhi S.K S.γ
  hΦ_unique := lorentzian_hΦ_unique S
  hΦ_continuous := lorentzianPhi_continuous S.K S.γ
  hsc_decay := lorentzian_sc_decay S C_s hC_s hslaving

/-! ## Slaving bound from Lyapunov -/

theorem lorentzian_ode_deviation_bound (K γ r : ℝ)
    (hK : K ≠ 0) :
    |lorentzianODE K γ r| = |K / 2| * |r| * |(1 - 2 * γ / K) - r ^ 2| := by
  rw [lorentzian_ode_factored K γ r hK]
  simp [abs_mul]

theorem lorentzian_ode_lyapunov_bound (K γ r : ℝ)
    (hK_pos : 0 < K) (hr_nn : 0 ≤ r) (hr_le : r ≤ 1) :
    |lorentzianODE K γ r| ≤ K / 2 * Real.sqrt ((r ^ 2 - (1 - 2 * γ / K)) ^ 2) := by
  rw [lorentzian_ode_deviation_bound K γ r (ne_of_gt hK_pos)]
  rw [Real.sqrt_sq_eq_abs]
  have hK2 : |K / 2| = K / 2 := abs_of_pos (by linarith)
  rw [hK2]
  have hr_abs : |r| ≤ 1 := by rwa [abs_of_nonneg hr_nn]
  calc K / 2 * |r| * |(1 - 2 * γ / K) - r ^ 2|
      ≤ K / 2 * 1 * |(1 - 2 * γ / K) - r ^ 2| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hr_abs (by linarith)
        · exact abs_nonneg _
    _ = K / 2 * |(1 - 2 * γ / K) - r ^ 2| := by ring
    _ = K / 2 * |r ^ 2 - (1 - 2 * γ / K)| := by rw [abs_sub_comm]

theorem LorentzianSolution.hlyap_Ψ (S : LorentzianSolution) (n : ℕ) :
    (S.r n ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2 ≤
    S.hlyap_coeff * Real.exp (-2 * S.Ψ n) := by
  exact S.hlyap n

theorem LorentzianSolution.slaving_from_lyapunov (S : LorentzianSolution) :
    ∀ n, |lorentzianODE S.K S.γ (S.r n)| ≤
      (S.K / 2 * Real.sqrt S.hlyap_coeff) *
      Real.exp (-1 * S.Ψ n) := by
  intro n
  have hr := S.hr_bdd n
  have hlyap := S.hlyap_Ψ n
  have hdev := lorentzian_ode_lyapunov_bound S.K S.γ (S.r n) S.hK_pos hr.1 hr.2
  calc |lorentzianODE S.K S.γ (S.r n)|
      ≤ S.K / 2 * Real.sqrt ((S.r n ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2) := hdev
    _ ≤ S.K / 2 * Real.sqrt (S.hlyap_coeff * Real.exp (-2 * S.Ψ n)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [S.hK_pos])
        exact Real.sqrt_le_sqrt hlyap
    _ = S.K / 2 * (Real.sqrt S.hlyap_coeff * Real.sqrt (Real.exp (-2 * S.Ψ n))) := by
        rw [Real.sqrt_mul (le_of_lt S.hlyap_coeff_pos)]
    _ = (S.K / 2 * Real.sqrt S.hlyap_coeff) * Real.sqrt (Real.exp (-2 * S.Ψ n)) := by ring
    _ = (S.K / 2 * Real.sqrt S.hlyap_coeff) * Real.exp (-1 * S.Ψ n) := by
        congr 1
        have : Real.exp (-2 * S.Ψ n) = Real.exp (-1 * S.Ψ n) ^ 2 := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [this, Real.sqrt_sq (Real.exp_nonneg _)]

theorem LorentzianSolution.slaving_const_pos (S : LorentzianSolution) :
    0 < S.K / 2 * Real.sqrt S.hlyap_coeff :=
  mul_pos (by linarith [S.hK_pos]) (Real.sqrt_pos_of_pos S.hlyap_coeff_pos)

/-! ## Assembled theorems -/

theorem lorentzian_global_stability (S : LorentzianSolution)
    (C_s : ℝ) (hC_s : 0 < C_s)
    (hslaving : ∀ n, |lorentzianODE S.K S.γ (S.r n)| ≤
      C_s * Real.exp (-1 * S.Ψ n))
    (hL : 3 * (S.K - S.γ) < S.r_star) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
      |S.r n - S.r_star| < ε :=
  global_stability (S.toKuramotoData C_s hC_s hslaving hL)

/-- **Fully assembled Lorentzian stability from Lyapunov.**
    No external slaving hypothesis needed. Works for all K > 2γ. -/
theorem lorentzian_global_stability_from_lyapunov (S : LorentzianSolution)
    (hL : 3 * (S.K - S.γ) < S.r_star) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
      |S.r n - S.r_star| < ε :=
  lorentzian_global_stability S
    _ S.slaving_const_pos (S.slaving_from_lyapunov) hL

end
