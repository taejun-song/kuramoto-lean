/-
  Kuramoto Stability — Lorentzian Solution from ODE
  ==================================================
  Constructs a LorentzianSolution from a continuous-time ODE solution.
  Proves fields (hr_bdd, hr_lip, hpersist, hlyap) from the ODE.

  hlyap bound: W(n) ≤ W(0)·exp(-2Ψ(n)) via left Riemann sum ≤ integral.
  Valid for NON-DECREASING r (r(0) ≤ r*), since then r(t) ≥ r(k) on [k, k+1].
  For non-decreasing r, persistence is trivial: r(n) ≥ r(0) > 0 for all n.

  toLorentzianSolution_nondec: full constructor (0 assumed fields) for r(0) ≤ r*.
  toLorentzianSolution_noninc: full constructor (0 assumed fields) for r(0) ≥ r*.
  hpersist for noninc derived via hpersist_from_convergence (ODE → parametric_convergence).

  lorentzian_subcritical_tendsto: K < 2γ → r(t) → 0 (V = r², V' ≤ -2μV).
  lorentzian_critical_tendsto: K = 2γ → r(t) → 0 (V' = -KV², contradiction + comparison_decay).
  Combined with existing K > 2γ → r(t) → r*: complete Lorentzian trifurcation.

  0 sorry.
-/

import KuramotoLean.InvariantBox
import KuramotoLean.Lorentzian
import KuramotoLean.GronwallBridge
import KuramotoLean.LorentzianEnvelope
import Mathlib.Analysis.ODE.Gronwall

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

/-! ## Order parameter (n=1) equals r -/

theorem LorentzianContinuousSolution.order_param_eq
    (S : LorentzianContinuousSolution) (t : ℝ) :
    S.toNPoleODEData.toBarrierData.r t = S.r t := by
  simp [NPoleBarrierData.r, NPoleODEData.toBarrierData,
        LorentzianContinuousSolution.toNPoleODEData, Fin.sum_univ_one]

/-! ## Critical K for n=1 Lorentzian equals 2γ -/

theorem lorentzian_npole_critical_K (K γ : ℝ) (hK : K > 2 * γ) (hγ : 0 < γ) :
    npoleCriticalK (fun _ : Fin 1 => γ) (fun _ : Fin 1 => (1 : ℝ)) < K := by
  unfold npoleCriticalK
  simp only [Fin.sum_univ_one]
  have h : 2 / ((1 : ℝ) / γ) = 2 * γ := by field_simp
  rw [h]; linarith

/-! ## Invariance from InvariantBox -/

theorem LorentzianContinuousSolution.r_pos
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    0 < S.r t :=
  lower_barrier S.toNPoleODEData 0 t ht

theorem LorentzianContinuousSolution.r_lt_one
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    S.r t < 1 :=
  upper_barrier S.toNPoleODEData 0 t ht

theorem LorentzianContinuousSolution.r_bdd
    (S : LorentzianContinuousSolution) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ S.r t ∧ S.r t ≤ 1 :=
  ⟨le_of_lt (S.r_pos t ht), le_of_lt (S.r_lt_one t ht)⟩

theorem LorentzianContinuousSolution.hr_bdd_discrete
    (S : LorentzianContinuousSolution) :
    ∀ n : ℕ, 0 ≤ S.r n ∧ S.r n ≤ 1 :=
  fun n => S.r_bdd n (Nat.cast_nonneg n)

/-! ## ODE velocity bound -/

theorem lorentzian_ode_abs_le (K γ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hKγ : K > 2 * γ)
    (hr_nn : 0 ≤ r) (hr_le : r ≤ 1) :
    |lorentzianODE K γ r| ≤ K - γ := by
  unfold lorentzianODE
  rw [abs_le]; constructor
  · nlinarith [sq_nonneg r, sq_nonneg (1 - r),
      mul_nonneg hr_nn (sq_nonneg r),
      mul_nonneg (by linarith : (0:ℝ) ≤ K/2) (mul_nonneg hr_nn
        (by nlinarith : 0 ≤ 1 - r ^ 2))]
  · nlinarith [sq_nonneg r,
      mul_nonneg (by linarith : (0:ℝ) ≤ K/2) (mul_nonneg hr_nn (sq_nonneg r))]

/-! ## Lipschitz bound via MVT -/

theorem LorentzianContinuousSolution.hr_lip_discrete
    (S : LorentzianContinuousSolution) :
    ∀ n : ℕ, |S.r (↑(n + 1)) - S.r (↑n)| ≤ S.K - S.γ := by
  intro n
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn_le : (n : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
  have h_deriv : ∀ x ∈ Icc (n : ℝ) (↑(n + 1)),
      HasDerivWithinAt S.r (lorentzianODE S.K S.γ (S.r x))
        (Icc (↑n) (↑(n + 1))) x :=
    fun x hx => (S.hr_ode x (le_trans hn_nn hx.1)).hasDerivWithinAt
  have h_bound : ∀ x ∈ Ico (n : ℝ) (↑(n + 1)),
      ‖lorentzianODE S.K S.γ (S.r x)‖ ≤ S.K - S.γ := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact lorentzian_ode_abs_le S.K S.γ (S.r x) S.hK_pos S.hγ_pos S.hK_gt
      (le_of_lt (S.r_pos x (le_trans hn_nn hx.1)))
      (le_of_lt (S.r_lt_one x (le_trans hn_nn hx.1)))
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment'
    h_deriv h_bound ↑(n + 1) (right_mem_Icc.mpr hn_le)
  rw [Real.norm_eq_abs, show (↑(n + 1) : ℝ) - ↑n = 1 from by push_cast; ring,
      mul_one] at h_mvt
  exact h_mvt

/-! ## Persistence from n-pole convergence -/

/-- For K > 2γ, the continuous Lorentzian solution converges to r*>0,
    so the discrete sequence visits values ≥ r*/2 infinitely often. -/
theorem LorentzianContinuousSolution.hpersist_from_convergence
    (S : LorentzianContinuousSolution) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ δ ≤ S.r n := by
  have hc_sum : ∑ k : Fin 1, S.toNPoleODEData.c k = 1 := by
    simp [LorentzianContinuousSolution.toNPoleODEData, Fin.sum_univ_one]
  have hKc : npoleCriticalK S.toNPoleODEData.γ S.toNPoleODEData.c < S.toNPoleODEData.K :=
    lorentzian_npole_critical_K S.K S.γ S.hK_gt S.hγ_pos
  obtain ⟨r_star, hr_star_pos, _, hconv⟩ :=
    parametric_convergence_from_ode S.toNPoleODEData one_pos hc_sum hKc
  refine ⟨r_star / 2, by linarith, fun N => ?_⟩
  obtain ⟨T, hT⟩ := hconv (r_star / 2) (by linarith)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max T (N : ℝ))
  refine ⟨n₀, ?_, ?_⟩
  · exact_mod_cast le_trans (le_max_right T (N : ℝ)) (le_of_lt hn₀)
  · have hT_le : T ≤ (n₀ : ℝ) :=
      le_trans (le_max_left T (N : ℝ)) (le_of_lt hn₀)
    have h_close := hT (n₀ : ℝ) hT_le
    rw [S.order_param_eq] at h_close
    linarith [(abs_lt.mp h_close).1]

/-! ## Lyapunov: W(n) ≤ W(0)·exp(-2Ψ(n)) for non-decreasing r -/

/-- One-step Lyapunov drop: dW/dt=-2Kr²W + r non-decreasing ⟹ W(m+1) ≤ W(m)·exp(-2Kr(m)²). -/
private theorem lorentzian_lyap_step
    (S : LorentzianContinuousSolution)
    (r_star_sq : ℝ) (hr_star_sq : r_star_sq = 1 - 2 * S.γ / S.K)
    (hr_nondec : ∀ s t, 0 ≤ s → s ≤ t → S.r s ≤ S.r t)
    (m : ℕ) :
    (S.r (↑(m + 1)) ^ 2 - r_star_sq) ^ 2 ≤
    (S.r (↑m) ^ 2 - r_star_sq) ^ 2 *
      Real.exp (-(2 * S.K * S.r m ^ 2) * 1) := by
  set V : ℝ → ℝ := fun t => (S.r t ^ 2 - r_star_sq) ^ 2 with hV_def
  have hV_cont : ContinuousOn V (Icc (m : ℝ) (↑m + 1)) := by
    apply ContinuousOn.pow
    apply ContinuousOn.sub _ continuousOn_const
    exact (S.hr_cont.mono (fun t ht => le_trans (Nat.cast_nonneg m) ht.1)).pow 2
  have hV_deriv : ∀ t, (m : ℝ) < t → t < (m : ℝ) + 1 →
      HasDerivAt V (-2 * S.K * S.r t ^ 2 * V t) t := by
    intro t ht_lo _
    have ht_nn : 0 ≤ t := le_trans (Nat.cast_nonneg m) (le_of_lt ht_lo)
    have h_r := S.hr_ode t ht_nn
    -- d(r²-c)/dt = 2r·ṙ via mul rule
    have h_f : HasDerivAt (fun s => S.r s ^ 2 - r_star_sq)
        (2 * S.r t * lorentzianODE S.K S.γ (S.r t)) t := by
      have hmul := h_r.mul h_r
      have h_sq : HasDerivAt (fun s => S.r s ^ 2)
          (2 * S.r t * lorentzianODE S.K S.γ (S.r t)) t := by
        convert hmul using 1
        · funext; simp [Pi.mul_apply, sq]
        · ring
      exact h_sq.sub_const r_star_sq
    -- d(r²-c)²/dt via mul rule
    have hmul2 := h_f.mul h_f
    have h_W : HasDerivAt V (-2 * S.K * S.r t ^ 2 * V t) t := by
      convert hmul2 using 1
      · funext; simp [hV_def, sq]
      · simp only [hV_def, sq]
        unfold lorentzianODE
        rw [hr_star_sq]
        field_simp [ne_of_gt S.hK_pos]
        ring
    exact h_W
  have hV_bound : ∀ t, (m : ℝ) < t → t < (m : ℝ) + 1 →
      -2 * S.K * S.r t ^ 2 * V t ≤ -(2 * S.K * S.r m ^ 2) * V t := by
    intro t ht_lo _
    have ht_nn : 0 ≤ t := le_trans (Nat.cast_nonneg m) (le_of_lt ht_lo)
    have hrm_le : S.r m ≤ S.r t :=
      hr_nondec m t (Nat.cast_nonneg m) (le_of_lt ht_lo)
    have hrm_nn : 0 ≤ S.r m := le_of_lt (S.r_pos m (Nat.cast_nonneg m))
    have hrt_nn : 0 ≤ S.r t := le_of_lt (S.r_pos t ht_nn)
    have hVt_nn : 0 ≤ V t := sq_nonneg _
    nlinarith [sq_nonneg (S.r t - S.r m),
              mul_nonneg hrt_nn (add_nonneg hrt_nn hrm_nn),
              mul_nonneg (mul_nonneg (by linarith [S.hK_pos] : (0:ℝ) ≤ 2 * S.K)
                (mul_nonneg (add_nonneg hrt_nn hrm_nn) (by linarith : 0 ≤ S.r t - S.r m)))
                hVt_nn]
  have h_cast : (m : ℝ) + 1 = ↑(m + 1) := by push_cast; ring
  rw [← h_cast]
  exact comparison_decay_interval V _ (2 * S.K * S.r m ^ 2) (m : ℝ) 1
    (by linarith) hV_cont hV_deriv hV_bound

/-- Discrete Lyapunov: W(n) ≤ W(0)·exp(-2Ψ(n)) for non-decreasing r (r(0)≤r*). -/
theorem LorentzianContinuousSolution.hlyap_from_nondecreasing
    (S : LorentzianContinuousSolution)
    (r_star_sq : ℝ) (hr_star_sq : r_star_sq = 1 - 2 * S.γ / S.K)
    (hr_nondec : ∀ s t, 0 ≤ s → s ≤ t → S.r s ≤ S.r t) :
    ∀ n : ℕ,
    (S.r n ^ 2 - r_star_sq) ^ 2 ≤
      (S.r 0 ^ 2 - r_star_sq) ^ 2 *
        Real.exp (-2 * (range n).sum (fun k => S.K * S.r k ^ 2)) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have h_step := lorentzian_lyap_step S r_star_sq hr_star_sq hr_nondec m
    simp only [mul_one] at h_step
    push_cast at h_step ih ⊢
    rw [sum_range_succ]
    push_cast
    calc (S.r (↑m + 1) ^ 2 - r_star_sq) ^ 2
        ≤ (S.r ↑m ^ 2 - r_star_sq) ^ 2 * Real.exp (-(2 * S.K * S.r ↑m ^ 2)) :=
          h_step
      _ ≤ ((S.r 0 ^ 2 - r_star_sq) ^ 2 *
              Real.exp (-2 * (range m).sum (fun k => S.K * S.r ↑k ^ 2))) *
            Real.exp (-(2 * S.K * S.r ↑m ^ 2)) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
      _ = (S.r 0 ^ 2 - r_star_sq) ^ 2 *
            Real.exp (-2 * ((range m).sum (fun k => S.K * S.r ↑k ^ 2) + S.K * S.r ↑m ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 1; ring

/-! ## Lyapunov: W(n) ≤ W(0)·exp(2K)·exp(-2Ψ(n)) for non-increasing r -/

/-- Right Riemann sum shift: Σₖ₌₀ⁿ⁻¹ K·r(k+1)² = Σₖ₌₀ⁿ⁻¹ K·r(k)² + K·(r(n)² - r(0)²). -/
private theorem lorentzian_sum_right_eq (S : LorentzianContinuousSolution) (n : ℕ) :
    (Finset.range n).sum (fun k => S.K * S.r ↑(k + 1) ^ 2) =
    (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2) + S.K * (S.r n ^ 2 - S.r 0 ^ 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    push_cast; ring

/-- One-step Lyapunov drop (non-increasing r): W(m+1) ≤ W(m)·exp(-2K·r(m+1)²). -/
private theorem lorentzian_lyap_step_noninc
    (S : LorentzianContinuousSolution)
    (r_star_sq : ℝ) (hr_star_sq : r_star_sq = 1 - 2 * S.γ / S.K)
    (hr_noninc : ∀ s t, 0 ≤ s → s ≤ t → S.r t ≤ S.r s)
    (m : ℕ) :
    (S.r (↑(m + 1)) ^ 2 - r_star_sq) ^ 2 ≤
    (S.r (↑m) ^ 2 - r_star_sq) ^ 2 *
      Real.exp (-(2 * S.K * S.r (↑(m + 1)) ^ 2) * 1) := by
  set V : ℝ → ℝ := fun t => (S.r t ^ 2 - r_star_sq) ^ 2 with hV_def
  have hV_cont : ContinuousOn V (Icc (m : ℝ) (↑m + 1)) := by
    apply ContinuousOn.pow
    apply ContinuousOn.sub _ continuousOn_const
    exact (S.hr_cont.mono (fun t ht => le_trans (Nat.cast_nonneg m) ht.1)).pow 2
  have hV_deriv : ∀ t, (m : ℝ) < t → t < (m : ℝ) + 1 →
      HasDerivAt V (-2 * S.K * S.r t ^ 2 * V t) t := by
    intro t ht_lo _
    have ht_nn : 0 ≤ t := le_trans (Nat.cast_nonneg m) (le_of_lt ht_lo)
    have h_r := S.hr_ode t ht_nn
    have h_f : HasDerivAt (fun s => S.r s ^ 2 - r_star_sq)
        (2 * S.r t * lorentzianODE S.K S.γ (S.r t)) t := by
      have hmul := h_r.mul h_r
      have h_sq : HasDerivAt (fun s => S.r s ^ 2)
          (2 * S.r t * lorentzianODE S.K S.γ (S.r t)) t := by
        convert hmul using 1
        · funext; simp [Pi.mul_apply, sq]
        · ring
      exact h_sq.sub_const r_star_sq
    have hmul2 := h_f.mul h_f
    have h_W : HasDerivAt V (-2 * S.K * S.r t ^ 2 * V t) t := by
      convert hmul2 using 1
      · funext; simp [hV_def, sq]
      · simp only [hV_def, sq]
        unfold lorentzianODE; rw [hr_star_sq]
        field_simp [ne_of_gt S.hK_pos]; ring
    exact h_W
  have hV_bound : ∀ t, (m : ℝ) < t → t < (m : ℝ) + 1 →
      -2 * S.K * S.r t ^ 2 * V t ≤ -(2 * S.K * S.r (↑(m + 1)) ^ 2) * V t := by
    intro t ht_lo ht_hi
    have ht_nn : 0 ≤ t := le_trans (Nat.cast_nonneg m) (le_of_lt ht_lo)
    have hrt_nn : 0 ≤ S.r t := le_of_lt (S.r_pos t ht_nn)
    have hrm1_nn : 0 ≤ S.r (↑(m + 1)) := le_of_lt (S.r_pos _ (Nat.cast_nonneg _))
    have hrm1_le : S.r t ≥ S.r (↑(m + 1)) := by
      apply hr_noninc t (↑(m + 1)) ht_nn
      push_cast; linarith
    have hVt_nn : 0 ≤ V t := sq_nonneg _
    nlinarith [sq_nonneg (S.r t - S.r (↑(m + 1))),
              mul_nonneg hrt_nn (add_nonneg hrt_nn hrm1_nn),
              mul_nonneg (mul_nonneg (by linarith [S.hK_pos] : (0:ℝ) ≤ 2 * S.K)
                (mul_nonneg (add_nonneg hrt_nn hrm1_nn)
                  (by linarith : 0 ≤ S.r t - S.r (↑(m + 1)))))
                hVt_nn]
  have h_cast : (m : ℝ) + 1 = ↑(m + 1) := by push_cast; ring
  simp only [← h_cast] at hV_bound
  rw [← h_cast]
  exact comparison_decay_interval V _ (2 * S.K * S.r ((m : ℝ) + 1) ^ 2) (m : ℝ) 1
    (by linarith) hV_cont hV_deriv hV_bound

/-- Discrete Lyapunov (non-increasing r): W(n) ≤ W(0)·exp(-2·Σₖ₌₀ⁿ⁻¹ K·r(k+1)²). -/
private theorem lorentzian_hlyap_noninc_raw
    (S : LorentzianContinuousSolution)
    (r_star_sq : ℝ) (hr_star_sq : r_star_sq = 1 - 2 * S.γ / S.K)
    (hr_noninc : ∀ s t, 0 ≤ s → s ≤ t → S.r t ≤ S.r s) :
    ∀ n : ℕ, (S.r n ^ 2 - r_star_sq) ^ 2 ≤
      (S.r 0 ^ 2 - r_star_sq) ^ 2 *
        Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑(k + 1) ^ 2)) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have h_step := lorentzian_lyap_step_noninc S r_star_sq hr_star_sq hr_noninc m
    simp only [mul_one] at h_step
    push_cast at h_step ih ⊢
    rw [sum_range_succ]
    push_cast
    calc (S.r (↑m + 1) ^ 2 - r_star_sq) ^ 2
        ≤ (S.r ↑m ^ 2 - r_star_sq) ^ 2 * Real.exp (-(2 * S.K * S.r (↑m + 1) ^ 2)) :=
          h_step
      _ ≤ ((S.r 0 ^ 2 - r_star_sq) ^ 2 *
              Real.exp (-2 * (range m).sum (fun k => S.K * S.r (↑k + 1) ^ 2))) *
            Real.exp (-(2 * S.K * S.r (↑m + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
      _ = (S.r 0 ^ 2 - r_star_sq) ^ 2 *
            Real.exp (-2 * ((range m).sum (fun k => S.K * S.r (↑k + 1) ^ 2) +
              S.K * S.r (↑m + 1) ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 1; ring

/-- Lyapunov bound for non-increasing r: W(n) ≤ W(0)·exp(2K)·exp(-2Ψ(n)).
    Uses: right Riemann sum + Σ_right = Ψ - K·(r(0)²-r(n)²) ≥ Ψ - K. -/
theorem LorentzianContinuousSolution.hlyap_from_nonincreasing
    (S : LorentzianContinuousSolution)
    (r_star_sq : ℝ) (hr_star_sq : r_star_sq = 1 - 2 * S.γ / S.K)
    (hr_noninc : ∀ s t, 0 ≤ s → s ≤ t → S.r t ≤ S.r s) :
    ∀ n : ℕ, (S.r n ^ 2 - r_star_sq) ^ 2 ≤
      (S.r 0 ^ 2 - r_star_sq) ^ 2 * Real.exp (2 * S.K) *
        Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r k ^ 2)) := by
  intro n
  have hraw := lorentzian_hlyap_noninc_raw S r_star_sq hr_star_sq hr_noninc n
  have hid : (Finset.range n).sum (fun k => S.K * S.r ↑(k + 1) ^ 2) =
      (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2) +
        S.K * (S.r n ^ 2 - S.r 0 ^ 2) := by
    have := lorentzian_sum_right_eq S n
    push_cast at this ⊢; linarith
  rw [hid] at hraw
  have hr0_le : S.r 0 ^ 2 ≤ 1 := by
    have : S.r 0 < 1 := S.hr_init_lt
    nlinarith [S.hr_init_pos.le]
  have hrn_nn : 0 ≤ S.r n ^ 2 := sq_nonneg _
  have hK_pos := S.hK_pos
  calc (S.r n ^ 2 - r_star_sq) ^ 2
      ≤ (S.r 0 ^ 2 - r_star_sq) ^ 2 *
          Real.exp (-2 * ((Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2) +
            S.K * (S.r n ^ 2 - S.r 0 ^ 2))) := hraw
    _ = (S.r 0 ^ 2 - r_star_sq) ^ 2 *
          (Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2) +
            (-2 * S.K * (S.r n ^ 2 - S.r 0 ^ 2)))) := by
          congr 2; ring
    _ = (S.r 0 ^ 2 - r_star_sq) ^ 2 *
          Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2)) *
          Real.exp (-2 * S.K * (S.r n ^ 2 - S.r 0 ^ 2)) := by
          rw [Real.exp_add]; ring
    _ ≤ (S.r 0 ^ 2 - r_star_sq) ^ 2 *
          Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2)) *
          Real.exp (2 * S.K) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
          apply Real.exp_le_exp.mpr
          nlinarith
    _ = (S.r 0 ^ 2 - r_star_sq) ^ 2 * Real.exp (2 * S.K) *
          Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2)) := by ring

/-! ## Constructor: LorentzianContinuousSolution → LorentzianSolution (non-decreasing r) -/

/-- Constructs a `LorentzianSolution` from a continuous ODE solution when r is non-decreasing.
    For non-decreasing r (r(0) ≤ r*): every field is proved from the ODE.
    - hr_bdd: from lower/upper barrier theorems
    - hr_lip: from ODE velocity bound via MVT
    - hpersist: trivial — r(n) ≥ r(0) > 0 for all n (monotone non-decreasing)
    - hlyap: left Riemann sum ≤ integral for non-decreasing r² (proved via lorentzian_lyap_step) -/
def LorentzianContinuousSolution.toLorentzianSolution_nondec
    (S : LorentzianContinuousSolution)
    (hr_nondec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → S.r s ≤ S.r t) :
    LorentzianSolution where
  K := S.K
  γ := S.γ
  hK_pos := S.hK_pos
  hK_gt := S.hK_gt
  r := fun n => S.r n
  hr_bdd := S.hr_bdd_discrete
  hr_lip := S.hr_lip_discrete
  δ := S.r 0 / 2
  hδ := by linarith [S.hr_init_pos]
  hpersist := fun N => ⟨N, le_refl N, by
    have h : S.r 0 ≤ S.r N := hr_nondec 0 N (le_refl 0) (Nat.cast_nonneg N)
    linarith [S.hr_init_pos]⟩
  hlyap_coeff := (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2 + 1
  hlyap_coeff_pos := by linarith [sq_nonneg (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K))]
  hlyap := fun n => by
    have h := S.hlyap_from_nondecreasing (1 - 2 * S.γ / S.K) rfl hr_nondec n
    simp only [Nat.cast_zero] at h ⊢
    set e := Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2))
    set W := (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2
    exact le_trans h (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Real.exp_nonneg _))

/-- Lorentzian global stability from a continuous ODE solution with non-decreasing r.
    All `LorentzianSolution` fields are proved from the ODE — 0 assumed. -/
theorem lorentzian_nondec_convergence
    (S : LorentzianContinuousSolution)
    (hr_nondec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → S.r s ≤ S.r t) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |S.r n - Real.sqrt (1 - 2 * S.γ / S.K)| < ε :=
  lorentzian_envelope_stability (S.toLorentzianSolution_nondec hr_nondec)

/-! ## Constructor: LorentzianContinuousSolution → LorentzianSolution (non-increasing r) -/

/-- Constructs a `LorentzianSolution` from a continuous ODE solution when r is non-increasing.
    For non-increasing r (r(0) ≥ r*): every field is proved from the ODE — 0 assumed.
    - hpersist: derived from hpersist_from_convergence (ODE → n-pole → convergence → persistence)
    - hlyap: right Riemann sum gives W(n) ≤ W(0)·exp(2K)·exp(-2Ψ(n)) -/
def LorentzianContinuousSolution.toLorentzianSolution_noninc
    (S : LorentzianContinuousSolution)
    (hr_noninc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → S.r t ≤ S.r s) :
    LorentzianSolution where
  K := S.K
  γ := S.γ
  hK_pos := S.hK_pos
  hK_gt := S.hK_gt
  r := fun n => S.r n
  hr_bdd := S.hr_bdd_discrete
  hr_lip := S.hr_lip_discrete
  δ := S.hpersist_from_convergence.choose
  hδ := S.hpersist_from_convergence.choose_spec.1
  hpersist := S.hpersist_from_convergence.choose_spec.2
  hlyap_coeff := (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2 * Real.exp (2 * S.K) + 1
  hlyap_coeff_pos := by
    have := mul_nonneg (sq_nonneg (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K))) (Real.exp_nonneg (2 * S.K))
    linarith
  hlyap := fun n => by
    have h := S.hlyap_from_nonincreasing (1 - 2 * S.γ / S.K) rfl hr_noninc n
    simp only [Nat.cast_zero] at h ⊢
    set e := Real.exp (-2 * (Finset.range n).sum (fun k => S.K * S.r ↑k ^ 2))
    set W := (S.r 0 ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2
    calc (S.r n ^ 2 - (1 - 2 * S.γ / S.K)) ^ 2
        ≤ W * Real.exp (2 * S.K) * e := h
      _ ≤ (W * Real.exp (2 * S.K) + 1) * e :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_nonneg _)

/-- Lorentzian global stability from a continuous ODE solution with non-increasing r.
    All `LorentzianSolution` fields are proved from the ODE — 0 assumed. -/
theorem lorentzian_noninc_convergence
    (S : LorentzianContinuousSolution)
    (hr_noninc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → S.r t ≤ S.r s) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |S.r n - Real.sqrt (1 - 2 * S.γ / S.K)| < ε :=
  lorentzian_envelope_stability (S.toLorentzianSolution_noninc hr_noninc)

/-! ## Subcritical Lorentzian convergence: K < 2γ → r(t) → 0

  For K < 2γ the ODE ṙ = (K/2-γ)r - (K/2)r³ is purely dissipative.
  V = r² satisfies V' = 2r·ṙ = -2μr² - Kr⁴ ≤ -2μr² = -2μV (μ = γ-K/2 > 0).
  The bound holds for ALL r ∈ ℝ: no sign constraint needed. -/

/-- Key algebraic bound: 2r·ṙ ≤ -2(γ-K/2)·r² for K < 2γ, for any r ∈ ℝ. -/
private lemma lorentzian_sq_deriv_subcritical (K γ r : ℝ)
    (hK : 0 < K) (hK_sub : K < 2 * γ) :
    2 * r * lorentzianODE K γ r ≤ -(2 * (γ - K / 2)) * r ^ 2 := by
  unfold lorentzianODE
  nlinarith [mul_nonneg hK.le (sq_nonneg (r ^ 2))]

/-- **Subcritical bound**: for K < 2γ, r(t)² ≤ r(0)²·exp(-2(γ-K/2)·t). -/
theorem lorentzian_subcritical_sq_bound
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hK_sub : K < 2 * γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t) :
    ∀ t, 0 ≤ t → r t ^ 2 ≤ r 0 ^ 2 * Real.exp (-(2 * (γ - K / 2)) * t) := by
  apply comparison_decay (fun t => r t ^ 2) (fun t => 2 * r t * lorentzianODE K γ (r t))
      (2 * (γ - K / 2)) (hr_cont.pow 2)
  · intro t ht
    have hmul := (hr_ode t ht.le).mul (hr_ode t ht.le)
    convert hmul using 1
    · funext s; simp [sq, Pi.mul_apply]
    · ring
  · intro t _
    exact lorentzian_sq_deriv_subcritical K γ (r t) hK hK_sub

/-- **Subcritical Lorentzian convergence**: K < 2γ → r(t) → 0 (Filter.Tendsto form). -/
theorem lorentzian_subcritical_tendsto
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hK_sub : K < 2 * γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  have hμ : 0 < 2 * (γ - K / 2) := by linarith
  have hC : 0 < r 0 ^ 2 + 1 := by linarith [sq_nonneg (r 0)]
  have hbound := lorentzian_subcritical_sq_bound K γ hK hγ hK_sub r hr_cont hr_ode
  have hC_exp : Filter.Tendsto
      (fun t : ℝ => (r 0 ^ 2 + 1) * Real.exp (-(2 * (γ - K / 2)) * t))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -(2 * (γ - K / 2)) * t) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (by linarith)
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := h2.const_mul (r 0 ^ 2 + 1)
    simpa only [mul_zero] using h3
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hC_exp
  obtain ⟨T, hT⟩ := hC_exp (ε ^ 2) (pow_pos hε 2)
  exact ⟨max T 0, fun t ht => by
    have ht_T : T ≤ t := le_trans (le_max_left _ _) ht
    have ht_nn : (0 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    rw [Real.dist_eq, sub_zero]
    have hC_lt : (r 0 ^ 2 + 1) * Real.exp (-(2 * (γ - K / 2)) * t) < ε ^ 2 := by
      have := hT t ht_T
      rwa [Real.dist_eq, sub_zero,
           abs_of_nonneg (mul_nonneg hC.le (Real.exp_nonneg _))] at this
    have hrsq : r t ^ 2 ≤ (r 0 ^ 2 + 1) * Real.exp (-(2 * (γ - K / 2)) * t) :=
      le_trans (hbound t ht_nn)
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_nonneg _))
    have h1 := Real.sqrt_lt_sqrt (sq_nonneg (r t)) (lt_of_le_of_lt hrsq hC_lt)
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hε.le] at h1⟩

/-! ## Critical Lorentzian convergence: K = 2γ → r(t) → 0

  For K = 2γ the ODE becomes ṙ = -γr³ (purely cubic dissipation).
  V = r² satisfies V' = 2r·ṙ = -2γr⁴ = -K·V².
  Contradiction argument: if V ≥ δ forever, then V' ≤ -(Kδ)·V,
  comparison_decay gives V → 0 exponentially — contradiction. -/

/-- Algebraic bound: for K = 2γ and r² ≥ δ, we have 2r·ṙ ≤ -(Kδ)·r². -/
private lemma lorentzian_sq_deriv_critical_linear (K γ δ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hK_eq : K = 2 * γ) (hδ : 0 < δ) (hrsq : δ ≤ r ^ 2) :
    2 * r * lorentzianODE K γ r ≤ -(K * δ) * r ^ 2 := by
  have hcrit : K / 2 - γ = 0 := by linarith
  have hγval : K / 2 = γ := by linarith
  unfold lorentzianODE
  nlinarith [mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ r ^ 2 - δ),
             mul_nonneg hγ.le (sq_nonneg r), sq_nonneg (r ^ 2)]

/-- **Critical Lorentzian convergence**: K = 2γ → r(t) → 0 (Filter.Tendsto form).
    The decay is algebraic (V ~ 1/t), proved via contradiction + comparison_decay. -/
theorem lorentzian_critical_tendsto
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hK_eq : K = 2 * γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 ≤ t → HasDerivAt r (lorentzianODE K γ (r t)) t) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra h_not
  push_neg at h_not
  have h_all : ∀ T : ℝ, ∃ t, T ≤ t ∧ ε ^ 2 ≤ r t ^ 2 := by
    intro T
    obtain ⟨t, hT_le, hdist⟩ := h_not T
    rw [Real.dist_eq, sub_zero] at hdist
    exact ⟨t, hT_le, by nlinarith [sq_abs (r t), abs_nonneg (r t), hε.le]⟩
  have hV_deriv_has : ∀ t, 0 < t →
      HasDerivAt (fun t => r t ^ 2) (2 * r t * lorentzianODE K γ (r t)) t := by
    intro t ht
    have hmul := (hr_ode t (le_of_lt ht)).mul (hr_ode t (le_of_lt ht))
    convert hmul using 1
    · funext s; simp [sq, Pi.mul_apply]
    · ring
  have hV_anti : AntitoneOn (fun t => r t ^ 2) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (𝕜 := ℝ) 0) (hr_cont.pow 2)
    · rw [interior_Ici]
      intro t ht
      exact (hV_deriv_has t (mem_Ioi.mp ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(hV_deriv_has t (mem_Ioi.mp ht)).deriv]
      have hcrit : K / 2 - γ = 0 := by linarith
      unfold lorentzianODE
      nlinarith [sq_nonneg (r t), sq_nonneg (r t ^ 2), hγ.le, mul_nonneg hγ.le (sq_nonneg (r t))]
  have hV_ge : ∀ t, 0 ≤ t → ε ^ 2 ≤ r t ^ 2 := by
    intro t ht
    obtain ⟨s, hst, hVs⟩ := h_all t
    exact le_trans hVs (hV_anti (mem_Ici.mpr ht) (mem_Ici.mpr (le_trans ht hst)) hst)
  have hV_linear : ∀ t, 0 < t →
      2 * r t * lorentzianODE K γ (r t) ≤ -(K * ε ^ 2) * r t ^ 2 :=
    fun t ht => lorentzian_sq_deriv_critical_linear K γ (ε ^ 2) (r t) hK hγ hK_eq
      (pow_pos hε 2) (hV_ge t (le_of_lt ht))
  have hV_exp := comparison_decay (fun t => r t ^ 2)
    (fun t => 2 * r t * lorentzianODE K γ (r t))
    (K * ε ^ 2) (hr_cont.pow 2) hV_deriv_has hV_linear
  have hC_pos : 0 < r 0 ^ 2 + 1 := by linarith [sq_nonneg (r 0)]
  have hKε_pos : 0 < K * ε ^ 2 := mul_pos hK (pow_pos hε 2)
  have hC_exp_tendsto : Filter.Tendsto
      (fun t : ℝ => (r 0 ^ 2 + 1) * Real.exp (-(K * ε ^ 2) * t))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -(K * ε ^ 2) * t) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (by linarith)
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := h2.const_mul (r 0 ^ 2 + 1)
    simpa only [mul_zero] using h3
  rw [Metric.tendsto_atTop] at hC_exp_tendsto
  obtain ⟨T, hT⟩ := hC_exp_tendsto (ε ^ 2) (pow_pos hε 2)
  have hT'_nn : (0 : ℝ) ≤ max T 0 := le_max_right T 0
  have hV_big := hV_ge (max T 0) hT'_nn
  have hexp_small := hT (max T 0) (le_max_left T 0)
  rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg hC_pos.le (Real.exp_nonneg _))] at hexp_small
  have hV_small : r (max T 0) ^ 2 ≤ (r 0 ^ 2 + 1) * Real.exp (-(K * ε ^ 2) * max T 0) :=
    le_trans (hV_exp (max T 0) hT'_nn)
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
  linarith

/-! ## Unified continuous trifurcation for scalar Lorentzian ODE -/

/-- For n=1 with uniform γ and c=1: the n-pole critical K equals 2γ. -/
theorem lorentzian_npole_critical_K_eq (γ : ℝ) (hγ : 0 < γ) :
    npoleCriticalK (fun _ : Fin 1 => γ) (fun _ : Fin 1 => (1 : ℝ)) = 2 * γ := by
  unfold npoleCriticalK
  simp only [Fin.sum_univ_one]
  field_simp

/-- Build NPoleODEData for n=1 Lorentzian ODE; works for any positive K. -/
private def lorentzian_to_npole (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 < t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1) : NPoleODEData 1 where
  γ := fun _ => γ
  c := fun _ => 1
  K := K
  α := fun t _ => r t
  hK := hK
  hγ := fun _ => hγ
  hc := fun _ => one_pos
  hα_ode := fun t ht k => by
    have h := hr_ode t ht
    rw [lorentzian_eq_npole_n1] at h
    exact Fin.fin_one_eq_zero k ▸ h
  hα_cont := fun _ => hr_cont
  hα_init_pos := fun _ => hr_init_pos
  hα_init_lt := fun _ => hr_init_lt

/-- **Complete Lorentzian trifurcation** (continuous time, Filter.Tendsto form).
    Any Lorentzian ODE solution with r(0) ∈ (0,1) converges to a limit r_∞ ∈ [0,1]:
    - K ≤ 2γ → r_∞ = 0 (incoherent/critical regime)
    - K > 2γ → 0 < r_∞ < 1 (partially synchronized regime)
    Proof: lift to NPoleODEData n=1, apply trifurcation_from_ode, bridge via
    lorentzian_npole_critical_K_eq. -/
theorem lorentzian_continuous_trifurcation
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 < t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_init_pos : 0 < r 0) (hr_init_lt : r 0 < 1) :
    ∃ r_limit : ℝ, 0 ≤ r_limit ∧ r_limit ≤ 1 ∧
      Filter.Tendsto r Filter.atTop (nhds r_limit) ∧
      (K ≤ 2 * γ → r_limit = 0) ∧
      (2 * γ < K → 0 < r_limit ∧ r_limit < 1) := by
  set D := lorentzian_to_npole K γ hK hγ r hr_cont hr_ode hr_init_pos hr_init_lt
  have hc_sum : ∑ k : Fin 1, D.c k = 1 := by
    change ∑ k : Fin 1, (fun _ => (1 : ℝ)) k = 1
    simp [Fin.sum_univ_one]
  have hKc_eq : npoleCriticalK D.γ D.c = 2 * γ := by
    change npoleCriticalK (fun _ : Fin 1 => γ) (fun _ : Fin 1 => (1 : ℝ)) = 2 * γ
    exact lorentzian_npole_critical_K_eq γ hγ
  obtain ⟨r_limit, hr_nn, hr_le, hr_tendsto, hle, hgt⟩ :=
    trifurcation_from_ode D one_pos hc_sum
  have heq : D.toBarrierData.r = r := funext fun t => by
    change ∑ k : Fin 1, (1 : ℝ) * r t = r t
    simp [Fin.sum_univ_one]
  refine ⟨r_limit, hr_nn, hr_le, ?_, ?_, ?_⟩
  · rw [heq] at hr_tendsto; exact hr_tendsto
  · intro hK_le; apply hle; rw [hKc_eq]; exact hK_le
  · intro hK_gt; apply hgt; rw [hKc_eq]; exact hK_gt

/-! ## ODE uniqueness: Lorentzian ODE is Lipschitz, enabling backward uniqueness -/

/-- The Lorentzian ODE is `LipschitzOnWith` on [0,1] with NNReal constant ⟨2K, ...⟩.
    Packages `lorentzian_ode_lipschitz` in the Mathlib `LipschitzOnWith` form. -/
theorem lorentzianODE_lipschitzOnWith (K γ : ℝ) (hK : 0 < K) (hK_gt : K > 2 * γ)
    (hγ : 0 ≤ γ) :
    LipschitzOnWith ⟨2 * K, by linarith⟩ (lorentzianODE K γ) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩
  rw [Real.dist_eq, Real.dist_eq]
  exact lorentzian_ode_lipschitz K γ x y hx0 hx1 hy0 hy1 hK hK_gt hγ

/-- The Lorentzian ODE vanishes at r* = √(1-2γ/K): the equilibrium point. -/
theorem lorentzianODE_at_rstar (K γ : ℝ) (hK : 0 < K) (hK_gt : K > 2 * γ) :
    lorentzianODE K γ (Real.sqrt (1 - 2 * γ / K)) = 0 := by
  set r_star := Real.sqrt (1 - 2 * γ / K)
  have hK_ne : K ≠ 0 := ne_of_gt hK
  have hrstar_sq : r_star ^ 2 = 1 - 2 * γ / K :=
    Real.sq_sqrt (le_of_lt (lorentzian_rstar_pos K γ hK hK_gt))
  have h3 : r_star ^ 3 = r_star * (1 - 2 * γ / K) := by
    calc r_star ^ 3 = r_star * r_star ^ 2 := by ring
      _ = r_star * (1 - 2 * γ / K) := by rw [hrstar_sq]
  unfold lorentzianODE
  rw [h3]
  field_simp [hK_ne]
  ring

/-- **ODE Monotonicity** (below equilibrium): if r(0) < r* = √(1-2γ/K) and r satisfies
    the Lorentzian ODE with K > 2γ, then r(t) < r* for all t ≥ 0.
    Proof: if r(T) ≥ r* for some T, IVT gives t₁ ∈ [0,T] with r(t₁) = r*.
    By ODE uniqueness (backward in time from t₁), r ≡ r* on [0,t₁].
    So r(0) = r* — contradiction. -/
theorem lorentzian_r_stays_below_rstar (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hK_gt : K > 2 * γ)
    (r : ℝ → ℝ) (hr_cont : ContinuousOn r (Ici 0))
    (hr_ode : ∀ t, 0 < t → HasDerivAt r (lorentzianODE K γ (r t)) t)
    (hr_bdd : ∀ t, 0 ≤ t → 0 ≤ r t ∧ r t ≤ 1)
    (hr_init : r 0 < Real.sqrt (1 - 2 * γ / K)) :
    ∀ t, 0 ≤ t → r t < Real.sqrt (1 - 2 * γ / K) := by
  set r_star := Real.sqrt (1 - 2 * γ / K) with hr_star_def
  intro t ht
  by_contra h_ge
  push_neg at h_ge
  -- r(0) < r* ≤ r(t), so by IVT there exists t₁ ∈ [0,t] with r(t₁) = r*
  have hr_cont_Icc : ContinuousOn r (Icc 0 t) :=
    hr_cont.mono (Icc_subset_Ici_self)
  have h_ivt : r_star ∈ r '' Icc 0 t := by
    apply intermediate_value_Icc ht hr_cont_Icc
    exact ⟨le_of_lt hr_init, h_ge⟩
  obtain ⟨t₁, ht₁_icc, hrt₁⟩ := h_ivt
  have ht₁_nn : 0 ≤ t₁ := ht₁_icc.1
  have ht₁_le : t₁ ≤ t := ht₁_icc.2
  -- Case t₁ = 0: r(0) = r*, contradicting r(0) < r*
  rcases eq_or_lt_of_le ht₁_nn with ht₁_zero | ht₁_pos
  · exfalso; rw [← ht₁_zero] at hrt₁; linarith [hr_init.trans_eq hrt₁.symm]
  -- Case t₁ > 0: apply ODE backward uniqueness on [0, t₁]
  -- The constant g(t) = r* satisfies the ODE with g(t₁) = r* = r(t₁)
  -- By ODE_solution_unique_of_mem_Icc_left, r ≡ r* on [0, t₁]
  -- In particular r(0) = r* — contradiction
  set lipK : NNReal := ⟨2 * K, by linarith⟩ with hlipK_def
  have hLip : ∀ s ∈ Set.Ioc 0 t₁,
      LipschitzOnWith lipK (lorentzianODE K γ) (Set.Icc 0 1) := by
    intro s _
    exact lorentzianODE_lipschitzOnWith K γ hK hK_gt (le_of_lt hγ)
  have hf_cont : ContinuousOn r (Set.Icc 0 t₁) :=
    hr_cont.mono Set.Icc_subset_Ici_self
  have hf_deriv : ∀ s ∈ Set.Ioc 0 t₁,
      HasDerivWithinAt r (lorentzianODE K γ (r s)) (Set.Iic s) s :=
    fun s hs => (hr_ode s hs.1).hasDerivWithinAt
  have hf_bdd : ∀ s ∈ Set.Ioc 0 t₁, r s ∈ Set.Icc 0 1 := by
    intro s hs; exact ⟨(hr_bdd s (le_of_lt hs.1)).1, (hr_bdd s (le_of_lt hs.1)).2⟩
  have hg_cont : ContinuousOn (fun _ => r_star) (Set.Icc 0 t₁) := continuousOn_const
  have hg_deriv : ∀ s ∈ Set.Ioc 0 t₁,
      HasDerivWithinAt (fun _ => r_star) (lorentzianODE K γ r_star) (Set.Iic s) s := by
    intro s _
    rw [lorentzianODE_at_rstar K γ hK hK_gt]
    simpa using (hasDerivAt_const s r_star).hasDerivWithinAt (s := Set.Iic s)
  have hg_bdd : ∀ s ∈ Set.Ioc 0 t₁, r_star ∈ Set.Icc 0 1 := by
    intro s _
    have hrstar_pos : 0 < r_star := Real.sqrt_pos_of_pos (lorentzian_rstar_pos K γ hK hK_gt)
    have hrstar_lt : r_star < 1 := by
      rw [hr_star_def]
      have h_nn : 0 ≤ 1 - 2 * γ / K := le_of_lt (lorentzian_rstar_pos K γ hK hK_gt)
      have h_lt : 1 - 2 * γ / K < 1 := by
        have : 0 < 2 * γ / K := by positivity
        linarith
      calc Real.sqrt (1 - 2 * γ / K) < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nn h_lt
        _ = 1 := Real.sqrt_one
    exact ⟨le_of_lt hrstar_pos, le_of_lt hrstar_lt⟩
  have hb : r t₁ = (fun _ => r_star) t₁ := hrt₁
  have hEqOn := ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => lorentzianODE K γ) (s := fun _ => Set.Icc 0 1)
    (K := lipK) (f := r) (g := fun _ => r_star)
    hLip hf_cont hf_deriv hf_bdd hg_cont hg_deriv hg_bdd hb
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_refl 0, le_of_lt ht₁_pos⟩
  have hreq : r 0 = r_star := hEqOn h0
  linarith

end
