import KuramotoLean.FullChainConvergence
import KuramotoLean.GroundedConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

private theorem suitable_epsilon (K lam cmin gmax : ℝ)
    (hK : 0 < K) (hlam : 0 < lam) (hcm : 0 < cmin) (hgm : 0 < gmax) :
    ∃ eps > 0, (K / 2) * 1 * eps ^ 2 ≤ lam / 2 ∧
      K * (cmin * eps * exp (-2)) ≤ 2 * gmax := by
  set b1 := lam / (K + lam)
  set b2 := 2 * gmax * exp 2 / (K * cmin)
  have hKlam : 0 < K + lam := by linarith
  have hKc : 0 < K * cmin := mul_pos hK hcm
  have hb1_pos : 0 < b1 := div_pos hlam hKlam
  have hb2_pos : 0 < b2 := div_pos (mul_pos (mul_pos (by linarith : (0:ℝ) < 2) hgm) (exp_pos 2)) hKc
  set eps := min b1 b2
  have heps : 0 < eps := lt_min hb1_pos hb2_pos
  refine ⟨eps, heps, ?_, ?_⟩
  · have h1 : eps ≤ b1 := min_le_left _ _
    have heps_sq : eps ^ 2 ≤ b1 ^ 2 := sq_le_sq' (by nlinarith) h1
    have hb1_eq : b1 = lam / (K + lam) := rfl
    suffices h : K * b1 ^ 2 ≤ lam by nlinarith
    rw [hb1_eq, div_pow]
    have hKlam_ne : (K + lam) ^ 2 ≠ 0 := ne_of_gt (pow_pos hKlam 2)
    rw [show K * (lam ^ 2 / (K + lam) ^ 2) = K * lam ^ 2 / (K + lam) ^ 2 from mul_div_assoc' K _ _]
    rw [div_le_iff₀ (pow_pos hKlam 2)]
    nlinarith [sq_nonneg K, sq_nonneg lam]
  · have h1 : eps ≤ b2 := min_le_right _ _
    have : cmin * eps * exp (-2) ≤ cmin * b2 * exp (-2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1 (le_of_lt hcm))
        (le_of_lt (exp_pos _))
    have key : K * (cmin * eps * exp (-2)) ≤ K * (cmin * b2 * exp (-2)) :=
      mul_le_mul_of_nonneg_left this (le_of_lt hK)
    suffices hsuff : K * (cmin * b2 * exp (-2)) = 2 * gmax by linarith
    have hb2_eq : b2 = 2 * gmax * exp 2 / (K * cmin) := rfl
    rw [hb2_eq]
    have hKc_ne : K * cmin ≠ 0 := ne_of_gt hKc
    field_simp
    rw [← exp_add]
    norm_num

theorem global_stability_supercritical (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K)
    (hinit_pos : ∀ k, 0 < D.α 0 k)
    (hinit_lt : ∀ k, D.α 0 k < 1)
    (gmax : ℝ) (hgmax_pos : 0 < gmax) (hgmax : ∀ k, D.γ k ≤ gmax)
    (cmin : ℝ) (hcmin_pos : 0 < cmin) (hcmin : ∀ k, cmin ≤ D.c k) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - r_star| < ε := by
  have hn' : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r_star, hr_pos, hr_lt, hsp, hsl, _, h_sc⟩ :=
    sc_fixed_point_grounds D.γ D.c D.K D.hγ D.hc D.hK hn' hK_super hc_sum
  obtain ⟨lam, hlam, hdisp⟩ :=
    incoherence_unstable D.γ D.c D.K D.hγ D.hc hn' D.hK hK_super
  set as := fun k => explicitEquil (D.γ k) D.K r_star
  obtain ⟨eps, heps, heps1, heps2⟩ :=
    suitable_epsilon D.K lam cmin gmax D.hK hlam hcmin_pos hgmax_pos
  have h_ode : ∀ k, nPoleODE D.γ D.c D.K as k = 0 :=
    fixed_point_nPoleODE D.γ D.c D.K r_star D.hγ D.hK hr_pos h_sc
  set FD : FullChainData n :=
    { D with
      hn := hn
      α_star := as
      hα_star_pos := hsp
      hα_star_lt := hsl
      h_equil := h_ode
      hc_sum := hc_sum
      hα_init_pos := hinit_pos
      hα_init_lt_one := hinit_lt
      lam := lam
      hlam := hlam
      hdisp := hdisp
      γ_max := gmax
      hγ_max_pos := hgmax_pos
      hγ_max := hgmax
      δ_star := explicitEquil gmax D.K r_star
      hδ_star_pos := explicitEquil_pos gmax D.K r_star hgmax_pos D.hK hr_pos
      hα_star_lb := fun k => explicitEquil_mono_gamma (D.γ k) gmax D.K r_star
        (D.hγ k) D.hK hr_pos (hgmax k)
      c_min := cmin
      hc_min_pos := hcmin_pos
      hc_min := hcmin
      ε_inst := eps
      hε_pos := heps
      hε_small := by convert heps1 using 2; rw [hc_sum]
      hε_beta := heps2 }
  refine ⟨r_star, hr_pos, hr_lt, ?_⟩
  intro ε hε
  obtain ⟨T, hT⟩ := full_chain_convergence FD ε hε
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  rwa [show (∑ k, D.c k * as k) = r_star from h_sc] at this

/-! ## Fully automatic: no gmax/cmin parameters -/

theorem parametric_convergence (D : NPoleBarrierData n)
    (hn : 0 < n) (hc_sum : ∑ k, D.c k = 1)
    (hK_super : npoleCriticalK D.γ D.c < D.K)
    (hinit_pos : ∀ k, 0 < D.α 0 k)
    (hinit_lt : ∀ k, D.α 0 k < 1) :
    ∃ r_star, 0 < r_star ∧ r_star < 1 ∧
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → |D.r t - r_star| < ε := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k_γ, _, hk_γ⟩ := Finset.exists_max_image Finset.univ D.γ Finset.univ_nonempty
  obtain ⟨k_c, _, hk_c⟩ := Finset.exists_min_image Finset.univ D.c Finset.univ_nonempty
  exact global_stability_supercritical D hn hc_sum hK_super hinit_pos hinit_lt
    (D.γ k_γ) (D.hγ k_γ) (fun k => hk_γ k (Finset.mem_univ k))
    (D.c k_c) (D.hc k_c) (fun k => hk_c k (Finset.mem_univ k))

end
