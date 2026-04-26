/-
  Kuramoto Stability — V(0) < V_incoherent gives r → r*
  =======================================================

  When the initial Lyapunov value is below the incoherent level,
  quantitative persistence gives r ≥ δ₁ > 0 permanently, then
  component propagation → EndToEndConvergence → r → r*.

  This theorem packages the full chain from V(0) < V_incoherent
  (which can be established either by α(0) ∈ (0, 2α*)^n or by
  the barrier drop in BarrierDrop.lean) to convergence.

  0 sorry target.
-/

import KuramotoLean.BarrierDrop

open Filter Topology Set Finset Real

noncomputable section

variable {n : ℕ}

/-! ## V(0) < V_incoherent gives r → r*

The full chain: V(0) < V_incoherent → quantitative r-persistence
→ component propagation → EndToEndConvergence → r → r*. -/

theorem sub_vinc_convergence (D : NPoleBarrierData n)
    (hn : 0 < n)
    (α_star : Fin n → ℝ) (γ_max δ_star : ℝ)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (hα_star_lt : ∀ k, α_star k < 1)
    (hγ_max_pos : 0 < γ_max)
    (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (hδ_star_pos : 0 < δ_star)
    (hα_star_lb : ∀ k, δ_star ≤ α_star k)
    (h_equil : ∀ k, nPoleODE D.γ D.c D.K α_star k = 0)
    (hc_sum : ∑ k, D.c k = 1)
    (hα_init_pos : ∀ k, 0 < D.α 0 k)
    (hα_init_lt_one : ∀ k, D.α 0 k < 1)
    (hV_init : l2Distance D.c (D.α 0) α_star < V_incoherent D.c α_star) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |D.r t - ∑ k, D.c k * α_star k| < ε := by
  set α_star_max := Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun k => α_star k)
  have hα_star_max_pos : 0 < α_star_max :=
    lt_of_lt_of_le (hα_star_pos ⟨0, hn⟩) (Finset.le_sup' _ (Finset.mem_univ _))
  set V_gap := V_incoherent D.c α_star - l2Distance D.c (D.α 0) α_star
  have hV_gap : 0 < V_gap := by linarith
  set δ₁ := V_gap / (2 * α_star_max)
  have hδ₁ : 0 < δ₁ := div_pos hV_gap (by positivity)
  have hV_anti : AntitoneOn (fun s => l2Distance D.c (D.α s) α_star) (Ici 0) :=
    l2_antitoneOn D α_star hα_star_pos hα_star_lt h_equil hα_init_pos
      (fun s hs k => component_strict_lt_one D hα_init_lt_one s hs k)
  have hr_persist : ∀ t, 0 ≤ t → δ₁ ≤ D.r t := by
    intro t ht
    have hV_le := hV_anti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
    have hV_lt : l2Distance D.c (D.α t) α_star < V_incoherent D.c α_star :=
      lt_of_le_of_lt hV_le hV_init
    have hr := r_lower_from_V_gap D.c (D.α t) α_star α_star_max
      hα_star_max_pos (fun k => Finset.le_sup' _ (Finset.mem_univ _))
      (D.hα_nn t ht) (D.hα_le t ht) D.hc hV_lt
    calc δ₁ ≤ (V_incoherent D.c α_star - l2Distance D.c (D.α t) α_star) /
          (2 * α_star_max) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity : 0 < 2 * α_star_max).le
      _ ≤ D.r t := hr
  set β := min (D.K * δ₁ / (4 * γ_max)) (1 / 2)
  have hβ : 0 < β :=
    lt_min (div_pos (mul_pos D.hK hδ₁)
      (mul_pos (by norm_num : (0:ℝ) < 4) hγ_max_pos)) (by norm_num)
  set T₀ := escapeTime D.K δ₁ β
  have h_comp_lb : ∀ t, T₀ ≤ t → ∀ k, β ≤ D.α t k := by
    intro t ht k
    exact component_persistence_from_r D k δ₁ β hδ₁ hβ
      (by calc β ≤ D.K * δ₁ / (4 * γ_max) := min_le_left _ _
            _ ≤ D.K * δ₁ / (4 * D.γ k) :=
              div_le_div_of_nonneg_left (le_of_lt (mul_pos D.hK hδ₁))
                (mul_pos (by norm_num : (0:ℝ) < 4) (D.hγ k))
                (mul_le_mul_of_nonneg_left (hγ_max k) (by norm_num : (0:ℝ) ≤ 4)))
      (min_le_right _ _) hα_init_pos 0 le_rfl
      (fun s hs => hr_persist s (by linarith)) t (by linarith)
  exact end_to_end_r_convergence
    { D with
      α_star := α_star
      hα_star_pos := hα_star_pos
      hα_star_lt := hα_star_lt
      h_equil := h_equil
      hc_sum := hc_sum
      hα_init_pos := hα_init_pos
      hα_strict_lt := fun t ht k => component_strict_lt_one D hα_init_lt_one t ht k
      comp_lb := β
      equil_lb := δ_star
      hcomp_lb := hβ
      hequil_lb := hδ_star_pos
      hequil_lb_bound := hα_star_lb
      T₀ := T₀
      hT₀ := le_of_lt (escapeTime_pos D.K δ₁ β D.hK hδ₁ hβ)
      hcomponent_lb := h_comp_lb }
    (∑ k, D.c k * α_star k) rfl

end
