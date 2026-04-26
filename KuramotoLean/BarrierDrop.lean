/-
  Kuramoto Stability — Initial Barrier V-Drop
  =============================================

  Proves V drops below V_incoherent in finite time by using the component
  barrier (α_k(t) ≥ α_k(0)·exp(-γ_max·t)) with pair coercivity.

  On [0, T]: all α_k ≥ α_min(0)·exp(-γ_max·T) > 0. The uniform rate gives
  dV/dt ≤ -K·δ₀·δ*·V, so V(T) ≤ V(0)·exp(-K·δ₀·δ*·T).

  If the drop puts V below V_incoherent, quantitative persistence kicks in
  → component propagation → EndToEndConvergence → V → 0 → r → r*.

  0 sorry target.
-/

import KuramotoLean.EndToEndConvergence

open Real Set Finset Filter

noncomputable section

variable {n : ℕ}

/-! ## Barrier drop: V(T) ≤ V(0)·exp(-μT) using component barrier -/

theorem barrier_drop_V (D : NPoleBarrierData n)
    (α_star : Fin n → ℝ)
    (hα_star_pos : ∀ k, 0 < α_star k)
    (hα_star_lt : ∀ k, α_star k < 1)
    (h_equil : ∀ k, nPoleODE D.γ D.c D.K α_star k = 0)
    (hc_sum : ∑ k, D.c k = 1)
    (hα_init_lt_one : ∀ k, D.α 0 k < 1)
    (α_min : ℝ) (hα_min_pos : 0 < α_min) (hα_min : ∀ k, α_min ≤ D.α 0 k)
    (γ_max : ℝ) (hγ_max_pos : 0 < γ_max) (hγ_max : ∀ k, D.γ k ≤ γ_max)
    (δ_star : ℝ) (hδ_star_pos : 0 < δ_star) (hδ_star : ∀ k, δ_star ≤ α_star k)
    (T : ℝ) (hT : 0 < T) :
    l2Distance D.c (D.α T) α_star ≤
      l2Distance D.c (D.α 0) α_star *
        exp (-(D.K * (α_min * exp (-(γ_max * T))) * δ_star) * T) := by
  have hcomp_lb : ∀ t, 0 ≤ t → t ≤ T → ∀ k,
      α_min * exp (-(γ_max * T)) ≤ D.α t k := by
    intro t ht htT k
    have h1 : α_min ≤ D.α 0 k := hα_min k
    have h2 : exp (-(γ_max * T)) ≤ exp (-(D.γ k * T)) :=
      exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (hγ_max k)
        (le_of_lt hT)))
    have h3 : α_min * exp (-(γ_max * T)) ≤ D.α 0 k * exp (-(D.γ k * T)) :=
      mul_le_mul h1 h2 (exp_pos _).le (le_of_lt (lt_of_lt_of_le hα_min_pos h1))
    have h4 : D.α 0 k * exp (-(D.γ k * T)) = D.α 0 k * exp (-(D.γ k) * T) := by
      congr 1; ring_nf
    have h5 := component_lower_on_interval D k T t ht htT
    linarith
  have hα_lt : ∀ t, 0 ≤ t → t ≤ T → ∀ k, D.α t k < 1 :=
    fun t ht _ k => component_strict_lt_one D hα_init_lt_one t ht k
  have hV_cont : ContinuousOn (fun t => l2Distance D.c (D.α t) α_star) (Icc 0 T) :=
    (l2_continuousOn D.c D.α α_star D.hα_cont).mono Icc_subset_Ici_self
  have h := l2_drop_from_bounds D.γ D.c D.K D.α α_star
    D.hK D.hγ D.hc h_equil hα_star_pos hα_star_lt
    (α_min * exp (-(γ_max * T))) δ_star
    (mul_pos hα_min_pos (exp_pos _)) hδ_star_pos hδ_star hc_sum
    0 T le_rfl (le_of_lt hT)
    (fun t ht1 ht2 k => hcomp_lb t ht1 (by linarith) k)
    (fun t ht1 ht2 k => hα_lt t ht1 (by linarith) k)
    (fun t ht k => D.hα_ode t ht k) (by rwa [zero_add])
  simp only [zero_add] at h; exact h

/-! ## Basin entry structure + convergence -/

structure BarrierBasinData (n : ℕ) extends NPoleBarrierData n where
  hn : 0 < n
  α_star : Fin n → ℝ
  γ_max : ℝ
  δ_star : ℝ
  α_min : ℝ
  hα_star_pos : ∀ k, 0 < α_star k
  hα_star_lt : ∀ k, α_star k < 1
  hγ_max_pos : 0 < γ_max
  hγ_max : ∀ k, γ k ≤ γ_max
  hδ_star_pos : 0 < δ_star
  hα_star_lb : ∀ k, δ_star ≤ α_star k
  hα_min_pos : 0 < α_min
  hα_min : ∀ k, α_min ≤ α 0 k
  h_equil : ∀ k, nPoleODE γ c K α_star k = 0
  hc_sum : ∑ k, c k = 1
  hα_init_lt_one : ∀ k, α 0 k < 1
  T_drop : ℝ
  hT_drop : 0 < T_drop
  h_basin_entry : l2Distance c (α 0) α_star *
    exp (-(K * (α_min * exp (-(γ_max * T_drop))) * δ_star) * T_drop) <
    V_incoherent c α_star

theorem BarrierBasinData.hα_init_pos (B : BarrierBasinData n) :
    ∀ k, 0 < B.α 0 k :=
  fun k => lt_of_lt_of_le B.hα_min_pos (B.hα_min k)

theorem BarrierBasinData.V_at_T_lt_Vinc (B : BarrierBasinData n) :
    l2Distance B.c (B.α B.T_drop) B.α_star < V_incoherent B.c B.α_star :=
  lt_of_le_of_lt
    (barrier_drop_V B.toNPoleBarrierData B.α_star
      B.hα_star_pos B.hα_star_lt B.h_equil B.hc_sum
      B.hα_init_lt_one B.α_min B.hα_min_pos B.hα_min
      B.γ_max B.hγ_max_pos B.hγ_max B.δ_star B.hδ_star_pos B.hα_star_lb
      B.T_drop B.hT_drop)
    B.h_basin_entry

theorem BarrierBasinData.r_persist_from_T (B : BarrierBasinData n)
    (t : ℝ) (ht : B.T_drop ≤ t) : 0 < B.toNPoleBarrierData.r t := by
  have hV_anti : AntitoneOn (fun s => l2Distance B.c (B.α s) B.α_star) (Ici 0) :=
    l2_antitoneOn B.toNPoleBarrierData B.α_star B.hα_star_pos B.hα_star_lt
      B.h_equil B.hα_init_pos
      (fun s hs k => component_strict_lt_one B.toNPoleBarrierData
        B.hα_init_lt_one s hs k)
  have hV_lt : l2Distance B.c (B.α t) B.α_star < V_incoherent B.c B.α_star :=
    lt_of_le_of_lt
      (hV_anti (mem_Ici.mpr (le_of_lt B.hT_drop))
        (mem_Ici.mpr (le_trans (le_of_lt B.hT_drop) ht)) ht)
      B.V_at_T_lt_Vinc
  exact energy_exclusion_r_pos B.c (B.α t) B.α_star B.hc
    (B.hα_nn t (le_trans (le_of_lt B.hT_drop) ht)) hV_lt

theorem barrier_basin_convergence (B : BarrierBasinData n) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t →
      |B.toNPoleBarrierData.r t - ∑ k, B.c k * B.α_star k| < ε := by
  have hV_anti : AntitoneOn (fun s => l2Distance B.c (B.α s) B.α_star) (Ici 0) :=
    l2_antitoneOn B.toNPoleBarrierData B.α_star B.hα_star_pos B.hα_star_lt
      B.h_equil B.hα_init_pos
      (fun s hs k => component_strict_lt_one B.toNPoleBarrierData
        B.hα_init_lt_one s hs k)
  set α_star_max := Finset.univ.sup' ⟨⟨0, B.hn⟩, Finset.mem_univ _⟩
    (fun k => B.α_star k) with hα_star_max_def
  have hα_star_max_pos : 0 < α_star_max := by
    have : B.α_star ⟨0, B.hn⟩ ≤ α_star_max :=
      Finset.le_sup' _ (Finset.mem_univ _)
    linarith [B.hα_star_pos ⟨0, B.hn⟩]
  have hα_star_max_bound : ∀ k, B.α_star k ≤ α_star_max :=
    fun k => Finset.le_sup' _ (Finset.mem_univ _)
  set V_gap := V_incoherent B.c B.α_star - l2Distance B.c (B.α B.T_drop) B.α_star
  have hV_gap : 0 < V_gap := by linarith [B.V_at_T_lt_Vinc]
  set δ₁ := V_gap / (2 * α_star_max)
  have hδ₁ : 0 < δ₁ := div_pos hV_gap (by positivity)
  have hr_persist : ∀ t, B.T_drop ≤ t → δ₁ ≤ B.toNPoleBarrierData.r t := by
    intro t ht
    have hV_le : l2Distance B.c (B.α t) B.α_star ≤
        l2Distance B.c (B.α B.T_drop) B.α_star :=
      hV_anti (mem_Ici.mpr (le_of_lt B.hT_drop))
        (mem_Ici.mpr (le_trans (le_of_lt B.hT_drop) ht)) ht
    have hV_lt : l2Distance B.c (B.α t) B.α_star < V_incoherent B.c B.α_star :=
      lt_of_le_of_lt hV_le B.V_at_T_lt_Vinc
    have hV_gap_le : V_gap ≤ V_incoherent B.c B.α_star -
        l2Distance B.c (B.α t) B.α_star := by linarith
    have hr := r_lower_from_V_gap B.c (B.α t) B.α_star α_star_max
      hα_star_max_pos hα_star_max_bound
      (B.hα_nn t (le_trans (le_of_lt B.hT_drop) ht))
      (B.hα_le t (le_trans (le_of_lt B.hT_drop) ht))
      B.hc hV_lt
    calc δ₁ = V_gap / (2 * α_star_max) := rfl
      _ ≤ (V_incoherent B.c B.α_star - l2Distance B.c (B.α t) B.α_star) /
          (2 * α_star_max) :=
        div_le_div_of_nonneg_right hV_gap_le (by positivity : 0 < 2 * α_star_max).le
      _ ≤ B.toNPoleBarrierData.r t := hr
  set β := min (B.K * δ₁ / (4 * B.γ_max)) (1 / 2)
  have hβ : 0 < β :=
    lt_min (div_pos (mul_pos B.hK hδ₁)
      (mul_pos (by norm_num : (0:ℝ) < 4) B.hγ_max_pos)) (by norm_num)
  have hβ_small : ∀ k, β ≤ B.K * δ₁ / (4 * B.γ k) := by
    intro k
    calc β ≤ B.K * δ₁ / (4 * B.γ_max) := min_le_left _ _
      _ ≤ B.K * δ₁ / (4 * B.γ k) :=
        div_le_div_of_nonneg_left (le_of_lt (mul_pos B.hK hδ₁))
          (mul_pos (by norm_num : (0:ℝ) < 4) (B.hγ k))
          (mul_le_mul_of_nonneg_left (B.hγ_max k) (by norm_num : (0:ℝ) ≤ 4))
  set T₀ := B.T_drop + escapeTime B.K δ₁ β
  have hT₀_pos : 0 < T₀ := by
    have := escapeTime_pos B.K δ₁ β B.hK hδ₁ hβ; linarith [B.hT_drop]
  have h_comp_lb : ∀ t, T₀ ≤ t → ∀ k, β ≤ B.α t k := by
    intro t ht k
    exact component_persistence_from_r B.toNPoleBarrierData k δ₁ β
      hδ₁ hβ (hβ_small k) (min_le_right _ _) B.hα_init_pos
      B.T_drop (le_of_lt B.hT_drop)
      (fun s hs => hr_persist s (by linarith))
      t (by linarith [ht])
  set D : EndToEndData n :=
    { B.toNPoleBarrierData with
      α_star := B.α_star
      hα_star_pos := B.hα_star_pos
      hα_star_lt := B.hα_star_lt
      h_equil := B.h_equil
      hc_sum := B.hc_sum
      hα_init_pos := B.hα_init_pos
      hα_strict_lt := fun t ht k => component_strict_lt_one B.toNPoleBarrierData
        B.hα_init_lt_one t ht k
      comp_lb := β
      equil_lb := B.δ_star
      hcomp_lb := hβ
      hequil_lb := B.hδ_star_pos
      hequil_lb_bound := B.hα_star_lb
      T₀ := T₀
      hT₀ := le_of_lt hT₀_pos
      hcomponent_lb := h_comp_lb }
  exact end_to_end_r_convergence D (∑ k, B.c k * B.α_star k) rfl

end
