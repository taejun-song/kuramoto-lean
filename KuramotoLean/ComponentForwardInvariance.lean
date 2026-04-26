/-
  Kuramoto Stability — Forward Invariance of Component Threshold
  ================================================================

  If α_k(a) ≥ β and the order parameter r(t) ≥ δ on [a,b],
  then α_k(t) ≥ β for all t ∈ [a,b].

  Proof: compact maximum of the level set + linear growth.

  0 sorry target.
-/

import KuramotoLean.RPersistenceComponent
import Mathlib.Topology.Order.Monotone

open Real Set Finset

noncomputable section

variable {n : ℕ}

/-- **Forward invariance of component threshold.** -/
theorem component_threshold_forward_inv (D : NPoleBarrierData n) (k : Fin n)
    (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 < β)
    (hβ_small : β ≤ D.K * δ / (4 * D.γ k))
    (hβ_half : β ≤ 1 / 2)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : ∀ t, a ≤ t → t ≤ b → δ ≤ D.r t)
    (hα_a : β ≤ D.α a k) :
    ∀ t, a ≤ t → t ≤ b → β ≤ D.α t k := by
  intro t₁ ht₁_lo ht₁_hi
  rcases eq_or_lt_of_le ht₁_lo with rfl | ha_lt
  · exact hα_a
  by_contra h_neg
  push_neg at h_neg
  -- S = Icc a t₁ ∩ {t | β ≤ α_k(t)} is nonempty, closed, bounded above
  set f : ℝ → ℝ := fun t => D.α t k
  set S := Icc a t₁ ∩ f ⁻¹' (Ici β)
  have hf_cont : ContinuousOn f (Icc a t₁) :=
    (D.hα_cont k).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha))
  have hS_ne : S.Nonempty := ⟨a, ⟨le_rfl, le_of_lt ha_lt⟩, hα_a⟩
  have hS_closed : IsClosed S :=
    hf_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_bdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  -- c = sSup S ∈ S (closed + nonempty + bdd above)
  have hc_mem : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  set c := sSup S
  have hc_lo : a ≤ c := hc_mem.1.1
  have hc_hi : c ≤ t₁ := hc_mem.1.2
  have hα_c_ge : β ≤ f c := hc_mem.2
  -- c < t₁ (since f(t₁) < β)
  have hc_lt : c < t₁ := lt_of_le_of_ne hc_hi (fun h => by rw [← h] at h_neg; linarith)
  -- α_k(c) = β: if > β, continuity gives points past c in S
  have hα_c_eq : f c = β := by
    refine le_antisymm ?_ hα_c_ge
    by_contra h_gt
    push_neg at h_gt
    rw [Metric.continuousOn_iff] at hf_cont
    obtain ⟨δ', hδ', hball⟩ := hf_cont c (mem_Icc.mpr ⟨hc_lo, hc_hi⟩)
      (f c - β) (by linarith)
    -- Pick ε = min(δ'/2, (t₁-c)/2) > 0
    set ε' := min (δ' / 2) ((t₁ - c) / 2)
    have hε'_pos : 0 < ε' := lt_min (by linarith) (by linarith)
    have hε'_lt_δ : ε' < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hcε_le : c + ε' ≤ t₁ := by linarith [min_le_right (δ'/2) ((t₁-c)/2)]
    have hcε_in : c + ε' ∈ Icc a t₁ := ⟨by linarith, hcε_le⟩
    have hcε_dist : dist (c + ε') c < δ' := by
      rw [Real.dist_eq, show c + ε' - c = ε' from by ring, abs_of_pos hε'_pos]; exact hε'_lt_δ
    have hα_cε := hball (c + ε') hcε_in hcε_dist
    rw [Real.dist_eq] at hα_cε
    have hα_cε_ge : β ≤ f (c + ε') := by
      have := (abs_lt.mp hα_cε).1; linarith
    exact absurd (le_csSup hS_bdd ⟨hcε_in, hα_cε_ge⟩) (not_le.mpr (by linarith))
  -- For t ∈ (c, t₁]: f(t) < β (by maximality of c)
  have hα_past : ∀ t, c < t → t ≤ t₁ → f t < β := by
    intro t ht_lo ht_hi
    by_contra h_ge
    push_neg at h_ge
    exact absurd (le_csSup hS_bdd ⟨⟨by linarith, ht_hi⟩, h_ge⟩) (not_le.mpr ht_lo)
  -- On [c, t₁]: f ≤ β
  have hα_le_on : ∀ t, c ≤ t → t ≤ t₁ → f t ≤ β := by
    intro t ht_lo ht_hi
    rcases eq_or_lt_of_le ht_lo with rfl | hlt
    · exact le_of_eq hα_c_eq
    · exact le_of_lt (hα_past t hlt ht_hi)
  -- Linear growth on [c, t₁] gives contradiction
  have hα_le_small : ∀ t, c ≤ t → t ≤ t₁ → D.α t k ≤ D.K * δ / (4 * D.γ k) :=
    fun t ht1 ht2 => le_trans (hα_le_on t ht1 ht2) hβ_small
  have hα_le_half : ∀ t, c ≤ t → t ≤ t₁ → D.α t k ≤ 1 / 2 :=
    fun t ht1 ht2 => le_trans (hα_le_on t ht1 ht2) hβ_half
  have h_growth := component_linear_growth D k δ hδ c t₁ (by linarith) (le_of_lt hc_lt)
    (fun t ht1 ht2 => hr t (by linarith) (by linarith))
    hα_le_small hα_le_half
  -- h_growth: D.α c k + D.K * δ / 8 * (t₁ - c) ≤ D.α t₁ k
  -- hα_c_eq: f c = β, i.e., D.α c k = β
  have hα_c_eq' : D.α c k = β := hα_c_eq
  have hμ_pos : (0:ℝ) < D.K * δ / 8 := div_pos (mul_pos D.hK hδ) (by norm_num : (0:ℝ) < 8)
  have htc_pos : (0:ℝ) < t₁ - c := by linarith
  have h_prod := mul_pos hμ_pos htc_pos
  linarith [hα_past t₁ hc_lt le_rfl]

/-! ## Combined: permanent component lower bound from r-persistence -/

/-- **Component persistence from order parameter persistence.** -/
theorem component_persistence_from_r (D : NPoleBarrierData n) (k : Fin n)
    (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 < β)
    (hβ_small : β ≤ D.K * δ / (4 * D.γ k))
    (hβ_half : β ≤ 1 / 2)
    (hα_init : ∀ j, 0 < D.α 0 j)
    (T : ℝ) (hT : 0 ≤ T)
    (hr : ∀ t, T ≤ t → δ ≤ D.r t) :
    ∀ t, T + escapeTime D.K δ β ≤ t → β ≤ D.α t k := by
  set τ := escapeTime D.K δ β
  have hτ_pos := escapeTime_pos D.K δ β D.hK hδ hβ
  obtain ⟨t₀, ht₀_lo, _, hα_t₀⟩ :=
    component_must_exceed D k δ β hδ hβ hβ_small hβ_half
      T τ hT hτ_pos le_rfl (fun t ht1 _ => hr t ht1)
      (component_positive D k (hα_init k) T hT)
  intro t ht
  exact component_threshold_forward_inv D k δ β hδ hβ hβ_small hβ_half
    t₀ t (by linarith) (by linarith) (fun s hs1 _ => hr s (by linarith))
    (le_of_lt hα_t₀) t (by linarith) le_rfl

end
