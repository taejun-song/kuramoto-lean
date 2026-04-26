/-
  Kuramoto Stability — Additive V-Drop Lemma
  ============================================

  If V'(t) ≤ -c on (a, a+Δ) with c > 0, then V(a+Δ) ≤ V(a) - c·Δ.

  Proof: W(t) = V(t) + c·t has W'(t) = V'(t) + c ≤ 0, so W is
  non-increasing (antitoneOn_of_deriv_nonpos). Hence W(a+Δ) ≤ W(a),
  i.e., V(a+Δ) + c·(a+Δ) ≤ V(a) + c·a, giving V(a+Δ) ≤ V(a) - c·Δ.

  Combined with pair_sum_lower_from_component, this gives a
  quantitative V-decrease when a component escapes.

  0 sorry target.
-/

import KuramotoLean.OrderParameterEscape

open Real Set

noncomputable section

/-! ## Additive drop from signed derivative bound -/

/-- **Additive drop lemma.** If V'(t) ≤ -c on (a, a+Δ) and V is
    continuous on [a, a+Δ], then V(a+Δ) ≤ V(a) - c·Δ.

    Proof: W(t) = V(t) + c·t is non-increasing (since W' = V' + c ≤ 0),
    so W(a+Δ) ≤ W(a), giving V(a+Δ) ≤ V(a) - c·Δ. -/
theorem additive_drop (V V' : ℝ → ℝ) (c a Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hc : 0 ≤ c)
    (hV_cont : ContinuousOn V (Icc a (a + Δ)))
    (hV_deriv : ∀ t, t ∈ Ioo a (a + Δ) → HasDerivAt V (V' t) t)
    (hV_bound : ∀ t, t ∈ Ioo a (a + Δ) → V' t ≤ -c) :
    V (a + Δ) ≤ V a - c * Δ := by
  set W : ℝ → ℝ := fun t => V t + c * t
  have hW_cont : ContinuousOn W (Icc a (a + Δ)) :=
    hV_cont.add (continuousOn_const.mul continuousOn_id)
  have hd_ct : ∀ t, HasDerivAt (fun s => c * s) c t := by
    intro t
    have := (hasDerivAt_id t).const_mul c; simp only [mul_one, id_eq] at this; exact this
  have hW_diff : DifferentiableOn ℝ W (interior (Icc a (a + Δ))) := by
    rw [interior_Icc]; intro t ht
    exact ((hV_deriv t ht).add (hd_ct t)).differentiableAt.differentiableWithinAt
  have hW_deriv_le : ∀ t ∈ interior (Icc a (a + Δ)), deriv W t ≤ 0 := by
    rw [interior_Icc]; intro t ht
    have hd_W : HasDerivAt W (V' t + c) t := (hV_deriv t ht).add (hd_ct t)
    rw [hd_W.deriv]
    linarith [hV_bound t ht]
  have hW_anti := antitoneOn_of_deriv_nonpos (convex_Icc a (a + Δ)) hW_cont
    hW_diff hW_deriv_le
  have hW_le : W (a + Δ) ≤ W a :=
    hW_anti (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
  linarith

/-- **Additive drop with non-negative c.** Variant where c is given
    as the negative of the derivative bound. -/
theorem additive_drop' (V V' : ℝ → ℝ) (m a Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hm : 0 ≤ m)
    (hV_cont : ContinuousOn V (Icc a (a + Δ)))
    (hV_deriv : ∀ t, t ∈ Ioo a (a + Δ) → HasDerivAt V (V' t) t)
    (hV_bound : ∀ t, t ∈ Ioo a (a + Δ) → V' t + m ≤ 0) :
    V (a + Δ) ≤ V a - m * Δ :=
  additive_drop V V' m a Δ hΔ hm hV_cont hV_deriv
    (fun t ht => by linarith [hV_bound t ht])

end
