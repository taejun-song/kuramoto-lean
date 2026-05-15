import KuramotoLean.ComplexOASymmetry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology Real MeasureTheory Set

noncomputable section

private lemma basin_invariance (f : ℝ → ℝ) (B rate : ℝ)
    (hrate : 0 < rate) (_hB : 0 < B)
    (hf_cont : Continuous f)
    (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hf0 : f 0 < B)
    (hf_deriv : ∀ t, 0 < t → f t < B →
      HasDerivAt f (deriv f t) t ∧ deriv f t ≤ -rate * f t)
    (t : ℝ) (ht : 0 ≤ t) : f t < B := by
  by_contra h
  push Not at h
  let S := Set.Ici (0 : ℝ) ∩ {s | B ≤ f s}
  have hS_ne : S.Nonempty := ⟨t, ht, h⟩
  have hS_bdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have hS_closed : IsClosed S := isClosed_Ici.inter (isClosed_le continuous_const hf_cont)
  set T := sInf S
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have hT_nn : (0 : ℝ) ≤ T := hT_mem.1
  have hfT : B ≤ f T := hT_mem.2
  have hT_pos : 0 < T := by
    rcases eq_or_lt_of_le hT_nn with h0 | h0
    · exfalso; linarith [h0 ▸ hfT]
    · exact h0
  have hf_lt_B : ∀ s, 0 ≤ s → s < T → f s < B := by
    intro s hs hsT
    by_contra hc
    push Not at hc
    exact absurd (csInf_le hS_bdd (show s ∈ S from ⟨hs, hc⟩)) (not_le.mpr hsT)
  have hf_anti : AntitoneOn f (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact hf_cont.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have ⟨hd, _⟩ := hf_deriv x hx.1 (hf_lt_B x (le_of_lt hx.1) hx.2)
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have ⟨_, hd⟩ := hf_deriv x hx.1 (hf_lt_B x (le_of_lt hx.1) hx.2)
      calc deriv f x ≤ -rate * f x := hd
        _ ≤ 0 := by nlinarith [hf_nn x (le_of_lt hx.1)]
  linarith [hf_anti (left_mem_Icc.mpr hT_nn) (right_mem_Icc.mpr hT_nn) hT_nn]

private lemma exp_decay_bound (f : ℝ → ℝ) (B rate : ℝ)
    (_hrate : 0 < rate) (_hB : 0 < B)
    (hf_cont : Continuous f)
    (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (_hf0 : f 0 < B)
    (hf_deriv : ∀ t, 0 < t → f t < B →
      HasDerivAt f (deriv f t) t ∧ deriv f t ≤ -rate * f t)
    (hf_basin : ∀ t, 0 ≤ t → f t < B)
    (t : ℝ) (ht : 0 ≤ t) : f t ≤ f 0 * exp (-rate * t) := by
  suffices h : f t * exp (rate * t) ≤ f 0 by
    have hexp_pos : (0 : ℝ) < exp (rate * t) := exp_pos _
    have : f t = f t * exp (rate * t) * exp (-(rate * t)) := by
      rw [mul_assoc, ← exp_add]; simp
    rw [this]
    calc f t * exp (rate * t) * exp (-(rate * t))
        ≤ f 0 * exp (-(rate * t)) := by
          apply mul_le_mul_of_nonneg_right h (le_of_lt (exp_pos _))
      _ = f 0 * exp (-rate * t) := by ring_nf
  let g := fun s => f s * exp (rate * s)
  suffices hg_anti : AntitoneOn g (Set.Icc 0 t) by
    have h1 : g t ≤ g 0 :=
      hg_anti (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    simp [g] at h1
    linarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
  · exact (hf_cont.mul (continuous_exp.comp (continuous_const.mul continuous_id'))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_pos := hx.1
    have hfx_lt_B := hf_basin x (le_of_lt hx_pos)
    have ⟨hfd, _⟩ := hf_deriv x hx_pos hfx_lt_B
    have hexp_d : HasDerivAt (fun s => exp (rate * s)) (exp (rate * x) * rate) x :=
      (hasDerivAt_const_mul rate (x := x)).exp
    exact (hfd.mul hexp_d).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx_pos := hx.1
    have hfx_lt_B := hf_basin x (le_of_lt hx_pos)
    have ⟨hfd, hd_le⟩ := hf_deriv x hx_pos hfx_lt_B
    have hexp_d : HasDerivAt (fun s => exp (rate * s)) (exp (rate * x) * rate) x :=
      (hasDerivAt_const_mul rate (x := x)).exp
    have hg_d : HasDerivAt g (deriv f x * exp (rate * x) + f x * (exp (rate * x) * rate)) x :=
      hfd.mul hexp_d
    rw [hg_d.deriv]
    have hexp_pos : (0 : ℝ) < exp (rate * x) := exp_pos _
    nlinarith [hf_nn x (le_of_lt hx_pos)]

/-- Gronwall bootstrap: f continuous, f(0) < B, f ≥ 0, f' ≤ -rate·f in basin → f → 0. -/
theorem gronwall_bootstrap_tendsto
    (f : ℝ → ℝ) (B rate : ℝ)
    (hrate : 0 < rate) (hB : 0 < B)
    (hf_cont : Continuous f)
    (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hf0 : f 0 < B)
    (hf_deriv : ∀ t, 0 < t → f t < B →
      HasDerivAt f (deriv f t) t ∧ deriv f t ≤ -rate * f t) :
    Tendsto f atTop (nhds 0) := by
  have hf_basin := basin_invariance f B rate hrate hB hf_cont hf_nn hf0 hf_deriv
  have hf_bound := exp_decay_bound f B rate hrate hB hf_cont hf_nn hf0 hf_deriv hf_basin
  apply squeeze_zero' (f := f) (g := fun t => f 0 * exp (-rate * t))
  · exact eventually_atTop.mpr ⟨0, fun t ht => hf_nn t ht⟩
  · exact eventually_atTop.mpr ⟨0, fun t ht => hf_bound t ht⟩
  · have h1 : Tendsto (fun t => rate * t) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b / rate, fun s hs => by
        calc b = rate * (b / rate) := by field_simp
          _ ≤ rate * s := mul_le_mul_of_nonneg_left hs (le_of_lt hrate)⟩
    have h2 : Tendsto (fun t => exp (-(rate * t))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 : Tendsto (fun t => f 0 * exp (-(rate * t))) atTop (𝓝 0) := by
      simpa [mul_zero] using h2.const_mul (f 0)
    exact h3.congr (fun t => by ring_nf)

end
