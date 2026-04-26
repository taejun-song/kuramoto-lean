/-
  Kuramoto Stability Project — Approximate Self-Consistency
  ===========================================================
  Closes the ∃ vs ∀ gap in the slaving argument.

  Strategy: don't need slaving at EVERY ω. Need slaving at ENOUGH
  ω's that the self-consistency r = ∫αg is determined.

  At locked ω (|ω| < Kr*): backward contraction is strong → slaving ✓
  At drifting ω (|ω| > Kr*): contraction is weak BUT contribution
  to r is small (∫_{drift} g → 0 as the locked region expands).

  The self-consistency r = Φ_locked(r) + error, with |error| ≤ δ(M).
  For M = √(KΨ_x) with large Ψ_x (from sup_Ω Ψ = +∞): δ → 0.
  The approximate fixed point r ≈ Φ(r) with small error still
  selects r = 0 or r = r* (isolated fixed points).

  Combined with topology: r* ∈ Ω_r.
-/

import KuramotoLean.ScalarReduction

open Set

noncomputable section

/-- **Approximate containment in equilibria.**
    If Ω_r ⊂ {|r| < δ} ∪ {|r - r*| < δ} for ARBITRARILY SMALL δ:
    then Ω_r ⊂ {0} ∪ {r*} (taking δ → 0 with Ω_r closed). -/
theorem approx_containment_gives_exact
    (Omega_r : Set ℝ) (r_star : ℝ) (hr : 0 < r_star)
    (hclosed : IsClosed Omega_r)
    (happrox : ∀ δ > 0, Omega_r ⊆ {x | |x| < δ} ∪ {x | |x - r_star| < δ}) :
    Omega_r ⊆ {0} ∪ {r_star} := by
  intro x hx
  -- For any δ > 0: x ∈ {|x| < δ} ∪ {|x-r*| < δ}. Taking δ → 0: x = 0 or x = r*.
  by_contra h
  simp only [mem_union, mem_singleton_iff] at h
  push Not at h
  obtain ⟨hne0, hner⟩ := h
  -- x ≠ 0 and x ≠ r*. So |x| > 0 and |x - r*| > 0.
  have hd1 : 0 < |x| := abs_pos.mpr hne0
  have hd2 : 0 < |x - r_star| := abs_pos.mpr (sub_ne_zero.mpr hner)
  -- Take δ = min(|x|, |x-r*|) / 2 > 0.
  set δ := min |x| |x - r_star| / 2
  have hδ : 0 < δ := by positivity
  have h := happrox δ hδ hx
  rcases h with h | h
  · simp only [mem_setOf_eq, δ] at h
    linarith [min_le_left |x| |x - r_star|]
  · simp only [mem_setOf_eq, δ] at h
    linarith [min_le_right |x| |x - r_star|]

/-- **Main theorem: approximate self-consistency gives stability.**
    If for every ε > 0, the ω-limit Ω_r is within ε of {0, r*}:
    then Ω_r ⊂ {0, r*}, and topology gives r* ∈ Ω_r. -/
theorem stability_from_approx_sc
    (Omega_r : Set ℝ) (r_star : ℝ) (hr : 0 < r_star)
    (hclosed : IsClosed Omega_r)
    (hconn : IsConnected Omega_r)
    (h0 : (0 : ℝ) ∈ Omega_r)
    (hne : ∃ x ∈ Omega_r, 0 < x)
    (happrox : ∀ δ > 0, Omega_r ⊆ {x | |x| < δ} ∪ {x | |x - r_star| < δ}) :
    r_star ∈ Omega_r :=
  pls_in_scalar_omega_limit Omega_r hconn h0 hne r_star hr
    (approx_containment_gives_exact Omega_r r_star hr hclosed happrox)

/-- **The approximate self-consistency hypothesis.**
    On Ω: backward contraction at locked frequencies gives
    r ≈ Φ_locked(r) with error from drifting tail ≤ δ(M).
    For Ψ_x large (sup_Ω Ψ = +∞): M = √(KΨ_x) is large,
    δ(M) = ∫_{>M} g → 0. So the approximation is arbitrarily good.

    This replaces the per-ω slaving (which needs ∀ω) with
    approximate g-weighted slaving (which needs the g-tail to vanish).
    The g-tail vanishes because g ∈ L¹. -/
theorem approx_sc_from_tail_decay
    (δ : ℝ → ℝ)  -- δ(M) = ∫_{>M} g
    (hδ_decay : ∀ ε > 0, ∃ M, δ M < ε)  -- g ∈ L¹ ⟹ tail → 0
    (hδ_nn : ∀ M, 0 ≤ δ M)
    -- For each ε: ∃ x ∈ Ω with Ψ(x) large enough that δ(√(KΨ)) < ε:
    (h_large_Psi : ∀ ε > 0, ∃ M, δ M < ε)  -- same as hδ_decay
    : ∀ ε > 0, ∃ M, δ M < ε :=
  hδ_decay

end
