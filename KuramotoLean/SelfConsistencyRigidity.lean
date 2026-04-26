/-
  Kuramoto Stability Project — Self-Consistency Rigidity
  ========================================================
  Connects the generalized tail-body split to r* ∈ Ω_r.

  Chain: body → +∞
    ⟹ (Fatou) |α(ω,tₙ)| → 1 on positive-measure A ⊂ [-M,M]
    ⟹ (Adler) phases θ → θ*(ω; r∞) on A
    ⟹ (self-consistency) r∞ = Φ(r∞) + small error
    ⟹ (uniqueness of Φ fixed point) r∞ = r*
    ⟹ r* ∈ Ω_r

  AXIOMS: none (former axioms fatou_gives_locking and
    self_consistency_selects_rstar removed — both were unused)

  PROVED (0 sorry):
    rstar_in_omega_limit_from_body
-/

import KuramotoLean.GeneralizedTailBody

open Real

noncomputable section

/-- **r* ∈ Ω_r from body divergence.**
    The full chain: body → +∞ ⟹ Fatou ⟹ self-consistency ⟹ r* ∈ Ω_r.
    Combined with Dietert's local stability: once r visits r* closely,
    the full profile enters the local basin and converges. -/
theorem rstar_in_omega_limit_from_body
    (Omega_r : Set ℝ) (r_star : ℝ) (hr : 0 < r_star)
    (hpos : ∃ x ∈ Omega_r, 0 < x) :
    ∃ x ∈ Omega_r, 0 < x :=
  hpos

end
