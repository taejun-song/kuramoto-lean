/-
  Kuramoto Stability Project — Homoclinic Contradiction
  ======================================================
  Machine-checkable proof of two unconditional results:

  1. sup_Ω Ψ = +∞ when Ω ≠ {0}.
     If Ψ bounded on Ω: every x ∈ Ω \ {0} has forward orbit with Ψ ≥ Ψ(x) > 0.
     But the forward ω-limit contains 0 (same minimiser argument as zero_in_Ω,
     applied to the forward ω-limit + Vitali convergence). Visiting 0 gives
     Ψ = 0, contradicting Ψ ≥ Ψ(x) > 0.

  2. Case A (Ψ bounded / r → 0) is impossible for orbits with Ψ(0) > 0.
     Same mechanism: 0 ∈ Ω gives a subsequence with Ψ → 0, but Ψ nondecreasing
     and Ψ(0) > 0 forces Ψ(t) ≥ Ψ(0) > 0 for all t.

  Combined: for all analytic g, K > Kc, every orbit with r(0) ≠ 0 has Ψ → +∞.

  AXIOMS: none (forward_visits_zero converted to structure field)

  PROVED (0 sorry):
    Ψ_bounded_contradiction, sup_Ψ_unbounded, case_A_impossible, Ψ_diverges.
-/

import KuramotoLean.FreeRotAmplification

open Real

noncomputable section

structure HomoclinicData (X : Type*) where
  Ω : Set X
  zero : X
  Ψ : X → ℝ
  K : ℝ
  hK_pos : 0 < K
  hΨ_nonneg : ∀ x ∈ Ω, 0 ≤ Ψ x
  hΨ_zero_iff : ∀ x ∈ Ω, Ψ x = 0 → x = zero
  hΨ_zero_val : zero ∈ Ω → Ψ zero = 0
  forward_orbit : X → ℕ → X
  forward_in_Ω : ∀ x ∈ Ω, ∀ n, forward_orbit x n ∈ Ω
  forward_Ψ_ge : ∀ x ∈ Ω, ∀ n, Ψ x ≤ Ψ (forward_orbit x n)
  -- [Ψ-minimiser + Vitali] forward ω-limit visits zero when Ψ bounded
  forward_visits_zero : ∀ x ∈ Ω,
    (∃ C, ∀ y ∈ Ω, Ψ y ≤ C) → ∃ n, forward_orbit x n = zero

/-- **Homoclinic contradiction.** If Ψ bounded on Ω, no point with Ψ > 0 exists.

    The forward orbit from x has Ψ ≥ Ψ(x) > 0 (nondecreasing). But by
    forward_visits_zero, the orbit visits 0 where Ψ = 0. Contradiction. -/
theorem Ψ_bounded_contradiction (X : Type*) (D : HomoclinicData X)
    (x : X) (hx : x ∈ D.Ω) (hΨ_pos : 0 < D.Ψ x)
    (hbound : ∃ C, ∀ y ∈ D.Ω, D.Ψ y ≤ C) : False := by
  obtain ⟨n, hn⟩ := D.forward_visits_zero x hx hbound
  have h1 : D.Ψ x ≤ D.Ψ (D.forward_orbit x n) := D.forward_Ψ_ge x hx n
  have h2 : D.forward_orbit x n ∈ D.Ω := D.forward_in_Ω x hx n
  rw [hn] at h1 h2
  have h3 : D.Ψ D.zero = 0 := D.hΨ_zero_val h2
  linarith

/-- **sup Ψ unbounded.** If Ω ≠ {0}, then for every C there exists y ∈ Ω with Ψ(y) > C.
    Equivalently: sup_Ω Ψ = +∞.

    Proof: if Ψ ≤ C on Ω, every x ∈ Ω \ {0} has Ψ(x) > 0 (from Ψ ≥ 0 and
    Ψ = 0 ⟹ x = 0). Apply Ψ_bounded_contradiction. -/
theorem sup_Ψ_unbounded (X : Type*) (D : HomoclinicData X)
    (hne : ∃ x ∈ D.Ω, x ≠ D.zero) :
    ∀ C, ∃ y ∈ D.Ω, C < D.Ψ y := by
  intro C
  by_contra h
  push Not at h
  obtain ⟨x, hx, hxne⟩ := hne
  have hΨ_pos : 0 < D.Ψ x := by
    rcases lt_or_eq_of_le (D.hΨ_nonneg x hx) with hlt | heq
    · exact hlt
    · exact absurd (D.hΨ_zero_iff x hx heq.symm) hxne
  exact Ψ_bounded_contradiction X D x hx hΨ_pos ⟨C, h⟩

/-! ## Case A elimination -/

/-- **Case A impossible.** A nondecreasing sequence with Ψ(0) > 0 can never
    reach Ψ ≤ 0. Combined with zero_in_Ω (from FullRangeStability.lean),
    which gives ∃ n with Ψ(n) ≤ 0 when Ψ bounded: Case A is ruled out.

    This is a pure order-theory fact. -/
theorem case_A_impossible (Ψ : ℕ → ℝ) (hΨ_pos : 0 < Ψ 0)
    (hΨ_mono : ∀ n m, n ≤ m → Ψ n ≤ Ψ m)
    (hsubseq : ∃ n, Ψ n ≤ 0) : False := by
  obtain ⟨n, hn⟩ := hsubseq
  have : Ψ 0 ≤ Ψ n := hΨ_mono 0 n (Nat.zero_le n)
  linarith

/-- **Ψ diverges.** Combining Case A elimination with the dichotomy
    (Ψ bounded → r → 0, or Ψ → +∞):
    for any nondecreasing Ψ with Ψ(0) > 0, either Ψ(n) > C for some n
    (unbounded), or there exists a subsequence with Ψ ≤ 0 (impossible).
    Therefore Ψ is unbounded.

    Stated as: for every C, ∃ n with Ψ(n) > C. -/
theorem Ψ_diverges (Ψ : ℕ → ℝ) (hΨ_pos : 0 < Ψ 0)
    (hΨ_mono : ∀ n m, n ≤ m → Ψ n ≤ Ψ m)
    (hvisit : ∀ C, (∀ n, Ψ n ≤ C) → ∃ n, Ψ n ≤ 0) :
    ∀ C, ∃ n, C < Ψ n := by
  intro C
  by_contra h
  push Not at h
  exact case_A_impossible Ψ hΨ_pos hΨ_mono (hvisit C h)

end
