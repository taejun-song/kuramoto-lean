/-
  Kuramoto Stability — PLS Continuity (GAP 2)
  =============================================
  Proves r*_n → r* as g_n → g (i.e., Φ_n → Φ uniformly).

  The self-consistency map Φ_g(r) = ∫ α*(ω,r) g(ω) dω has r* as an
  isolated fixed point. When Φ_n → Φ uniformly on [0,1], the gap condition
  forces the fixed points r*_n of Φ_n into any ε-neighborhood of r*.

  This fills the h_pls hypothesis of continuum_convergence_argument
  (PassageToLimit.lean).

  0 sorry.
-/

import KuramotoLean.PassageToLimit

open Real Filter Topology

noncomputable section

/-! ## Fixed-point continuity from gap condition + uniform convergence

Key idea: if |x - Φ(x)| ≥ m on the "gap region" (away from fixed points),
and |Φ_n(x) - Φ(x)| < m/2 uniformly, then Φ_n has no fixed point in the
gap region. So r*_n must be near r*. -/

theorem pls_continuity
    (Φ : ℕ → ℝ → ℝ) (Φ_lim : ℝ → ℝ)
    (r_star : ℝ) (r_star_n : ℕ → ℝ)
    (hr_pos : 0 < r_star) (hr_le : r_star ≤ 1)
    (h_fp_lim : Φ_lim r_star = r_star)
    (h_fp_n : ∀ n, Φ n (r_star_n n) = r_star_n n)
    (hr_n_nn : ∀ n, 0 ≤ r_star_n n)
    (hr_n_le : ∀ n, r_star_n n ≤ 1)
    (hΦ_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, 0 ≤ x → x ≤ 1 →
      |Φ n x - Φ_lim x| < ε)
    (h_gap : ∀ η > 0, η < r_star / 3 →
      ∃ m > 0, ∀ x, 0 ≤ x → x ≤ 1 →
        (η ≤ x ∧ x ≤ r_star - η) ∨ (r_star + η ≤ x) →
        m ≤ |x - Φ_lim x|)
    (hr_n_away : ∀ ε > 0, ∃ N, ∀ n ≥ N, ε ≤ r_star_n n) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |r_star_n n - r_star| < ε := by
  intro ε hε
  set η := min (ε / 2) (r_star / 4) with hη_def
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  have hη_lt : η < r_star / 3 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨m, hm_pos, hm_gap⟩ := h_gap η hη_pos hη_lt
  obtain ⟨N₁, hN₁⟩ := hΦ_unif (m / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hr_n_away η hη_pos
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  by_contra h_far
  push_neg at h_far
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hr_n_lb : η ≤ r_star_n n := hN₂ n hn₂
  have hr_n_in_gap : (η ≤ r_star_n n ∧ r_star_n n ≤ r_star - η) ∨
      (r_star + η ≤ r_star_n n) := by
    by_cases h_above : r_star + η ≤ r_star_n n
    · exact Or.inr h_above
    · push_neg at h_above
      left; exact ⟨hr_n_lb, by
        by_contra h_close; push_neg at h_close
        have h1 : r_star - η < r_star_n n := h_close
        have h2 : r_star_n n < r_star + η := h_above
        have h3 : |r_star_n n - r_star| < η := by rw [abs_lt]; constructor <;> linarith
        have h4 : η ≤ ε / 2 := min_le_left _ _
        linarith [h_far]⟩
  have h_gap_bound := hm_gap (r_star_n n) (hr_n_nn n) (hr_n_le n) hr_n_in_gap
  have h_approx := hN₁ n hn₁ (r_star_n n) (hr_n_nn n) (hr_n_le n)
  have h_fp := h_fp_n n
  have : |r_star_n n - Φ_lim (r_star_n n)| =
      |Φ n (r_star_n n) - Φ_lim (r_star_n n)| := by rw [h_fp]
  linarith

/-! ## Corollary: pls_error → 0

Wraps pls_continuity into the form needed by continuum_convergence_argument. -/

theorem pls_error_vanishes
    (Φ : ℕ → ℝ → ℝ) (Φ_lim : ℝ → ℝ)
    (r_star : ℝ) (r_star_n : ℕ → ℝ)
    (hr_pos : 0 < r_star) (hr_le : r_star ≤ 1)
    (h_fp_lim : Φ_lim r_star = r_star)
    (h_fp_n : ∀ n, Φ n (r_star_n n) = r_star_n n)
    (hr_n_nn : ∀ n, 0 ≤ r_star_n n)
    (hr_n_le : ∀ n, r_star_n n ≤ 1)
    (hΦ_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, 0 ≤ x → x ≤ 1 →
      |Φ n x - Φ_lim x| < ε)
    (h_gap : ∀ η > 0, η < r_star / 3 →
      ∃ m > 0, ∀ x, 0 ≤ x → x ≤ 1 →
        (η ≤ x ∧ x ≤ r_star - η) ∨ (r_star + η ≤ x) →
        m ≤ |x - Φ_lim x|)
    (hr_n_away : ∀ ε > 0, ∃ N, ∀ n ≥ N, ε ≤ r_star_n n) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (fun k => |r_star_n k - r_star|) n < ε :=
  pls_continuity Φ Φ_lim r_star r_star_n hr_pos hr_le h_fp_lim h_fp_n
    hr_n_nn hr_n_le hΦ_unif h_gap hr_n_away

end
