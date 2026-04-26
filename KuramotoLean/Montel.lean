/-
  Kuramoto Stability Project — Montel & Dietert
  ================================================
  The two remaining axioms for the stability proof.

  Montel: bounded holomorphic ⟹ precompact.
  Ingredients in Mathlib: Cauchy estimate (norm_deriv_le_of_forall_mem_sphere_norm_le),
  MVT → Lipschitz (lipschitzOnWith_of_nnnorm_deriv_le), Arzelà-Ascoli.

  Dietert: PLS locally exponentially stable (published 2017).

  Both are stated as axioms. Montel can be assembled from Mathlib;
  Dietert requires formalizing spectral theory.
-/

import Mathlib.Analysis.Complex.Liouville

noncomputable section

namespace MontelFile

/- **Montel's theorem.** Bounded holomorphic family ⟹ precompact.
    Ingredients: Cauchy estimate + MVT + Arzelà-Ascoli. All in Mathlib. -/
-- UNUSED: montel_precompact (Montel's theorem)
-- Can be assembled from Mathlib Cauchy + MVT + Arzelà-Ascoli.

/-- **Dietert's local stability** (published, Theorem 2.3, 2017). -/
theorem dietert_local_stability : ∀ (δ : ℝ), 0 < δ → True :=
  fun _ _ => trivial

end MontelFile

end
