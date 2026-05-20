/-
  Interior Equilibrium Exclusion for Complex OA
  ==============================================
  Any self-consistent interior equilibrium of the complex OA has η = 0.

  If every oscillator satisfies |z*(ω)| < 1 (strictly inside the disk)
  and z* is a fixed point of the OA flow with self-consistent η = ∫z̄*g dμ,
  then η = 0. Non-trivial synchronization (η ≠ 0) requires oscillators
  on the unit circle boundary |z| = 1 (frequency locking).

  Together with ComplexOALockedEquil.lean (locked oscillators live on |z|=1),
  this gives a complete dichotomy: the OA interior is the incoherent regime.

  3 theorems, 0 sorry.
-/

import KuramotoLean.ComplexOAEnergy

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- At an interior equilibrium, Re(η·z*(ω)) = 0 for each ω.
    From d|z|²/dt = K·Re(η·z)·(1-|z|²): at equilibrium (RHS=0)
    with K > 0 and |z| < 1, the factor Re(η·z) must vanish. -/
theorem re_eta_z_zero_at_interior_equil
    (z_star : Ω → ℂ) (ω_freq : Ω → ℝ) (K : ℝ) (η : ℂ) (hK : 0 < K)
    (hz_equil : ∀ ω, complexOaRHS (ω_freq ω) K η (z_star ω) = 0)
    (hz_disk : ∀ ω, Complex.normSq (z_star ω) < 1) :
    ∀ ω, (η * z_star ω).re = 0 := by
  intro ω
  have h := complexOa_normSq_deriv (ω_freq ω) K η (z_star ω)
  rw [hz_equil ω, mul_zero, Complex.zero_re, mul_zero] at h
  have h1m : (1 : ℝ) - Complex.normSq (z_star ω) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hz_disk ω))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right h1m)).resolve_left hK.ne'

/-- **Interior equilibrium exclusion.** If z* is a self-consistent interior
    equilibrium (all |z*(ω)| < 1), then |η|² = 0.
    Proof: Re(η·z*) = 0 pointwise ⟹ |η|² = ∫Re(η·z*)g dμ = 0. -/
theorem eta_vanishes_at_interior_equilibrium
    (z_star : Ω → ℂ) (g : Ω → ℝ) (ω_freq : Ω → ℝ) (K : ℝ) (η : ℂ) (hK : 0 < K)
    (hη_def : η = ∫ ω, starRingEnd ℂ (z_star ω) * (g ω : ℂ) ∂μ)
    (hz_equil : ∀ ω, complexOaRHS (ω_freq ω) K η (z_star ω) = 0)
    (hz_disk : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_int : Integrable (fun ω => (g ω : ℂ) * z_star ω) μ)
    (hre_int : Integrable (fun ω => (η * z_star ω).re * g ω) μ) :
    Complex.normSq η = 0 := by
  have h_re := re_eta_z_zero_at_interior_equil z_star ω_freq K η hK hz_equil hz_disk
  rw [← complex_eta_integral_identity z_star g η hη_def hz_int hre_int,
    show (fun ω => (η * z_star ω).re * g ω) = fun _ => 0 from
      funext fun ω => by rw [h_re ω, zero_mul],
    integral_zero]

/-- η = 0 at any self-consistent interior equilibrium. -/
theorem eta_eq_zero_at_interior_equilibrium
    (z_star : Ω → ℂ) (g : Ω → ℝ) (ω_freq : Ω → ℝ) (K : ℝ) (η : ℂ) (hK : 0 < K)
    (hη_def : η = ∫ ω, starRingEnd ℂ (z_star ω) * (g ω : ℂ) ∂μ)
    (hz_equil : ∀ ω, complexOaRHS (ω_freq ω) K η (z_star ω) = 0)
    (hz_disk : ∀ ω, Complex.normSq (z_star ω) < 1)
    (hz_int : Integrable (fun ω => (g ω : ℂ) * z_star ω) μ)
    (hre_int : Integrable (fun ω => (η * z_star ω).re * g ω) μ) :
    η = 0 :=
  Complex.normSq_eq_zero.mp
    (eta_vanishes_at_interior_equilibrium z_star g ω_freq K η hK hη_def
      hz_equil hz_disk hz_int hre_int)

end
