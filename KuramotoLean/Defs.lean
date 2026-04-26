/-
  Kuramoto Stability Project — Phase 0: Definitions
  ==================================================
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Complex.Basic

open Complex MeasureTheory Real

noncomputable section

/-! ## The unit disk -/

/-- The open unit disk in ℂ, defined via normSq. -/
def UnitDisk : Set ℂ := {z : ℂ | Complex.normSq z < 1}

/-- 1 - ‖z‖² > 0 for z in the unit disk. -/
lemma UnitDisk.one_sub_normSq_pos {z : ℂ} (hz : z ∈ UnitDisk) :
    0 < 1 - Complex.normSq z :=
  sub_pos.mpr hz

/-! ## Frequency distribution -/

/-- A frequency distribution: a nonneg function on ℝ. -/
structure FreqDist where
  g : ℝ → ℝ
  g_nonneg : ∀ ω, 0 ≤ g ω

/-! ## Ott–Antonsen state -/

/-- An OA state: a function ℝ → ℂ with values in the unit disk. -/
structure OAState where
  α : ℝ → ℂ
  mem_disk : ∀ ω, α ω ∈ UnitDisk

/-! ## Mean field -/

/-- The complex mean field r = ∫ α(ω) g(ω) dω. -/
def meanField (gd : FreqDist) (α : ℝ → ℂ) : ℂ :=
  ∫ ω, (gd.g ω : ℂ) * α ω

/-! ## OA velocity field -/

/-- The OA velocity: ∂ₜα = -iωα + (K/2)(r - r̄ α²) -/
def oaVelocity (K : ℝ) (ω : ℝ) (α r : ℂ) : ℂ :=
  -Complex.I * (ω : ℂ) * α + ((K : ℂ) / 2) * (r - starRingEnd ℂ r * α ^ 2)

/-! ## Lyapunov kernel -/

/-- The log-ratio kernel ℋ(α; α*) = log((1 - |α|²) / |α - α*|²). -/
def lyapunovKernel (α α_star : ℂ) : ℝ :=
  Real.log ((1 - Complex.normSq α) / Complex.normSq (α - α_star))

/-! ## Lyapunov functional -/

/-- Φ_OA[α] = ∫ g(ω) ℋ(α(ω); α*_K(ω)) dω. -/
def PhiOA (gd : FreqDist) (α α_star : ℝ → ℂ) : ℝ :=
  ∫ ω, gd.g ω * lyapunovKernel (α ω) (α_star ω)

/-! ## Critical coupling -/

/-- K_c = 2 / (π g(0)). -/
def criticalCoupling (gd : FreqDist) : ℝ :=
  2 / (Real.pi * gd.g 0)

/-! ## The OA flow (axiomatised) -/

/-- An OA flow: time-dependent state satisfying the OA ODE. -/
structure OAFlow (gd : FreqDist) (K : ℝ) where
  α : ℝ → ℝ → ℂ  -- α t ω
  mem_disk : ∀ t ω, α t ω ∈ UnitDisk
  is_ode : ∀ t ω, HasDerivAt (α · ω)
    (oaVelocity K ω (α t ω) (meanField gd (α t))) t

/-! ## Main theorem statement -/

-- lyapunov_decrease removed: obsolete (old approach).
-- The stability proof now uses WindowedApproximation.lean.

end
