/-
  Kuramoto Stability — N-Pole to Continuum Bridge
  ================================================

  Constructs concrete ContinuumGlobalStability structure instances from
  n-pole ODE data, instantiating both abstract proof paths.

  PATH B (discrete, pointwise): NPoleStabilityData → ContinuumPointwiseData
    V(m) = l2Distance(c, α(m), α*) is non-negative, non-increasing (L²
    Lyapunov), and → 0 (Barbalat). Direct field-for-field construction.

  PATH A (continuous, coercive): NPoleStabilityData → CoerciveConvergenceData
    Step-function lift: stepLift V t = V(Int.toNat ⌊t⌋).
    · Antitone:  Int.floor_le_floor + Int.toNat_le_toNat + discrete antitone
    · Drops:     use M = ⌈T⌉ (Nat.le_ceil gives T ≤ ⌈T⌉ ≤ m)

  0 sorry.
-/

import KuramotoLean.ContinuumGlobalStability
import KuramotoLean.NPoleGlobalStability

open Filter Topology Real Int

noncomputable section

variable {n : ℕ}

/-! ## Path B: NPoleStabilityData → ContinuumPointwiseData -/

/-- Construct ContinuumPointwiseData from NPoleStabilityData.
    The weighted L² distance l2Distance(c, α(m), α*) is:
    · non-negative:    l2Distance_nonneg
    · non-increasing:  NPoleStabilityData.hV_mono
    · converging to 0: npole_stability_l2 (Barbalat)
    This instantiates Path B of ContinuumGlobalStability.lean. -/
def NPoleStabilityData.toContinuumPointwiseData (D : NPoleStabilityData n) :
    ContinuumPointwiseData where
  V       := fun m => l2Distance D.c (D.α m) D.α_star
  hV_nn   := fun m => l2Distance_nonneg D.c (D.α m) D.α_star
    (fun k => le_of_lt (D.hc k))
  hV_anti := D.hV_mono
  hV_zero := npole_stability_l2 D

/-- N-pole L² convergence via ContinuumGlobalStability Path B.
    l2Distance(c, α(m), α*) → 0 as m → ∞. -/
theorem npole_convergence_via_path_b (D : NPoleStabilityData n) :
    Tendsto (fun m => l2Distance D.c (D.α m) D.α_star) atTop (nhds 0) :=
  pointwise_convergence D.toContinuumPointwiseData

/-! ## Discrete antitone helper -/

private theorem nat_antitone_succ {V : ℕ → ℝ} (hV : ∀ m, V (m + 1) ≤ V m) :
    ∀ {a b : ℕ}, a ≤ b → V b ≤ V a := by
  intro a b hab
  induction hab with
  | refl => exact le_refl _
  | @step k _ ih => exact le_trans (hV k) ih

/-! ## Step-function lift: discrete → continuous -/

/-- Lift a discrete sequence to a continuous step function via ⌊·⌋:
    stepLift V t = V(Int.toNat ⌊t⌋). -/
def stepLift (V : ℕ → ℝ) : ℝ → ℝ := fun t => V (Int.toNat ⌊t⌋)

theorem stepLift_nn (V : ℕ → ℝ) (hV : ∀ m, 0 ≤ V m) : ∀ t, 0 ≤ stepLift V t :=
  fun _ => hV _

/-- stepLift V is antitone: s ≤ t → ⌊s⌋ ≤ ⌊t⌋ → V(⌊t⌋) ≤ V(⌊s⌋). -/
theorem stepLift_antitone (V : ℕ → ℝ) (hV : ∀ m, V (m + 1) ≤ V m) :
    Antitone (stepLift V) := by
  intro s t hst
  simp only [stepLift]
  exact nat_antitone_succ hV (Int.toNat_le_toNat (Int.floor_le_floor hst))

/-- stepLift V at a natural number equals V m. -/
private theorem stepLift_at_nat (V : ℕ → ℝ) (m : ℕ) :
    stepLift V (m : ℝ) = V m := by
  simp [stepLift]

/-- stepLift V at m+1 equals V(m+1). -/
private theorem stepLift_at_nat_add_one (V : ℕ → ℝ) (m : ℕ) :
    stepLift V ((m : ℝ) + 1) = V (m + 1) := by
  simp only [stepLift]
  congr 1
  have : ⌊(m : ℝ) + 1⌋ = (m : ℤ) + 1 := by
    rw [Int.floor_add_one (m : ℝ), Int.floor_natCast]
  simp [this]

/-- Discrete coercive drops lift to continuous drops with Δ = 1.
    Uses M = ⌈T⌉ so that m ≥ ⌈T⌉ ≥ T. -/
theorem stepLift_drops (V : ℕ → ℝ) (q : ℝ)
    (hdrops : ∀ M : ℕ, ∃ m, M ≤ m ∧ V (m + 1) ≤ q * V m)
    (T : ℝ) : ∃ t : ℝ, T ≤ t ∧ stepLift V (t + 1) ≤ q * stepLift V t := by
  obtain ⟨m, hm, hdrop⟩ := hdrops (Nat.ceil T)
  refine ⟨(m : ℝ), ?_, ?_⟩
  · calc T ≤ ↑(Nat.ceil T)    := Nat.le_ceil T
      _ ≤ (m : ℝ) := by exact_mod_cast hm
  · rw [stepLift_at_nat_add_one, stepLift_at_nat]
    exact hdrop

/-! ## Path A: NPoleStabilityData → CoerciveConvergenceData -/

/-- Construct CoerciveConvergenceData from NPoleStabilityData via step lift.
    This instantiates Path A of ContinuumGlobalStability.lean. -/
def NPoleStabilityData.toCoerciveConvergenceData (D : NPoleStabilityData n) :
    CoerciveConvergenceData where
  V       := stepLift (fun m => l2Distance D.c (D.α m) D.α_star)
  hV_nn   := stepLift_nn _ (fun m => l2Distance_nonneg D.c (D.α m) D.α_star
    (fun k => le_of_lt (D.hc k)))
  hV_anti := stepLift_antitone _ D.hV_mono
  q       := D.q
  hq0     := D.hq0
  hq1     := D.hq1
  Δ       := 1
  hΔ      := one_pos
  hdrops  := stepLift_drops _ D.q D.hpersist_drop

/-- N-pole convergence via ContinuumGlobalStability Path A.
    Step-lifted L² distance converges to 0 via coercive Barbalat. -/
theorem npole_convergence_via_path_a (D : NPoleStabilityData n) :
    Tendsto (stepLift (fun m => l2Distance D.c (D.α m) D.α_star)) atTop (nhds 0) :=
  coercive_convergence D.toCoerciveConvergenceData

end
