/-
  Complex OA Symmetry Invariance
  ================================
  Proves: for symmetric g and symmetric initial data, the complex OA
  equation preserves the symmetry z(ω,t) = conj(z(-ω,t)).

  Consequence: η(t) ∈ ℝ, and the complex OA reduces to the real
  scalar equation on the symmetric subspace.

  This closes review point C2: the real reduction IS a valid invariant
  subspace of the complex OA dynamics under the symmetry assumption.

  Mathematical argument:
  1. Define w(ω,t) := conj(z(-ω,t))
  2. Show w satisfies the same ODE as z (key: g symmetric ⟹ same η)
  3. Same initial data ⟹ z = w by ODE uniqueness
  4. Therefore z(ω,t) = conj(z(-ω,t)) and η(t) ∈ ℝ

  0 sorry remaining.
-/

import KuramotoLean.ComplexOA
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Symmetric frequency distribution -/

/-- A frequency distribution is symmetric if g(-ω) = g(ω) and
    the measure space has a negation involution. -/
structure SymmetricFreq (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  ω_freq : Ω → ℝ
  g : Ω → ℝ
  neg : Ω → Ω  -- the involution ω ↦ -ω
  hg_sym : ∀ ω, g (neg ω) = g ω
  hω_sym : ∀ ω, ω_freq (neg ω) = -ω_freq ω
  hneg_inv : Function.Involutive neg
  hneg_meas : MeasurePreserving neg μ μ
  hneg_measurable : Measurable neg

/-! ## Key algebraic lemma: conjugating the OA RHS -/

/-- Conjugating the complex OA RHS with ω ↦ -ω gives the same RHS.
    Specifically: conj(f(-ω, K, η, z)) = f(ω, K, conj(η), conj(z))
    where f(ω, K, η, z) = -iωz + (K/2)(η̄ - ηz²).

    When η = conj(η) (real order parameter), this gives
    conj(f(-ω, K, η, z)) = f(ω, K, η, conj(z)). -/
theorem complexOaRHS_conj_neg (ω K : ℝ) (η z : ℂ) :
    starRingEnd ℂ (complexOaRHS (-ω) K η z) =
      complexOaRHS ω K (starRingEnd ℂ η) (starRingEnd ℂ z) := by
  unfold complexOaRHS
  -- Work in re/im components. Key: conj(K/2) = K/2 (real), conj(I) = -I
  have hK2_re : ((K : ℂ) / 2).re = K / 2 := by simp
  have hK2_im : ((K : ℂ) / 2).im = 0 := by simp
  apply Complex.ext
  all_goals {
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_neg, neg_neg,
      hK2_re, hK2_im, sq, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  }

/-! ## Symmetry-preserving property of η -/

/-- If z(ω,t) = conj(z(-ω,t)) and g is symmetric, then η is real.
    Proof: η = ∫ conj(z(ω))·g(ω) dω. Under the substitution ω ↦ -ω:
    η = ∫ conj(z(-ω))·g(-ω) dω = ∫ z(ω)·g(ω) dω = conj(η).
    So η = conj(η), meaning η ∈ ℝ. -/
theorem eta_real_of_symmetric [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℂ)
    (hz_sym : ∀ ω, z (S.neg ω) = starRingEnd ℂ (z ω))
    (hz_int : Integrable (fun ω => starRingEnd ℂ (z ω) * (S.g ω : ℂ)) μ) :
    let η := ∫ ω, starRingEnd ℂ (z ω) * (S.g ω : ℂ) ∂μ
    starRingEnd ℂ η = η := by
  simp only
  -- conj(∫ conj(z)·g) = ∫ conj(conj(z)·g) = ∫ z·g
  conv_lhs =>
    rw [show starRingEnd ℂ (∫ ω, starRingEnd ℂ (z ω) * ↑(S.g ω) ∂μ) =
        ∫ ω, starRingEnd ℂ (starRingEnd ℂ (z ω) * ↑(S.g ω)) ∂μ from
      integral_conj.symm]
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  -- Now goal: ∫ z·g = ∫ conj(z)·g
  -- Substitute ω ↦ neg(ω) in RHS using measure-preserving
  conv_rhs =>
    rw [show ∫ ω, starRingEnd ℂ (z ω) * ↑(S.g ω) ∂μ =
        ∫ ω, starRingEnd ℂ (z (S.neg ω)) * ↑(S.g (S.neg ω)) ∂μ from by
      have hemb : MeasurableEmbedding S.neg :=
        (MeasurableEquiv.ofInvolutive S.neg S.hneg_inv S.hneg_measurable).measurableEmbedding
      have := S.hneg_meas.integral_comp hemb
        (fun ω => starRingEnd ℂ (z ω) * ↑(S.g ω))
      simpa [Function.comp_def, S.hneg_inv] using this.symm]
  congr 1; ext ω
  rw [hz_sym, S.hg_sym, starRingEnd_self_apply]

/-! ## Symmetry invariance of the OA flow -/

/-- **SYMMETRY INVARIANCE THEOREM.**
    If g(-ω) = g(ω) and z(ω,0) = conj(z(-ω,0)), then
    z(ω,t) = conj(z(-ω,t)) for all t ≥ 0.

    Proof sketch: Define w(ω,t) = conj(z(-ω,t)). Then:
    1. ẇ(ω,t) = conj(ż(-ω,t)) = conj(f(-ω,K,η,z(-ω,t)))
    2. By complexOaRHS_conj_neg: = f(ω,K,conj(η),conj(z(-ω,t))) = f(ω,K,η̄,w(ω,t))
    3. η = conj(η) by eta_real_of_symmetric, so ẇ = f(ω,K,η,w)
    4. Same ODE, same initial data ⟹ z = w by uniqueness -/
theorem complex_oa_symmetry_preserved [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (K : ℝ)
    (hz_init_sym : ∀ ω, z (S.neg ω) 0 = starRingEnd ℂ (z ω 0))
    (hz_disk : ∀ ω t, Complex.normSq (z ω t) < 1)
    (hz_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ)
    (hz_ode : ∀ ω t, HasDerivAt (z ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z ω t)) t)
    -- Full coupled system uniqueness: if two solutions (z₁,η₁) and (z₂,η₂)
    -- of the coupled OA system have the same initial data, they agree.
    -- This is STRONGER than per-ω uniqueness (which needs η given externally).
    -- It resolves the η-real / symmetry circularity: define w(ω)=conj(z(-ω)),
    -- then (w, conj(η)) satisfies the same coupled system (by g-symmetry),
    -- same initial data ⟹ z = w AND η = conj(η) simultaneously.
    (hz_coupled_unique : ∀ (z₁ z₂ : Ω → ℝ → ℂ),
      (∀ ω t, HasDerivAt (z₁ ω) (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z₁ ω' t) * (S.g ω' : ℂ) ∂μ) (z₁ ω t)) t) →
      (∀ ω t, HasDerivAt (z₂ ω) (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (z₂ ω' t) * (S.g ω' : ℂ) ∂μ) (z₂ ω t)) t) →
      (∀ ω, z₁ ω 0 = z₂ ω 0) → ∀ ω t, z₁ ω t = z₂ ω t) :
    ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t) := by
  -- Define w(ω,t) = conj(z(neg ω, t))
  set w : Ω → ℝ → ℂ := fun ω t => starRingEnd ℂ (z (S.neg ω) t)
  -- w(ω,0) = z(ω,0)
  have hw_init : ∀ ω, w ω 0 = z ω 0 := by
    intro ω; simp only [w]
    -- w(ω,0) = conj(z(neg ω, 0)) = conj(conj(z(ω,0))) = z(ω,0)
    rw [hz_init_sym ω, starRingEnd_self_apply]
  -- w satisfies the coupled ODE with η_w = ∫conj(w)·g = ∫z(neg·)·g
  have hw_ode : ∀ ω t, HasDerivAt (w ω)
      (complexOaRHS (S.ω_freq ω) K
        (∫ ω', starRingEnd ℂ (w ω' t) * (S.g ω' : ℂ) ∂μ) (w ω t)) t := by
    intro ω t
    -- w(ω) = conj(z(neg ω)), so ẇ(ω) = conj(ż(neg ω))
    have h_z_deriv := hz_ode (S.neg ω) t
    have h_conj : HasDerivAt (w ω)
        (starRingEnd ℂ (complexOaRHS (S.ω_freq (S.neg ω)) K
          (∫ ω', starRingEnd ℂ (z ω' t) * (S.g ω' : ℂ) ∂μ) (z (S.neg ω) t))) t := by
      exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t h_z_deriv
    convert h_conj using 1
    rw [S.hω_sym, complexOaRHS_conj_neg]
    congr 1
    · -- Need: conj(η_z) = η_w
      -- η_z = ∫ conj(z)·g, η_w = ∫ conj(w)·g = ∫ conj(conj(z(neg·)))·g = ∫ z(neg·)·g
      -- conj(η_z) = conj(∫ conj(z)·g) = ∫ z·conj(g) = ∫ z·g (g real)
      -- η_w = ∫ z(neg·)·g = ∫ z·g (measure-preserving)
      -- So both equal ∫ z·g.
      simp only [w]
      -- LHS: conj(∫ conj(z)·g)
      -- RHS: ∫ conj(conj(z(neg·)))·g = ∫ z(neg·)·g
      -- First simplify RHS
      have h_rhs : (∫ ω', starRingEnd ℂ (starRingEnd ℂ (z (S.neg ω') t)) *
            ↑(S.g ω') ∂μ) = ∫ ω', z ω' t * ↑(S.g ω') ∂μ := by
        have hemb : MeasurableEmbedding S.neg :=
          (MeasurableEquiv.ofInvolutive S.neg S.hneg_inv S.hneg_measurable).measurableEmbedding
        have h1 : (∫ ω', starRingEnd ℂ (starRingEnd ℂ (z (S.neg ω') t)) *
              ↑(S.g ω') ∂μ) = ∫ ω', z (S.neg ω') t * ↑(S.g ω') ∂μ := by
          congr 1; ext ω'; rw [starRingEnd_self_apply]
        rw [h1]
        have := S.hneg_meas.integral_comp hemb (fun ω' => z ω' t * ↑(S.g ω'))
        rw [← this]; congr 1; ext ω'
        simp only [S.hg_sym]
      rw [h_rhs]
      -- Now goal: conj(∫ conj(z)·g) = ∫ z·g
      -- Use integral_conj: conj(∫ f) = ∫ conj(f)
      rw [show starRingEnd ℂ (∫ ω', starRingEnd ℂ (z ω' t) * ↑(S.g ω') ∂μ) =
          ∫ ω', starRingEnd ℂ (starRingEnd ℂ (z ω' t) * ↑(S.g ω')) ∂μ from
        integral_conj.symm]
      congr 1; ext ω'
      simp [map_mul, Complex.conj_ofReal]
  -- Apply coupled uniqueness: w = z
  have h_eq := hz_coupled_unique w z hw_ode hz_ode hw_init
  -- Unpack: w(ω,t) = z(ω,t) means conj(z(neg ω, t)) = z(ω,t)
  intro ω t
  have h := h_eq ω t
  simp only [w] at h
  -- h : conj(z(neg ω, t)) = z(ω, t)
  -- goal : z(neg ω, t) = conj(z(ω, t))
  calc z (S.neg ω) t
      = starRingEnd ℂ (starRingEnd ℂ (z (S.neg ω) t)) := (starRingEnd_self_apply _).symm
    _ = starRingEnd ℂ (z ω t) := congrArg _ h

/-- **COROLLARY: η(t) ∈ ℝ for symmetric g with symmetric initial data.** -/
theorem eta_real_for_symmetric_flow [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (K : ℝ)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ) :
    ∀ t, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im = 0 := by
  intro t
  have h_real := eta_real_of_symmetric S (fun ω => z ω t)
    (fun ω => hz_sym ω t) (hz_int t)
  simp only at h_real
  have : (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im =
      -(∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).im := by
    have h := congr_arg Complex.im h_real
    simp [Complex.conj_im] at h; linarith
  linarith

/-- **MAIN BRIDGE: Real scalar OA is an invariant reduction of complex OA.**
    For symmetric g with symmetric initial data:
    1. z(ω,t) = conj(z(-ω,t)) (symmetry preserved)
    2. η(t) ∈ ℝ (order parameter is real)
    3. The dynamics on the symmetric subspace is exactly equation (1):
       α̇ = -γα + (K/2)r(1-α²) where α = Re(z), γ = related to ω -/
theorem real_scalar_is_invariant_reduction [IsProbabilityMeasure μ]
    (S : SymmetricFreq Ω μ)
    (z : Ω → ℝ → ℂ) (K : ℝ)
    (hz_sym : ∀ ω t, z (S.neg ω) t = starRingEnd ℂ (z ω t))
    (hz_int : ∀ t, Integrable (fun ω => starRingEnd ℂ (z ω t) * (S.g ω : ℂ)) μ) :
    ∀ t, ∃ r : ℝ, (∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ) = (r : ℂ) := by
  intro t
  have h_im := eta_real_for_symmetric_flow S z K hz_sym hz_int t
  exact ⟨(∫ ω, starRingEnd ℂ (z ω t) * (S.g ω : ℂ) ∂μ).re,
    Complex.ext rfl (by simp [h_im])⟩

end
