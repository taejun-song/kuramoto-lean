/-
  Body LaSalle Bridge: Connecting BodyLeibnizProof to BodyLaSalleConvergence
  ==========================================================================
  This file bridges the gap between:
  1. `body_leibniz_hasDerivAt` (BodyLeibnizProof.lean): proves HasDerivAt for V_body(M)
     with derivative = ∫_{γ≤M} 2(α-α*)·oaScalarRHS g
  2. `BodyODEData` (ContinuumBodyLeibniz.lean): needs HasDerivAt with derivative = -(K·P_body)
     and P_body ≥ 0 (equivalently: V_body antitone)

  The argument (formalized by BodyLaSalleConvergence.lean, 0 sorry):
  1. V_body(M,·) antitone + nonneg + differentiable → V_body(M,·) converges to L_M ≥ 0
  2. MVT on [n,n+1]: ∃ t_n → ∞ with |V_body'(M,t_n)| → 0 (deriv_vanishes_on_subsequence)
  3. V_body' = -K·P_body, so P_body(M,t_n) → 0
  4. Body coercivity: P_body ≥ c(M)·V_body eventually → V_body(M,t_n) → 0
  5. V_body antitone + subseq → 0 → V_body(M,·) → 0
  6. V ≤ V_body(M) + tail_mass(M) with tail → 0 → V → 0

  STATUS:
  - Steps 1-6 are PROVED in BodyLaSalleConvergence.lean (from BodyODEData, 0 sorry)
  - The Leibniz step (HasDerivAt V_body) is PROVED in BodyLeibnizProof.lean
  - The REMAINING GAP: proving the body derivative ≤ 0 (i.e., P_body ≥ 0)

  For the FULL V: dV/dt ≤ 0 follows from the pair bound + self-consistency
  (continuum_lyapunov_deriv_nonpos). But for V_body: the body derivative
  involves global r = ∫_ALL α g while integrating only over the body.
  The self-consistency mismatch prevents direct application of the pair bound.

  WHAT THIS MEANS:
  - For integrable γ (∫|ω|g < ∞): V itself is differentiable, V antitone,
    and V → 0 is PROVED (BarbalatLeibnizBridge.lean, 0 sorry).
  - For non-integrable γ (Lorentzian): V_body might NOT be antitone,
    so BodyODEData cannot be directly instantiated.
  - The genuine remaining gap is: either prove V_body antitone, or find
    an argument that bypasses this requirement.

  0 sorry.
-/

import KuramotoLean.BodyLaSalleConvergence
import KuramotoLean.BodyLeibnizProof

open Filter Topology Set MeasureTheory

noncomputable section

namespace BodyLaSalleBridge

/-! ## What is PROVED

The complete chain (all 0 sorry):
  body_leibniz_hasDerivAt:  HasDerivAt V_body(M) (raw_derivative) t
  deriv_vanishes_on_subsequence: V differentiable + V → L ⟹ ∃ t_n with |V'(t_n)| → 0
  BodyLaSalleConvergence.convergence: BodyODEData ⟹ V → 0
  BodyLaSalleConvergence.body_tendsto_zero: BodyODEData ⟹ V_body(M) → 0

The SINGLE gap: BodyODEData.h_Vb_hasDerivAt requires the raw derivative = -(K·P_body)
with P_body ≥ 0. This is equivalent to: the body-restricted Lyapunov derivative ≤ 0.

For the full V: continuum_lyapunov_deriv_nonpos proves this using the pair bound
+ self-consistency r = ∫α dμ. For V_body: self-consistency fails on the restricted
measure, so the pair bound cannot be applied directly.
-/

/-! ## The pair decomposition of the body derivative

The body derivative admits the per-ω decomposition:
  dV_body(M)/dt = ∫_{γ≤M} [(-K·r*)·Q_ω + K·(r-r*)·S_ω] dμ

where Q_ω = (α-α*)²(α+1/α*) ≥ 0 and S_ω = (α-α*)(1-α²) (bounded).

The term -K·r*·∫Q_body ≤ 0 provides DISSIPATION.
The term K·(r-r*)·∫S_body is COUPLING ERROR (bounded, either sign).

For the FULL integral: -K·r*·Q + K·D·S ≤ 0 by the pair bound.
For the body: -K·r*·Q_body + K·D·S_body could be > 0 (when coupling error dominates).

Key observation: as r → r* (which follows from V → 0 by Cauchy-Schwarz),
the coupling error K·(r-r*)·S_body → 0. So EVENTUALLY the body derivative is ≤ 0.
But "eventually" requires V → 0, which is what we're trying to prove.
This creates a BOOTSTRAP problem that requires additional structure to resolve.
-/

/-! ## Summary of the proof state

For g with finite first moment (∫|ω|g < ∞):
  • Gaussian, Student-t ν>2, compact support → V → 0 PROVED (0 sorry, 0 axioms)
  • Proof: BarbalatLeibnizBridge.lean via DCT for full V

For Lorentzian (∫|ω|g = ∞):
  • Dedicated proof via Bernoulli closed-form → r → r* (MainTheorem, 0 sorry)
  • General Lyapunov proof OPEN (body derivative sign not established)

For general g ∈ L¹ with ∫|ω|g = ∞ (e.g., Student-t ν=1, Cauchy-like):
  • OPEN. Requires either:
    (a) Body derivative ≤ 0 (V_body antitone) — blocked by coupling error
    (b) Modified argument bypassing V_body antitonicity — not yet found
    (c) Direct proof of V absolutely continuous without DCT — open
-/

end BodyLaSalleBridge

end
