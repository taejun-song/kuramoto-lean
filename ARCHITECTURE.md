# Kuramoto Lean 4 — System Architecture

## Dependency Graph

```
                              ┌─────────────────────────────┐
                              │        Mathlib + Defs        │
                              └──────────────┬──────────────-┘
                                             │
                              ┌──────────────▼──────────────-┐
                              │        ComplexOA.lean         │
                              │  complexOaRHS, psiComplex     │
                              │  disk invariance, Re lower    │
                              │  bound, zero-freq positivity  │
                              └──┬──────────┬──────────┬─────┘
                                 │          │          │
                    ┌────────────▼───┐  ┌───▼────────┐ │
                    │ ComplexOA      │  │ ComplexOA   │ │
                    │ Symmetry.lean  │  │ Energy.lean │ │
                    │ SymmetricFreq  │  │ dΨ/dt=K|η|²│ │
                    │ η real         │  │ Ψ monotone  │ │
                    └──┬─────────┬──-┘  └──┬──────┬──┘ │
                       │         │         │      │    │
          ┌────────────▼──┐      │    ┌────▼────┐ │  ┌─▼──────────────┐
          │ ComplexOA     │      │    │ComplexOA│ │  │ ComplexOA      │
          │ PairBound.lean│      │    │Stability│ │  │ LockedEquil    │
          │ rotation = 0  │      │    │.lean    │ │  │ .lean          │
          │ dV/dt formula │      │    │complexV │ │  │ lockedEquil    │
          └──┬────────────┘      │    └────┬────┘ │  │ selfConsistF   │
             │                   │         │      │  │ 19 theorems    │
    ┌────────▼──────┐            │    ┌────▼─────-┐│  └──────┬─────────┘
    │ BasinDecay    │            │    │ ComplexOA  ││         │
    │ .lean         │            │    │ Convergence││         │
    │ coercivity    │            │    │ .lean      ││         │
    └──┬────────────┘            │    └────┬──────-┘│         │
       │                         │         │        │         │
  ┌────▼─────────────────────────▼──┐ ┌────▼──────┐ │         │
  │ ComplexLeibniz.lean             │ │ ComplexOA  │ │         │
  │ Leibniz rule (V differentiable) │ │ PairBound  │ │         │
  │ V' = coercivity + forcing       │ │ Proof.lean │ │         │
  │ complex_V_basin_decay           │ └────┬──────-┘ │         │
  └──┬────────────────────┬─────────┘      │         │         │
     │                    │          ┌─────▼─────────▼──┐      │
     │     ┌──────────────▼──────┐   │ ComplexOA        │      │
     │     │ ComplexOA           │   │ EndToEnd.lean     │      │
     │     │ ErrorIdentity.lean  │   │ eta_re_cauchy_    │      │
     │     │ forcing_eq_eta_diff │   │   schwarz         │      │
     │     │ error_deriv_neg     │   │ complex_oa_       │      │
     │     └──────────┬──────────┘   │   end_to_end      │      │
     │                │              └──┬───────┬────────┘      │
     │                │                 │       │               │
     │  ┌─────────────▼────────┐        │       │               │
     │  │ GronwallBootstrap    │        │       │               │
     │  │ .lean                │        │       │               │
     │  │ basin_invariance     │        │       │               │
     │  │ basin_invariance_    │        │       │               │
     │  │   history            │        │       │               │
     │  │ eventually_below ★NEW│        │       │               │
     │  │ gronwall_bootstrap_  │        │       │               │
     │  │   tendsto            │        │       │               │
     │  │ gronwall_bootstrap_  │        │       │               │
     │  │   tendsto_history    │        │       │               │
     │  └─┬────────┬───────┬──-┘        │       │               │
     │    │        │       │            │       │               │
     │    │        │       │            │       │               │
     │    │        │  ┌────▼────────────▼─┐     │               │
     │    │        │  │ KuramotoFresh     │     │               │
     │    │        │  │ .lean             │     │               │
     │    │        │  │ y_damping_in_basin│     │               │
     │    │        │  │ kuramoto_fresh    │     │               │
     │    │        │  └───────────────────┘     │               │
     │    │        │                            │               │
┌────▼────▼────────▼────────────────────────────▼───────────────▼──┐
│                CompactSupportConvergence.lean                    │
│                45 theorems, 0 sorry, 0 axioms                   │
│                                                                  │
│  ┌─ Algebraic ──────────────────────────────────────────────┐    │
│  │ normSq_one_minus_sq_of_unit, forcing_integral_identity   │    │
│  │ weighted_cs_sq, forcing_bound_of_cs                      │    │
│  └──────────────────────────────────────────────────────────┘    │
│  ┌─ ODE Barrier ────────────────────────────────────────────┐    │
│  │ positive_barrier, positive_barrier_on_Icc ★NEW           │    │
│  │ body_persistence, body_persistence_on_Icc ★NEW           │    │
│  │ complexOaRHS_re_pos_at_re_zero                           │    │
│  └──────────────────────────────────────────────────────────┘    │
│  ┌─ Basin Coupling ─────────────────────────────────────────┐    │
│  │ coupling_bound_in_basin, eta_re_ge_of_cs_bound           │    │
│  │ coercivity_pointwise_of_body                             │    │
│  └──────────────────────────────────────────────────────────┘    │
│  ┌─ Decay Assembly ─────────────────────────────────────────┐    │
│  │ compact_support_h_basin_decay_at (per-time, in basin)    │    │
│  │ compact_support_h_decay_of_r_floor ★NEW (per-time,       │    │
│  │   NO basin — uses r-floor instead)                       │    │
│  │ compact_support_h_basin_decay  (universal, delegates)    │    │
│  │ V_deriv_rate_bound, net_decay_of_coercivity_forcing      │    │
│  └──────────────────────────────────────────────────────────┘    │
│  ┌─ End-to-End Theorems ────────────────────────────────────┐    │
│  │ compact_support_convergence     (takes h_basin_decay)    │    │
│  │ compact_support_full_convergence(takes h_body)           │    │
│  │ compact_support_convergence_locked                       │    │
│  │   (takes hz0_re + h_lock, FULLY SELF-CONTAINED)          │    │
│  │ compact_support_convergence_r_floor ★NEW                 │    │
│  │   (takes r-floor + body, NO BASIN CONDITION)             │    │
│  │ compact_support_convergence_r_floor_locked ★NEW          │    │
│  │   (takes r-floor + locking + hz0_re, NO BASIN)           │    │
│  └──────────────────────────────────────────────────────────┘    │
└──────────────────────────────────────────────────────────────────┘

   ┌───────────────────────────────────┐
   │ KuramotoComplete.lean             │
   │ kuramoto_complete                 │  ← 0 sorry, 0 axioms
   │ (takes h_coercivity hypothesis)   │     uses: ComplexLeibniz
   └───────────────────────────────────┘     + GronwallBootstrap
                                             + ComplexOAEndToEnd

   ┌───────────────────────────────────┐
   │ KuramotoEndToEnd.lean             │
   │ kuramoto_stability_complex_oa     │  ← 0 sorry, 1 AXIOM
   │ DietertLinearlyStable (opaque)    │     (Dietert 2017
   │ DietertSobolevSmall   (opaque)    │      Landau damping)
   │ DietertRegularG       (opaque)    │
   │ dietert_landau_damping_2017       │
   └───────────────────────────────────┘

   ┌───────────────────────────────────┐
   │ FullKuramotoTheorem.lean          │
   │ full_kuramoto_pde_stability       │  ← 0 sorry, 1 AXIOM
   │ OAManifoldAttractive  (opaque)    │     (Dietert-Fernandez 2018
   │ oa_manifold_attractivity          │      OA attractivity)
   └───────────────────────────────────┘

════════════════════════════════════════════
 Real Scalar Track (independent)
════════════════════════════════════════════

  ContinuumSolvedFinal.lean
    │  kuramoto_standard_tendsto        ← 0 sorry, 0 axioms
    │
    ├──▶ KuramotoGlobal.lean
    │      kuramoto_global_unconditional← 0 sorry, 0 axioms
    │
    └──▶ FullKuramotoTheorem.lean
           (uses ContinuumSolvedFinal
            + OA attractivity axiom)
```

## Proof Chain: compact_support_convergence_locked

The main axiom-free result for the complex OA. Shows how the circularity is broken:

```
    ┌─────────────────────────────────────────────────────────────┐
    │  HYPOTHESES (all checkable for specific K, g)               │
    │                                                             │
    │  hz0_re  : ∀ ω, 0 < Re(z(ω,0))      initial body positive │
    │  h_lock  : ∀ ω, |ω| < K(r*-√B)/2    frequency locking     │
    │  hV0     : V(0) < B                   initial basin         │
    │  hrate   : K(r*-√B)δ₀ - K√F > 0      net decay rate       │
    └───────────────────────────┬─────────────────────────────────┘
                                │
                                ▼
    ┌─────────────────────────────────────────────────────────────┐
    │  gronwall_bootstrap_tendsto_history                         │
    │  (V continuous, V ≥ 0, V(0) < B)                            │
    │                                                             │
    │  For each t > 0, given HISTORY {∀ s < t, V(s) < B}:        │
    │                                                             │
    │  ┌───────────────────────────────────────────────────────┐  │
    │  │ Step 1: CS bound                                      │  │
    │  │   (η.re - r*)² ≤ V(s) < B  for all s ≤ t             │  │
    │  │   ⟹  η(s).re ≥ r* - √B  for all s ≤ t               │  │
    │  ├───────────────────────────────────────────────────────┤  │
    │  │ Step 2: Coupling on [0,t]                             │  │
    │  │   h_lock + CS ⟹  |ω| < K·η(s).re/2  for s ∈ [0,t]   │  │
    │  │   (coupling_bound_in_basin)                           │  │
    │  ├───────────────────────────────────────────────────────┤  │
    │  │ Step 3: Body persistence on [0,t]                     │  │
    │  │   coupling on [0,t] + hz0_re                          │  │
    │  │   ⟹  Re(z(ω,s)) > 0  for s ∈ [0,t]                  │  │
    │  │   (body_persistence_on_Icc + positive_barrier_on_Icc) │  │
    │  │   ↑ BREAKS CIRCULARITY: uses history, not V(t) alone  │  │
    │  ├───────────────────────────────────────────────────────┤  │
    │  │ Step 4: Coercivity dominates forcing                  │  │
    │  │   Re(z) > 0 ⟹  coercivity ≥ K·r_min·δ₀·V            │  │
    │  │   CS + forcing identity ⟹  |forcing| ≤ K·√F·V        │  │
    │  │   rate > 0 ⟹  V'(t) ≤ -rate·V(t)                     │  │
    │  │   (compact_support_h_basin_decay_at)                  │  │
    │  └───────────────────────────────────────────────────────┘  │
    │                                                             │
    │  basin_invariance_history: V antitone on [0,T] ⟹ V < B     │
    │  exp_decay_bound: V(t) ≤ V(0)·e^{-rate·t}                  │
    │  ⟹  V → 0                                                  │
    └───────────────────────────┬─────────────────────────────────┘
                                │
                                ▼
    ┌─────────────────────────────────────────────────────────────┐
    │  complex_oa_end_to_end                                      │
    │                                                             │
    │  V → 0  +  eta_re_cauchy_schwarz                            │
    │  ⟹  (Re(η) - r*)² ≤ V → 0                                 │
    │  ⟹  Re(η)² → r*²                                           │
    └─────────────────────────────────────────────────────────────┘
```

## Status Summary

| Track | Theorem | Sorry | Axioms | Status |
|-------|---------|-------|--------|--------|
| Complex OA (locked) | `compact_support_convergence_locked` | 0 | 0 | **PROVED** |
| Complex OA (r-floor) | `compact_support_convergence_r_floor` | 0 | 0 | **PROVED** (takes r-floor + body, no basin) |
| Complex OA (general) | `compact_support_full_convergence` | 0 | 0 | **PROVED** (takes h_body) |
| Complex OA (coercivity) | `kuramoto_complete` | 0 | 0 | **PROVED** (takes h_coercivity) |
| Complex OA (Landau) | `kuramoto_stability_complex_oa` | 0 | 1 | Dietert 2017 axiom |
| Full PDE | `full_kuramoto_pde_stability` | 0 | 1 | OA attractivity axiom |
| Real scalar | `kuramoto_standard_tendsto` | 0 | 0 | **PROVED** |
| Real scalar global | `kuramoto_global_unconditional` | 0 | 0 | **PROVED** |
| Y-damping | `kuramoto_fresh` | 0 | 0 | **PROVED** (takes h_basin_decay) |
