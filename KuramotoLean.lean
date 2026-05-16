-- Core proof chain only. Non-core modules preserved in repo but excluded from build.
-- Real scalar model (0 sorry)
import KuramotoLean.ContinuumSolvedFinal
-- Complex OA (0 sorry, hV_zero hypothesis)
import KuramotoLean.ComplexOA
import KuramotoLean.ComplexOAEnergy
import KuramotoLean.ComplexOASymmetry
import KuramotoLean.ComplexOAPairBound
import KuramotoLean.ComplexPairBoundProof
import KuramotoLean.ComplexOAStability
import KuramotoLean.ComplexOAConvergence
import KuramotoLean.ComplexOAEndToEnd
-- Full PDE (1 axiom)
import KuramotoLean.FullKuramotoTheorem
import KuramotoLean.KuramotoEndToEnd
import KuramotoLean.ComplexOAContDep
-- Gronwall bootstrap (0 sorry)
import KuramotoLean.GronwallBootstrap
import KuramotoLean.KuramotoViaPassage
import KuramotoLean.BasinDecay
import KuramotoLean.ComplexLeibniz
-- Complete wiring (0 sorry, 0 custom axioms)
import KuramotoLean.KuramotoComplete
-- Real scalar end-to-end (0 sorry, derives body persistence internally)
import KuramotoLean.RealScalarComplete
