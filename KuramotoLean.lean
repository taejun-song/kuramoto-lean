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
