/-
Axiom audit. Not part of either library (the lakefile globs are `RequestProject.+` and
`Computations.+`), so it adds nothing to the build; it is run in CI by

    lake env lean Audit.lean

and its output is the audit record. Every theorem below should report exactly
`propext, Classical.choice, Quot.sound`.
-/
import RequestProject.ZLineProof
import RequestProject.ZLineAlgMain
import RequestProject.ZLineAlgRels
import RequestProject.ShiftProof
import RequestProject.AverageTableau
import RequestProject.DiagonalArrivalAllN
import RequestProject.RingKernel

-- Conjecture 3.2 of avgRS.tex, for all k ≥ 2, all N and all t.
#print axioms AvgRS.zline_identity
-- the algebraic core, and the two halves it is assembled from
#print axioms AvgRS.zline_alg
#print axioms AvgRS.zline_formal
#print axioms AvgRS.zrels
-- Theorem 2.1 (the shift identity) and its corollary F(k,k) = F(k−1,k+1)+1
#print axioms AvgRS.shift_identity
#print axioms AvgRS.avgEntry_diag
-- Theorem 3.6 (k = 2 on the line), Theorem 4.1 (finite form), Giambelli
#print axioms AvgRS.zline_identity_two
#print axioms AvgRS.content0_all
#print axioms AvgRS.giambelli_formula
#print axioms AvgRS.giambelli_content
-- the reflection tactic's soundness lemma
#print axioms AvgRS.RingKernel.eq_of_toPolyK_eq
