/-
Axiom audit for the part of the development that does not touch the z-line algebra:
Theorem 2.1 and its corollary, Theorem 3.6 (the case `k = 2`), Theorem 4.1, and the
two Giambelli statements of Section 5.  None of the four large `ZLineAlg*` modules is
in the import closure of any of them, so this audit runs even when those modules fail
to build.

    lake env lean AuditShift.lean

Every theorem below should report exactly `propext, Classical.choice, Quot.sound`.
-/
import RequestProject.ShiftProof
import RequestProject.AverageTableau
import RequestProject.DiagonalArrivalAllN
import RequestProject.ZLine

-- Theorem 2.1 (the shift identity) and its corollary F(k,k) = F(k−1,k+1)+1
#print axioms AvgRS.shift_identity
#print axioms AvgRS.avgEntry_diag
-- Theorem 3.6 (k = 2 on the line z + z' = −2), Theorem 4.1 (the finite form)
#print axioms AvgRS.zline_identity_two
#print axioms AvgRS.content0_all
-- Section 5: Giambelli, and its content-weighted form
#print axioms AvgRS.giambelli_formula
#print axioms AvgRS.giambelli_content
