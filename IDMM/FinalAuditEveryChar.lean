/- Rebuilt with the library. The every-characteristic theorem lives in its own import closure:
`Matmul` and `OAI.LinearAlgebra.MatrixMultiplication.Main` declare clashing names, so this file
cannot import `IDMM.FinalAudit`. -/
import IDMM.EveryChar

#print axioms IDMM.id_bound_every_char
#print axioms IDMM.rankAtMost_of_scheme
#print axioms IDMM.uz_exponent_slack
#print axioms IDMM.construction_gen
#print axioms IDMM.oracles_of_scheme
#print axioms IDMM.exists_ext_of_algClosure
#print axioms IDMM.IDBoundF.of_ext
#print axioms Matmul.RectangularRankBridge.exists_scheme_certificate
#check @IDMM.id_bound_every_char
#print IDMM.IDBoundF
#print IDMM.S4BoundF
#print IDMM.Perm4BoundF
