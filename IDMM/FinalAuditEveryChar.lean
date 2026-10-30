/- Rebuilt with the library. The every-characteristic theorem lives in its own import closure:
`Matmul` and `OAI.LinearAlgebra.MatrixMultiplication.Main` declare clashing names, so this file
cannot import `IDMM.FinalAudit`. -/
import IDMM.EveryChar
import IDMM.StrictEveryChar

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
#print axioms IDMM.strict_id_bound_every_char
#print axioms IDMM.id_bound_every_char_rat
#print axioms IDMM.id_bound_every_char_zmod3
#print axioms IDMM.ncSizeLE_strict
#print axioms IDMM.StrictNCSizeLE.ncSizeLE
#print axioms IDMM.strict_of_bound
#print axioms IDMM.two_mul_le_of_ncSizeLE_ID
#print axioms IDMM.not_idBoundF_of_lt_one
#print axioms IDMM.not_strictIDBoundF_of_lt_one
#print axioms IDMM.strict_id_trivial
#print axioms IDMM.not_strictNCSizeLE_zero
#check @IDMM.strict_id_bound_every_char
#check @IDMM.id_bound_every_char_rat
#check @IDMM.id_bound_every_char_zmod3
#check @IDMM.two_mul_le_of_ncSizeLE_ID
#check @IDMM.not_idBoundF_of_lt_one
#check @IDMM.ncSizeLE_strict
#check @IDMM.rankAtMost_of_scheme
#check @IDMM.uz_exponent_slack
#check @IDMM.construction_gen
#check @IDMM.oracles_of_scheme
#check @IDMM.exists_ext_of_algClosure
#check @IDMM.IDBoundF.of_ext
#check @Matmul.RectangularRankBridge.exists_scheme_certificate
#check @IDMM.StrictNCSizeLE.ncSizeLE
#check @IDMM.strict_of_bound
#check @IDMM.not_strictIDBoundF_of_lt_one
#check @IDMM.strict_id_trivial
#check @IDMM.not_strictNCSizeLE_zero
