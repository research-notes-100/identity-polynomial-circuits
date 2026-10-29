/-
Prints the axioms behind the theorems:
    lake build && lake env lean scripts/PrintAxioms.lean
Expected for each: propext, Classical.choice, Quot.sound (some sanity checks need fewer).
-/
import TheoremB.Corollaries
import TheoremB.PTRank
import TheoremB.CharPGrowth
import TheoremB.Rectangular
import TheoremB.Sanity

#print axioms TheoremB.crossWidth
#print axioms TheoremB.width_le
#print axioms TheoremB.p_le
#print axioms TheoremB.p_le_rpow
#print axioms TheoremB.prodLE_of_PLE
#print axioms TheoremB.sosLE_of_prodLE
#print axioms TheoremB.hurwitz_le
#print axioms TheoremB.hurwitz_le_rpow
#print axioms TheoremB.ptle_two
#print axioms TheoremB.ptle_of_halves
#print axioms TheoremB.pt_rank_le
#print axioms TheoremB.pt_rank_le_rpow
#print axioms TheoremB.sos_two
#print axioms TheoremB.sos_trivial
#print axioms TheoremB.ple_trivial
#print axioms TheoremB.not_sos_one_zero
#print axioms TheoremB.not_ple_one_zero
#print axioms TheoremB.ptle_trivial
#print axioms TheoremB.not_ptle_zero
#print axioms TheoremB.CharP.op_dvd
#print axioms TheoremB.CharP.pairF_aFam
#print axioms TheoremB.CharP.sum_piece
#print axioms TheoremB.CharP.piece_row
#print axioms TheoremB.CharP.piece_col
#print axioms TheoremB.CharP.plef_le
#print axioms TheoremB.CharP.d_eq
#print axioms TheoremB.CharP.C_le
#print axioms TheoremB.CharP.le_C
#print axioms TheoremB.CharP.d_unbounded
#print axioms TheoremB.CharP.plef_rpow
#print axioms TheoremB.CharP.prodLE_of_PLEF
#print axioms TheoremB.CharP.sosLE_of_prodLE_three
#print axioms TheoremB.CharP.hurwitz_le_rpow
#print axioms TheoremB.plef_trivial
#print axioms TheoremB.not_plef_one_zero
#print axioms TheoremB.sos_two_zmod3
#print axioms TheoremB.Rect.sum_piece
#print axioms TheoremB.Rect.piece_row
#print axioms TheoremB.Rect.piece_col
#print axioms TheoremB.Rect.pler_le
#print axioms TheoremB.Rect.prodLER_of_PLER
#print axioms TheoremB.Rect.sosLER_of_prodLER
#print axioms TheoremB.Rect.key
#print axioms TheoremB.Rect.log_succ_le
#print axioms TheoremB.Rect.pler_exp_le
#print axioms TheoremB.Rect.hurwitzR_exp_le
#print axioms TheoremB.Rect.hurwitzR_diag
#print axioms TheoremB.sosR_trivial
#print axioms TheoremB.pler_trivial
#print axioms TheoremB.not_sosR_one_zero
#print axioms TheoremB.not_pler_one_zero
