import OAI.LinearAlgebra.MatrixMultiplication.Main
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

namespace IDMM
open OAI.MatrixMultiplication OAI.MatrixMultiplication.Arithmetic

/-- The strict dual-exponent theorem supplies an admissible exponent at the exact rational aspect.
It is not enough merely to rewrite the supremum definition as an attained maximum. -/
theorem thin_admissible : RectangularAdmissibleExponent ℂ (93/200) 2 := by
  obtain ⟨k,hk,hlt⟩ := exists_lt_of_lt_csSup complexAlpha_set_nonempty
    complex_alpha_gt_93_div_200
  apply rectangularAdmissibleExponent_iff_omega_le.mpr
  exact (rectangularOmega_mono (F := ℂ) hlt.le).trans hk.2.le

theorem wide_admissible : RectangularAdmissibleExponent ℂ (709/1000) (523/250) :=
  rectangularAdmissibleExponent_iff_omega_le.mpr complex_rectangular_omega_lt_523_div_250.le

theorem square_input : omega ℂ ≤ 9/4 := complex_omega_le_nine_quarters
end IDMM
