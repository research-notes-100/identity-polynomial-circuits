import IDMM.Statements
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexRationalLogCertificate

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IDMM
open OAI.MatrixMultiplication.Foundation.RationalLogCertificate

private theorem log_two_bounds :
    (6931471805 : ℝ)/10^10 ≤ Real.log (2/1) ∧
    Real.log (2/1) ≤ (6931471806 : ℝ)/10^10 := by
  have h := normalized_log_error (2/1 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_three_halves_bounds :
    (4054651081 : ℝ)/10^10 ≤ Real.log (3/2) ∧
    Real.log (3/2) ≤ (4054651082 : ℝ)/10^10 := by
  have h := normalized_log_error (3/2 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_x_bounds :
    (4561796226 : ℝ)/10^10 ≤ Real.log (10000/6337) ∧
    Real.log (10000/6337) ≤ (4561796227 : ℝ)/10^10 := by
  have h := normalized_log_error (10000/6337 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_y_bounds :
    (1914325214 : ℝ)/10^10 ≤ Real.log (7674/6337) ∧
    Real.log (7674/6337) ≤ (1914325215 : ℝ)/10^10 := by
  have h := normalized_log_error (7674/6337 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

/-- Rational parameters; the gap to the requested exponent is positive, not a rounded equality. -/
noncomputable def chosenMu : ℝ := 6337/10000
noncomputable def chosenK : ℝ := 3663/6337
noncomputable def chosenW : ℝ :=
  2 + (chosenK - 93/200) * ((523/250 - 2)/(709/1000 - 93/200))

theorem chosen_parameters :
    1/2 < chosenMu ∧ chosenMu < 1 ∧
    chosenK = (1-chosenMu)/chosenMu ∧ 93/200 < chosenK ∧ chosenK < 709/1000 := by
  norm_num [chosenMu, chosenK]

/-- Numerical lemma only: this does not assert admissibility of the interpolated MM exponent. -/
theorem chosen_exponent_lt_target : constructionExponent chosenMu chosenW < targetExponent := by
  have h2 := log_two_bounds
  have h3 := log_three_halves_bounds
  have hx := log_x_bounds
  have hy := log_y_bounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    rw [h4]
    ring
  have hb : Real.log (3/4 : ℝ) = Real.log (3/2 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hc : Real.log (2500/6337 : ℝ) = Real.log (10000/6337 : ℝ) - 2 * Real.log 2 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    rw [← h4, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hd : Real.log (3837/6337 : ℝ) = Real.log (7674/6337 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  unfold constructionExponent binaryEntropy chosenMu chosenW chosenK targetExponent
  norm_num only [show (1:ℝ)/4 = 1/4 from rfl,
    show (1:ℝ) - 1/4 = 3/4 by norm_num,
    show (1:ℝ)/(4*(6337/10000)) = 2500/6337 by norm_num,
    show (1:ℝ)-2500/6337 = 3837/6337 by norm_num]
  rw [ha, hb, hc, hd]
  apply (mul_lt_mul_iff_of_pos_right hlog2).mp
  field_simp
  nlinarith [h2.1,h2.2,h3.1,h3.2,hx.1,hx.2,hy.1,hy.2]
end IDMM
