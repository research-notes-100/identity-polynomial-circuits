/-
The exponent of the thin-endpoint construction: `constructionExponent (200/293) 2 < 1.6939`.
-/
import IDMM.Layout
import IDMM.Numerical
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexRationalLogCertificate

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IDMM
open OAI.MatrixMultiplication.Foundation.RationalLogCertificate

private theorem log_two_bounds' :
    (6931471805 : ℝ)/10^10 ≤ Real.log (2/1) ∧ Real.log (2/1) ≤ (6931471806 : ℝ)/10^10 := by
  have h := normalized_log_error (2/1 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_three_halves_bounds' :
    (4054651081 : ℝ)/10^10 ≤ Real.log (3/2) ∧ Real.log (3/2) ≤ (4054651082 : ℝ)/10^10 := by
  have h := normalized_log_error (3/2 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_p_bounds :
    (3112919380 : ℝ)/10^10 ≤ Real.log (400/293) ∧ Real.log (400/293) ≤ (3112919381 : ℝ)/10^10 := by
  have h := normalized_log_error (400/293 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_q_bounds :
    (4561007240 : ℝ)/10^10 ≤ Real.log (800/507) ∧ Real.log (800/507) ≤ (4561007241 : ℝ)/10^10 := by
  have h := normalized_log_error (800/507 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_x_bounds' :
    (4561796226 : ℝ)/10^10 ≤ Real.log (10000/6337) ∧
    Real.log (10000/6337) ≤ (4561796227 : ℝ)/10^10 := by
  have h := normalized_log_error (10000/6337 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_y_bounds' :
    (1914325214 : ℝ)/10^10 ≤ Real.log (7674/6337) ∧
    Real.log (7674/6337) ≤ (1914325215 : ℝ)/10^10 := by
  have h := normalized_log_error (7674/6337 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

/-- **The thin-endpoint exponent.** `2H(1/4) − 2μH(1/(4μ)) + 2μ < 1.6939` at `μ = 200/293`
(the value is `1.6938884…`). -/
theorem thin_exponent_lt : constructionExponent muQ 2 < 16939 / 10000 := by
  have h2 := log_two_bounds'
  have h3 := log_three_halves_bounds'
  have hp := log_p_bounds
  have hq := log_q_bounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have ha : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, h4]; ring
  have hb : Real.log (3/4 : ℝ) = Real.log (3/2 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hc : Real.log (293/800 : ℝ) = -(Real.log (400/293 : ℝ) + Real.log 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_inv]; norm_num
  have hd : Real.log (507/800 : ℝ) = -Real.log (800/507 : ℝ) := by
    rw [← Real.log_inv]; norm_num
  unfold constructionExponent binaryEntropy muQ
  norm_num only [show (1:ℝ) - 1/4 = 3/4 by norm_num,
    show (1:ℝ)/(4*(200/293)) = 293/800 by norm_num,
    show (1:ℝ) - 293/800 = 507/800 by norm_num]
  rw [ha, hb, hc, hd]
  simp only [div_one] at h2
  apply (mul_lt_mul_iff_of_pos_right hlog2).mp
  field_simp
  nlinarith [h2.1, h2.2, h3.1, h3.2, hp.1, hp.2, hq.1, hq.2]

/-- `gHalf + 2μ` is the construction exponent at `w = 2`. -/
theorem gHalf_add : gHalf + 2 * muQ = constructionExponent muQ 2 := by
  unfold gHalf constructionExponent
  have : (1 : ℝ) / (4 * muQ) = 293 / 800 := by unfold muQ; norm_num
  rw [this]; ring

theorem constructionExponent_add (μ w δ : ℝ) :
    constructionExponent μ (w + δ) = constructionExponent μ w + μ * δ := by
  unfold constructionExponent; ring

/-- **Slack at the chosen point.** `C(0.6337, chosenW) + 10⁻⁷ < 1.690568` (the value is `1.6905677…`). -/
theorem chosen_exponent_slack : constructionExponent chosenMu chosenW + 1 / 10 ^ 7 < targetExponent := by
  have h2 := log_two_bounds'
  have h3 := log_three_halves_bounds'
  have hx := log_x_bounds'
  have hy := log_y_bounds'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have ha : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, h4]; ring
  have hb : Real.log (3/4 : ℝ) = Real.log (3/2 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hc : Real.log (2500/6337 : ℝ) = Real.log (10000/6337 : ℝ) - 2 * Real.log 2 := by
    rw [← h4, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hd : Real.log (3837/6337 : ℝ) = Real.log (7674/6337 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  unfold constructionExponent binaryEntropy chosenMu chosenW chosenK targetExponent
  norm_num only [show (1:ℝ)/4 = 1/4 from rfl,
    show (1:ℝ) - 1/4 = 3/4 by norm_num,
    show (1:ℝ)/(4*(6337/10000)) = 2500/6337 by norm_num,
    show (1:ℝ)-2500/6337 = 3837/6337 by norm_num]
  rw [ha, hb, hc, hd]
  simp only [div_one] at h2
  apply (mul_lt_mul_iff_of_pos_right hlog2).mp
  field_simp
  nlinarith [h2.1, h2.2, h3.1, h3.2, hx.1, hx.2, hy.1, hy.2]

private theorem log_a_bounds :
    (2162231084 : ℝ)/10^10 ≤ Real.log (36/29) ∧ Real.log (36/29) ≤ (2162231085 : ℝ)/10^10 := by
  have h := normalized_log_error (36/29 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

private theorem log_b_bounds :
    (5154660033 : ℝ)/10^10 ≤ Real.log (72/43) ∧ Real.log (72/43) ≤ (5154660034 : ℝ)/10^10 := by
  have h := normalized_log_error (72/43 : ℝ) (by norm_num) (by norm_num) 24
  norm_num [realApprox, sumPower, Finset.sum_range_succ] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

/-- **The rectangular-curve exponent.** At `μ = 18/29` (aspect `11/18`, `w = 1 + k + 1/(4k) = 200/99`),
`C(μ, w) + 10⁻⁵ < 1.6692` (the value is `1.66916842…`). -/
theorem uz_exponent_slack : constructionExponent (18 / 29) (200 / 99) + 1 / 10 ^ 5 < 4173 / 2500 := by
  have h2 := log_two_bounds'
  have h3 := log_three_halves_bounds'
  have ha' := log_a_bounds
  have hb' := log_b_bounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have ha : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, h4]; ring
  have hb : Real.log (3/4 : ℝ) = Real.log (3/2 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hc : Real.log (29/72 : ℝ) = -(Real.log (36/29 : ℝ) + Real.log 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_inv]; norm_num
  have hd : Real.log (43/72 : ℝ) = -Real.log (72/43 : ℝ) := by
    rw [← Real.log_inv]; norm_num
  unfold constructionExponent binaryEntropy
  norm_num only [show (1:ℝ) - 1/4 = 3/4 by norm_num,
    show (1:ℝ)/(4*(18/29)) = 29/72 by norm_num,
    show (1:ℝ) - 29/72 = 43/72 by norm_num]
  rw [ha, hb, hc, hd]
  simp only [div_one] at h2
  apply (mul_lt_mul_iff_of_pos_right hlog2).mp
  field_simp
  nlinarith [h2.1, h2.2, h3.1, h3.2, ha'.1, ha'.2, hb'.1, hb'.2]

end IDMM
