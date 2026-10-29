/-
**The 1.690568 theorem: `MainTarget`.** `ID_N`, `S4_N` and `perm4_N` have noncommutative circuits with
`O(N^{211321/125000 + ε})` gates over `ℂ`, for every `ε > 0`.

The cycle-055 construction (`construction_target`) at `μ = 6337/10000`, with the rectangular exponent at the aspect
`3663/6337` obtained by interpolating OpenAI's two proved endpoints (`ω(93/200) = 2`, `ω(709/1000) ≤ 523/250`) at the
ratio `829933 : 716295`.
-/
import IDMM.Interp
import IDMM.ProgramRank
import IDMM.Construction
import IDMM.Main

noncomputable section
namespace IDMM
open OAI.MatrixMultiplication.Arithmetic

/-- **Rectangular interpolation at a rational ratio.** -/
theorem rect_interp {k₁ k₂ τ₁ τ₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₁' : k₁ ≤ 1) (hk₂' : k₂ ≤ 1)
    (hτ₁ : 2 ≤ τ₁) (hτ₂ : 2 ≤ τ₂)
    (h₁ : RectangularAdmissibleExponent ℂ k₁ τ₁) (h₂ : RectangularAdmissibleExponent ℂ k₂ τ₂)
    (p q : ℕ) (hpq : 0 < p + q) :
    RectangularAdmissibleExponent ℂ ((p * k₁ + q * k₂) / (p + q)) ((p * τ₁ + q * τ₂) / (p + q)) :=
  rect_interp_of_rank (fun P hP => rank_of_program P hP) hk₁ hk₂ hk₁' hk₂' hτ₁ hτ₂ h₁ h₂ p q hpq

/-- **The interpolated exponent** `chosenW = 2.0426…` at the aspect `chosenK = 3663/6337`. -/
theorem chosen_interpolation : RectangularAdmissibleExponent ℂ chosenK chosenW := by
  have h := rect_interp (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    thin_admissible wide_admissible 829933 716295 (by norm_num)
  have hk : (((829933 : ℕ) : ℝ) * (93 / 200) + ((716295 : ℕ) : ℝ) * (709 / 1000)) /
      (((829933 : ℕ) : ℝ) + ((716295 : ℕ) : ℝ)) = chosenK := by
    unfold chosenK; norm_num
  have hw : (((829933 : ℕ) : ℝ) * 2 + ((716295 : ℕ) : ℝ) * (523 / 250)) /
      (((829933 : ℕ) : ℝ) + ((716295 : ℕ) : ℝ)) = chosenW := by
    unfold chosenW chosenK; norm_num
  rw [hk, hw] at h
  exact h

/-- **`MainTarget`.** `ID_N`, `S4_N` and `perm4_N` have noncommutative circuits with `O(N^{1.690568 + ε})` gates over
`ℂ`, for every `ε > 0`. -/
theorem main_target : MainTarget :=
  mainTarget_of_remaining_bridges construction_target chosen_interpolation

end IDMM
