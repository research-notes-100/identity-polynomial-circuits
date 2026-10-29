/-
**The 1.6692 bound in every characteristic other than two.**

Over every field `F` with `char F ≠ 2`, `ID_N`, `S4_N` and `perm4_N` have noncommutative circuits with
`O(N^{1.6692 + ε})` gates. The matrix-multiplication input is the rectangular curve `ω(1,k,1) ≤ 1 + k + 1/(4k)`
(Uznański), in the integer-scheme form formalized by Yang Zhou and Mingsheng Wang (`Matmul.RectangularRankBridge`): one integer
rank decomposition of `⟨a, b, a⟩` at aspect `11/18` maps into every field, so no characteristic is excluded and no
transfer principle is needed.
-/

import IDMM.SchemeOracle
import IDMM.CharPTools
import IDMM.FinalNumerics
import Matmul.RectangularRankBridge

noncomputable section
namespace IDMM
open OAI.MatrixMultiplication.Foundation
universe u

/-- An integer scheme gives a rank decomposition of the matrix tensor over every commutative ring. -/
theorem rankAtMost_of_scheme {K : Type*} [CommRing K] {a b ρ : ℕ}
    (alg : Matmul.UniversalRecursiveAlgorithm.Scheme a b a ρ)
    (h : alg.tensor = Matmul.IntegerBilinear.matrixTensor a b a) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a)) ρ := by
  refine ⟨fun q x => (alg.left q x : K), fun q y => (alg.right q y : K), fun q z => (alg.output q z : K), ?_⟩
  funext x y z
  have hxyz := congrFun (congrFun (congrFun h x) y) z
  simp only [Matmul.IntegerBilinear.Algorithm.tensor, Matmul.IntegerBilinear.matrixTensor,
    Tensor.rankOne] at hxyz
  simp only [Tensor.matrixCoefficients, Tensor.rankOne]
  have hcast := congrArg (Int.cast : ℤ → K) hxyz
  push_cast at hcast
  rw [← hcast]

/-- **`ID_N`, `S4_N`, `perm4_N` in `O(N^{1.6692+ε})` over every field of characteristic other than two.** -/
theorem id_bound_every_char (F : Type u) [Field F] (h2 : ringChar F ≠ 2) :
    IDBoundF F (4173 / 2500) ∧ S4BoundF F (4173 / 2500) ∧ Perm4BoundF F (4173 / 2500) := by
  set ε₀ : ℝ := 1 / 10 ^ 5 with hε₀
  obtain ⟨cert⟩ := Matmul.RectangularRankBridge.exists_scheme_certificate (k := 11 / 18) (by norm_num)
    (ε := ε₀) (by norm_num [hε₀])
  have hbound : Matmul.RectangularOptimization.rectangularBound (11 / 18) = 200 / 99 := by
    unfold Matmul.RectangularOptimization.rectangularBound; norm_num
  have hlt : Real.log (cert.ρ : ℝ) / Real.log (cert.a : ℝ) < 200 / 99 + ε₀ :=
    cert.rankExponent_lt.trans_eq (by rw [hbound])
  -- the scheme's size conditions
  have ha2 : 2 ≤ cert.a := cert.a_ge_two
  have haR : (1 : ℝ) < cert.a := by exact_mod_cast (show 1 < cert.a by omega)
  have hvol := Matmul.RecursiveCost.blockVolume_bounds cert.a cert.b cert.a
  have hab_vol : cert.a * cert.b ≤ cert.ρ := hvol.1.trans cert.volume
  have haa_vol : cert.a * cert.a ≤ cert.ρ := hvol.2.2.trans cert.volume
  have hρpos : (0 : ℝ) < cert.ρ := by
    have : 0 < cert.a * cert.a := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.trans_le haa_vol
  have hR : (cert.ρ : ℝ) ≤ (cert.a : ℝ) ^ (200 / 99 + ε₀) := by
    have hloga : 0 < Real.log cert.a := Real.log_pos haR
    rw [div_lt_iff₀ hloga] at hlt
    rw [← Real.exp_log hρpos, Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hin : ((cert.a * cert.b : ℕ) : ℝ) ≤ (cert.a : ℝ) ^ (200 / 99 + ε₀) :=
    (by exact_mod_cast hab_vol : ((cert.a * cert.b : ℕ) : ℝ) ≤ cert.ρ).trans hR
  have hout : (cert.a : ℝ) ^ (2 : ℕ) ≤ (cert.a : ℝ) ^ (200 / 99 + ε₀) := by
    have : ((cert.a * cert.a : ℕ) : ℝ) ≤ cert.ρ := by exact_mod_cast haa_vol
    rw [sq]; push_cast at this; exact this.trans hR
  have hμ0 : (1 : ℝ) / 2 < 18 / 29 := by norm_num
  have hμ1 : (18 : ℝ) / 29 < 1 := by norm_num
  have hab : (cert.a : ℝ) ^ (((1 : ℝ) - 18 / 29) / (18 / 29)) ≤ cert.b := by
    have : (1 - (18 : ℝ) / 29) / (18 / 29) = 11 / 18 := by norm_num
    rw [this]; exact cert.shape
  -- a finite extension holding `√−1`
  have hRkL := rankAtMost_of_scheme (K := AlgebraicClosure F) cert.alg cert.correct
  obtain ⟨E, _, _, hfin, ⟨i, hi⟩, hRkE⟩ := exists_ext_of_algClosure F hRkL
  haveI : SqrtNegOne E := ⟨i, hi⟩
  haveI : NeZero (2 : E) := ⟨Ring.two_ne_zero (by rw [← Algebra.ringChar_eq F E]; exact h2)⟩
  -- the construction over `E`, then descent
  have hw2 : (2 : ℝ) ≤ 200 / 99 + ε₀ := by norm_num [hε₀]
  have hE : IDBoundF E (constructionExponent (18 / 29) (200 / 99 + ε₀)) :=
    construction_gen hμ0 hμ1 hw2 fun ε hε => oracles_of_scheme hμ0 hμ1 hRkE ha2 hab hR hin hout hε
  have hle : constructionExponent (18 / 29) (200 / 99 + ε₀) ≤ 4173 / 2500 := by
    rw [constructionExponent_add]
    have h := uz_exponent_slack
    have hμ : (18 : ℝ) / 29 * ε₀ ≤ 1 / 10 ^ 5 := by rw [hε₀]; norm_num
    linarith
  have hF : IDBoundF F (4173 / 2500) := IDBoundF.of_ext (by norm_num) (hE.mono hle)
  have hs := hF.s4 (by norm_num)
  exact ⟨hF, hs, hs.perm4⟩

end IDMM
