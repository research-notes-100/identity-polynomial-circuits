/-
Pauli matrices in bit coordinates and transvection gates.

`pmat K α β` is the matrix `[y = x + α] (−1)^{β·x}`; it is the real Pauli matrix of the word `ofXZ α β`.
Products: `P_{(α,β)} P_{(α',β')} = (−1)^{β'·α} P_{(α+α', β+β')}`. A gate `G = 1 + K` with `K² = −1`
conjugates a matrix that commutes with `K` to itself, and one that anticommutes with `K` to `−P K`.
-/
import IDMM.MajClass
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
namespace IDMM
open Finset Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The Pauli matrix with x-part `α` and z-part `β`. -/
def pmat (K : Type*) [Field K] (α β : Bits n) : Matrix (Bits n) (Bits n) K :=
  fun x y => if y = x + α then sgnB (dot β x) else 0

theorem pauliWord_ofXZ (α β x y : Bits n) : PauliCubes.pauliWord K (ofXZ α β) x y = pmat K α β x y := by
  rw [pauliWord_eq, wX_ofXZ, wZ_ofXZ]; rfl

theorem pmat_mul (α β α' β' : Bits n) :
    pmat K α β * pmat K α' β' = (sgnB (dot β' α) : K) • pmat K (α + α') (β + β') := by
  classical
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [pmat]
  rw [Finset.sum_eq_single (x + α)]
  · rw [if_pos rfl]
    by_cases h : y = x + α + α'
    · rw [if_pos h, if_pos (show y = x + (α + α') by rw [h, add_assoc])]
      rw [dot_add_right, dot_add_left, sgnB_add, sgnB_add]
      ring
    · rw [if_neg h, if_neg (show ¬ y = x + (α + α') by rwa [← add_assoc])]; ring
  · intro w _ hw; rw [if_neg hw]; ring
  · simp

theorem pmat_zero : pmat K (0 : Bits n) 0 = 1 := by
  classical
  ext x y
  simp only [pmat, add_zero, one_apply]
  by_cases h : y = x
  · subst h; simp [dot, sgnB_zero]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem pmat_sq (α β : Bits n) : pmat K α β * pmat K α β = (sgnB (dot β α) : K) • (1 : Matrix (Bits n) (Bits n) K) := by
  rw [pmat_mul, bits_add_self, bits_add_self, pmat_zero]

/-- The commutation sign: `P_u P_v = (−1)^{symp(u,v)} P_v P_u`. -/
theorem pmat_comm (α β α' β' : Bits n) :
    pmat K α β * pmat K α' β' = (sgnB (dot β' α + dot β α') : K) • (pmat K α' β' * pmat K α β) := by
  rw [pmat_mul, pmat_mul, smul_smul, add_comm α' α, add_comm β' β, sgnB_add, mul_assoc, sgnB_sq,
    mul_one]

/-- **Conjugation by a gate `1 + G` with `K² = −1`.** -/
theorem conj_commute [NeZero (2 : K)] {R : Type*} [Ring R] [Algebra K R] (G P : R) (hK : G * G = -1) (hc : G * P = P * G) :
    (1 + G) * P * ((2 : K)⁻¹ • (1 - G)) = P := by
  have h2 : (2 : K)⁻¹ • (2 : R) = 1 := by
    rw [Algebra.smul_def, ← map_ofNat (algebraMap K R) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
      map_one]
  have : (1 + G) * P * (1 - G) = (2 : R) * P := by
    calc (1 + G) * P * (1 - G) = P + G * P - P * G - G * P * G := by noncomm_ring
      _ = P + G * P - P * G - P * (G * G) := by rw [hc, mul_assoc]
      _ = 2 * P := by rw [hK, hc]; noncomm_ring
  rw [mul_smul_comm, this, ← smul_mul_assoc, h2, one_mul]

theorem conj_anticommute [NeZero (2 : K)] {R : Type*} [Ring R] [Algebra K R] (G P : R) (hK : G * G = -1)
    (ha : G * P = -(P * G)) :
    (1 + G) * P * ((2 : K)⁻¹ • (1 - G)) = -(P * G) := by
  have h2 : (2 : K)⁻¹ • (2 : R) = 1 := by
    rw [Algebra.smul_def, ← map_ofNat (algebraMap K R) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
      map_one]
  have : (1 + G) * P * (1 - G) = (2 : R) * -(P * G) := by
    calc (1 + G) * P * (1 - G) = P + G * P - P * G - G * P * G := by noncomm_ring
      _ = P - P * G - P * G + P * (G * G) := by rw [ha]; noncomm_ring
      _ = 2 * -(P * G) := by rw [hK]; noncomm_ring
  rw [mul_smul_comm, this, ← smul_mul_assoc, h2, one_mul]

theorem gate_inv [NeZero (2 : K)] {R : Type*} [Ring R] [Algebra K R] (G : R) (hK : G * G = -1) :
    (1 + G) * ((2 : K)⁻¹ • (1 - G)) = 1 := by
  have := conj_commute (K := K) G 1 hK (by simp)
  simpa using this

end IDMM
