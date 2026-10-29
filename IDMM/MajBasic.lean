/-
Bit coordinates and Majorana (Jordan–Wigner) coordinates for real Pauli words.

A word `ν : Fin n → Fin 4` (letters I, X, Z, J) has an x-part and a z-part in `Fin n → ZMod 2`, and its
matrix is `P_ν[x, y] = [y = x + x_ν] · (−1)^{z_ν · x}` (`pauliWord_eq`).

Jordan–Wigner: the `2n` Majoranas are `Z⋯Z X_j` (symmetric) and `Z⋯Z J_j` (skew). A word is, up to sign,
the product of the Majoranas in a set described by two bit vectors `s` (symmetric) and `a` (skew):
`x_j = s_j + a_j` and `z_j = a_j + Σ_{k>j} x_k` (`jwX`, `jwZ`). Its class is `(|s|, |a|)`.
-/
import PauliCubes.Defs
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace IDMM
open Finset PauliCubes

/-- Bit vectors of length `n`. Definitionally the same type as `Fin n → Fin 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The x-bit of a letter: I = 0, X = 1, Z = 0, J = 1. -/
def xbit : Fin 4 → ZMod 2 := ![0, 1, 0, 1]
/-- The z-bit of a letter: I = 0, X = 0, Z = 1, J = 1. -/
def zbit : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- A chosen square root of `−1` (the Majorana gates need one). -/
class SqrtNegOne (K : Type*) [Field K] where
  i : K
  i_mul_i : i * i = -1

instance : SqrtNegOne ℂ := ⟨Complex.I, Complex.I_mul_I⟩

/-- `±1` from a bit. -/
def sgnB {R : Type*} [Ring R] (k : ZMod 2) : R := if k = 0 then 1 else -1

theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
theorem zmod2_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by revert k; decide

section sgn
variable {R : Type*} [Ring R]

theorem sgnB_zero : (sgnB 0 : R) = 1 := by simp [sgnB]

theorem sgnB_add (j k : ZMod 2) : (sgnB (j + k) : R) = sgnB j * sgnB k := by
  rcases zmod2_cases j with rfl | rfl <;> rcases zmod2_cases k with rfl | rfl <;>
    simp [sgnB, zmod2_one_add_one, zmod2_one_ne_zero]

theorem sgnB_sq (k : ZMod 2) : (sgnB k : R) * sgnB k = 1 := by
  rcases zmod2_cases k with rfl | rfl <;> simp [sgnB, zmod2_one_ne_zero]

end sgn

theorem sgnB_sum {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (sgnB (∑ i ∈ s, f i) : R) = ∏ i ∈ s, sgnB (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgnB_zero]
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, sgnB_add, ih]

variable {n : ℕ} {K : Type*} [Field K]

/-- The x-part of a word. -/
def wX (ν : Fin n → Fin 4) : Bits n := fun i => xbit (ν i)
/-- The z-part of a word. -/
def wZ (ν : Fin n → Fin 4) : Bits n := fun i => zbit (ν i)

/-- The dot product over `ZMod 2`. -/
def dot (u v : Bits n) : ZMod 2 := ∑ i, u i * v i

theorem pauli1_eq (a : Fin 4) (s t : ZMod 2) :
    pauli1 K a s t = if t = s + xbit a then sgnB (zbit a * s) else 0 := by
  fin_cases a <;> fin_cases s <;> fin_cases t <;> rfl

/-- **The matrix of a word in bit coordinates.** `P_ν[x, y] = [y = x + x_ν] (−1)^{z_ν · x}`. -/
theorem pauliWord_eq (ν : Fin n → Fin 4) (x y : Bits n) :
    pauliWord K ν x y = if y = x + wX ν then sgnB (dot (wZ ν) x) else 0 := by
  classical
  simp only [pauliWord, pauli1_eq]
  by_cases h : y = x + wX ν
  · rw [if_pos h, dot, sgnB_sum]
    refine prod_congr rfl fun i _ => ?_
    rw [if_pos (by rw [h]; rfl)]
    simp [wZ, mul_comm]
  · rw [if_neg h]
    have : ∃ i, ¬ y i = x i + xbit (ν i) := by
      by_contra hc
      push Not at hc
      exact h (funext fun i => by simpa [wX] using hc i)
    obtain ⟨i, hi⟩ := this
    exact prod_eq_zero (mem_univ i) (by rw [if_neg hi])

/-! ## Jordan–Wigner coordinates -/

/-- The letter with x-bit `x` and z-bit `z`. -/
def letterOf (x z : ZMod 2) : Fin 4 := ⟨x.val + 2 * z.val, by
  have hx := ZMod.val_lt x; have hz := ZMod.val_lt z; omega⟩

theorem xbit_letterOf (x z : ZMod 2) : xbit (letterOf x z) = x := by
  fin_cases x <;> fin_cases z <;> rfl

theorem zbit_letterOf (x z : ZMod 2) : zbit (letterOf x z) = z := by
  fin_cases x <;> fin_cases z <;> rfl

theorem letterOf_bits (a : Fin 4) : letterOf (xbit a) (zbit a) = a := by
  fin_cases a <;> rfl

/-- The word with x-part `x` and z-part `z`. -/
def ofXZ (x z : Bits n) : Fin n → Fin 4 := fun i => letterOf (x i) (z i)

theorem wX_ofXZ (x z : Bits n) : wX (ofXZ x z) = x := funext fun i => xbit_letterOf _ _
theorem wZ_ofXZ (x z : Bits n) : wZ (ofXZ x z) = z := funext fun i => zbit_letterOf _ _
theorem ofXZ_wX_wZ (ν : Fin n → Fin 4) : ofXZ (wX ν) (wZ ν) = ν := funext fun i => letterOf_bits _

/-- The suffix sum `Σ_{k > j} v_k`. -/
def suffix (v : Bits n) (j : Fin n) : ZMod 2 := ∑ k ∈ univ.filter (fun k => j < k), v k

/-- Jordan–Wigner x-part: `x_j = s_j + a_j`. -/
def jwX (s a : Bits n) : Bits n := s + a
/-- Jordan–Wigner z-part: `z_j = a_j + Σ_{k > j} x_k`. -/
def jwZ (s a : Bits n) : Bits n := fun j => a j + suffix (s + a) j
/-- The word of the Majorana set `(s, a)`. -/
def jw (s a : Bits n) : Fin n → Fin 4 := ofXZ (jwX s a) (jwZ s a)

/-- The skew Majorana bits of a word: `a_j = z_j + Σ_{k > j} x_k`. -/
def majA (ν : Fin n → Fin 4) : Bits n := fun j => wZ ν j + suffix (wX ν) j
/-- The symmetric Majorana bits of a word: `s_j = x_j + a_j`. -/
def majS (ν : Fin n → Fin 4) : Bits n := wX ν + majA ν

theorem ZMod2_add_self (k : ZMod 2) : k + k = 0 := by fin_cases k <;> decide

theorem jw_maj (ν : Fin n → Fin 4) : jw (majS ν) (majA ν) = ν := by
  have hx : majS ν + majA ν = wX ν := by
    funext j; simp only [majS, Pi.add_apply]; rw [add_assoc, ZMod2_add_self, add_zero]
  have hz : jwZ (majS ν) (majA ν) = wZ ν := by
    funext j; simp only [jwZ, hx, majA]; rw [add_assoc, ZMod2_add_self, add_zero]
  rw [jw, jwX, hx, hz, ofXZ_wX_wZ]

theorem majA_jw (s a : Bits n) : majA (jw s a) = a := by
  funext j
  simp only [majA, jw, wX_ofXZ, wZ_ofXZ, jwZ, jwX]
  rw [add_assoc, ZMod2_add_self, add_zero]

theorem majS_jw (s a : Bits n) : majS (jw s a) = s := by
  rw [majS, majA_jw]
  funext j
  simp only [jw, wX_ofXZ, jwX, Pi.add_apply]
  rw [add_assoc, ZMod2_add_self, add_zero]

/-- The number of ones. -/
def weight (v : Bits n) : ℕ := (univ.filter fun i => v i = 1).card

/-- The Majorana class `(|s|, |a|)` of a word. -/
def classOf (ν : Fin n → Fin 4) : ℕ × ℕ := (weight (majS ν), weight (majA ν))

/-- Words and Majorana sets correspond bijectively. -/
def jwEquiv : Bits n × Bits n ≃ (Fin n → Fin 4) where
  toFun p := jw p.1 p.2
  invFun ν := (majS ν, majA ν)
  left_inv p := by simp [majS_jw, majA_jw]
  right_inv ν := jw_maj ν

end IDMM
