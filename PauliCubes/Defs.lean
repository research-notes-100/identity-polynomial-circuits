/-
Definitions for the Pauli-cube circuit bound. This file imports Mathlib only: a reader who wants to
know what is claimed needs to read only these definitions and the theorem statements.

Notation: `n` qubits; a word `ν : Fin n → Fin 4` uses the letters I, X, Z, J = ZX = −XZ (indices 0, 1, 2, 3);
bit strings `x : Fin n → Fin 2` index the `2^n` coordinates of the vectors `X`, `Y`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Finset

namespace PauliCubes

/-- The one-qubit real Pauli matrices I, X, Z and J = [[0, 1], [-1, 0]], indexed by `Fin 4`;
`pauli1 K a s t` is the entry in row `s`, column `t`. -/
def pauli1 (K : Type*) [CommRing K] : Fin 4 → Fin 2 → Fin 2 → K :=
  ![![![1, 0], ![0, 1]], ![![0, 1], ![1, 0]], ![![1, 0], ![0, -1]], ![![0, 1], ![-1, 0]]]

/-- The real Pauli matrix of a word: the tensor product of its letters, as a function of the row and
column bit strings. -/
def pauliWord (K : Type*) [CommRing K] {n : ℕ} (ν : Fin n → Fin 4) (x y : Fin n → Fin 2) : K :=
  ∏ i, pauli1 K (ν i) (x i) (y i)

/-- The bilinear form `Xᵀ P_ν Y`. -/
def pauliForm (K : Type*) [CommRing K] {n : ℕ} (ν : Fin n → Fin 4)
    (X Y : (Fin n → Fin 2) → K) : K :=
  ∑ x, ∑ y, pauliWord K ν x y * X x * Y y

/-- The cube with letters `a i` or `b i` at each position `i`. -/
def cube {n : ℕ} (a b : Fin n → Fin 4) : Finset (Fin n → Fin 4) :=
  Fintype.piFinset fun i => ({a i, b i} : Finset (Fin 4))

/-- A cube: a product of two-letter sets, one pair of distinct letters per position. -/
def IsCube {n : ℕ} (Q : Finset (Fin n → Fin 4)) : Prop :=
  ∃ a b : Fin n → Fin 4, (∀ i, a i ≠ b i) ∧ Q = cube a b

/-- `S` is covered by at most `R` cubes. -/
def CubeCovered {n : ℕ} (S : Finset (Fin n → Fin 4)) (R : ℕ) : Prop :=
  ∃ C : Finset (Finset (Fin n → Fin 4)), C.card ≤ R ∧ (∀ Q ∈ C, IsCube Q) ∧ S ⊆ C.biUnion id

open scoped Classical in
/-- **A Pauli-cube identity with at most `R` cubes**: `(X₁² + ⋯)(Y₁² + ⋯) = Σ_ν w_ν (Xᵀ P_ν Y)²` for all
`X, Y : K^(2^n)`, and the words with `w_ν ≠ 0` are covered by at most `R` cubes. -/
def PauliCubeSOS (K : Type*) [CommRing K] (n R : ℕ) : Prop :=
  ∃ w : (Fin n → Fin 4) → K,
    (∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2) ∧
    CubeCovered (univ.filter fun ν => w ν ≠ 0) R

/-- **The target** (stated here; proved in a later module): for every `ε > 0` and all large `n`, a
Pauli-cube identity with at most `2^(n (0.727899 + ε))` cubes exists. Each cube's `2^n` forms cost
`2^n` multiplications (`cube_bilinear_rank`), so the forms cost `2^(n (1.727899 + ε))` in all. -/
def MainTarget (K : Type*) [CommRing K] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
    PauliCubeSOS K n ⌊(2 : ℝ) ^ ((n : ℝ) * (0.727899 + ε))⌋₊

end PauliCubes
