/-
Noncommutative arithmetic circuits, in Hrubeš's model: a directed acyclic graph whose sources are
input variables or field constants and whose other nodes add, or multiply in a given order, two earlier
nodes; its size is the number of nodes. A circuit is recorded here as the list of its node values in
topological order, so no graph syntax is needed: each listed value must be an input or a constant, or
the sum or product of two values listed before it.

`ID N = Σ_{i,j} x_i y_j x_i y_j` is Hrubeš's identity polynomial in `2N` noncommuting variables, `S4 N`
is the noncommutative elementary symmetric polynomial of degree four, and `perm4 N` is the noncommutative
permanent of a `4 × N` matrix.
-/
import Mathlib.Algebra.FreeAlgebra

open Finset

namespace PauliCubes

section Generic

variable {R : Type*} [Ring R]

/-- `g` is a gate over the earlier values `B`: an input (from `inp`), or the sum or the product (in
either order) of two earlier values. -/
def IsGate (inp B : Set R) (g : R) : Prop :=
  g ∈ inp ∨ ∃ p ∈ B, ∃ q ∈ B, g = p + q ∨ g = p * q

/-- `gs` lists the values of successive gates, each a gate over `B` and the values listed before it. -/
def Builds (inp : Set R) : Set R → List R → Prop
  | _, [] => True
  | B, g :: gs => IsGate inp B g ∧ Builds inp (insert g B) gs

end Generic

variable (K : Type*) [CommRing K] (V : Type*)

/-- The inputs of a noncommutative circuit over `K` in the variables `V`: the variables and the
constants of `K`. -/
def ncInputs : Set (FreeAlgebra K V) :=
  Set.range (FreeAlgebra.ι K) ∪ Set.range (algebraMap K (FreeAlgebra K V))

variable {K V}

/-- **Circuit size.** `f` is computed by a noncommutative circuit over `K` with at most `s` gates. -/
def NCSizeLE (f : FreeAlgebra K V) (s : ℕ) : Prop :=
  ∃ gs : List (FreeAlgebra K V), Builds (ncInputs K V) ∅ gs ∧ gs.length ≤ s ∧ f ∈ gs

variable (K) in
/-- **The identity polynomial** `ID_N = Σ_{i,j} x_i y_j x_i y_j`, with variables `x = Sum.inl`,
`y = Sum.inr`. -/
noncomputable def ID (N : ℕ) : FreeAlgebra K (Fin N ⊕ Fin N) :=
  ∑ i : Fin N, ∑ j : Fin N, FreeAlgebra.ι K (Sum.inl i) * FreeAlgebra.ι K (Sum.inr j) *
    FreeAlgebra.ι K (Sum.inl i) * FreeAlgebra.ι K (Sum.inr j)

variable (K) in
/-- **The noncommutative elementary symmetric polynomial** `S_{4,N}`: the sum of `x_i x_j x_k x_l` over the
ordered quadruples of pairwise distinct indices. -/
noncomputable def S4 (N : ℕ) : FreeAlgebra K (Fin N) :=
  ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
      FreeAlgebra.ι K i * FreeAlgebra.ι K j * FreeAlgebra.ι K k * FreeAlgebra.ι K l
    else 0

variable (K) in
/-- **The rectangular permanent** `perm_{4,N}` of a `4 × N` matrix of noncommuting variables `x_{r,i}`
(variable `(r, i)`): the sum of `x_{0,i} x_{1,j} x_{2,k} x_{3,l}` over the ordered quadruples of pairwise
distinct columns. -/
noncomputable def perm4 (N : ℕ) : FreeAlgebra K (Fin 4 × Fin N) :=
  ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
      FreeAlgebra.ι K (0, i) * FreeAlgebra.ι K (1, j) * FreeAlgebra.ι K (2, k) * FreeAlgebra.ι K (3, l)
    else 0

end PauliCubes
