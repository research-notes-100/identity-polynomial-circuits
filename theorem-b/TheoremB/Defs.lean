/-
The definitions in which the main theorems of `TheoremB.Corollaries` are stated. This file imports
Mathlib only: a reader who wants to know what is claimed needs to read only these definitions and
the theorem statements.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Defs

open Finset

namespace TheoremB

/-- **P(N) ≤ M over ℚ** for the alphabet `α`: the crossing [x = v][y = u] on `α` is a sum of `M`
terms, each g(x,y)·g'(u,v) or g(x,u)·g'(y,v), with rational values. -/
def PLE (α : Type) [DecidableEq α] (M : ℕ) : Prop :=
  ∃ (g g' : Fin M → α → α → ℚ) (col : Fin M → Bool),
    ∀ x y u v : α, (if x = v ∧ y = u then 1 else 0 : ℚ) =
      ∑ j, if col j then g j x u * g' j y v else g j x y * g' j u v

/-- **P(N) ≤ M over K**: as `PLE`, with values in a commutative ring K. -/
def PLEF (K : Type) [CommRing K] (α : Type) [DecidableEq α] (M : ℕ) : Prop :=
  ∃ (g g' : Fin M → α → α → K) (col : Fin M → Bool),
    ∀ x y u v : α, (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ j, if col j then g j x u * g' j y v else g j x y * g' j u v

/-- The bilinear form Σ_{i,j} f(i,j)·X_i·Y_j. -/
def bil {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Fin N → K) (X Y : Fin N → K) : K :=
  ∑ i, ∑ j, f i j * X i * Y j

/-- (X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of M products of two bilinear forms over K. -/
def ProdLE (K : Type) [CommRing K] (N M : ℕ) : Prop :=
  ∃ f f' : Fin M → Fin N → Fin N → K, ∀ X Y : Fin N → K,
    (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) = ∑ t, bil (f t) X Y * bil (f' t) X Y

/-- **Hurwitz's problem**: (X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of M squares of bilinear
forms over K (a composition formula of type [N, N, M]). -/
def SOSLE (K : Type) [CommRing K] (N M : ℕ) : Prop :=
  ∃ f : Fin M → Fin N → Fin N → K, ∀ X Y : Fin N → K,
    (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) = ∑ t, bil (f t) X Y ^ 2

/-- The index tuple that takes coordinates in `κ` from `b` and the others from `a`. -/
def mix {d n : ℕ} (κ : Finset (Fin d)) (a b : Fin d → Fin n) : Fin d → Fin n :=
  fun i => if i ∈ κ then b i else a i

/-- **PT-rank(I) ≤ M over K** (Rossman–Zhu, arXiv:2512.01227, Definition 3.4): the identity matrix
on `(Fin n)^d`, with entries `[a = b]`, is a sum of `M` matrices, each of which has rank 1 after the
partial transpose that swaps the coordinates in some `κ ⊆ [d]` between row and column. -/
def PTLE (K : Type) [CommRing K] (n d M : ℕ) : Prop :=
  ∃ (κ : Fin M → Finset (Fin d)) (g g' : Fin M → (Fin d → Fin n) → K),
    ∀ a b : Fin d → Fin n,
      (if a = b then 1 else 0 : K) = ∑ t, g t (mix (κ t) a b) * g' t (mix (κ t) b a)

/-! ### Two alphabets -/

/-- **P(N₁, N₂) ≤ M over K**, for the alphabets `α` (the letters x, v) and `β` (the letters y, u):
the crossing [x = v][y = u] is a sum of `M` terms, each g(x,y)·g'(v,u) (row-wise) or
g(x,u)·g'(v,y) (column-wise). -/
def PLER (K : Type) [CommRing K] (α β : Type) [DecidableEq α] [DecidableEq β] (M : ℕ) : Prop :=
  ∃ (g g' : Fin M → α → β → K) (col : Fin M → Bool),
    ∀ (x v : α) (y u : β), (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ j, if col j then g j x u * g' j v y else g j x y * g' j v u

/-- The bilinear form Σ_{i,j} f(i,j)·X_i·Y_j, with X ∈ K^{N₁} and Y ∈ K^{N₂}. -/
def bilR {K : Type} [CommRing K] {N₁ N₂ : ℕ} (f : Fin N₁ → Fin N₂ → K) (X : Fin N₁ → K)
    (Y : Fin N₂ → K) : K :=
  ∑ i, ∑ j, f i j * X i * Y j

/-- (X₁² + ⋯ + X_{N₁}²)(Y₁² + ⋯ + Y_{N₂}²) is a sum of M products of two bilinear forms over K. -/
def ProdLER (K : Type) [CommRing K] (N₁ N₂ M : ℕ) : Prop :=
  ∃ f f' : Fin M → Fin N₁ → Fin N₂ → K, ∀ (X : Fin N₁ → K) (Y : Fin N₂ → K),
    (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) = ∑ t, bilR (f t) X Y * bilR (f' t) X Y

/-- **Hurwitz's problem for two lengths**: (X₁² + ⋯ + X_{N₁}²)(Y₁² + ⋯ + Y_{N₂}²) is a sum of M
squares of bilinear forms over K (a composition formula of type [N₁, N₂, M]). -/
def SOSLER (K : Type) [CommRing K] (N₁ N₂ M : ℕ) : Prop :=
  ∃ f : Fin M → Fin N₁ → Fin N₂ → K, ∀ (X : Fin N₁ → K) (Y : Fin N₂ → K),
    (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) = ∑ t, bilR (f t) X Y ^ 2

end TheoremB
