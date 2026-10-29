/-
Noncommutative Pauli forms, for Hrubeš's Lemma 22. In an `L`-algebra with elements `X x`, `Y y`, the form
of a word `ν` is read in two orders, `f^xy = Σ P_ν[x,y] X_x Y_y` and `f^yx = Σ P_ν[x,y] Y_y X_x`, and with an
element inserted in the middle, `f ⋆ z = Σ P_ν[x,y] X_x z Y_y`. The combination
`f^[2] = ½ (f^xy f^xy + f ⋆ f^yx)` plays the role of the square `f²`: a commutative sum-of-squares identity
`Σ w_ν f_ν² = |X|²|Y|²` becomes `Σ w_ν f_ν^[2] = Σ_{x,y} X_x Y_y X_x Y_y`.
-/
import PauliCubes.Defs

open Finset

namespace PauliCubes

variable {L : Type*} [Field L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {n : ℕ}
  (X Y : (Fin n → Fin 2) → 𝒜)

/-- `f^xy = Σ_{x,y} P_ν[x,y] X_x Y_y`. -/
noncomputable def fxy (ν : Fin n → Fin 4) : 𝒜 := ∑ x, ∑ y, pauliWord L ν x y • (X x * Y y)

/-- `f^yx = Σ_{x,y} P_ν[x,y] Y_y X_x`. -/
noncomputable def fyx (ν : Fin n → Fin 4) : 𝒜 := ∑ x, ∑ y, pauliWord L ν x y • (Y y * X x)

/-- `f ⋆ z = Σ_{x,y} P_ν[x,y] X_x z Y_y`. -/
noncomputable def fstar (ν : Fin n → Fin 4) (z : 𝒜) : 𝒜 :=
  ∑ x, ∑ y, pauliWord L ν x y • (X x * z * Y y)

/-- `f^[2] = ½ (f^xy f^xy + f ⋆ f^yx)`. -/
noncomputable def f2 (ν : Fin n → Fin 4) : 𝒜 :=
  (2 : L)⁻¹ • (fxy (L := L) X Y ν * fxy (L := L) X Y ν + fstar (L := L) X Y ν (fyx (L := L) X Y ν))

end PauliCubes
