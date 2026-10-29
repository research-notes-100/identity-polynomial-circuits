/-
`ID*_N = Σ_{i,j} x_i x_j x_i x_j`, Hrubeš's `ID_N` with each `y_i` identified with `x_i`. Substituting
variables for variables carries circuits gate for gate, so `ID*_N` is no harder than `ID_N`.
-/
import PauliCubes.Circuit

open Finset

namespace PauliCubes

variable (K : Type*) [CommRing K]

/-- `ID*_N = Σ_{i,j} x_i x_j x_i x_j`. -/
noncomputable def IDstar (N : ℕ) : FreeAlgebra K (Fin N) :=
  ∑ i : Fin N, ∑ j : Fin N, FreeAlgebra.ι K i * FreeAlgebra.ι K j * FreeAlgebra.ι K i * FreeAlgebra.ι K j

variable {K}

/-- `ID*_N` has a circuit as small as `ID_N`'s (substitute `y_i := x_i`). -/
theorem ncSizeLE_IDstar {N s : ℕ} (h : NCSizeLE (ID K N) s) : NCSizeLE (IDstar K N) s := by
  let φ : FreeAlgebra K (Fin N ⊕ Fin N) →ₐ[K] FreeAlgebra K (Fin N) :=
    FreeAlgebra.lift K (Sum.elim (FreeAlgebra.ι K) (FreeAlgebra.ι K))
  have hφ := h.map φ fun v => Or.inl ⟨Sum.elim id id v, by rcases v with v | v <;> simp [φ]⟩
  convert hφ using 1
  simp [IDstar, ID, φ]

end PauliCubes
