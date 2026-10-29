/-
**The rectangular permanent from `S_{4,N}`** (Hrubeš–Wigderson–Yehudayoff, Theorem 7.1, for degree 4;
inequality (11) in Hrubeš 2026). Send each variable `x_i` to the 5×5 matrix `T_i` with the row variables
`x_{0,i}, …, x_{3,i}` on the superdiagonal. A product `x_i x_j x_k x_l` goes to `T_i T_j T_k T_l`, whose
top-right entry is `x_{0,i} x_{1,j} x_{2,k} x_{3,l}`, so the top-right entry of the image of `S_{4,N}` is
`perm_{4,N}`. A circuit for `S_{4,N}` maps to a circuit over 5×5 matrices, and reading off the entries costs
`5² · 11 = 275` gates per gate (`Builds.entriesN`).
-/
import PauliCubes.Circuit
import Mathlib.Data.Matrix.Basic

open Finset

namespace PauliCubes

variable {K : Type*} [CommRing K] {N : ℕ}

/-- The row whose variable sits in position `(a, a + 1)` of the superdiagonal. -/
def rowOf : Fin 5 → Fin 4 := ![0, 1, 2, 3, 0]

/-- The superdiagonal matrix of the column variables `x_{0,i}, …, x_{3,i}`. -/
noncomputable def supMat (i : Fin N) : Matrix (Fin 5) (Fin 5) (FreeAlgebra K (Fin 4 × Fin N)) :=
  Matrix.of fun a b => if (b : ℕ) = a + 1 then FreeAlgebra.ι K (rowOf a, i) else 0

/-- `x_i ↦ T_i`. -/
noncomputable def ordHom (K : Type*) [CommRing K] (N : ℕ) :
    FreeAlgebra K (Fin N) →ₐ[K] Matrix (Fin 5) (Fin 5) (FreeAlgebra K (Fin 4 × Fin N)) :=
  FreeAlgebra.lift K supMat

theorem supMat_prod_corner (i j k l : Fin N) :
    (supMat (K := K) i * supMat j * supMat k * supMat l : Matrix (Fin 5) (Fin 5) _) 0 4 =
      FreeAlgebra.ι K (0, i) * FreeAlgebra.ι K (1, j) * FreeAlgebra.ι K (2, k) *
        FreeAlgebra.ι K (3, l) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five, supMat, rowOf, mul_assoc]

/-- The top-right entry of the image of `S_{4,N}` is `perm_{4,N}`. -/
theorem ordHom_S4 : ordHom K N (S4 K N) 0 4 = perm4 K N := by
  simp only [S4, perm4, map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [map_mul, ordHom, FreeAlgebra.lift_ι_apply]
    exact supMat_prod_corner i j k l
  · simp

/-- **Inequality (11).** A circuit for `S_{4,N}` with `s` gates gives one for `perm_{4,N}` with `275 s`. -/
theorem ncSizeLE_perm4_of_S4 {s : ℕ} (h : NCSizeLE (S4 K N) s) : NCSizeLE (perm4 K N) (275 * s) := by
  have hinp : (ordHom K N).toRingHom '' ncInputs K (Fin N) ⊆ entrywise (m := 5) (ncInputs K (Fin 4 × Fin N)) := by
    rintro _ ⟨x, ⟨v, rfl⟩ | ⟨c, rfl⟩, rfl⟩ a b
    · change (ordHom K N) (FreeAlgebra.ι K v) a b ∈ ncInputs K (Fin 4 × Fin N)
      simp only [ordHom, FreeAlgebra.lift_ι_apply, supMat, Matrix.of_apply]
      split_ifs
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨0, map_zero _⟩
    · change (ordHom K N) (algebraMap K _ c) a b ∈ ncInputs K (Fin 4 × Fin N)
      rw [AlgHom.commutes, Matrix.algebraMap_matrix_apply]
      split_ifs
      · exact Or.inr ⟨c, rfl⟩
      · exact Or.inr ⟨0, map_zero _⟩
  obtain ⟨gs, hb, hl, hf⟩ := h.reach.map _ hinp
  rw [Set.image_empty] at hb hf
  have he := Builds.entriesN (m := 5) (inp := ncInputs K (Fin 4 × Fin N)) (Or.inr ⟨0, map_zero _⟩) hb
    (BA := ∅)
    (by rintro _ ⟨M, hM, -⟩; exact absurd hM (Set.notMem_empty M))
  apply Reach.ncSizeLE
  refine he.mono le_rfl ?_ (by omega)
  rintro _ rfl
  rcases hf ⟨S4 K N, rfl, rfl⟩ with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact ⟨_, h, 0, 4, (ordHom_S4).symm⟩

end PauliCubes
