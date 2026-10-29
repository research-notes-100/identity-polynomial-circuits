/-
**Descent along a finite extension.** If `E` is a finite extension of `F`, a noncommutative circuit over
`E` for (the image of) a polynomial with coefficients in `F` gives a circuit over `F` with a constant
factor more gates, the constant depending only on `d = [E : F]`.

The regular representation `ρ : E → M_d(F)` (`Algebra.leftMulMatrix`) is the only input. The `d × d`
matrices over `FreeAlgebra F V` that commute with `ρ(E)` form an `E`-algebra `CL ρ` containing the scalar
matrices; the free `E`-algebra maps into it sending `x_v` to the scalar matrix `x_v`, and so sends the
image of `f` to the scalar matrix `f`. A circuit over `E` thus becomes a circuit over `CL ρ` whose inputs
have entries that are inputs over `F`, which entrywise simulation (`Builds.entriesN`) turns into a
circuit over `F` with `d² (2d + 1)` gates per gate, one of whose values is the diagonal entry `f`.

This generalizes `PauliCubes/Descent.lean` from `2 × 2` to `d × d`; injectivity of `ρ` is never used.
-/
import PauliCubes.Circuit
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open Finset PauliCubes

namespace IDMM

namespace ExtDescent

section Centralizer

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [Algebra F E] {V : Type*} {d : ℕ}
  (ρ : E →ₐ[F] Matrix (Fin d) (Fin d) F)

variable (F V d) in
/-- `d × d` matrices over the free algebra. -/
abbrev MatN := Matrix (Fin d) (Fin d) (FreeAlgebra F V)

/-- `ρ`, with the constants of `F` included in the free algebra. -/
noncomputable def ρA : E →ₐ[F] MatN F V d := (Algebra.ofId F (FreeAlgebra F V)).mapMatrix.comp ρ

theorem ρA_apply (c : E) (i j : Fin d) :
    ρA (V := V) ρ c i j = algebraMap F (FreeAlgebra F V) (ρ c i j) := rfl

/-- The matrices commuting with every `ρ c`. -/
noncomputable def CL : Subalgebra F (MatN F V d) := Subalgebra.centralizer F (Set.range (ρA (V := V) ρ))

theorem ρA_mem (c : E) : ρA (V := V) ρ c ∈ CL (V := V) ρ := by
  rw [CL, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨e, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

/-- `ρ` into the centralizer. -/
noncomputable def ρC : E →+* CL (V := V) ρ :=
  (ρA (V := V) ρ).toRingHom.codRestrict _ (ρA_mem ρ)

/-- The centralizer is an `E`-algebra through `ρ`. -/
noncomputable instance : Algebra E (CL (V := V) ρ) :=
  RingHom.toAlgebra' (ρC ρ) fun c x => Subtype.ext <|
    ((Subalgebra.mem_centralizer_iff F).mp x.2 _ ⟨c, rfl⟩)

theorem coe_algebraMap_CL (c : E) :
    ((algebraMap E (CL (V := V) ρ) c : CL (V := V) ρ) : MatN F V d) = ρA ρ c := rfl

/-- Scalar matrices over the free algebra commute with `ρ(E)`. -/
theorem scalar_mem_CL (a : FreeAlgebra F V) : Matrix.scalar (Fin d) a ∈ CL (V := V) ρ := by
  rw [CL, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ρA_apply]
  exact Algebra.commutes _ _

/-- A scalar matrix as an element of the centralizer. -/
noncomputable def scalarCL (a : FreeAlgebra F V) : CL (V := V) ρ :=
  ⟨Matrix.scalar (Fin d) a, scalar_mem_CL ρ a⟩

/-- `scalarCL` is a ring homomorphism. -/
noncomputable def scalarCLHom : FreeAlgebra F V →+* CL (V := V) ρ :=
  (Matrix.scalar (Fin d)).codRestrict _ (scalar_mem_CL ρ)

theorem scalarCLHom_apply (a : FreeAlgebra F V) : scalarCLHom ρ a = scalarCL ρ a := rfl

/-- Inputs in the centralizer: the constants of `E` and the scalar matrices of the variables. -/
def cInputs : Set (CL (V := V) ρ) :=
  Set.range (algebraMap E (CL (V := V) ρ)) ∪ Set.range fun v => scalarCL ρ (FreeAlgebra.ι F v)

/-- **Reading off an entry.** A circuit over `E` in the centralizer, ending at an element whose `(i, i)`
entry is `f`, gives a circuit over `F` for `f` with `d² (2d + 1)` gates per gate. -/
theorem ncSizeLE_of_reach_CL (i : Fin d) {z : CL (V := V) ρ} {f : FreeAlgebra F V}
    (hz : (z : MatN F V d) i i = f) {s : ℕ} (h : Reach (cInputs ρ) ∅ {z} s) :
    NCSizeLE f (d * d * (2 * d + 1) * s) := by
  have hinp : (CL (V := V) ρ).val.toRingHom '' cInputs ρ ⊆ entrywise (ncInputs F V) := by
    rintro _ ⟨x, hx, rfl⟩ i j
    rcases hx with ⟨c, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inr ⟨ρ c i j, rfl⟩
    · change Matrix.scalar (Fin d) (FreeAlgebra.ι F v) i j ∈ ncInputs F V
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr ⟨0, map_zero _⟩
  obtain ⟨gs, hb, hl, hc⟩ := h.map _ hinp
  rw [Set.image_empty] at hb hc
  have he := Builds.entriesN (inp := ncInputs F V) (Or.inr ⟨0, map_zero _⟩) (BA := ∅) hb
    (by rintro _ ⟨M, hM, -⟩; exact absurd hM (Set.notMem_empty M))
  apply Reach.ncSizeLE
  refine he.mono le_rfl ?_ (Nat.mul_le_mul_left _ hl)
  rintro _ rfl
  rcases hc ⟨z, rfl, rfl⟩ with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact ⟨_, h, i, i, hz.symm⟩

end Centralizer

section Transport

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [Algebra F E] {V : Type*} {d : ℕ}
  (ρ : E →ₐ[F] Matrix (Fin d) (Fin d) F)

variable (E) in
/-- Extension of scalars on the free algebra: the same polynomial, read with coefficients in `E`. -/
noncomputable def toExt : FreeAlgebra F V →ₐ[F] FreeAlgebra E V := FreeAlgebra.lift F (FreeAlgebra.ι E)

@[simp]
theorem toExt_ι (v : V) : toExt E (FreeAlgebra.ι F v) = FreeAlgebra.ι E v := by
  simp [toExt]

/-- The free `E`-algebra into the centralizer, sending each variable to its scalar matrix. -/
noncomputable def φ : FreeAlgebra E V →ₐ[E] CL (V := V) ρ :=
  FreeAlgebra.lift E fun v => scalarCL ρ (FreeAlgebra.ι F v)

/-- The image over `E` of a polynomial over `F` goes to its scalar matrix. -/
theorem φ_toExt (f : FreeAlgebra F V) : φ ρ (toExt E f) = scalarCL ρ f := by
  induction f using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F E (FreeAlgebra E V), AlgHom.commutes]
    apply Subtype.ext
    rw [coe_algebraMap_CL]
    ext i j
    rw [ρA_apply, AlgHom.commutes]
    simp only [Matrix.algebraMap_matrix_apply, scalarCL, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  | grade1 v => simp [φ]
  | mul a b ha hb =>
    rw [map_mul, map_mul, ha, hb, ← scalarCLHom_apply, ← scalarCLHom_apply, ← map_mul,
      scalarCLHom_apply]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, ← scalarCLHom_apply, ← scalarCLHom_apply, ← map_add,
      scalarCLHom_apply]

end Transport

end ExtDescent

open ExtDescent

/-- **Descent through a matrix representation.** If `E` maps to `d × d` matrices over `F` (`d ≥ 1`), a
circuit over `E` with `s` gates for the image of `f` gives a circuit over `F` for `f` with
`d² (2d + 1) s` gates. -/
theorem ncSizeLE_descent_of_rep {F : Type*} [CommRing F] {E : Type*} [CommRing E] [Algebra F E]
    {V : Type*} {d : ℕ} (ρ : E →ₐ[F] Matrix (Fin d) (Fin d) F) (i : Fin d) {f : FreeAlgebra F V}
    {s : ℕ} (h : NCSizeLE (toExt E f) s) : NCSizeLE f (d * d * (2 * d + 1) * s) := by
  have hφ : (φ (V := V) ρ).toRingHom '' ncInputs E V ⊆ cInputs ρ := by
    rintro _ ⟨x, ⟨v, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · exact Or.inr ⟨v, by simp [φ]⟩
    · exact Or.inl ⟨c, ((φ ρ).commutes c).symm⟩
  have hr := h.reach.map (φ ρ).toRingHom hφ
  rw [Set.image_empty, Set.image_singleton] at hr
  have hz : (φ ρ).toRingHom (toExt E f) = scalarCL ρ f := φ_toExt ρ f
  rw [hz] at hr
  exact ncSizeLE_of_reach_CL ρ i (by simp [scalarCL]) hr

/-- **Descent along a finite extension.** For a finite field extension `E / F` there is a constant `c`
(namely `d² (2d + 1)`, `d = [E : F]`) such that a noncommutative circuit over `E` with `s` gates for the
image of any polynomial `f` over `F` gives a circuit over `F` for `f` with `c s + c` gates. -/
theorem ncSizeLE_extDescent (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    ∃ c : ℕ, ∀ {V : Type*} (f : FreeAlgebra F V) (s : ℕ), NCSizeLE (toExt E f) s →
      NCSizeLE f (c * s + c) := by
  set d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  obtain ⟨i⟩ := b.index_nonempty
  refine ⟨d * d * (2 * d + 1), fun f s h => ?_⟩
  exact (ncSizeLE_descent_of_rep (Algebra.leftMulMatrix b) i h).mono (Nat.le_add_right _ _)

/-- `ID_N` over `F`, read over `E`, is `ID_N` over `E`. -/
theorem toExt_ID (F E : Type*) [Field F] [Field E] [Algebra F E] (N : ℕ) :
    toExt E (ID F N) = ID E N := by
  simp [ID, map_sum, map_mul]

/-- **Circuits for `ID_N` descend along a finite extension**, with a constant-factor loss independent
of `N`. -/
theorem ncSizeLE_ID_descent {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ c : ℕ, ∀ (N s : ℕ), NCSizeLE (ID E N) s → NCSizeLE (ID F N) (c * s + c) := by
  obtain ⟨c, hc⟩ := ncSizeLE_extDescent F E
  exact ⟨c, fun N s h => hc (ID F N) s (by rwa [toExt_ID])⟩

end IDMM
