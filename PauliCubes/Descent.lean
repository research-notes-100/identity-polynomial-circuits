/-
Adjoining a square root of `-1`. Every field `K` has an extension `L` containing `i` with `i² = -1`,
together with a `K`-algebra map `ρ : L → M₂(K)`: `L = K` if `K` already contains `i`, and otherwise
`L = K[X]/(X² + 1)` with `X ↦ [[0, 1], [-1, 0]]`. The 2×2 matrices over the free algebra that commute
with `ρ(L)` form an `L`-algebra containing the scalar matrices of the variables. A circuit over `L` there
becomes, entry by entry, a circuit over `K` with 12 gates per gate (`Builds.entries`).
-/
import PauliCubes.Circuit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Matrix.Basic

open Finset Polynomial

namespace PauliCubes

universe u

/-- **A square root of `-1` over `K`.** Some extension `L` of `K` contains `i` with `i * i = -1` and
maps to 2×2 matrices over `K` (stated as an eliminator). -/
theorem sqrt_neg_one_ext {K : Type u} [Field K] {P : Prop}
    (hP : ∀ (L : Type u) [Field L] [Algebra K L] (i : L), i * i = -1 →
      (L →ₐ[K] Matrix (Fin 2) (Fin 2) K) → P) : P := by
  by_cases h : ∃ i : K, i * i = -1
  · obtain ⟨i, hi⟩ := h
    exact hP K i hi (Algebra.ofId K _)
  · have h' : ∀ x : K, x * x ≠ -1 := fun x hx => h ⟨x, hx⟩
    set p : K[X] := X ^ 2 + 1 with hp
    have hdeg : p.natDegree = 2 := by
      rw [hp, show (1 : K[X]) = C 1 from C_1.symm, natDegree_X_pow_add_C]
    have hirr : Irreducible p := by
      refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => h' x ?_
      simp only [hp, IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at hx
      linear_combination hx
    have : Fact (Irreducible p) := ⟨hirr⟩
    let J : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]
    have hJ : aeval J p = 0 := by
      simp only [hp, map_add, map_pow, aeval_X, map_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [J, sq]
    refine hP (AdjoinRoot p) (AdjoinRoot.root p) ?_
      (Ideal.Quotient.liftₐ (Ideal.span {p}) (aeval J) fun a ha => ?_)
    · have := AdjoinRoot.eval₂_root p
      simp only [hp, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at this
      linear_combination this
    · obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hJ, mul_zero]

section Centralizer

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] {V : Type*}
  (ρ : L →ₐ[K] Matrix (Fin 2) (Fin 2) K)

variable (K V) in
/-- 2×2 matrices over the free algebra. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) (FreeAlgebra K V)

/-- `ρ`, with the constants of `K` included in the free algebra. -/
noncomputable def ρA : L →ₐ[K] Mat K V := (Algebra.ofId K (FreeAlgebra K V)).mapMatrix.comp ρ

theorem ρA_apply (c : L) (i j : Fin 2) :
    ρA (V := V) ρ c i j = algebraMap K (FreeAlgebra K V) (ρ c i j) := rfl

/-- The matrices commuting with every `ρ c`. -/
noncomputable def CL : Subalgebra K (Mat K V) := Subalgebra.centralizer K (Set.range (ρA (V := V) ρ))

theorem ρA_mem (c : L) : ρA (V := V) ρ c ∈ CL (V := V) ρ := by
  rw [CL, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨d, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

/-- `ρ` into the centralizer. -/
noncomputable def ρC : L →+* CL (V := V) ρ :=
  (ρA (V := V) ρ).toRingHom.codRestrict _ (ρA_mem ρ)

/-- The centralizer is an `L`-algebra through `ρ`. -/
noncomputable instance : Algebra L (CL (V := V) ρ) :=
  RingHom.toAlgebra' (ρC ρ) fun c x => Subtype.ext <|
    ((Subalgebra.mem_centralizer_iff K).mp x.2 _ ⟨c, rfl⟩)

theorem coe_algebraMap_CL (c : L) :
    ((algebraMap L (CL (V := V) ρ) c : CL (V := V) ρ) : Mat K V) = ρA ρ c := rfl

/-- Scalar matrices over the free algebra commute with `ρ(L)`. -/
theorem scalar_mem_CL (a : FreeAlgebra K V) : Matrix.scalar (Fin 2) a ∈ CL (V := V) ρ := by
  rw [CL, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ρA_apply]
  exact Algebra.commutes _ _

/-- A scalar matrix as an element of the centralizer. -/
noncomputable def scalarCL (a : FreeAlgebra K V) : CL (V := V) ρ := ⟨Matrix.scalar (Fin 2) a, scalar_mem_CL ρ a⟩

/-- `scalarCL` is a ring homomorphism. -/
noncomputable def scalarCLHom : FreeAlgebra K V →+* CL (V := V) ρ :=
  (Matrix.scalar (Fin 2)).codRestrict _ (scalar_mem_CL ρ)

theorem scalarCLHom_apply (a : FreeAlgebra K V) : scalarCLHom ρ a = scalarCL ρ a := rfl

/-- Inputs in the centralizer: the constants of `L` and the scalar matrices of the variables. -/
def cInputs : Set (CL (V := V) ρ) :=
  Set.range (algebraMap L (CL (V := V) ρ)) ∪ Set.range fun v => scalarCL ρ (FreeAlgebra.ι K v)

/-- **Descent.** A circuit over `L` in the centralizer, ending at an element whose top-left entry is
`f`, gives a circuit over `K` for `f` with 12 gates per gate. -/
theorem ncSizeLE_of_reach_CL {z : CL (V := V) ρ} {f : FreeAlgebra K V}
    (hz : (z : Mat K V) 0 0 = f) {s : ℕ} (h : Reach (cInputs ρ) ∅ {z} s) : NCSizeLE f (12 * s) := by
  have hinp : (CL (V := V) ρ).val.toRingHom '' cInputs ρ ⊆ entrywise (ncInputs K V) := by
    rintro _ ⟨x, hx, rfl⟩ i j
    rcases hx with ⟨c, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inr ⟨ρ c i j, rfl⟩
    · change Matrix.scalar (Fin 2) (FreeAlgebra.ι K v) i j ∈ ncInputs K V
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr ⟨0, map_zero _⟩
  obtain ⟨gs, hb, hl, hc⟩ := h.map _ hinp
  rw [Set.image_empty] at hb hc
  have he := hb.entries (BA := ∅) (by rintro _ ⟨M, hM, -⟩; exact absurd hM (Set.notMem_empty M))
  apply Reach.ncSizeLE
  refine he.mono le_rfl ?_ (Nat.mul_le_mul_left 12 hl)
  rintro _ rfl
  rcases hc ⟨z, rfl, rfl⟩ with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact ⟨_, h, 0, 0, hz.symm⟩

end Centralizer

end PauliCubes
