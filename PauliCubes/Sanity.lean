/-
Checks that the definitions mean what they say: `PauliCubeSOS` is neither trivially true (no identity
uses zero cubes) nor unsatisfiable (on one qubit the two-square identity is a Pauli-cube identity with
one cube, the words I and J). For circuits: `ID_N` has the trivial circuit with `4N² + 2N + 1` gates,
the quadratic baseline that `id_circuit` improves, and no element is computed by zero gates.
-/
import PauliCubes.Defs
import PauliCubes.Circuit

open Finset

namespace PauliCubes

/-- No Pauli-cube identity uses zero cubes (in a nontrivial ring): the empty cover forces `w = 0`. -/
theorem not_pauliCubeSOS_zero (K : Type*) [CommRing K] [Nontrivial K] (n : ℕ) :
    ¬ PauliCubeSOS K n 0 := by
  classical
  rintro ⟨w, hid, C, hC, -, hcov⟩
  have hC0 : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hC)
  have hw : ∀ ν, w ν = 0 := by
    intro ν; by_contra h
    have : ν ∈ C.biUnion id := hcov (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp [hC0] at this
  have := hid (fun x => if x = 0 then 1 else 0) (fun x => if x = 0 then 1 else 0)
  simp [hw] at this

/-- On one qubit, `(X₀² + X₁²)(Y₀² + Y₁²) = (X₀Y₀ + X₁Y₁)² + (X₀Y₁ - X₁Y₀)²` is a Pauli-cube identity
with one cube: the words I and J, weight 1 each. -/
theorem pauliCubeSOS_one (K : Type*) [CommRing K] : PauliCubeSOS K 1 1 := by
  classical
  let I1 : Fin 1 → Fin 4 := fun _ => 0
  let J1 : Fin 1 → Fin 4 := fun _ => 3
  have hIJ : I1 ≠ J1 := fun h => by simpa [I1, J1] using congr_fun h 0
  have hs : ∀ g : (Fin 1 → Fin 2) → K, ∑ x, g x = g (fun _ => 0) + g (fun _ => 1) := by
    intro g
    rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp g, Fin.sum_univ_two]
    rfl
  refine ⟨fun ν => if ν = I1 ∨ ν = J1 then 1 else 0, ?_, ?_⟩
  · intro X Y
    rw [Fintype.sum_eq_add I1 J1 hIJ (fun ν hν => by simp [hν.1, hν.2])]
    simp only [pauliForm, pauliWord, hs, Fin.prod_univ_one]
    simp [I1, J1, pauli1, hIJ]
    ring
  · refine ⟨{cube I1 J1}, by simp, ?_, ?_⟩
    · intro Q hQ
      rw [Finset.mem_singleton] at hQ
      exact ⟨I1, J1, fun _ => by simp [I1, J1], hQ⟩
    · intro ν hν
      have h : ν = I1 ∨ ν = J1 := by
        by_contra h'; simp [h'] at hν
      simp only [Finset.mem_biUnion, Finset.mem_singleton, id, exists_eq_left, cube,
        Fintype.mem_piFinset, Finset.mem_insert]
      intro j
      rcases h with rfl | rfl <;> simp

/-- No element is computed by a circuit with zero gates. -/
theorem not_ncSizeLE_zero {K V : Type*} [CommRing K] (f : FreeAlgebra K V) : ¬ NCSizeLE f 0 := by
  rintro ⟨gs, -, hl, hf⟩
  rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hf
  exact List.not_mem_nil hf

/-- **The trivial circuit.** `ID_N` is computed with `4N² + 2N + 1` gates: the `2N` variables, three
products for each of the `N²` monomials, and their sum. -/
theorem id_trivial (K : Type*) [CommRing K] (N : ℕ) : NCSizeLE (ID K N) (4 * N ^ 2 + 2 * N + 1) := by
  classical
  let x : Fin N → FreeAlgebra K (Fin N ⊕ Fin N) := fun i => FreeAlgebra.ι K (Sum.inl i)
  let y : Fin N → FreeAlgebra K (Fin N ⊕ Fin N) := fun j => FreeAlgebra.ι K (Sum.inr j)
  let B : Set (FreeAlgebra K (Fin N ⊕ Fin N)) := (⋃ i ∈ (univ : Finset (Fin N)), {x i}) ∪
    ⋃ j ∈ (univ : Finset (Fin N)), {y j}
  have hx : ∀ i, x i ∈ B := fun i => Or.inl (Set.mem_biUnion (mem_univ i) (Set.mem_singleton _))
  have hy : ∀ j, y j ∈ B := fun j => Or.inr (Set.mem_biUnion (mem_univ j) (Set.mem_singleton _))
  have hin : Reach (ncInputs K (Fin N ⊕ Fin N)) ∅ B (N + N) := by
    have h1 := Reach.biUnion (inp := ncInputs K (Fin N ⊕ Fin N)) (B := ∅) (univ : Finset (Fin N))
      (S := fun i => {x i}) (t := fun _ => 1) fun i _ => Reach.input (Or.inl ⟨_, rfl⟩)
    have h2 := Reach.biUnion (inp := ncInputs K (Fin N ⊕ Fin N)) (B := ∅) (univ : Finset (Fin N))
      (S := fun j => {y j}) (t := fun _ => 1) fun j _ => Reach.input (Or.inl ⟨_, rfl⟩)
    exact (h1.union h2).mono le_rfl le_rfl (by simp)
  let m : Fin N × Fin N → FreeAlgebra K (Fin N ⊕ Fin N) := fun ij =>
    x ij.1 * y ij.2 * x ij.1 * y ij.2
  have hmono : ∀ ij ∈ (univ : Finset (Fin N × Fin N)),
      Reach (ncInputs K (Fin N ⊕ Fin N)) (∅ ∪ B) {m ij} 3 := by
    rintro ⟨i, j⟩ -
    have h1 : Reach (ncInputs K (Fin N ⊕ Fin N)) (∅ ∪ B) {x i * y j} 1 :=
      Reach.mul (Or.inr (hx i)) (Or.inr (hy j))
    have h2 : Reach (ncInputs K (Fin N ⊕ Fin N)) (∅ ∪ B ∪ {x i * y j}) {x i * y j * x i} 1 :=
      Reach.mul (Or.inr rfl) (Or.inl (Or.inr (hx i)))
    have h3 : Reach (ncInputs K (Fin N ⊕ Fin N)) (∅ ∪ B ∪ ({x i * y j} ∪ {x i * y j * x i}))
        {x i * y j * x i * y j} 1 :=
      Reach.mul (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (hy j)))
    exact (h1.trans h2).seq h3
  have hall := hin.seq (Reach.biUnion univ hmono)
  have hsum := Reach.sum (inp := ncInputs K (Fin N ⊕ Fin N))
    (B := ∅ ∪ ⋃ ij ∈ (univ : Finset (Fin N × Fin N)), {m ij}) (Or.inr ⟨0, map_zero _⟩) univ (p := m)
    fun ij _ => Or.inr (Set.mem_biUnion (mem_univ ij) (Set.mem_singleton _))
  have htot := hall.seq hsum
  have hid : ∑ ij : Fin N × Fin N, m ij = ID K N := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hid] at htot
  refine (htot.mono le_rfl le_rfl ?_).ncSizeLE
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  nlinarith

end PauliCubes
