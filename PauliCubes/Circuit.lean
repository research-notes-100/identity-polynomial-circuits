/-
Composing circuits. `Reach inp B S s`: starting from the available values `B`, at most `s` further gates
make every value of `S` available. Sequential and parallel composition add the gate counts; ring
homomorphisms that send inputs to inputs carry circuits along; and a circuit over 2×2 matrices whose
inputs have input entries is simulated entrywise with 12 gates per gate.
-/
import PauliCubes.CircuitDefs
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace PauliCubes

variable {R : Type*} [Ring R] {inp : Set R}

theorem IsGate.mono {B B' : Set R} {g : R} (h : IsGate inp B g) (hB : B ⊆ B') : IsGate inp B' g := by
  rcases h with h | ⟨p, hp, q, hq, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hB hp, q, hB hq, h⟩

theorem Builds.mono : ∀ {gs : List R} {B B' : Set R}, Builds inp B gs → B ⊆ B' → Builds inp B' gs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, ⟨hg, hgs⟩, hB => ⟨hg.mono hB, hgs.mono (Set.insert_subset_insert hB)⟩

theorem Builds.append : ∀ {gs hs : List R} {B : Set R}, Builds inp B gs →
    Builds inp (B ∪ {x | x ∈ gs}) hs → Builds inp B (gs ++ hs)
  | [], _, B, _, h => by simpa using h
  | g :: gs, hs, B, ⟨hg, hgs⟩, h => by
    refine ⟨hg, hgs.append (h.mono ?_)⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Set.mem_insert_of_mem _ hx)
    · simp only [Set.mem_ofPred_eq, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl (Set.mem_insert _ _)
      · exact Or.inr hx

/-- From the values `B`, at most `s` further gates make every value of `S` available. -/
def Reach (inp B S : Set R) (s : ℕ) : Prop :=
  ∃ gs : List R, Builds inp B gs ∧ gs.length ≤ s ∧ S ⊆ B ∪ {x | x ∈ gs}

namespace Reach

variable {B B' S S' T : Set R} {s s' t : ℕ}

theorem refl (h : S ⊆ B) : Reach inp B S 0 :=
  ⟨[], trivial, le_rfl, fun _ hx => Or.inl (h hx)⟩

theorem mono (h : Reach inp B S s) (hB : B ⊆ B') (hS : S' ⊆ S) (hs : s ≤ s') :
    Reach inp B' S' s' := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  refine ⟨gs, hb.mono hB, hl.trans hs, fun x hx => ?_⟩
  rcases hc (hS hx) with h | h
  · exact Or.inl (hB h)
  · exact Or.inr h

theorem trans (h₁ : Reach inp B S s) (h₂ : Reach inp (B ∪ S) T t) : Reach inp B (S ∪ T) (s + t) := by
  obtain ⟨gs, hb, hl, hc⟩ := h₁
  obtain ⟨hs, hb', hl', hc'⟩ := h₂
  have hsub : B ∪ S ⊆ B ∪ {x | x ∈ gs} := Set.union_subset Set.subset_union_left hc
  refine ⟨gs ++ hs, hb.append (hb'.mono hsub), by simp; omega, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rcases hc hx with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_append_left _ h)
  · rcases hc' hx with h | h
    · rcases hsub h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · exact Or.inr (List.mem_append_right _ h)

/-- Sequential composition, keeping only the final values. -/
theorem seq (h₁ : Reach inp B S s) (h₂ : Reach inp (B ∪ S) T t) : Reach inp B T (s + t) :=
  (h₁.trans h₂).mono le_rfl Set.subset_union_right le_rfl

/-- Parallel composition. -/
theorem union (h₁ : Reach inp B S s) (h₂ : Reach inp B T t) : Reach inp B (S ∪ T) (s + t) :=
  h₁.trans (h₂.mono Set.subset_union_left le_rfl le_rfl)

theorem gate {g : R} (h : IsGate inp B g) : Reach inp B {g} 1 :=
  ⟨[g], ⟨h, trivial⟩, le_rfl, fun x hx => Or.inr (by simp at hx; simp [hx])⟩

theorem input {g : R} (h : g ∈ inp) : Reach inp B {g} 1 := gate (Or.inl h)

theorem add {p q : R} (hp : p ∈ B) (hq : q ∈ B) : Reach inp B {p + q} 1 :=
  gate (Or.inr ⟨p, hp, q, hq, Or.inl rfl⟩)

theorem mul {p q : R} (hp : p ∈ B) (hq : q ∈ B) : Reach inp B {p * q} 1 :=
  gate (Or.inr ⟨p, hp, q, hq, Or.inr rfl⟩)

/-- Parallel composition over a finite family. -/
theorem biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) {S : ι → Set R} {t : ι → ℕ}
    (h : ∀ i ∈ s, Reach inp B (S i) (t i)) : Reach inp B (⋃ i ∈ s, S i) (∑ i ∈ s, t i) := by
  induction s using Finset.induction_on with
  | empty => exact refl (by simp)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a s)).union (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A finite sum of available values, given the constant `0` as an input. -/
theorem sum {ι : Type*} [DecidableEq ι] (h0 : (0 : R) ∈ inp) (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, p i ∈ B) : Reach inp B {∑ i ∈ s, p i} (s.card + 1) := by
  induction s using Finset.induction_on with
  | empty => simpa using input (B := B) h0
  | @insert a s ha ih =>
    have h₁ := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have h₂ : Reach inp (B ∪ {∑ i ∈ s, p i}) {p a + ∑ i ∈ s, p i} 1 :=
      add (Or.inl (hp a (Finset.mem_insert_self a s))) (Or.inr rfl)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    exact (h₁.seq h₂).mono le_rfl le_rfl (by omega)

/-- A linear combination of available values with input coefficients. -/
theorem linComb {ι : Type*} [DecidableEq ι] (h0 : (0 : R) ∈ inp) (s : Finset ι) {c p : ι → R}
    (hc : ∀ i ∈ s, c i ∈ inp) (hp : ∀ i ∈ s, p i ∈ B) :
    Reach inp B {∑ i ∈ s, c i * p i} (3 * s.card + 1) := by
  set C : Set R := ⋃ i ∈ s, ({c i} : Set R) with hC
  set P : Set R := ⋃ i ∈ s, ({c i * p i} : Set R) with hP
  have h₁ : Reach inp B C (∑ i ∈ s, 1) := biUnion s fun i hi => input (hc i hi)
  have h₂ : Reach inp (B ∪ C) P (∑ i ∈ s, 1) :=
    biUnion s fun i hi => mul (Or.inr (Set.mem_biUnion hi (Set.mem_singleton _))) (Or.inl (hp i hi))
  have h₃ := sum (B := B ∪ (C ∪ P)) h0 s (p := fun i => c i * p i)
    fun i hi => Or.inr (Or.inr (Set.mem_biUnion hi (Set.mem_singleton _)))
  refine ((h₁.trans h₂).seq h₃).mono le_rfl le_rfl ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  omega

end Reach

/-! ## Ring homomorphisms carry circuits -/

section Map

variable {R' : Type*} [Ring R'] {inp' : Set R'}

theorem Builds.map (φ : R →+* R') (hφ : φ '' inp ⊆ inp') :
    ∀ {gs : List R} {B : Set R}, Builds inp B gs → Builds inp' (φ '' B) (gs.map φ)
  | [], _, _ => trivial
  | g :: gs, B, ⟨hg, hgs⟩ => by
    refine ⟨?_, by simpa [Set.image_insert_eq] using hgs.map φ hφ⟩
    rcases hg with hg | ⟨p, hp, q, hq, h | h⟩
    · exact Or.inl (hφ ⟨g, hg, rfl⟩)
    · exact Or.inr ⟨φ p, ⟨p, hp, rfl⟩, φ q, ⟨q, hq, rfl⟩, Or.inl (by rw [h, map_add])⟩
    · exact Or.inr ⟨φ p, ⟨p, hp, rfl⟩, φ q, ⟨q, hq, rfl⟩, Or.inr (by rw [h, map_mul])⟩

theorem Reach.map (φ : R →+* R') (hφ : φ '' inp ⊆ inp') {B S : Set R} {s : ℕ}
    (h : Reach inp B S s) : Reach inp' (φ '' B) (φ '' S) s := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  refine ⟨gs.map φ, hb.map φ hφ, by simpa using hl, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases hc hx with h | h
  · exact Or.inl ⟨x, h, rfl⟩
  · exact Or.inr (List.mem_map_of_mem h)

end Map

/-! ## Simulating 2×2 matrix circuits entrywise -/

section Matrix

/-- Matrices all of whose entries lie in `S`. -/
def entrywise {m : ℕ} (S : Set R) : Set (Matrix (Fin m) (Fin m) R) := {M | ∀ i j, M i j ∈ S}

/-- All entries of the matrices in `T`. -/
def entries {m : ℕ} (T : Set (Matrix (Fin m) (Fin m) R)) : Set R := {x | ∃ M ∈ T, ∃ i j, x = M i j}

theorem reach_entries_gate {B : Set (Matrix (Fin 2) (Fin 2) R)} {BA : Set R} {g : Matrix (Fin 2) (Fin 2) R}
    (hg : IsGate (entrywise inp) B g) (hB : entries B ⊆ BA) : Reach inp BA (entries {g}) 12 := by
  have hent : entries {g} = ⋃ ij ∈ (univ : Finset (Fin 2 × Fin 2)), {g ij.1 ij.2} := by
    ext x
    simp [entries, eq_comm]
  rw [hent]
  have hB' : ∀ M ∈ B, ∀ i j, M i j ∈ BA := fun M hM i j => hB ⟨M, hM, i, j, rfl⟩
  rcases hg with hg | ⟨p, hp, q, hq, rfl | rfl⟩
  · exact (Reach.biUnion univ fun ij _ => Reach.input (hg ij.1 ij.2)).mono le_rfl le_rfl (by simp)
  · exact (Reach.biUnion univ fun ij _ => Reach.add (hB' p hp ij.1 ij.2) (hB' q hq ij.1 ij.2)).mono
      le_rfl le_rfl (by simp)
  · have h : ∀ ij ∈ (univ : Finset (Fin 2 × Fin 2)), Reach inp BA {(p * q) ij.1 ij.2} 3 := by
      intro ij _
      have h₁ := (Reach.mul (inp := inp) (hB' p hp ij.1 0) (hB' q hq 0 ij.2)).union
        (Reach.mul (inp := inp) (hB' p hp ij.1 1) (hB' q hq 1 ij.2))
      have h₂ : Reach inp (BA ∪ ({p ij.1 0 * q 0 ij.2} ∪ {p ij.1 1 * q 1 ij.2}))
          {p ij.1 0 * q 0 ij.2 + p ij.1 1 * q 1 ij.2} 1 :=
        Reach.add (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact h₁.seq h₂
    exact (Reach.biUnion univ h).mono le_rfl le_rfl (by simp)

/-- **Entrywise simulation.** A circuit over 2×2 matrices whose inputs have input entries is simulated
by a circuit computing all entries, with at most 12 gates per matrix gate. -/
theorem Builds.entries : ∀ {gs : List (Matrix (Fin 2) (Fin 2) R)} {B : Set (Matrix (Fin 2) (Fin 2) R)}
    {BA : Set R}, Builds (entrywise inp) B gs → PauliCubes.entries B ⊆ BA →
    Reach inp BA (PauliCubes.entries {x | x ∈ gs}) (12 * gs.length)
  | [], _, _, _, _ => Reach.refl (by simp [PauliCubes.entries])
  | g :: gs, B, BA, ⟨hg, hgs⟩, hB => by
    have h₁ := reach_entries_gate hg hB
    have hB₂ : PauliCubes.entries (insert g B) ⊆ BA ∪ PauliCubes.entries {g} := by
      rintro x ⟨M, hM, i, j, rfl⟩
      rcases hM with rfl | hM
      · exact Or.inr ⟨M, rfl, i, j, rfl⟩
      · exact Or.inl (hB ⟨M, hM, i, j, rfl⟩)
    have h₂ := Builds.entries hgs hB₂
    refine (h₁.trans h₂).mono le_rfl ?_ (by simp; omega)
    rintro x ⟨M, hM, i, j, rfl⟩
    simp only [List.mem_cons, Set.mem_ofPred_eq] at hM
    rcases hM with rfl | hM
    · exact Or.inl ⟨M, rfl, i, j, rfl⟩
    · exact Or.inr ⟨M, hM, i, j, rfl⟩

/-- One gate over `m × m` matrices, simulated entrywise: `m²` entries, each a sum of `m` products. -/
theorem reach_entries_gateN {m : ℕ} (h0 : (0 : R) ∈ inp) {B : Set (Matrix (Fin m) (Fin m) R)} {BA : Set R}
    {g : Matrix (Fin m) (Fin m) R} (hg : IsGate (entrywise inp) B g) (hB : entries B ⊆ BA) :
    Reach inp BA (entries {g}) (m * m * (2 * m + 1)) := by
  have hent : entries {g} = ⋃ ij ∈ (univ : Finset (Fin m × Fin m)), {g ij.1 ij.2} := by
    ext x
    simp [entries, eq_comm]
  rw [hent]
  have hB' : ∀ M ∈ B, ∀ i j, M i j ∈ BA := fun M hM i j => hB ⟨M, hM, i, j, rfl⟩
  have hcard : ∑ _ij ∈ (univ : Finset (Fin m × Fin m)), (2 * m + 1) = m * m * (2 * m + 1) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
  rcases hg with hg | ⟨p, hp, q, hq, rfl | rfl⟩
  · refine (Reach.biUnion univ fun ij _ => Reach.input (hg ij.1 ij.2)).mono le_rfl le_rfl ?_
    rw [← hcard]
    exact Finset.sum_le_sum fun _ _ => by omega
  · refine (Reach.biUnion univ fun ij _ => Reach.add (hB' p hp ij.1 ij.2) (hB' q hq ij.1 ij.2)).mono
      le_rfl le_rfl ?_
    rw [← hcard]
    exact Finset.sum_le_sum fun _ _ => by omega
  · have h : ∀ ij ∈ (univ : Finset (Fin m × Fin m)), Reach inp BA {(p * q) ij.1 ij.2} (2 * m + 1) := by
      intro ij _
      have h₁ : Reach inp BA (⋃ k ∈ (univ : Finset (Fin m)), {p ij.1 k * q k ij.2}) (∑ _k : Fin m, 1) :=
        Reach.biUnion univ fun k _ => Reach.mul (hB' p hp ij.1 k) (hB' q hq k ij.2)
      have h₂ := Reach.sum (B := BA ∪ ⋃ k ∈ (univ : Finset (Fin m)), {p ij.1 k * q k ij.2}) h0 univ
        (p := fun k => p ij.1 k * q k ij.2) fun k _ => Or.inr (Set.mem_biUnion (mem_univ k) rfl)
      rw [Matrix.mul_apply]
      refine (h₁.seq h₂).mono le_rfl le_rfl ?_
      simp
      omega
    rw [← hcard]
    exact Reach.biUnion univ h

/-- **Entrywise simulation, `m × m`.** A circuit over `m × m` matrices whose inputs have input entries is
simulated by a circuit computing all entries, with at most `m² (2m + 1)` gates per matrix gate. -/
theorem Builds.entriesN {m : ℕ} (h0 : (0 : R) ∈ inp) :
    ∀ {gs : List (Matrix (Fin m) (Fin m) R)} {B : Set (Matrix (Fin m) (Fin m) R)} {BA : Set R},
    Builds (entrywise inp) B gs → PauliCubes.entries B ⊆ BA →
    Reach inp BA (PauliCubes.entries {x | x ∈ gs}) (m * m * (2 * m + 1) * gs.length)
  | [], _, _, _, _ => Reach.refl (by simp [PauliCubes.entries])
  | g :: gs, B, BA, ⟨hg, hgs⟩, hB => by
    have h₁ := reach_entries_gateN h0 hg hB
    have hB₂ : PauliCubes.entries (insert g B) ⊆ BA ∪ PauliCubes.entries {g} := by
      rintro x ⟨M, hM, i, j, rfl⟩
      rcases hM with rfl | hM
      · exact Or.inr ⟨M, rfl, i, j, rfl⟩
      · exact Or.inl (hB ⟨M, hM, i, j, rfl⟩)
    have h₂ := Builds.entriesN h0 hgs hB₂
    refine (h₁.trans h₂).mono le_rfl ?_ (by simp only [List.length_cons]; ring_nf; omega)
    rintro x ⟨M, hM, i, j, rfl⟩
    simp only [List.mem_cons, Set.mem_ofPred_eq] at hM
    rcases hM with rfl | hM
    · exact Or.inl ⟨M, rfl, i, j, rfl⟩
    · exact Or.inr ⟨M, hM, i, j, rfl⟩

end Matrix

/-! ## Circuit size -/

theorem Reach.ncSizeLE {K V : Type*} [CommRing K] {f : FreeAlgebra K V} {s : ℕ}
    (h : Reach (ncInputs K V) ∅ {f} s) : NCSizeLE f s := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  refine ⟨gs, hb, hl, ?_⟩
  rcases hc rfl with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact h

/-! ## Basic facts about circuit size -/

section Size

variable {K : Type*} [CommRing K] {V V' : Type*}

theorem NCSizeLE.mono {f : FreeAlgebra K V} {s t : ℕ} (h : NCSizeLE f s) (hst : s ≤ t) :
    NCSizeLE f t := by
  obtain ⟨gs, hb, hl, hf⟩ := h
  exact ⟨gs, hb, hl.trans hst, hf⟩

/-- Algebra maps sending variables to inputs carry circuits, gate for gate. -/
theorem NCSizeLE.map (φ : FreeAlgebra K V →ₐ[K] FreeAlgebra K V')
    (hφ : ∀ v, φ (FreeAlgebra.ι K v) ∈ ncInputs K V') {f : FreeAlgebra K V} {s : ℕ}
    (h : NCSizeLE f s) : NCSizeLE (φ f) s := by
  obtain ⟨gs, hb, hl, hf⟩ := h
  have hinp : φ.toRingHom '' ncInputs K V ⊆ ncInputs K V' := by
    rintro _ ⟨x, ⟨v, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · exact hφ v
    · exact Or.inr ⟨c, (φ.commutes c).symm⟩
  have hb' := hb.map φ.toRingHom hinp
  rw [Set.image_empty] at hb'
  exact ⟨gs.map φ.toRingHom, hb', by simpa using hl, List.mem_map_of_mem hf⟩

/-- Every element of the free algebra has some circuit. -/
theorem exists_reach (f : FreeAlgebra K V) : ∃ s, Reach (ncInputs K V) ∅ {f} s := by
  induction f using FreeAlgebra.induction with
  | grade0 r => exact ⟨1, Reach.input (Or.inr ⟨r, rfl⟩)⟩
  | grade1 v => exact ⟨1, Reach.input (Or.inl ⟨v, rfl⟩)⟩
  | mul a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    exact ⟨s + t + 1, (hs.union ht).seq (Reach.mul (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    exact ⟨s + t + 1, (hs.union ht).seq (Reach.add (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))⟩

end Size

theorem NCSizeLE.reach {K V : Type*} [CommRing K] {f : FreeAlgebra K V} {s : ℕ} (h : NCSizeLE f s) :
    Reach (ncInputs K V) ∅ {f} s := by
  obtain ⟨gs, hb, hl, hf⟩ := h
  exact ⟨gs, hb, hl, fun x hx => Or.inr (by rw [Set.mem_singleton_iff.mp hx]; exact hf)⟩

end PauliCubes
