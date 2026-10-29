/-
The `2^n` forms of a Pauli cube have bilinear rank `2^n`, through Kronecker products of 2×2 matrices.
Over a field with `2 ≠ 0` and a square root `i` of `-1`, every pair of distinct one-qubit Pauli forms is
computed by two multiplications (`local_pair`); tensoring gives `cube_bilinear_rank`.
-/
import PauliCubes.Defs

open Finset

namespace PauliCubes

variable {K : Type*} [Field K]

/-- `S` has a common two-multiplication algorithm: `P_ν[s, t] = Σ_κ c_ν(κ) A[κ, s] B[κ, t]` for `ν ∈ S`. -/
def PairAlg (K : Type*) [Field K] (S : Finset (Fin 4)) : Prop :=
  ∃ (A B : Fin 2 → Fin 2 → K) (c : Fin 4 → Fin 2 → K),
    ∀ ν ∈ S, ∀ s t, pauli1 K ν s t = ∑ κ, c ν κ * A κ s * B κ t

theorem PairAlg.symm {a b : Fin 4} (h : PairAlg K {a, b}) : PairAlg K {b, a} := by
  rwa [Finset.pair_comm]

set_option hygiene false in
/-- Closes the entrywise identities of the local algorithms. -/
macro "close_local" : tactic => `(tactic| first
  | rfl | ring1
  | (ring_nf; simp [inv_mul_cancel₀ h2, mul_inv_cancel₀ h2]; done)
  | (ring_nf; rw [hi2]; ring_nf; simp [inv_mul_cancel₀ h2, mul_inv_cancel₀ h2]; done))

/-- I and X: Hadamard. -/
theorem pair_IX (h2 : (2 : K) ≠ 0) : PairAlg K {0, 1} := by
  refine ⟨![![1, 1], ![1, -1]], ![![1, 1], ![1, -1]], ![![2⁻¹, 2⁻¹], ![2⁻¹, -2⁻¹], 0, 0], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] <;> close_local

/-- I and Z: identity. -/
theorem pair_IZ : PairAlg K {0, 2} := by
  refine ⟨![![1, 0], ![0, 1]], ![![1, 0], ![0, 1]], ![![1, 1], 0, ![1, -1], 0], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] 

/-- I and J: (x0 ± i x1)(y0 ∓ i y1). -/
theorem pair_IJ (h2 : (2 : K) ≠ 0) {i : K} (hi2 : i ^ 2 = -1) : PairAlg K {0, 3} := by
  refine ⟨![![1, i], ![1, -i]], ![![1, -i], ![1, i]], ![![2⁻¹, 2⁻¹], 0, 0, ![i * 2⁻¹, -(i * 2⁻¹)]], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] <;> close_local

/-- X and Z: Z = J X, so the I–J algorithm with `B` composed with X. -/
theorem pair_XZ (h2 : (2 : K) ≠ 0) {i : K} (hi2 : i ^ 2 = -1) : PairAlg K {1, 2} := by
  refine ⟨![![1, i], ![1, -i]], ![![-i, 1], ![i, 1]], ![0, ![2⁻¹, 2⁻¹], ![i * 2⁻¹, -(i * 2⁻¹)], 0], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] <;> close_local

/-- X and J: J = Z X, so the I–Z algorithm with `B = X`. -/
theorem pair_XJ : PairAlg K {1, 3} := by
  refine ⟨![![1, 0], ![0, 1]], ![![0, 1], ![1, 0]], ![0, ![1, 1], 0, ![1, -1]], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] 

/-- Z and J: J = -X Z, so the I–X algorithm with `B` composed with Z. -/
theorem pair_ZJ (h2 : (2 : K) ≠ 0) : PairAlg K {2, 3} := by
  refine ⟨![![1, 1], ![1, -1]], ![![1, -1], ![1, 1]], ![0, 0, ![2⁻¹, 2⁻¹], ![-2⁻¹, 2⁻¹]], ?_⟩
  intro ν hν s t; simp only [Finset.mem_insert, Finset.mem_singleton] at hν
  rcases hν with rfl | rfl <;> fin_cases s <;> fin_cases t <;> simp [pauli1, Fin.sum_univ_two] <;> close_local


/-- Two one-qubit forms `a ≠ b` share a two-multiplication algorithm (over a field with `2 ≠ 0` and
`i * i = -1`). -/
theorem local_pair (h2 : (2 : K) ≠ 0) {i : K} (hi : i * i = -1) (a b : Fin 4) (hab : a ≠ b) :
    PairAlg K {a, b} := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  fin_cases a <;> fin_cases b <;> simp at hab <;>
    first
    | exact pair_IX h2 | exact (pair_IX h2).symm | exact pair_IZ | exact pair_IZ.symm
    | exact pair_IJ h2 hi2 | exact (pair_IJ h2 hi2).symm | exact pair_XZ h2 hi2 | exact (pair_XZ h2 hi2).symm
    | exact pair_XJ | exact pair_XJ.symm | exact pair_ZJ h2 | exact (pair_ZJ h2).symm

/-- **Cube rank.** The forms of a cube are computed by `2^n` products of linear forms,
`Xᵀ P_ν Y = Σ_k c_ν(k) (A X)_k (B Y)_k`, where `A` and `B` are Kronecker products of 2×2 matrices
(so each is applied in `O(n 2^n)` operations). Needs `2 ≠ 0` and `i * i = -1`. -/
theorem cube_bilinear_rank (h2 : (2 : K) ≠ 0) {i : K} (hi : i * i = -1) {n : ℕ}
    (a b : Fin n → Fin 4) (hab : ∀ j, a j ≠ b j) :
    ∃ (A B : Fin n → Fin 2 → Fin 2 → K) (c : (Fin n → Fin 4) → (Fin n → Fin 2) → K),
      ∀ ν ∈ cube a b, ∀ X Y : (Fin n → Fin 2) → K,
        pauliForm K ν X Y = ∑ k : Fin n → Fin 2,
          c ν k * (∑ x, (∏ j, A j (k j) (x j)) * X x) * (∑ y, (∏ j, B j (k j) (y j)) * Y y) := by
  classical
  have hloc := fun j => local_pair h2 hi (a j) (b j) (hab j)
  simp only [PairAlg] at hloc
  choose A B c hc using hloc
  refine ⟨A, B, fun ν k => ∏ j, c j (ν j) (k j), ?_⟩
  intro ν hν X Y
  have hmem : ∀ j, ν j ∈ ({a j, b j} : Finset (Fin 4)) := fun j => Fintype.mem_piFinset.mp hν j
  have hword : ∀ x y : Fin n → Fin 2, pauliWord K ν x y =
      ∑ k : Fin n → Fin 2, ∏ j, (c j (ν j) (k j) * A j (k j) (x j) * B j (k j) (y j)) := by
    intro x y
    rw [pauliWord, Finset.prod_congr rfl fun j _ => hc j (ν j) (hmem j) (x j) (y j),
      Finset.prod_univ_sum, Fintype.piFinset_univ]
  have e : ∀ k : Fin n → Fin 2, (∏ j, c j (ν j) (k j)) * (∑ x, (∏ j, A j (k j) (x j)) * X x) *
      (∑ y, (∏ j, B j (k j) (y j)) * Y y) =
      ∑ x, ∑ y, (∏ j, c j (ν j) (k j)) * ((∏ j, A j (k j) (x j)) * X x) *
        ((∏ j, B j (k j) (y j)) * Y y) := by
    intro k
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hR : (∑ k : Fin n → Fin 2, (∏ j, c j (ν j) (k j)) * (∑ x, (∏ j, A j (k j) (x j)) * X x) *
        (∑ y, (∏ j, B j (k j) (y j)) * Y y)) =
      ∑ x, ∑ y, ∑ k : Fin n → Fin 2, (∏ j, c j (ν j) (k j)) * ((∏ j, A j (k j) (x j)) * X x) *
        ((∏ j, B j (k j) (y j)) * Y y) := by
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  simp only [pauliForm, hword]
  rw [hR]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end PauliCubes
