/-
Sanity checks of the definitions in `TheoremB.Defs`: they encode the classical problems and are not
satisfied trivially.

* `sos_two`: the two-square identity (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)² is a composition
  formula of type [2, 2, 2] in the sense of `SOSLE`.
* `sos_trivial`, `ple_trivial`: the trivial bounds, N² squares and N² terms. The bound N^{√2 + ε}
  of `hurwitz_le_rpow` and `p_le_rpow` improves on them.
* `not_sos_one_zero`, `not_ple_one_zero`: zero terms never suffice.
* `ptle_trivial`, `not_ptle_zero`: for `PTLE`, the trivial bound n^d (one rank-1 term per index)
  holds over every commutative ring, and zero terms never suffice over a field.
* `plef_trivial`, `not_plef_one_zero`: the same two checks for `PLEF` over any commutative ring
  (zero terms never suffice once 1 ≠ 0), so the positive-characteristic bound is not vacuous.
* `sos_two_zmod3`: over 𝔽₃, where −1 = 1² + 1², the two-square identity is a composition formula.
* `sosR_trivial`, `pler_trivial`, `not_sosR_one_zero`, `not_pler_one_zero`: the same checks for the
  two-alphabet definitions `SOSLER` and `PLER` (trivial bounds N₁N₂, and zero terms never suffice).
-/
import TheoremB.Defs
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

open Finset

namespace TheoremB

/-- The two-square identity (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)². -/
theorem sos_two : SOSLE ℂ 2 2 := by
  refine ⟨![![![1, 0], ![0, -1]], ![![0, 1], ![1, 0]]], fun X Y => ?_⟩
  simp [bil, Fin.sum_univ_two]
  ring

/-- The trivial formula (Σ X_i²)(Σ Y_j²) = Σ_{i,j} (X_i·Y_j)², with N² squares. -/
theorem sos_trivial (N : ℕ) : SOSLE ℂ N (N * N) := by
  refine ⟨fun t i j => if i = (finProdFinEquiv.symm t).1 ∧ j = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun X Y => ?_⟩
  have hb : ∀ p : Fin N × Fin N,
      bil (fun i j => if i = p.1 ∧ j = p.2 then (1 : ℂ) else 0) X Y = X p.1 * Y p.2 := by
    intro p
    simp [bil, ite_and]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p => (X p.1 * Y p.2) ^ 2) (fun t => by rw [hb]),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The trivial decomposition of the crossing, [x = v][y = u] = Σ_{a,b} [x = a][y = b]·[u = b][v = a],
with N² row-wise rank-1 terms. -/
theorem ple_trivial (N : ℕ) : PLE (Fin N) (N * N) := by
  refine ⟨fun t x y => if x = (finProdFinEquiv.symm t).1 ∧ y = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun t u v => if u = (finProdFinEquiv.symm t).2 ∧ v = (finProdFinEquiv.symm t).1 then 1 else 0,
    fun _ => false, fun x y u v => ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin N × Fin N => (if x = p.1 ∧ y = p.2 then (1 : ℚ) else 0) *
      (if u = p.2 ∧ v = p.1 then 1 else 0)) (fun t => rfl), Fintype.sum_prod_type]
  by_cases hxv : x = v <;> by_cases hyu : y = u <;> simp [ite_and, hxv, hyu]

/-- Zero squares never suffice. -/
theorem not_sos_one_zero : ¬ SOSLE ℂ 1 0 := by
  rintro ⟨f, hf⟩
  simpa using hf (fun _ => 1) (fun _ => 1)

/-- Zero terms never suffice. -/
theorem not_ple_one_zero : ¬ PLE (Fin 1) 0 := by
  rintro ⟨g, g', col, hg⟩
  simpa using hg 0 0 0 0

/-- The trivial bound: the identity on `(Fin n)^d` is a sum of `n^d` rank-1 matrices `[a = c][b = c]`,
with no partial transposes. -/
theorem ptle_trivial (K : Type) [CommRing K] (n d : ℕ) : PTLE K n d (n ^ d) := by
  refine ⟨fun _ => ∅, fun t a => if a = finFunctionFinEquiv.symm t then 1 else 0,
    fun t b => if b = finFunctionFinEquiv.symm t then 1 else 0, fun a b => ?_⟩
  have hmix : ∀ x y : Fin d → Fin n, mix ∅ x y = x := fun x y => by
    funext i
    simp [mix]
  simp only [hmix]
  rw [Equiv.sum_comp finFunctionFinEquiv.symm
    (fun c => (if a = c then (1 : K) else 0) * (if b = c then 1 else 0))]
  by_cases h : a = b
  · subst h
    simp
  · rw [if_neg h, Finset.sum_eq_zero]
    intro c _
    by_cases ha : a = c
    · subst ha
      simp [Ne.symm h]
    · simp [ha]

/-- Zero terms never suffice. -/
theorem not_ptle_zero (K : Type) [Field K] {n : ℕ} (d : ℕ) (hn : 0 < n) : ¬ PTLE K n d 0 := by
  rintro ⟨κ, g, g', h⟩
  simpa using h (fun _ => ⟨0, hn⟩) (fun _ => ⟨0, hn⟩)

/-- The trivial decomposition of the crossing with values in any commutative ring, N² terms. -/
theorem plef_trivial (K : Type) [CommRing K] (N : ℕ) : PLEF K (Fin N) (N * N) := by
  refine ⟨fun t x y => if x = (finProdFinEquiv.symm t).1 ∧ y = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun t u v => if u = (finProdFinEquiv.symm t).2 ∧ v = (finProdFinEquiv.symm t).1 then 1 else 0,
    fun _ => false, fun x y u v => ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin N × Fin N => (if x = p.1 ∧ y = p.2 then (1 : K) else 0) *
      (if u = p.2 ∧ v = p.1 then 1 else 0)) (fun t => rfl), Fintype.sum_prod_type]
  by_cases hxv : x = v <;> by_cases hyu : y = u <;> simp [ite_and, hxv, hyu]

/-- Zero terms never suffice, over any ring with 1 ≠ 0. -/
theorem not_plef_one_zero (K : Type) [CommRing K] [Nontrivial K] : ¬ PLEF K (Fin 1) 0 := by
  rintro ⟨g, g', col, hg⟩
  simpa using hg 0 0 0 0

/-- Over 𝔽₃ the two-square identity is a composition formula of type [2, 2, 2]. -/
theorem sos_two_zmod3 : SOSLE (ZMod 3) 2 2 := by
  refine ⟨![![![1, 0], ![0, -1]], ![![0, 1], ![1, 0]]], fun X Y => ?_⟩
  simp [bil, Fin.sum_univ_two]
  ring

/-- The trivial bound for two lengths: N₁N₂ squares, one for each product X_i·Y_j. -/
theorem sosR_trivial (N₁ N₂ : ℕ) : SOSLER ℂ N₁ N₂ (N₁ * N₂) := by
  refine ⟨fun t i j => if i = (finProdFinEquiv.symm t).1 ∧ j = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun X Y => ?_⟩
  have hb : ∀ p : Fin N₁ × Fin N₂,
      bilR (fun i j => if i = p.1 ∧ j = p.2 then (1 : ℂ) else 0) X Y = X p.1 * Y p.2 := by
    intro p
    simp [bilR, ite_and]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p => (X p.1 * Y p.2) ^ 2) (fun t => by rw [hb]),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The trivial decomposition of the crossing on two alphabets, with N₁N₂ row-wise terms
[x = a][y = b]·[v = a][u = b]. -/
theorem pler_trivial (K : Type) [CommRing K] (N₁ N₂ : ℕ) : PLER K (Fin N₁) (Fin N₂) (N₁ * N₂) := by
  refine ⟨fun t x y => if x = (finProdFinEquiv.symm t).1 ∧ y = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun t v u => if v = (finProdFinEquiv.symm t).1 ∧ u = (finProdFinEquiv.symm t).2 then 1 else 0,
    fun _ => false, fun x v y u => ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin N₁ × Fin N₂ => (if x = p.1 ∧ y = p.2 then (1 : K) else 0) *
      (if v = p.1 ∧ u = p.2 then 1 else 0)) (fun t => rfl), Fintype.sum_prod_type]
  by_cases hxv : x = v <;> by_cases hyu : y = u <;> simp [ite_and, hxv, hyu]

/-- Zero squares never suffice for two lengths. -/
theorem not_sosR_one_zero : ¬ SOSLER ℂ 1 1 0 := by
  rintro ⟨f, hf⟩
  simpa using hf (fun _ => 1) (fun _ => 1)

/-- Zero terms never suffice for two alphabets, over any ring with 1 ≠ 0. -/
theorem not_pler_one_zero (K : Type) [CommRing K] [Nontrivial K] : ¬ PLER K (Fin 1) (Fin 1) 0 := by
  rintro ⟨g, g', col, hg⟩
  simpa using hg 0 0 0 0

end TheoremB
