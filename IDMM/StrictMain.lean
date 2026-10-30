/-
Theorems 1.2 and 1.3 in Hrubeš's model read strictly (every gate has two different inputs).
-/
import IDMM.CharP
import IDMM.CircuitModel

namespace IDMM
open PauliCubes

universe u

private theorem target_nonneg : (0 : ℝ) ≤ targetExponent := by norm_num [targetExponent]

/-- **Theorem 1.2(a) over `ℂ`, strict model.** -/
theorem strict_main_target :
    StrictIDBoundF ℂ targetExponent ∧ StrictS4BoundF ℂ targetExponent ∧
      StrictPerm4BoundF ℂ targetExponent := by
  obtain ⟨h1, hs, hp⟩ := main_target
  exact ⟨StrictIDBoundF.of target_nonneg h1, StrictS4BoundF.of target_nonneg hs,
    StrictPerm4BoundF.of target_nonneg hp⟩

/-- **Theorem 1.2(a), every field of characteristic zero, strict model.** -/
theorem strict_main_target_char_zero (F : Type u) [Field F] [CharZero F] :
    StrictIDBoundF F targetExponent ∧ StrictS4BoundF F targetExponent ∧
      StrictPerm4BoundF F targetExponent := by
  obtain ⟨h1, hs, hp⟩ := main_target_char_zero F
  exact ⟨StrictIDBoundF.of target_nonneg h1, StrictS4BoundF.of target_nonneg hs,
    StrictPerm4BoundF.of target_nonneg hp⟩

/-- **Theorem 1.2(b), strict model.** -/
theorem strict_main_target_almost_every_char : ∃ S : Finset ℕ, ∀ (F : Type u) [Field F],
    ringChar F ≠ 2 → (ringChar F = 0 ∨ ringChar F ∉ S) →
    StrictIDBoundF F targetExponent ∧ StrictS4BoundF F targetExponent ∧
      StrictPerm4BoundF F targetExponent := by
  obtain ⟨S, hS⟩ := main_target_almost_every_char.{u}
  refine ⟨S, fun F _ h2 hch => ?_⟩
  obtain ⟨h1, hs, hp⟩ := hS F h2 hch
  exact ⟨StrictIDBoundF.of target_nonneg h1, StrictS4BoundF.of target_nonneg hs,
    StrictPerm4BoundF.of target_nonneg hp⟩

/-- **Theorem 1.3** (Pauli cubes, no fast matrix multiplication) as bound predicates. -/
theorem cubes_bound (K : Type u) [Field K] (h2 : (2 : K) ≠ 0) :
    IDBoundF K 1.727899 ∧ S4BoundF K 1.727899 ∧ Perm4BoundF K 1.727899 := by
  have lift : ∀ {W : ℕ → Type} (f : ∀ N, FreeAlgebra K (W N)),
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → NCSizeLE (f N) ⌊C * (N : ℝ) ^ (1.727899 + ε)⌋₊) →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        NCSizeLE (f N) ⌊C * (N : ℝ) ^ (1.727899 + ε)⌋₊ := by
    intro W f h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨max C 1, lt_max_of_lt_right one_pos, fun N hN => (hC N hN).mono (Nat.floor_le_floor ?_)⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  exact ⟨lift (ID K) fun ε hε => id_circuit h2 hε, lift (S4 K) fun ε hε => s4_circuit h2 hε,
    lift (perm4 K) fun ε hε => perm4_circuit h2 hε⟩

/-- **Theorem 1.3, strict model.** -/
theorem strict_cubes_bound (K : Type u) [Field K] (h2 : (2 : K) ≠ 0) :
    StrictIDBoundF K 1.727899 ∧ StrictS4BoundF K 1.727899 ∧ StrictPerm4BoundF K 1.727899 := by
  obtain ⟨h1, hs, hp⟩ := cubes_bound K h2
  have hc : (0 : ℝ) ≤ 1.727899 := by norm_num
  exact ⟨StrictIDBoundF.of hc h1, StrictS4BoundF.of hc hs, StrictPerm4BoundF.of hc hp⟩

end IDMM
