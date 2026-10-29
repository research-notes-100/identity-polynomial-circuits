/-
**Noncommutative circuits for `S_{4,N}` and `perm_{4,N}`** (Hrubeš's Corollary 27 for `k = 4`): `ID*_N`
inherits the circuits of `ID_N` (`ncSizeLE_IDstar`), Proposition 26 builds `S_{4,N}` from `ID*_N` with
`O(N)` more gates (`ncSizeLE_S4_of_IDstar`), and inequality (11) builds `perm_{4,N}` from `S_{4,N}` with
275 gates per gate (`ncSizeLE_perm4_of_S4`). Both have the exponent of `id_circuit`.
-/
import PauliCubes.IDCircuit
import PauliCubes.Prop26
import PauliCubes.Perm4

namespace PauliCubes

universe u

/-- **Noncommutative circuits for `S_{4,N}`.** Over every field with `2 ≠ 0`, for every `ε > 0` there is
`C` such that `S_{4,N}` has a noncommutative circuit with at most `C N^(1.727899 + ε)` gates for every
`N ≥ 1`. -/
theorem s4_circuit {K : Type u} [Field K] (h2 : (2 : K) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → NCSizeLE (S4 K N) ⌊C * (N : ℝ) ^ (1.727899 + ε)⌋₊ := by
  obtain ⟨C, hC⟩ := id_circuit h2 hε
  refine ⟨max C 0 + 200, fun N hN => ?_⟩
  refine (ncSizeLE_S4_of_IDstar (ncSizeLE_IDstar (hC N hN))).mono (Nat.le_floor ?_)
  set x : ℝ := (N : ℝ) ^ (1.727899 + ε) with hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxN : (N : ℝ) ≤ x := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hfl : (⌊C * x⌋₊ : ℝ) ≤ max C 0 * x := by
    calc (⌊C * x⌋₊ : ℝ) ≤ ⌊max C 0 * x⌋₊ :=
          Nat.cast_le.mpr (Nat.floor_le_floor (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by linarith)))
      _ ≤ max C 0 * x := Nat.floor_le (mul_nonneg (le_max_right _ _) (by linarith))
  push_cast
  nlinarith

/-- **Noncommutative circuits for `perm_{4,N}`.** Over every field with `2 ≠ 0`, for every `ε > 0` there
is `C` such that the permanent of a `4 × N` matrix of noncommuting variables has a noncommutative circuit
with at most `C N^(1.727899 + ε)` gates for every `N ≥ 1`. -/
theorem perm4_circuit {K : Type u} [Field K] (h2 : (2 : K) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → NCSizeLE (perm4 K N) ⌊C * (N : ℝ) ^ (1.727899 + ε)⌋₊ := by
  obtain ⟨C, hC⟩ := s4_circuit h2 hε
  refine ⟨275 * max C 0, fun N hN => ?_⟩
  refine (ncSizeLE_perm4_of_S4 (hC N hN)).mono (Nat.le_floor ?_)
  set x : ℝ := (N : ℝ) ^ (1.727899 + ε) with hx
  have hx0 : 0 ≤ x := by positivity
  have hfl : (⌊C * x⌋₊ : ℝ) ≤ max C 0 * x := by
    calc (⌊C * x⌋₊ : ℝ) ≤ ⌊max C 0 * x⌋₊ :=
          Nat.cast_le.mpr (Nat.floor_le_floor (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0))
      _ ≤ max C 0 * x := Nat.floor_le (mul_nonneg (le_max_right _ _) hx0)
  push_cast
  nlinarith

end PauliCubes
