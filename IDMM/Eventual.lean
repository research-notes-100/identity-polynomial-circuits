/-
From word-length bounds to `IDBound`: circuits for `ID` on the `2^n` words of length `n` with
`≤ K·2^{n(c+ε)}` gates for all large `n` give `IDBound c`. Same conversion as `PauliCubes.id_circuit`:
take `n = max (clog₂ N) n₀`, so `N ≤ 2^n ≤ 2N·2^{n₀}`.
-/
import IDMM.Statements
import PauliCubes.IDCircuit
import PauliCubes.IDStar
import PauliCubes.Prop26
import PauliCubes.Perm4

namespace IDMM
open PauliCubes

universe u

/-- `IDBound` over an arbitrary field: a uniform constant and every positive slack. `IDBound c` is
`IDBoundF ℂ c`. -/
def IDBoundF (F : Type u) [Field F] (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → NCSizeLE (ID F N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

def S4BoundF (F : Type u) [Field F] (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → NCSizeLE (S4 F N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

def Perm4BoundF (F : Type u) [Field F] (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → NCSizeLE (perm4 F N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

theorem idBound_iff (c : ℝ) : IDBound c ↔ IDBoundF ℂ c := Iff.rfl

variable {F : Type u} [Field F]

theorem IDBoundF.mono {c d : ℝ} (h : IDBoundF F c) (hcd : c ≤ d) : IDBoundF F d := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := h ε hε
  refine ⟨C, hC, fun N hN => (h N hN).mono (Nat.floor_le_floor ?_)⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)) hC.le

theorem IDBoundF.s4 {c : ℝ} (h : IDBoundF F c) (hc : 1 ≤ c) : S4BoundF F c := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := h ε hε
  refine ⟨C + 200, by linarith, fun N hN => ?_⟩
  refine (ncSizeLE_S4_of_IDstar (ncSizeLE_IDstar (h N hN))).mono (Nat.le_floor ?_)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxN : (N : ℝ) ≤ (N : ℝ) ^ (c + ε) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hfl := Nat.floor_le (show 0 ≤ C * (N : ℝ) ^ (c + ε) by positivity)
  push_cast
  nlinarith

theorem S4BoundF.perm4 {c : ℝ} (h : S4BoundF F c) : Perm4BoundF F c := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := h ε hε
  refine ⟨275 * C, by positivity, fun N hN => ?_⟩
  refine (ncSizeLE_perm4_of_S4 (h N hN)).mono (Nat.le_floor ?_)
  have hfl := Nat.floor_le (show 0 ≤ C * (N : ℝ) ^ (c + ε) by positivity)
  push_cast
  nlinarith

/-- Circuits for `ID` on `2^n` words with `≤ K·2^{n(c+ε)}` gates for all large `n` give `IDBoundF F c`. -/
theorem idBoundF_of_eventual {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ s : ℕ,
      NCSizeLE (IDw F n) s ∧ (s : ℝ) ≤ K * (2 : ℝ) ^ ((n : ℝ) * (c + ε))) :
    IDBoundF F c := by
  intro ε hε
  obtain ⟨K, n₀, hK⟩ := h ε hε
  set e : ℝ := c + ε with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  refine ⟨K' * (2 : ℝ) ^ e * ((2 : ℝ) ^ n₀) ^ e, by positivity, fun N hN => ?_⟩
  set n := max (Nat.clog 2 N) n₀ with hn
  obtain ⟨s, hs, hsK⟩ := hK n (le_max_right _ _)
  have hcirc := ncSizeLE_ID_le (Nat.le_pow_clog one_lt_two N |>.trans
    (Nat.pow_le_pow_right two_pos (le_max_left _ _))) (ncSizeLE_ID_pow hs)
  refine hcirc.mono (Nat.le_floor ?_)
  -- `2^{n e} = (2^n)^e`, and `2^n ≤ 2 N 2^n₀`
  have hexp : (2 : ℝ) ^ ((n : ℝ) * e) = ((2 : ℝ) ^ n) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hpow : ((2 : ℝ) ^ n) ≤ 2 * N * (2 : ℝ) ^ n₀ := by
    have h1 : 2 ^ n ≤ 2 ^ Nat.clog 2 N * 2 ^ n₀ := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right two_pos (by omega)
    have h2' : 2 ^ Nat.clog 2 N * 2 ^ n₀ ≤ 2 * N * 2 ^ n₀ :=
      Nat.mul_le_mul_right _ (two_pow_clog_le hN)
    exact_mod_cast h1.trans h2'
  calc (s : ℝ) ≤ K * (2 : ℝ) ^ ((n : ℝ) * e) := hsK
    _ ≤ K' * (2 : ℝ) ^ ((n : ℝ) * e) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = K' * ((2 : ℝ) ^ n) ^ e := by rw [hexp]
    _ ≤ K' * (2 * N * (2 : ℝ) ^ n₀) ^ e := by gcongr
    _ = K' * (2 : ℝ) ^ e * ((2 : ℝ) ^ n₀) ^ e * (N : ℝ) ^ e := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]
        ring

/-- The ℂ case. -/
theorem idBound_of_eventual {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ s : ℕ,
      NCSizeLE (IDw ℂ n) s ∧ (s : ℝ) ≤ K * (2 : ℝ) ^ ((n : ℝ) * (c + ε))) :
    IDBound c :=
  idBoundF_of_eventual hc h

end IDMM
