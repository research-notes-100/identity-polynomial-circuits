import TheoremB.Defs
import TheoremB.Corollaries
import Mathlib.Algebra.BigOperators.Fin

/-!
# Partial-transpose rank of identity matrices

Rossman and Zhu (arXiv:2512.01227, Section 6) bound the PT-rank of the identity matrix on
`(Fin n)^d` by feeding Hrubeš's `O(N^1.62)` into two steps: for two factors, PT-rank of the identity
is a sum-of-squares-type count; for `d = m + m` factors, group the coordinates into two halves.
Here the same two steps take Theorem B's `P(N) ≤ N^(√2+o(1))` as input, over every field of
characteristic 0.
-/

open Finset

namespace TheoremB

/-- Two factors: a crossing decomposition is a PT-rank decomposition of the identity, after
renaming `u ↔ v`. A term g(x,y)·g'(u,v) has rank 1; a term g(x,u)·g'(y,v) has rank 1 after
transposing the second coordinate. -/
theorem ptle_two (K : Type) [Field K] [CharZero K] {N M : ℕ} (h : PLE (Fin N) M) :
    PTLE K N 2 M := by
  obtain ⟨g, g', col, hg⟩ := h
  refine ⟨fun t => if col t then {1} else ∅, fun t c => (g t (c 0) (c 1) : K),
    fun t c => (g' t (c 1) (c 0) : K), fun a b => ?_⟩
  have hab : a = b ↔ a 0 = b 0 ∧ a 1 = b 1 := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · exact h0
      · exact h1
  have hI : (if a = b then (1 : K) else 0) =
      ((if a 0 = b 0 ∧ a 1 = b 1 then 1 else 0 : ℚ) : K) := by
    by_cases h : a = b
    · rw [if_pos h, if_pos (hab.1 h), Rat.cast_one]
    · rw [if_neg h, if_neg (fun h' => h (hab.2 h')), Rat.cast_zero]
  rw [hI, hg (a 0) (a 1) (b 1) (b 0), Rat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : col t = true
  · simp [hc, mix]
  · simp [hc, mix]

/-- The two halves of an index on `m + m` coordinates, each encoded as a number below `n ^ m`. -/
def halves {n m : ℕ} (a : Fin (m + m) → Fin n) : Fin 2 → Fin (n ^ m) :=
  ![finFunctionFinEquiv (fun i => a (Fin.castAdd m i)),
    finFunctionFinEquiv (fun i => a (Fin.natAdd m i))]

theorem halves_injective {n m : ℕ} : Function.Injective (halves (n := n) (m := m)) := by
  intro a b h
  have l := finFunctionFinEquiv.injective (congrFun h 0)
  have r := finFunctionFinEquiv.injective (congrFun h 1)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrFun l j
  · exact congrFun r j

/-- The half a coordinate belongs to. -/
def blk {m : ℕ} (i : Fin (m + m)) : Fin 2 := if (i : ℕ) < m then 0 else 1

theorem blk_castAdd {m : ℕ} (i : Fin m) : blk (Fin.castAdd m i) = 0 := by
  simp [blk]

theorem blk_addNat {m : ℕ} (i : Fin m) : blk (Fin.addNat i m) = 1 := by
  simp [blk]

/-- Grouping commutes with partial transposes: transposing a whole half of the coordinates is
transposing one coordinate of the grouped index. -/
theorem halves_mix {n m : ℕ} (κ : Finset (Fin 2)) (a b : Fin (m + m) → Fin n) :
    halves (mix (univ.filter fun i => blk i ∈ κ) a b) = mix κ (halves a) (halves b) := by
  funext j
  fin_cases j
  · by_cases h0 : (0 : Fin 2) ∈ κ
    · simp [halves, mix, blk_castAdd, h0]
    · simp [halves, mix, blk_castAdd, h0]
  · by_cases h1 : (1 : Fin 2) ∈ κ
    · simp [halves, mix, blk_addNat, h1]
    · simp [halves, mix, blk_addNat, h1]

/-- From two factors of size `n^m` to `m + m` factors of size `n`: the first step of
Rossman–Zhu's Proposition 6.1, which uses only the partial transposes of whole halves. -/
theorem ptle_of_halves {K : Type} [CommRing K] {n m M : ℕ} (h : PTLE K (n ^ m) 2 M) :
    PTLE K n (m + m) M := by
  obtain ⟨κ, g, g', hg⟩ := h
  refine ⟨fun t => univ.filter fun i => blk i ∈ κ t, fun t c => g t (halves c),
    fun t c => g' t (halves c), fun a b => ?_⟩
  have key := hg (halves a) (halves b)
  simp only [halves_injective.eq_iff] at key
  rw [key]
  refine Finset.sum_congr rfl fun t _ => ?_
  dsimp only
  rw [halves_mix, halves_mix]

/-- **Corollary 4(a), explicit form.** Over every field of characteristic 0, the identity matrix on
`(Fin n)^(m+m)` has PT-rank at most `(2 n^m)^√2 · (2 log₂ n^m + 2)^(3c/2)`, where `c` is Theorem B's
constant. Rossman–Zhu's Proposition 6.1 gives `n^(0.81 (m+m) + O(1))`. -/
theorem pt_rank_le : ∃ c : ℕ, ∀ (K : Type) [Field K] [CharZero K] (n m : ℕ), 2 ≤ n → 1 ≤ m →
    ∃ M : ℕ, PTLE K n (m + m) M ∧
      (M : ℝ) ≤ (2 * (n : ℝ) ^ m) ^ Real.sqrt 2 *
        (2 * Real.logb 2 ((n : ℝ) ^ m) + 2) ^ (3 * c / 2 : ℝ) := by
  obtain ⟨c, hc⟩ := p_le
  refine ⟨c, fun K _ _ n m hn hm => ?_⟩
  have hN : 2 ≤ n ^ m := le_trans hn (Nat.le_self_pow (by omega) n)
  obtain ⟨M, hM, hle⟩ := hc (n ^ m) hN
  refine ⟨M, ptle_of_halves (ptle_two K hM), ?_⟩
  simpa [Nat.cast_pow] using hle

/-- **Corollary 4(a), asymptotic form.** For every `ε > 0` there is `n₀` such that for all `n ≥ n₀`
and all `m ≥ 1`, over every field of characteristic 0, the identity matrix on `(Fin n)^(m+m)` has
PT-rank at most `n^((√2+ε)·m)`, that is `n^(d·(1/√2 + ε/2))` with `d = m + m` factors. -/
theorem pt_rank_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (K : Type) [Field K] [CharZero K] (n m : ℕ), n₀ ≤ n → 1 ≤ m →
      ∃ M : ℕ, PTLE K n (m + m) M ∧ (M : ℝ) ≤ (n : ℝ) ^ ((Real.sqrt 2 + ε) * m) := by
  obtain ⟨N₀, hN₀⟩ := p_le_rpow hε
  refine ⟨N₀, fun K _ _ n m hn hm => ?_⟩
  have hnm : N₀ ≤ n ^ m := le_trans hn (Nat.le_self_pow (by omega) n)
  obtain ⟨M, hM, hle⟩ := hN₀ (n ^ m) hnm
  refine ⟨M, ptle_of_halves (ptle_two K hM), ?_⟩
  calc (M : ℝ) ≤ ((n ^ m : ℕ) : ℝ) ^ (Real.sqrt 2 + ε) := hle
    _ = (n : ℝ) ^ ((Real.sqrt 2 + ε) * m) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), mul_comm]

end TheoremB
