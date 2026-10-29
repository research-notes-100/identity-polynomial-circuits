/-
Classes, shifts and blocks (cycle 055 §3).

A word of class `(a, b)` has Majorana vector `V = A + σ` where the shift `σ` complements the symmetric (skew) part
when `a > n − a` (`b > n − b`), so that `A` has weights `(min(a, n−a), min(b, n−b))`. A block is a pair `(U_s, U_a)`
of qubit sets; its Majoranas are `U_s ⊔ U_a`, and a fixed list of swaps moves them onto the first `m` qubits.
-/
import IDMM.MajBlockForm

noncomputable section
namespace IDMM
open Finset

variable {n m : ℕ}

/-- The support of a bit vector. -/
def supp (v : Bits n) : Finset (Fin n) := univ.filter fun i => v i = 1

theorem card_supp (v : Bits n) : (supp v).card = weight v := rfl

/-- The complement shift of one part. -/
def cshift (n a : ℕ) : Bits n := fun _ => if a ≤ n - a then 0 else 1

/-- The class shift. -/
def shiftCl (n a b : ℕ) : MV n := (cshift n a, cshift n b)

/-- The all-ones vector. -/
def ones : Bits n := fun _ => 1

theorem weight_add_ones (v : Bits n) : weight (v + ones) = n - weight v := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => v i = 1)
  rw [card_univ, Fintype.card_fin] at hsplit
  have : (univ.filter fun i : Fin n => (v + ones : Bits n) i = 1) = univ.filter fun i => ¬ v i = 1 :=
    filter_congr fun i _ => by
      show v i + 1 = 1 ↔ ¬ v i = 1
      rcases zmod2_cases (v i) with h | h <;> rw [h] <;> decide
  rw [weight, this]
  unfold weight at *
  omega

theorem weight_cshift (v : Bits n) (a : ℕ) (hv : weight v = a) :
    weight (v + cshift n a) = min a (n - a) := by
  unfold cshift
  split_ifs with h
  · rw [show (v + fun _ => (0 : ZMod 2)) = v from funext fun _ => by simp, hv, min_eq_left h]
  · rw [show (v + fun _ => (1 : ZMod 2)) = v + ones from rfl, weight_add_ones, hv, min_eq_right (by omega)]

/-- The Majorana vector of a word. -/
def majV (ν : Fin n → Fin 4) : MV n := (majS ν, majA ν)

/-- The block-relative vector of a word. -/
def relA (ν : Fin n → Fin 4) : MV n := majV ν + shiftCl n (classOf ν).1 (classOf ν).2

theorem majV_eq_relA_add (ν : Fin n → Fin 4) : majV ν = relA ν + shiftCl n (classOf ν).1 (classOf ν).2 := by
  rw [relA, add_assoc]
  have : shiftCl n (classOf ν).1 (classOf ν).2 + shiftCl n (classOf ν).1 (classOf ν).2 = 0 := by
    ext i <;> exact ZMod2_add_self _
  rw [this, add_zero]

theorem card_supp_relA (ν : Fin n → Fin 4) :
    (supp (relA ν).1).card = min (classOf ν).1 (n - (classOf ν).1) ∧
      (supp (relA ν).2).card = min (classOf ν).2 (n - (classOf ν).2) :=
  ⟨weight_cshift _ _ rfl, weight_cshift _ _ rfl⟩

/-! ## Blocks -/

/-- The Majoranas of a block. -/
def blockU (p : Finset (Fin n) × Finset (Fin n)) : Finset (MIdx n) := p.1.disjSum p.2

theorem card_blockU (p : Finset (Fin n) × Finset (Fin n)) : (blockU p).card = p.1.card + p.2.card :=
  card_disjSum _ _

theorem suppIn_blockU {A : MV n} {p : Finset (Fin n) × Finset (Fin n)}
    (h1 : supp A.1 ⊆ p.1) (h2 : supp A.2 ⊆ p.2) : SuppIn A (blockU p) := by
  intro k hk
  rcases k with i | i
  · exact inl_mem_disjSum.mpr (h1 (mem_filter.mpr ⟨mem_univ _, hk⟩))
  · exact inr_mem_disjSum.mpr (h2 (mem_filter.mpr ⟨mem_univ _, hk⟩))

theorem exists_moveL (hm : m ≤ n) (p : Finset (Fin n) × Finset (Fin n)) (hp : (blockU p).card = 2 * m) :
    ∃ L : List (MIdx n × MIdx n), (∀ q ∈ L, q.1 ≠ q.2) ∧ L.length ≤ 2 * m ∧
      ∀ A : MV n, SuppIn A (blockU p) → SuppIn (mswapList L A) (canon n m) := by
  classical
  obtain ⟨L, hL, hlen, hmove⟩ := exists_move _ (blockU p) (canon n m) (by rw [hp, card_canon hm]) rfl
  refine ⟨L, hL, hlen.trans ?_, hmove⟩
  rw [← hp]; exact card_le_card sdiff_subset

end IDMM
