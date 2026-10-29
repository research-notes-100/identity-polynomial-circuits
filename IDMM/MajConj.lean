/-
Moving Majoranas by conjugation (cycle 055 §2).

A Majorana-coordinate vector `A = (s, a)` names the Pauli matrix `pmatM K A = pmat K (jwX s a) (jwZ s a)`.
For two distinct Majorana indices `k, l`, the gate `G = 1 + c·P_u` with `u = e_k + e_l` (and `c ∈ {1, i}` chosen
so that `(c P_u)² = −1`) satisfies `G · pmatM K A · G⁻¹ = λ · pmatM K (swap_{k,l} A)` with `λ ≠ 0`.
-/
import IDMM.MajTransvect

noncomputable section
namespace IDMM
open Finset Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- Majorana-coordinate vectors: symmetric bits and skew bits. -/
abbrev MV (n : ℕ) := Bits n × Bits n
/-- Majorana indices: `inl i` is the symmetric Majorana of qubit `i`, `inr i` the skew one. -/
abbrev MIdx (n : ℕ) := Fin n ⊕ Fin n

/-- The coordinate of `A` at a Majorana index. -/
def coord (A : MV n) : MIdx n → ZMod 2
  | .inl i => A.1 i
  | .inr i => A.2 i

/-- The vector with coordinates `f`. -/
def ofCoord (f : MIdx n → ZMod 2) : MV n := (fun i => f (.inl i), fun i => f (.inr i))

theorem coord_ofCoord (f : MIdx n → ZMod 2) : coord (ofCoord f) = f := by
  funext k; cases k <;> rfl

theorem ofCoord_coord (A : MV n) : ofCoord (coord A) = A := rfl

/-- The Pauli matrix of a Majorana-coordinate vector. -/
def pmatM (K : Type*) [Field K] (A : MV n) : Matrix (Bits n) (Bits n) K := pmat K (jwX A.1 A.2) (jwZ A.1 A.2)

theorem suffix_add (v w : Bits n) (j : Fin n) : suffix (v + w) j = suffix v j + suffix w j := by
  simp [suffix, sum_add_distrib]

theorem jwX_add (A B : MV n) : jwX (A + B).1 (A + B).2 = jwX A.1 A.2 + jwX B.1 B.2 := by
  funext j; simp only [jwX, Prod.fst_add, Prod.snd_add, Pi.add_apply]; abel

theorem jwZ_add (A B : MV n) : jwZ (A + B).1 (A + B).2 = jwZ A.1 A.2 + jwZ B.1 B.2 := by
  funext j
  simp only [jwZ, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [show A.1 + B.1 + (A.2 + B.2) = (A.1 + A.2) + (B.1 + B.2) by abel, suffix_add]
  abel

theorem dot_comm' (u v : Bits n) : dot u v = dot v u := by
  simp [dot, mul_comm]

/-- The commutation form in Majorana coordinates. -/
def spair (U A : MV n) : ZMod 2 :=
  (bsum U.1 + bsum U.2) * (bsum A.1 + bsum A.2) + dot U.1 A.1 + dot U.2 A.2

theorem pmatM_comm (U A : MV n) :
    pmatM K U * pmatM K A = (sgnB (spair U A) : K) • (pmatM K A * pmatM K U) := by
  rw [pmatM, pmatM, pmat_comm, spair, ← symp_jw, dot_comm' (jwZ A.1 A.2) (jwX U.1 U.2)]

/-- The Majorana basis vector of index `k`. -/
def mbasis (k : MIdx n) : MV n := ofCoord (Pi.single k 1)

theorem coord_mbasis (k j : MIdx n) : coord (mbasis k) j = if j = k then 1 else 0 := by
  rw [mbasis, coord_ofCoord, Pi.single_apply]

theorem bsum_add_bsum_eq_sum_coord (A : MV n) : bsum A.1 + bsum A.2 = ∑ k, coord A k := by
  rw [Fintype.sum_sum_type]; rfl

theorem dot_add_dot_eq_sum_coord (U A : MV n) :
    dot U.1 A.1 + dot U.2 A.2 = ∑ k, coord U k * coord A k := by
  rw [Fintype.sum_sum_type]; rfl

/-- The pair vector `e_k + e_l`. -/
def mpair (k l : MIdx n) : MV n := mbasis k + mbasis l

theorem coord_mpair (k l j : MIdx n) :
    coord (mpair k l) j = (if j = k then 1 else 0) + (if j = l then 1 else 0) := by
  rw [mpair, show coord (mbasis k + mbasis l) j = coord (mbasis k) j + coord (mbasis l) j by
    cases j <;> rfl, coord_mbasis, coord_mbasis]

theorem spair_mpair (k l : MIdx n) (A : MV n) :
    spair (mpair k l) A = coord A k + coord A l := by
  classical
  rw [spair, add_assoc, dot_add_dot_eq_sum_coord, bsum_add_bsum_eq_sum_coord]
  have h2 : ∑ j, coord (mpair k l) j = 0 := by
    simp only [coord_mpair, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    exact ZMod2_add_self 1
  rw [h2, zero_mul, zero_add]
  simp only [coord_mpair, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq',
    mem_univ, if_true]

/-- Swapping two Majorana coordinates. -/
def mswap (k l : MIdx n) (A : MV n) : MV n := ofCoord fun j => coord A (Equiv.swap k l j)

theorem mswap_eq (k l : MIdx n) (hkl : k ≠ l) (A : MV n) :
    mswap k l A = A + spair (mpair k l) A • mpair k l := by
  classical
  rw [spair_mpair]
  apply (show Function.Injective (coord (n := n)) from fun A B h => by
    rw [← ofCoord_coord A, ← ofCoord_coord B, h])
  funext j
  rw [mswap, coord_ofCoord]
  rw [show coord (A + (coord A k + coord A l) • mpair k l) j =
      coord A j + (coord A k + coord A l) * coord (mpair k l) j by cases j <;> rfl, coord_mpair]
  by_cases hjk : j = k
  · subst hjk
    rw [Equiv.swap_apply_left, if_pos rfl, if_neg hkl]
    generalize coord A j = p; generalize coord A l = q
    revert p q; decide
  · by_cases hjl : j = l
    · subst hjl
      rw [Equiv.swap_apply_right, if_neg hjk, if_pos rfl]
      generalize coord A j = p; generalize coord A k = q
      revert p q; decide
    · rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, if_neg hjk, if_neg hjl]; simp

/-! ## The gate -/

/-- The scalar making `(c P_u)² = −1`. -/
def gscal (K : Type*) [Field K] [SqrtNegOne K] (U : MV n) : K := if dot (jwX U.1 U.2) (jwZ U.1 U.2) = 1 then 1 else SqrtNegOne.i

/-- `K = c P_u`. -/
def gK (K : Type*) [Field K] [SqrtNegOne K] (U : MV n) : Matrix (Bits n) (Bits n) K := gscal K U • pmatM K U

theorem gK_sq [SqrtNegOne K] (U : MV n) : gK K U * gK K U = -1 := by
  rw [gK, smul_mul_smul_comm, pmatM, pmat_sq, gscal]
  rcases zmod2_cases (dot (jwX U.1 U.2) (jwZ U.1 U.2)) with h | h
  · rw [dot_comm' (jwZ _ _) (jwX _ _), h]
    simp only [show (0 : ZMod 2) ≠ 1 by decide, if_false, sgnB_zero]
    simp [smul_smul, SqrtNegOne.i_mul_i]
  · rw [dot_comm' (jwZ _ _) (jwX _ _), h, if_pos rfl]
    simp [sgnB]

/-- **One Majorana swap by conjugation.** -/
theorem gate_conj [NeZero (2 : K)] [SqrtNegOne K] (k l : MIdx n) (hkl : k ≠ l) (A : MV n) :
    ∃ lam : K, lam ≠ 0 ∧
      (1 + gK K (mpair k l)) * pmatM K A * ((2 : K)⁻¹ • (1 - gK K (mpair k l))) =
        lam • pmatM K (mswap k l A) := by
  have hK := gK_sq (K := K) (mpair k l)
  have hcomm := pmatM_comm (K := K) (mpair k l) A
  rcases zmod2_cases (spair (mpair k l) A) with h | h
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [conj_commute (K := K) _ _ hK (by rw [gK, smul_mul_assoc, hcomm, h, sgnB_zero, one_smul, mul_smul_comm]),
      mswap_eq k l hkl, h, zero_smul, add_zero, one_smul]
  · have hg : gscal K (mpair k l) ≠ 0 := by
      unfold gscal; split_ifs
      · exact one_ne_zero
      · intro h0; have := SqrtNegOne.i_mul_i (K := K); rw [h0, zero_mul] at this
        exact one_ne_zero (neg_eq_zero.mp this.symm)
    refine ⟨-(gscal K (mpair k l) * sgnB (dot (jwZ (mpair k l).1 (mpair k l).2) (jwX A.1 A.2))), ?_, ?_⟩
    · have : (sgnB (dot (jwZ (mpair k l).1 (mpair k l).2) (jwX A.1 A.2)) : K) ≠ 0 := by
        unfold sgnB; split_ifs <;> norm_num
      exact neg_ne_zero.mpr (mul_ne_zero hg this)
    · rw [conj_anticommute (K := K) _ _ hK (by
          rw [gK, smul_mul_assoc, hcomm, h, mul_smul_comm]
          simp [sgnB, zmod2_one_ne_zero])]
      rw [mswap_eq k l hkl, h, one_smul, gK, mul_smul_comm, pmatM, pmatM, pmatM, pmat_mul, jwX_add,
        jwZ_add, smul_smul]
      simp [neg_smul, mul_comm]

end IDMM
