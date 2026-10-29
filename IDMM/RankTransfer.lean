import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.Analysis.Complex.Polynomial.Basic
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/-!
# Characteristic transfer of matrix-multiplication rank bounds

A rank decomposition of the matrix-multiplication tensor with `r` terms is a solution of a
finite system of polynomial equations with integer (`0`/`1`) coefficients in finitely many
unknowns. Its existence is therefore a first-order sentence in the language of rings.

If such a decomposition exists over `ℂ`, then the sentence holds in `ℂ`, hence (by completeness
of `ACF 0`) in every algebraically closed field of characteristic `0`, and by the Lefschetz
principle in every algebraically closed field of characteristic `p` for all but finitely many
primes `p`.
-/

noncomputable section

namespace IDMM
universe u

namespace RankTransfer

open FirstOrder FirstOrder.Language FirstOrder.Ring FirstOrder.Field
open OAI.MatrixMultiplication.Foundation

variable (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] (r : ℕ)

/-- The unknowns: the coefficients of the three factor families of an `r`-term decomposition. -/
abbrev Var := (Fin r × (A × B)) ⊕ ((Fin r × (B × C)) ⊕ (Fin r × (C × A)))

/-- The polynomial `∑ i, u i x * v i y * w i z` in the unknowns. -/
def lhs (x : A × B) (y : B × C) (z : C × A) : FreeCommRing (Var A B C r) :=
  ∑ i : Fin r, FreeCommRing.of (Sum.inl (i, x)) *
    FreeCommRing.of (Sum.inr (Sum.inl (i, y))) * FreeCommRing.of (Sum.inr (Sum.inr (i, z)))

/-- The matrix-multiplication coefficient as a constant polynomial. -/
def rhs (x : A × B) (y : B × C) (z : C × A) : FreeCommRing (Var A B C r) :=
  if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

/-- The system of equations `∑ i, u i x * v i y * w i z = T x y z` for all `x y z`. -/
def eqns : Language.ring.Formula (Var A B C r) :=
  Formula.iInf fun t : (A × B) × ((B × C) × (C × A)) =>
    Term.equal (termOfFreeCommRing (lhs A B C r t.1 t.2.1 t.2.2))
      (termOfFreeCommRing (rhs A B C r t.1 t.2.1 t.2.2))

/-- The sentence "the matrix-multiplication tensor `⟨A, B, C⟩` has rank at most `r`". -/
def rankSentence : Language.ring.Sentence :=
  Formula.iExs (Var A B C r) ((eqns A B C r).relabel Sum.inr)

omit [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem lift_lhs {K : Type*} [CommRing K] (val : Var A B C r → K)
    (x : A × B) (y : B × C) (z : C × A) :
    FreeCommRing.lift val (lhs A B C r x y z) =
      ∑ i : Fin r, val (Sum.inl (i, x)) * val (Sum.inr (Sum.inl (i, y))) *
        val (Sum.inr (Sum.inr (i, z))) := by
  simp only [lhs, map_sum, map_mul, FreeCommRing.lift_of]

omit [Fintype A] [Fintype B] [Fintype C] in
theorem lift_rhs {K : Type*} [CommRing K] (val : Var A B C r → K)
    (x : A × B) (y : B × C) (z : C × A) :
    FreeCommRing.lift val (rhs A B C r x y z) =
      Tensor.matrixCoefficients (K := K) A B C x y z := by
  unfold rhs Tensor.matrixCoefficients
  split_ifs <;> simp

theorem realize_rankSentence (K : Type*) [Field K] [CompatibleRing K] :
    K ⊨ rankSentence A B C r ↔
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) A B C) r := by
  simp only [Sentence.Realize, rankSentence, eqns, Formula.realize_iExs,
    Formula.realize_relabel, Formula.realize_iInf, Formula.realize_equal,
    realize_termOfFreeCommRing, Sum.elim_comp_inr]
  constructor
  · rintro ⟨val, hval⟩
    refine ⟨fun i x => val (Sum.inl (i, x)), fun i y => val (Sum.inr (Sum.inl (i, y))),
      fun i z => val (Sum.inr (Sum.inr (i, z))), ?_⟩
    funext x y z
    have := hval (x, y, z)
    rw [lift_lhs, lift_rhs] at this
    simp only [Tensor.rankOne]
    exact this.symm
  · rintro ⟨u, v, w, huvw⟩
    refine ⟨Sum.elim (fun p => u p.1 p.2) (Sum.elim (fun p => v p.1 p.2) (fun p => w p.1 p.2)),
      ?_⟩
    rintro ⟨x, y, z⟩
    have := congrFun (congrFun (congrFun huvw x) y) z
    simp only [Tensor.rankOne] at this
    rw [lift_lhs, lift_rhs, this]
    rfl

end RankTransfer

open FirstOrder FirstOrder.Language FirstOrder.Ring FirstOrder.Field RankTransfer

open OAI.MatrixMultiplication.Foundation in
/-- **Characteristic transfer.** A rank bound for the matrix-multiplication tensor over `ℂ` holds
over every algebraically closed field whose characteristic is `0` or outside a finite set. -/
theorem rank_transfer {a b c r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) r) :
    ∃ S : Finset ℕ, ∀ (K : Type u) [Field K] [IsAlgClosed K], (ringChar K = 0 ∨ ringChar K ∉ S) →
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) r := by
  have hC : Theory.ACF 0 ⊨ᵇ rankSentence (Fin a) (Fin b) (Fin c) r := by
    let _ := compatibleRingOfRing ℂ
    rw [← (ACF_isComplete (Or.inr rfl)).realize_sentence_iff _ ℂ, realize_rankSentence]
    exact h
  have hfin := finite_ACF_prime_not_realize_of_ACF_zero_realize _ hC
  refine ⟨hfin.toFinset.image (fun p : Nat.Primes => (p : ℕ)), ?_⟩
  intro K _ _ hK
  let _ := compatibleRingOfRing K
  have hmod : Theory.ACF (ringChar K) ⊨ᵇ rankSentence (Fin a) (Fin b) (Fin c) r := by
    rcases hK with h0 | hS
    · rw [h0]; exact hC
    · rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
      · by_contra hnot
        apply hS
        rw [Finset.mem_image]
        exact ⟨⟨ringChar K, hp⟩, hfin.mem_toFinset.2 hnot, rfl⟩
      · rw [h0]; exact hC
  rw [← realize_rankSentence]
  exact hmod.realize_sentence K

end IDMM
