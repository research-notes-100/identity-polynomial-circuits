/-
Tools for the characteristic-transfer theorem.

* `IDBoundF.of_ext`: a bound over a finite extension `E/F` gives the same bound over `F` (`ncSizeLE_ID_descent`).
* `exists_ext_of_algClosure`: a rank decomposition over the algebraic closure of `F`, together with `√−1`, already
  lives over a finite extension `E` of `F`.
-/
import IDMM.Eventual
import IDMM.ExtDescent
import IDMM.MajBasic
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

noncomputable section
namespace IDMM
open PauliCubes OAI.MatrixMultiplication.Foundation

universe u

/-- **Descent of `IDBoundF`** along a finite extension. -/
theorem IDBoundF.of_ext {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {c : ℝ}
    (hc : 0 ≤ c) (h : IDBoundF E c) : IDBoundF F c := by
  obtain ⟨c₀, hc₀⟩ := ncSizeLE_ID_descent (F := F) (E := E)
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨(c₀ + 1) * C + c₀, by positivity, fun N hN => ?_⟩
  refine (hc₀ N _ (hb N hN)).mono (Nat.le_floor ?_)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (c + ε) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hfl := Nat.floor_le (show 0 ≤ C * (N : ℝ) ^ (c + ε) by positivity)
  push_cast
  nlinarith

/-- **The finite extension.** A rank decomposition of `⟨a, b, c⟩` over the algebraic closure of `F` and a square root
of `−1` lie in one finite extension `E` of `F`. -/
theorem exists_ext_of_algClosure (F : Type u) [Field F] {a b c R : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := AlgebraicClosure F) (Fin a) (Fin b) (Fin c)) R) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E), FiniteDimensional F E ∧ (∃ i : E, i * i = -1) ∧
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := E) (Fin a) (Fin b) (Fin c)) R := by
  classical
  set L := AlgebraicClosure F
  obtain ⟨u, v, w, hT⟩ := h
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) (n := 2) (by norm_num)
  let S : Set L := Set.range (fun p : Fin R × (Fin a × Fin b) => u p.1 p.2) ∪
    Set.range (fun p : Fin R × (Fin b × Fin c) => v p.1 p.2) ∪
    Set.range (fun p : Fin R × (Fin c × Fin a) => w p.1 p.2) ∪ {i}
  have hSfin : S.Finite := by
    refine (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_singleton _)
  haveI : Finite S := hSfin.to_subtype
  let E := IntermediateField.adjoin F S
  haveI : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x ∈ S, x ∈ E := fun x hx => IntermediateField.subset_adjoin F S hx
  refine ⟨E, inferInstance, inferInstance, inferInstance,
    ⟨⟨i, hmem i (Or.inr rfl)⟩, Subtype.ext (by simpa [sq] using hi)⟩, ?_⟩
  refine ⟨fun q x => ⟨u q x, hmem _ (Or.inl (Or.inl (Or.inl ⟨(q, x), rfl⟩)))⟩,
    fun q y => ⟨v q y, hmem _ (Or.inl (Or.inl (Or.inr ⟨(q, y), rfl⟩)))⟩,
    fun q z => ⟨w q z, hmem _ (Or.inl (Or.inr ⟨(q, z), rfl⟩))⟩, ?_⟩
  funext x y z
  apply Subtype.ext
  have hxyz := congrFun (congrFun (congrFun hT x) y) z
  simp only [Tensor.rankOne, Tensor.matrixCoefficients] at hxyz ⊢
  rw [IntermediateField.coe_sum]
  simp only [IntermediateField.coe_mul]
  rw [← hxyz]
  split_ifs <;> simp

end IDMM
