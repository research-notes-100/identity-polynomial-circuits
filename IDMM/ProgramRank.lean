import IDMM.BilinearExtraction
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/-!
# Programs give tensor rank bounds

A correct straight-line matrix-multiplication program of cost `s` over `ℂ` gives a
decomposition of the matrix-multiplication tensor into `2 s` rank-one terms.

Every register's mixed part (the `A`-by-`B` bilinear component of its polynomial) lies in the
span of rank-one forms `u ⊗ v`, where each multiplication gate `p * q` contributes the two forms
`L_A(p) ⊗ L_B(q)` and `L_A(q) ⊗ L_B(p)` (product rule `mixedPart_mul`), additions and
subtractions contribute two zero placeholders, and constants and inputs contribute nothing.
-/

noncomputable section
namespace IDMM
open MvPolynomial Finset
open OAI.MatrixMultiplication.Arithmetic

section Forms

variable {A B : Type*}

/-- A pair of linear forms, one on the `A`-inputs and one on the `B`-inputs. -/
abbrev FormPair (A B : Type*) := (A → ℂ) × (B → ℂ)

/-- The rank-one bilinear form `u ⊗ v`. -/
def form (w : FormPair A B) : A → B → ℂ := fun i j => w.1 i * w.2 j

/-- The span of the rank-one forms of a finite family of pairs. -/
def formSpan {N : ℕ} (w : Fin N → FormPair A B) : Submodule ℂ (A → B → ℂ) :=
  Submodule.span ℂ (Set.range fun t => form (w t))

def leftVec (p : Poly A B) : A → ℂ := fun i => derivativePart p (.inl i)
def rightVec (p : Poly A B) : B → ℂ := fun j => derivativePart p (.inr j)

theorem mixedPart_add' (p q : Poly A B) :
    mixedPart (p + q) = mixedPart p + mixedPart q := by
  funext i j
  simp [mixedPart, scalarPart]

theorem mixedPart_sub' (p q : Poly A B) :
    mixedPart (p - q) = mixedPart p - mixedPart q := by
  funext i j
  simp [mixedPart, scalarPart]

theorem mixedPart_C' (z : ℂ) : mixedPart (C z : Poly A B) = 0 := by
  funext i j
  simp [mixedPart, scalarPart]

theorem mixedPart_X' (k : A ⊕ B) : mixedPart (X k : Poly A B) = 0 := by
  classical
  funext i j
  simp [mixedPart, scalarPart, pderiv_X, Pi.single_apply, apply_ite]

theorem mixedPart_mul' [Fintype A] [Fintype B] (p q : Poly A B) :
    mixedPart (p * q) = scalarPart q • mixedPart p + scalarPart p • mixedPart q +
      form (leftVec p, rightVec q) + form (leftVec q, rightVec p) := by
  funext i j
  simp only [mixedPart_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, form, leftVec, rightVec]
  ring

theorem formSpan_le_append {N M : ℕ} (w : Fin N → FormPair A B) (w' : Fin M → FormPair A B) :
    formSpan w ≤ formSpan (Fin.append w w') := by
  apply Submodule.span_mono
  rintro _ ⟨t, rfl⟩
  exact ⟨Fin.castAdd M t, by simp⟩

theorem form_mem_append {N M : ℕ} (w : Fin N → FormPair A B) (w' : Fin M → FormPair A B)
    (t : Fin M) : form (w' t) ∈ formSpan (Fin.append w w') :=
  Submodule.subset_span ⟨Fin.natAdd N t, by simp⟩

/-- `N` rank-one forms suffice to span the mixed part of every register of `p`. -/
def Spanned {r : ℕ} (p : Program ℂ (A ⊕ B) r) (N : ℕ) : Prop :=
  ∃ w : Fin N → FormPair A B, ∀ k, mixedPart (polynomialProgram p k) ∈ formSpan w

theorem spanned_step_of {r N M : ℕ} {p : Program ℂ (A ⊕ B) r} {g : Gate ℂ (A ⊕ B) (Fin r)}
    {w : Fin N → FormPair A B} {w' : Fin M → FormPair A B}
    (hw : ∀ k, mixedPart (polynomialProgram p k) ∈ formSpan w)
    (hle : formSpan w ≤ formSpan w')
    (hnew : mixedPart (polynomialGate g (polynomialProgram p)) ∈ formSpan w') :
    Spanned (.step p g) M := by
  refine ⟨w', fun k => ?_⟩
  induction k using Fin.cases with
  | zero => simpa [polynomialProgram] using hnew
  | succ k => simpa [polynomialProgram] using hle (hw k)

theorem spanned_step [Fintype A] [Fintype B] {r N : ℕ} {p : Program ℂ (A ⊕ B) r}
    (g : Gate ℂ (A ⊕ B) (Fin r)) (h : Spanned p N) : Spanned (.step p g) (N + 2 * g.cost) := by
  obtain ⟨w, hw⟩ := h
  cases g with
  | constant z =>
    exact spanned_step_of (w' := w) hw le_rfl (by simp [polynomialGate, mixedPart_C'])
  | input k =>
    exact spanned_step_of (w' := w) hw le_rfl (by simp [polynomialGate, mixedPart_X'])
  | add i j =>
    show Spanned _ (N + 2)
    refine spanned_step_of (w' := Fin.append w ![0, 0]) hw (formSpan_le_append _ _) ?_
    rw [polynomialGate, mixedPart_add']
    exact add_mem (formSpan_le_append _ _ (hw i)) (formSpan_le_append _ _ (hw j))
  | sub i j =>
    show Spanned _ (N + 2)
    refine spanned_step_of (w' := Fin.append w ![0, 0]) hw (formSpan_le_append _ _) ?_
    rw [polynomialGate, mixedPart_sub']
    exact sub_mem (formSpan_le_append _ _ (hw i)) (formSpan_le_append _ _ (hw j))
  | mul i j =>
    show Spanned _ (N + 2)
    let v := polynomialProgram p
    let new : Fin 2 → FormPair A B :=
      ![(leftVec (v i), rightVec (v j)), (leftVec (v j), rightVec (v i))]
    refine spanned_step_of (w' := Fin.append w new) hw (formSpan_le_append _ _) ?_
    rw [polynomialGate, mixedPart_mul']
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact Submodule.smul_mem _ _ (formSpan_le_append _ _ (hw i))
    · exact Submodule.smul_mem _ _ (formSpan_le_append _ _ (hw j))
    · exact form_mem_append w new 0
    · exact form_mem_append w new 1

/-- Every program's registers are spanned by `2 · cost` rank-one forms. -/
theorem spanned_program [Fintype A] [Fintype B] {r : ℕ} (p : Program ℂ (A ⊕ B) r) :
    Spanned p (2 * p.cost) := by
  induction p with
  | nil => exact ⟨Fin.elim0, fun k => Fin.elim0 k⟩
  | step p g ih =>
    have h := spanned_step g ih
    rw [← Nat.mul_add] at h
    exact h

theorem derivativePart_X' [DecidableEq A] [DecidableEq B] (k l : A ⊕ B) :
    derivativePart (X k : Poly A B) l = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h; simp [derivativePart, scalarPart, pderiv_X]
  · simp [derivativePart, scalarPart, pderiv_X, h]

theorem mixedPart_sum {ι : Type*} (s : Finset ι) (f : ι → Poly A B) :
    mixedPart (∑ t ∈ s, f t) = ∑ t ∈ s, mixedPart (f t) := by
  funext i j
  simp [mixedPart, scalarPart, map_sum, Finset.sum_apply]

end Forms

open OAI.MatrixMultiplication.Foundation.Tensor

/-- The mixed part of output `(i, k)` of a correct program is the `(k, i)` slice of the
matrix-multiplication tensor. -/
theorem mixedPart_output {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct)
    (i : Fin a) (k : Fin c) (x : Fin a × Fin b) (y : Fin b × Fin c) :
    mixedPart (A := Fin a × Fin b) (B := Fin b × Fin c)
        (polynomialProgram P.program (P.output i k)) x y =
      matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) x y (k, i) := by
  rw [correct_polynomial P hP, mixedPart_sum, Finset.sum_apply, Finset.sum_apply]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [mixedPart_mul, scalarPart_X, derivativePart_X', mixedPart_X']
  simp only [mul_zero, zero_mul, add_zero, zero_add, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, ite_false, Prod.mk.injEq, matrixCoefficients]
  rw [Finset.sum_eq_single y1 (fun j _ hj => by simp [hj]) (by simp)]
  split_ifs <;> simp_all

/-- A correct straight-line matrix-multiplication program of cost `s` over `ℂ` gives a rank
decomposition of the `a × b × c` matrix-multiplication tensor with `2 s` terms. -/
theorem rank_of_program {a b c : ℕ}
    (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) :
    RankAtMost (matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) (2 * P.cost) := by
  obtain ⟨w, hw⟩ := spanned_program (A := Fin a × Fin b) (B := Fin b × Fin c) P.program
  have hd : ∀ z : Fin c × Fin a, ∃ d : Fin (2 * P.program.cost) → ℂ,
      ∑ t, d t • form (w t) = mixedPart (polynomialProgram P.program (P.output z.2 z.1)) :=
    fun z => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hw _)
  choose d hd using hd
  refine ⟨fun t => (w t).1, fun t => (w t).2, fun t z => d z t, ?_⟩
  funext x y z
  obtain ⟨k, i⟩ := z
  rw [← mixedPart_output P hP i k x y, ← hd (k, i)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, form, rankOne]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end IDMM
