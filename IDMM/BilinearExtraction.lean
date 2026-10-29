import IDMM.Symbolic
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
namespace IDMM
open MvPolynomial Finset

variable {A B : Type*} [Fintype A] [Fintype B]
abbrev Poly (A B : Type*) := MvPolynomial (A ⊕ B) ℂ
abbrev NC (A B : Type*) := FreeAlgebra ℂ (A ⊕ B)

def scalarPart (p : Poly A B) : ℂ := MvPolynomial.eval (fun _ => 0) p

def derivativePart (p : Poly A B) (i : A ⊕ B) : ℂ :=
  scalarPart (pderiv i p)

def mixedPart (p : Poly A B) (i : A) (j : B) : ℂ :=
  scalarPart (pderiv (.inr j) (pderiv (.inl i) p))

def leftPart (p : Poly A B) : NC A B :=
  ∑ i, derivativePart p (.inl i) • FreeAlgebra.ι ℂ (.inl i)

def rightPart (p : Poly A B) : NC A B :=
  ∑ j, derivativePart p (.inr j) • FreeAlgebra.ι ℂ (.inr j)

/-- The ordered mixed component. B variables always occur after A variables. -/
def orderedPart (p : Poly A B) : NC A B :=
  ∑ i, ∑ j, mixedPart p i j • (FreeAlgebra.ι ℂ (.inl i) * FreeAlgebra.ι ℂ (.inr j))

theorem derivativePart_mul (p q : Poly A B) (i : A ⊕ B) :
    derivativePart (p*q) i = derivativePart p i * scalarPart q +
      scalarPart p * derivativePart q i := by
  simp only [derivativePart, scalarPart, pderiv_mul, map_add, map_mul]

theorem mixedPart_mul (p q : Poly A B) (i : A) (j : B) :
    mixedPart (p*q) i j = mixedPart p i j * scalarPart q +
      derivativePart p (.inl i) * derivativePart q (.inr j) +
      derivativePart q (.inl i) * derivativePart p (.inr j) +
      scalarPart p * mixedPart q i j := by
  simp only [mixedPart, derivativePart, scalarPart, pderiv_mul, map_add, map_mul]
  ring

theorem leftPart_mul (p q : Poly A B) :
    leftPart (p*q) = scalarPart q • leftPart p + scalarPart p • leftPart q := by
  simp only [leftPart, derivativePart_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem rightPart_mul (p q : Poly A B) :
    rightPart (p*q) = scalarPart q • rightPart p + scalarPart p • rightPart q := by
  simp only [rightPart, derivativePart_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The compiler's multiplication rule: the reversed cross term is reordered A before B.
This is not ordinary noncommutative substitution into the original program. -/
theorem orderedPart_mul (p q : Poly A B) :
    orderedPart (p*q) = scalarPart q • orderedPart p +
      leftPart p * rightPart q + leftPart q * rightPart p +
      scalarPart p • orderedPart q := by
  simp only [orderedPart, mixedPart_mul, add_smul, Finset.sum_add_distrib,
    leftPart, rightPart, Finset.sum_mul, Finset.mul_sum,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  all_goals exact Finset.sum_comm

@[simp] theorem leftPart_C (c : ℂ) : leftPart (C c : Poly A B) = 0 := by
  simp [leftPart, derivativePart, scalarPart, pderiv_C]
@[simp] theorem rightPart_C (c : ℂ) : rightPart (C c : Poly A B) = 0 := by
  simp [rightPart, derivativePart, scalarPart, pderiv_C]
@[simp] theorem orderedPart_C (c : ℂ) : orderedPart (C c : Poly A B) = 0 := by
  simp [orderedPart, mixedPart, scalarPart, pderiv_C]

@[simp] theorem leftPart_X_left (i : A) : leftPart (X (.inl i) : Poly A B) =
    FreeAlgebra.ι ℂ (.inl i) := by
  classical
  simp [leftPart, derivativePart, scalarPart, pderiv_X, Pi.single_apply]
@[simp] theorem leftPart_X_right (j : B) : leftPart (X (.inr j) : Poly A B) = 0 := by
  classical
  simp [leftPart, derivativePart, scalarPart, pderiv_X, Pi.single_apply]
@[simp] theorem rightPart_X_left (i : A) : rightPart (X (.inl i) : Poly A B) = 0 := by
  classical
  simp [rightPart, derivativePart, scalarPart, pderiv_X, Pi.single_apply]
@[simp] theorem rightPart_X_right (j : B) : rightPart (X (.inr j) : Poly A B) =
    FreeAlgebra.ι ℂ (.inr j) := by
  classical
  simp [rightPart, derivativePart, scalarPart, pderiv_X, Pi.single_apply]
@[simp] theorem orderedPart_X (i : A ⊕ B) : orderedPart (X i : Poly A B) = 0 := by
  classical
  cases i <;> simp [orderedPart, mixedPart, scalarPart, pderiv_X, Pi.single_apply, apply_ite, pderiv_C]

@[simp] theorem scalarPart_X (i : A ⊕ B) : scalarPart (X i : Poly A B) = 0 := by
  simp [scalarPart]

@[simp] theorem orderedPart_add (p q : Poly A B) : orderedPart (p+q) = orderedPart p + orderedPart q := by
  simp [orderedPart, mixedPart, scalarPart, add_smul, Finset.sum_add_distrib]
@[simp] theorem leftPart_add (p q : Poly A B) : leftPart (p+q) = leftPart p + leftPart q := by
  simp [leftPart, derivativePart, scalarPart, add_smul, Finset.sum_add_distrib]
@[simp] theorem rightPart_add (p q : Poly A B) : rightPart (p+q) = rightPart p + rightPart q := by
  simp [rightPart, derivativePart, scalarPart, add_smul, Finset.sum_add_distrib]

@[simp] theorem orderedPart_sub (p q : Poly A B) : orderedPart (p-q) = orderedPart p - orderedPart q := by
  simp [orderedPart, mixedPart, scalarPart, sub_smul, Finset.sum_sub_distrib]
@[simp] theorem leftPart_sub (p q : Poly A B) : leftPart (p-q) = leftPart p - leftPart q := by
  simp [leftPart, derivativePart, scalarPart, sub_smul, Finset.sum_sub_distrib]
@[simp] theorem rightPart_sub (p q : Poly A B) : rightPart (p-q) = rightPart p - rightPart q := by
  simp [rightPart, derivativePart, scalarPart, sub_smul, Finset.sum_sub_distrib]

@[simp] theorem orderedPart_zero : orderedPart (0 : Poly A B) = 0 := by
  simp [orderedPart, mixedPart, scalarPart]

theorem orderedPart_sum {J : Type*} (s : Finset J) (p : J → Poly A B) :
    orderedPart (∑ j ∈ s, p j) = ∑ j ∈ s, orderedPart (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, ih]

/-- Every correct OpenAI rectangular algorithm gives the correct ordered bilinear output. -/
theorem orderedPart_correct {a b c : ℕ}
    (P : OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ a b c) (hP : P.Correct)
    (i : Fin a) (k : Fin c) :
    orderedPart (polynomialProgram P.program (P.output i k)) =
      ∑ j : Fin b, FreeAlgebra.ι ℂ (.inl (i,j)) * FreeAlgebra.ι ℂ (.inr (j,k)) := by
  rw [correct_polynomial P hP, orderedPart_sum]
  simp [orderedPart_mul]
end IDMM
