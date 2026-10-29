import IDMM.Statements
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
namespace IDMM
open OAI.MatrixMultiplication.Arithmetic
open MvPolynomial

variable {F I : Type*} [Field F]

/-- Formal polynomial semantics of the unchanged OpenAI program syntax. -/
def polynomialGate {r : ℕ} (g : Gate F I (Fin r))
    (v : Fin r → MvPolynomial I F) : MvPolynomial I F :=
  match g with
  | .constant c => C c
  | .input i => X i
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .mul i j => v i * v j

def polynomialProgram : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases (polynomialGate g (polynomialProgram p)) (polynomialProgram p)

theorem eval_polynomialGate {r : ℕ} (g : Gate F I (Fin r))
    (v : Fin r → MvPolynomial I F) (x : I → F) :
    MvPolynomial.eval x (polynomialGate g v) = g.eval x (fun i => MvPolynomial.eval x (v i)) := by
  cases g <;> simp [polynomialGate, Gate.eval]

theorem eval_polynomialProgram {r : ℕ} (p : Program F I r) (x : I → F) (j : Fin r) :
    MvPolynomial.eval x (polynomialProgram p j) = p.eval x j := by
  induction p with
  | nil => exact Fin.elim0 j
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [polynomialProgram, Program.eval, Fin.cases_zero, eval_polynomialGate]
      congr 1
      funext j
      exact ih j
    · simpa only [polynomialProgram, Program.eval, Fin.cases_succ] using ih j

/-- Functional correctness over an infinite field implies the exact formal bilinear identity.
This would be false over a finite field without additional degree hypotheses. -/
theorem correct_polynomial [Infinite F] {a b c : ℕ} (P : MatrixAlgorithm F a b c)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    polynomialProgram P.program (P.output i k) =
      ∑ j : Fin b, X (Sum.inl (i,j)) * X (Sum.inr (j,k)) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialProgram]
  have h := congrFun (congrFun (hP (fun i j => x (.inl (i,j)))
    (fun j k => x (.inr (j,k)))) i) k
  have hx : matrixInputs (fun i j => x (.inl (i,j))) (fun j k => x (.inr (j,k))) = x := by
    funext z
    cases z <;> rfl
  change P.program.eval _ (P.output i k) = ∑ j, x (.inl (i,j)) * x (.inr (j,k)) at h
  rw [hx] at h
  simpa using h

end IDMM
