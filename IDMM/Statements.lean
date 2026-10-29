/- Auditable targets only. Definitions below do not assert that the targets are proved. -/
import PauliCubes.CircuitDefs
import OAI.LinearAlgebra.MatrixMultiplication.Model

noncomputable section
namespace IDMM
open PauliCubes

/-- Binary entropy, with the usual continuous endpoint convention from `Real.log 0 = 0`. -/
def binaryEntropy (x : ℝ) : ℝ :=
  -(x * Real.log x + (1 - x) * Real.log (1 - x)) / Real.log 2

def constructionExponent (μ w : ℝ) : ℝ :=
  2 * binaryEntropy (1 / 4) - 2 * μ * binaryEntropy (1 / (4 * μ)) + μ * w

/-- A uniform constant and arbitrary positive exponent slack. -/
def IDBound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    NCSizeLE (ID ℂ N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

def S4Bound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    NCSizeLE (S4 ℂ N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

def Perm4Bound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    NCSizeLE (perm4 ℂ N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

/-- The exact requested rational exponent; no floating point literals. -/
def targetExponent : ℝ := 211321 / 125000

/-- OPEN target, not an axiom or a theorem. -/
def MainTarget : Prop :=
  IDBound targetExponent ∧ S4Bound targetExponent ∧ Perm4Bound targetExponent

/-- OPEN cycle-055 bridge target, not an assumed theorem. -/
def ConditionalTarget : Prop :=
  ∀ μ w : ℝ, 1 / 2 < μ → μ < 1 →
    OAI.MatrixMultiplication.Arithmetic.RectangularAdmissibleExponent
      ℂ ((1 - μ) / μ) w → IDBound (constructionExponent μ w)
end IDMM
