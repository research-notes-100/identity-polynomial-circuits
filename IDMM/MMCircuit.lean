import IDMM.BridgeCost
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

noncomputable section
namespace IDMM
open PauliCubes OAI.MatrixMultiplication.Arithmetic

/-- The bridge at the exact arithmetic-exponent level, with one shared circuit for all entries. -/
theorem rectangular_nc_shared {k w : ℝ} (h : RectangularAdmissibleExponent ℂ k w) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Reach (ncInputs ℂ (MatrixInput n (innerSize n k) n)) ∅
        (Set.range (fun ik : Fin n × Fin n =>
          ∑ j : Fin (innerSize n k),
            FreeAlgebra.ι ℂ (.inl (ik.1,j)) * FreeAlgebra.ι ℂ (.inr (j,ik.2))))
        ⌊C * (n : ℝ) ^ (w+ε)⌋₊ := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := h ε hε
  refine ⟨91*C,by positivity,fun n hn => ?_⟩
  obtain ⟨P,hP,hcost⟩ := h n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hb : 1 ≤ innerSize n k := by
    change 1 ≤ ⌈(n:ℝ)^k⌉₊
    have := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos k)
    omega
  refine (matrixAlgorithm_reach_linear P hP hb).mono le_rfl le_rfl (Nat.le_floor ?_)
  push_cast
  nlinarith
end IDMM
