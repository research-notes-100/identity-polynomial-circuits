/-
The reduction of `MainTarget` to two bridges. Both are now proved (`construction_target` in `IDMM/Construction.lean`,
`chosen_interpolation` in `IDMM/Final.lean`), and `IDMM.main_target` in `IDMM/Final.lean` applies this reduction.
-/
import IDMM.MMCircuit
import IDMM.MMInputs
import IDMM.Numerical
import IDMM.Transfers
import PauliCubes.S4Circuit

namespace IDMM
open OAI.MatrixMultiplication.Arithmetic

/-- The reduction of the final goal to the two bridges (both proved; see `IDMM.main_target`). -/
theorem mainTarget_of_remaining_bridges
    (construction : ConditionalTarget)
    (interpolation : RectangularAdmissibleExponent ℂ chosenK chosenW) : MainTarget := by
  obtain ⟨hμ₁,hμ₂,hk,_,_⟩ := chosen_parameters
  have hID := construction chosenMu chosenW hμ₁ hμ₂ (hk ▸ interpolation)
  exact mainTarget_of_id (hID.mono chosen_exponent_lt_target.le)

end IDMM
