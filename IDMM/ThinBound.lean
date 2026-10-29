/-
**The unconditional thin-endpoint bound.** `ConditionalTarget` at `μ = 200/293` with the thin rectangular
matrix-multiplication exponent (`k = 93/200`, `ω_k = 2`, proved in OpenAI's development): `ID_N`, `S4_N` and
`perm4_N` have noncommutative circuits of size `O(N^{1.6939 + ε})` for every `ε > 0` (the exponent is
`2H(1/4) − 2μH(1/(4μ)) + 2μ = 1.6938884…`). It needs no interpolation.
-/
import IDMM.Construction
import IDMM.FinalNumerics
import IDMM.MMInputs
import IDMM.Transfers

namespace IDMM

/-- **`ID_N` at the thin-endpoint exponent** `2H(1/4) − 2μH(1/(4μ)) + 2μ`, `μ = 200/293`. -/
theorem id_bound_thin : IDBound (constructionExponent muQ 2) := by
  have hk : (1 - muQ) / muQ = 93 / 200 := by unfold muQ; norm_num
  exact construction_target muQ 2 (by unfold muQ; norm_num) (by unfold muQ; norm_num)
    (hk ▸ thin_admissible)

/-- `ID_N`, `S4_N` and `perm4_N` have noncommutative circuits with `O(N^{1.6939 + ε})` gates over `ℂ`, for every
`ε > 0`. -/
theorem thin_main :
    IDBound (16939 / 10000) ∧ S4Bound (16939 / 10000) ∧ Perm4Bound (16939 / 10000) := by
  have h := id_bound_thin.mono thin_exponent_lt.le
  have hs := h.s4 (by norm_num)
  exact ⟨h, hs, hs.perm4⟩

end IDMM
