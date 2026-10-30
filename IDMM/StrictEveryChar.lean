/-
Theorem 1.1 in Hrubeš's model read strictly (every gate has two different inputs), and the main theorem
applied to two concrete fields, so that its hypothesis is visibly satisfiable.
-/
import IDMM.EveryChar
import IDMM.CircuitModel

namespace IDMM

universe u

/-- **Theorem 1.1, strict model.** -/
theorem strict_id_bound_every_char (F : Type u) [Field F] (h2 : ringChar F ≠ 2) :
    StrictIDBoundF F (4173 / 2500) ∧ StrictS4BoundF F (4173 / 2500) ∧
      StrictPerm4BoundF F (4173 / 2500) := by
  obtain ⟨h1, hs, hp⟩ := id_bound_every_char F h2
  have hc : (0 : ℝ) ≤ 4173 / 2500 := by norm_num
  exact ⟨StrictIDBoundF.of hc h1, StrictS4BoundF.of hc hs, StrictPerm4BoundF.of hc hp⟩

/-- Theorem 1.1 over `ℚ`. -/
theorem id_bound_every_char_rat :
    IDBoundF ℚ (4173 / 2500) ∧ S4BoundF ℚ (4173 / 2500) ∧ Perm4BoundF ℚ (4173 / 2500) :=
  id_bound_every_char ℚ (by rw [ringChar.eq_zero]; norm_num)

/-- Theorem 1.1 over `ZMod 3`. -/
theorem id_bound_every_char_zmod3 :
    IDBoundF (ZMod 3) (4173 / 2500) ∧ S4BoundF (ZMod 3) (4173 / 2500) ∧
      Perm4BoundF (ZMod 3) (4173 / 2500) :=
  id_bound_every_char (ZMod 3) (by rw [ZMod.ringChar_zmod_n]; norm_num)

end IDMM
