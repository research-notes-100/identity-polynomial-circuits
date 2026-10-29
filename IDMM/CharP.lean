/-
The 1.690568 bound in almost every characteristic, now a specialization of the
parametric field-transfer theorem. The exceptional set is not computed.
-/
import IDMM.FieldTransfer

noncomputable section
namespace IDMM
universe u

/-- There is one finite exceptional set, independent of the field and the positive
circuit slack, outside which the 1.690568 bound holds. -/
theorem main_target_almost_every_char : ∃ S : Finset ℕ, ∀ (F : Type u) [Field F], ringChar F ≠ 2 →
    (ringChar F = 0 ∨ ringChar F ∉ S) →
    IDBoundF F targetExponent ∧ S4BoundF F targetExponent ∧ Perm4BoundF F targetExponent := by
  obtain ⟨hμ0, hμ1, hK, -, -⟩ := chosen_parameters
  exact construction_almost_every_char hμ0 hμ1 (hK ▸ chosen_interpolation)
    (by norm_num [targetExponent]) chosen_exponent_lt_target

/-- The numerical main theorem over every characteristic-zero field, with no
exceptional-set hypothesis and no assumption that the field contains √−1. -/
theorem main_target_char_zero (F : Type u) [Field F] [CharZero F] :
    IDBoundF F targetExponent ∧ S4BoundF F targetExponent ∧ Perm4BoundF F targetExponent := by
  obtain ⟨S, hS⟩ := main_target_almost_every_char.{u}
  exact hS F (by simp [ringChar.eq_zero]) (Or.inl ringChar.eq_zero)

end IDMM
