/-
Parametric field transfer for the Majorana construction.

A strict upper bound on the entropy formula transfers to all but finitely many
characteristics. The exceptional set is independent of the circuit slack ε.
In characteristic zero the strict margin can be removed, since there is no
exceptional-prime condition to keep uniform while the margin tends to zero.
-/
import IDMM.Final
import IDMM.SchemeOracle
import IDMM.CharPTools
import IDMM.RankTransfer
import IDMM.FinalNumerics

noncomputable section
namespace IDMM
open OAI.MatrixMultiplication OAI.MatrixMultiplication.Arithmetic
  OAI.MatrixMultiplication.Foundation
universe u

/-- Any strict bound on the Majorana formula transfers to almost every characteristic.
The single finite exceptional set works for every field and every positive circuit slack. -/
theorem construction_almost_every_char {μ w c : ℝ}
    (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1)
    (hw : RectangularAdmissibleExponent ℂ ((1 - μ) / μ) w)
    (hc : 1 ≤ c) (hgap : constructionExponent μ w < c) :
    ∃ S : Finset ℕ, ∀ (F : Type u) [Field F], ringChar F ≠ 2 →
      (ringChar F = 0 ∨ ringChar F ∉ S) →
      IDBoundF F c ∧ S4BoundF F c ∧ Perm4BoundF F c := by
  have hμpos : 0 < μ := by linarith
  have hk0 : 0 ≤ (1 - μ) / μ := div_nonneg (by linarith) hμpos.le
  have hk1 : (1 - μ) / μ ≤ 1 := (div_le_one hμpos).2 (by linarith)
  have hw2 : 2 ≤ w := rectangularAdmissibleExponent_two_le hw
  let η : ℝ := (c - constructionExponent μ w) / (4 * μ)
  have hη : 0 < η := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨a, b, R, hRk, ha2, hab, hR, hin, hout⟩ :=
    exists_interp_scheme (fun P hP => rank_of_program P hP)
      hk0 hk0 hk1 hk1 hw2 hw2 hw hw 1 0 (by norm_num) hη
  simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero, div_one]
    at hab hR hin hout
  obtain ⟨S, hS⟩ := rank_transfer.{u} hRk
  refine ⟨S, fun F _ h2 hchar => ?_⟩
  have hcharL : ringChar (AlgebraicClosure F) = ringChar F :=
    (Algebra.ringChar_eq F _).symm
  have hRkL := hS (AlgebraicClosure F) (by rw [hcharL]; exact hchar)
  obtain ⟨E, _, _, hfin, ⟨i, hi⟩, hRkE⟩ := exists_ext_of_algClosure F hRkL
  haveI : SqrtNegOne E := ⟨i, hi⟩
  haveI : NeZero (2 : E) :=
    ⟨Ring.two_ne_zero (by rw [← Algebra.ringChar_eq F E]; exact h2)⟩
  have hE : IDBoundF E (constructionExponent μ (w + 2 * η)) :=
    construction_gen hμ0 hμ1 (by linarith) fun ε hε =>
      oracles_of_scheme hμ0 hμ1 hRkE ha2 hab hR hin hout hε
  have hηeq : μ * (2 * η) = (c - constructionExponent μ w) / 2 := by
    dsimp [η]
    field_simp
    ring
  have hle : constructionExponent μ (w + 2 * η) ≤ c := by
    rw [constructionExponent_add, hηeq]
    linarith
  have hF : IDBoundF F c := IDBoundF.of_ext (by linarith) (hE.mono hle)
  exact ⟨hF, hF.s4 hc, (hF.s4 hc).perm4⟩

/-- Bounds at every strictly larger exponent imply the endpoint bound, because
`IDBoundF` already quantifies over every positive slack. -/
theorem IDBoundF.of_forall_add {F : Type u} [Field F] {c : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → IDBoundF F (c + δ)) : IDBoundF F c := by
  intro ε hε
  obtain ⟨C, hC, hN⟩ := h (ε / 2) (by linarith) (ε / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  have heq : c + ε / 2 + ε / 2 = c + ε := by ring
  simpa only [heq] using hN

/-- The exact parametric entropy formula holds over every characteristic-zero field,
without any decimal rounding or fixed positive margin. -/
theorem construction_char_zero (F : Type u) [Field F] [CharZero F] {μ w : ℝ}
    (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1)
    (hw : RectangularAdmissibleExponent ℂ ((1 - μ) / μ) w)
    (hc : 1 ≤ constructionExponent μ w) :
    IDBoundF F (constructionExponent μ w) ∧
      S4BoundF F (constructionExponent μ w) ∧
      Perm4BoundF F (constructionExponent μ w) := by
  have hF : IDBoundF F (constructionExponent μ w) := by
    apply IDBoundF.of_forall_add
    intro δ hδ
    obtain ⟨S, hS⟩ := construction_almost_every_char.{u} hμ0 hμ1 hw
      (show 1 ≤ constructionExponent μ w + δ by linarith)
      (show constructionExponent μ w < constructionExponent μ w + δ by linarith)
    exact (hS F (by simp [ringChar.eq_zero]) (Or.inl (ringChar.eq_zero : ringChar F = 0))).1
  exact ⟨hF, hF.s4 hc, (hF.s4 hc).perm4⟩

end IDMM
