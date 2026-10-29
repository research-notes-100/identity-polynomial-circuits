import IDMM.Statements
import PauliCubes.IDStar
import PauliCubes.Prop26
import PauliCubes.Perm4

namespace IDMM
open PauliCubes

theorem IDBound.mono {c d : ℝ} (h : IDBound c) (hcd : c ≤ d) : IDBound d := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := h ε hε
  refine ⟨C,hC,fun N hN => (h N hN).mono (Nat.floor_le_floor ?_)⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)) hC.le

theorem IDBound.s4 {c : ℝ} (h : IDBound c) (hc : 1 ≤ c) : S4Bound c := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := h ε hε
  refine ⟨C+200,by linarith,fun N hN => ?_⟩
  refine (ncSizeLE_S4_of_IDstar (ncSizeLE_IDstar (h N hN))).mono (Nat.le_floor ?_)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hxN : (N:ℝ) ≤ (N:ℝ)^(c+ε) := by
    calc (N:ℝ) = (N:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hfl := Nat.floor_le (show 0 ≤ C*(N:ℝ)^(c+ε) by positivity)
  push_cast
  nlinarith

theorem S4Bound.perm4 {c : ℝ} (h : S4Bound c) : Perm4Bound c := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := h ε hε
  refine ⟨275*C,by positivity,fun N hN => ?_⟩
  refine (ncSizeLE_perm4_of_S4 (h N hN)).mono (Nat.le_floor ?_)
  have hfl := Nat.floor_le (show 0 ≤ C*(N:ℝ)^(c+ε) by positivity)
  push_cast
  nlinarith

/-- The remaining substantive target is the ID bound; transfers are closed. -/
theorem mainTarget_of_id (h : IDBound targetExponent) : MainTarget :=
  ⟨h, h.s4 (by norm_num [targetExponent]), (h.s4 (by norm_num [targetExponent])).perm4⟩
end IDMM
