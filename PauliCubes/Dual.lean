/-
Linear duality for the crossing: either the crossing decomposes into row-cut and column-cut Pauli words
from an allowed ("cheap") set, or a dual certificate exists.
-/
import PauliCubes.Crossing
import Mathlib.LinearAlgebra.Dual.Lemmas

open Finset

namespace PauliCubes

variable {K : Type*} [Field K] {n : ℕ}

/-- The column-cut word `ν` in the row basis: `β ↦ Π_i M(ν_i, β_i)`. -/
noncomputable def colVec (K : Type*) [Field K] (ν : Fin n → Fin 4) : (Fin n → Fin 4) → K :=
  fun β => ∏ i, cutM K (ν i) (β i)

/-- The crossing in the row basis: `β ↦ Π_i s_{β_i} / 2`. -/
noncomputable def crossVec (K : Type*) [Field K] : (Fin n → Fin 4) → K :=
  fun β => ∏ i, (2⁻¹ * sgn1 K (β i))

theorem sum_subtype_dite {ι : Type*} [Fintype ι] [DecidableEq ι] (ch : ι → Prop) [DecidablePred ch]
    (f : {x // ch x} → K) (g : ι → K) :
    ∑ x : {x // ch x}, f x * g x.1 = ∑ x, (if h : ch x then f ⟨x, h⟩ else 0) * g x := by
  have : ∑ x, (if h : ch x then f ⟨x, h⟩ else 0) * g x =
      ∑ x ∈ univ.filter ch, (if h : ch x then f ⟨x, h⟩ else 0) * g x := by
    rw [Finset.sum_filter_of_ne]
    intro x _ hne
    by_contra hc
    exact hne (by simp [hc])
  rw [this, Finset.sum_subtype (univ.filter ch) (p := ch) (by simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [x.2]

/-- **Duality.** Either the crossing decomposes using only allowed words (in both cuts), or there is a
certificate `y` vanishing on allowed row words, orthogonal to every allowed column word, and pairing
nontrivially with the crossing. -/
theorem decomp_or_dual (h2 : (2 : K) ≠ 0) (ch : (Fin n → Fin 4) → Prop) [DecidablePred ch] :
    (∃ r d : (Fin n → Fin 4) → K, (∀ β, ¬ ch β → r β = 0) ∧ (∀ ν, ¬ ch ν → d ν = 0) ∧
      ∀ x y u v, (if x = v ∧ y = u then 1 else 0 : K) =
        ∑ β, r β * rowT K β x y u v + ∑ ν, d ν * colT K ν x y u v) ∨
    (∃ y : (Fin n → Fin 4) → K, (∀ β, ch β → y β = 0) ∧
      (∀ ν, ch ν → ∑ β, y β * colVec K ν β = 0) ∧ ∑ β, y β * crossVec K β ≠ 0) := by
  classical
  let v : {β // ch β} ⊕ {ν // ch ν} → (Fin n → Fin 4) → K := fun i =>
    match i with
    | Sum.inl β => fun γ => if γ = β.1 then 1 else 0
    | Sum.inr ν => colVec K ν.1
  by_cases hb : crossVec K ∈ Submodule.span K (Set.range v)
  · left
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hb
    let r : (Fin n → Fin 4) → K := fun β => if h : ch β then c (Sum.inl ⟨β, h⟩) else 0
    let d : (Fin n → Fin 4) → K := fun ν => if h : ch ν then c (Sum.inr ⟨ν, h⟩) else 0
    have hrow : ∀ β, r β + ∑ ν, d ν * colVec K ν β = crossVec K β := by
      intro β
      have hβ := congr_fun hc β
      simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at hβ
      rw [← hβ]
      congr 1
      · rw [sum_subtype_dite ch (fun x => c (Sum.inl x)) (fun γ => if β = γ then 1 else 0)]
        simp [r]
      · rw [sum_subtype_dite ch (fun x => c (Sum.inr x)) (fun ν => colVec K ν β)]
    refine ⟨r, d, fun β h => by simp [r, h], fun ν h => by simp [d, h], ?_⟩
    intro x y u w
    rw [cross_eq_row h2 x y u w]
    have hcol : ∀ ν, colT K ν x y u w = ∑ β, colVec K ν β * rowT K β x y u w :=
      fun ν => col_eq_row h2 ν x y u w
    simp only [hcol, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun ν β => d ν * (colVec K ν β * rowT K β x y u w)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hβ := hrow β
    unfold crossVec at hβ
    rw [← hβ, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => by ring
  · right
    obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
    have hzero : ∀ w ∈ Submodule.span K (Set.range v), φ w = 0 := by
      intro w hw
      have : φ w ∈ (Submodule.span K (Set.range v)).map φ := Submodule.mem_map_of_mem hw
      rw [hmap] at this
      simpa using this
    let y : (Fin n → Fin 4) → K := fun γ => φ (fun j => if γ = j then 1 else 0)
    have hφy : ∀ w : (Fin n → Fin 4) → K, φ w = ∑ γ, y γ * w γ := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ φ w]
      exact Finset.sum_congr rfl fun γ _ => by simp [y, smul_eq_mul, mul_comm]
    refine ⟨y, fun β h => ?_, fun ν h => ?_, ?_⟩
    · have := hzero (v (Sum.inl ⟨β, h⟩)) (Submodule.subset_span (Set.mem_range_self (f := v) (Sum.inl ⟨β, h⟩)))
      rw [hφy] at this
      simpa [v] using this
    · have := hzero (v (Sum.inr ⟨ν, h⟩)) (Submodule.subset_span (Set.mem_range_self (f := v) (Sum.inr ⟨ν, h⟩)))
      rw [hφy] at this
      simpa [v] using this
    · rw [← hφy]; exact hφ

end PauliCubes
