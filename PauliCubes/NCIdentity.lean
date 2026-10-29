/-
The algebraic core of Hrubeš's Lemma 22: a commutative weighted sum-of-squares identity of Pauli
forms, `(Σ X_x²)(Σ Y_y²) = Σ_ν w_ν (Xᵀ P_ν Y)²` for all `X, Y` over a field `K` with `2 ≠ 0`,
implies the noncommutative identity `Σ_ν w_ν f_ν^[2] = Σ_{x,y} X_x Y_y X_x Y_y` in every algebra
over an extension field `L` of `K`.

The field may be finite, so polynomial coefficients are not compared directly. Polarizing the
hypothesis in `X` and in `Y` and evaluating at unit vectors gives the tensor identity
`Σ_ν w_ν (P_ν[x,y] P_ν[u,v] + P_ν[x,v] P_ν[u,y]) = 2 [x = u ∧ y = v]`, and the noncommutative left
side expands to exactly these coefficients.
-/
import PauliCubes.NCForms

open Finset

namespace PauliCubes

section Commutative

variable {K : Type*} [CommRing K] {n : ℕ}

/-- `Xᵀ P_ν Y` is additive in `X`. -/
theorem pauliForm_add_left (ν : Fin n → Fin 4) (X₁ X₂ Y : (Fin n → Fin 2) → K) :
    pauliForm K ν (X₁ + X₂) Y = pauliForm K ν X₁ Y + pauliForm K ν X₂ Y := by
  simp only [pauliForm, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

/-- `Xᵀ P_ν Y` is additive in `Y`. -/
theorem pauliForm_add_right (ν : Fin n → Fin 4) (X Y₁ Y₂ : (Fin n → Fin 2) → K) :
    pauliForm K ν X (Y₁ + Y₂) = pauliForm K ν X Y₁ + pauliForm K ν X Y₂ := by
  simp only [pauliForm, Pi.add_apply, mul_add, sum_add_distrib]

/-- At unit vectors, `Xᵀ P_ν Y` is an entry of `P_ν`. -/
theorem pauliForm_single (ν : Fin n → Fin 4) (x y : Fin n → Fin 2) :
    pauliForm K ν (Pi.single x 1) (Pi.single y 1) = pauliWord K ν x y := by
  simp [pauliForm, Pi.single_apply]

/-- Pauli words have entries `0, ±1`, so a ring hom carries them to the target's Pauli words. -/
theorem map_pauliWord {L : Type*} [CommRing L] (f : K →+* L) (ν : Fin n → Fin 4)
    (x y : Fin n → Fin 2) : f (pauliWord K ν x y) = pauliWord L ν x y := by
  rw [pauliWord, pauliWord, map_prod]
  refine prod_congr rfl fun i _ => ?_
  generalize ν i = a
  generalize x i = s
  generalize y i = t
  fin_cases a <;> fin_cases s <;> fin_cases t <;> simp [pauli1]

end Commutative

section Field

variable {K : Type*} [Field K] {n : ℕ} {w : (Fin n → Fin 4) → K}

/-- First polarization (in `X`) of the sum-of-squares identity. -/
theorem sos_polar_left (h2 : (2 : K) ≠ 0)
    (hw : ∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2)
    (X₁ X₂ Y : (Fin n → Fin 2) → K) :
    ∑ ν, w ν * (pauliForm K ν X₁ Y * pauliForm K ν X₂ Y) =
      (∑ x, X₁ x * X₂ x) * ∑ y, Y y ^ 2 := by
  have h12 := hw (X₁ + X₂) Y
  have h1 := hw X₁ Y
  have h2' := hw X₂ Y
  simp only [pauliForm_add_left, Pi.add_apply] at h12
  have e1 : ∑ x, (X₁ x + X₂ x) ^ 2 =
      ∑ x, X₁ x ^ 2 + ∑ x, X₂ x ^ 2 + 2 * ∑ x, X₁ x * X₂ x := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  have e2 : ∑ ν, w ν * (pauliForm K ν X₁ Y + pauliForm K ν X₂ Y) ^ 2 =
      ∑ ν, w ν * pauliForm K ν X₁ Y ^ 2 + ∑ ν, w ν * pauliForm K ν X₂ Y ^ 2 +
        2 * ∑ ν, w ν * (pauliForm K ν X₁ Y * pauliForm K ν X₂ Y) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ν _ => by ring
  rw [e1, e2] at h12
  apply mul_left_cancel₀ h2
  linear_combination h1 + h2' - h12

/-- Full polarization (in `X` and in `Y`) of the sum-of-squares identity. -/
theorem sos_polar (h2 : (2 : K) ≠ 0)
    (hw : ∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2)
    (X₁ X₂ Y₁ Y₂ : (Fin n → Fin 2) → K) :
    ∑ ν, w ν * (pauliForm K ν X₁ Y₁ * pauliForm K ν X₂ Y₂ +
        pauliForm K ν X₁ Y₂ * pauliForm K ν X₂ Y₁) =
      2 * ((∑ x, X₁ x * X₂ x) * ∑ y, Y₁ y * Y₂ y) := by
  have h12 := sos_polar_left h2 hw X₁ X₂ (Y₁ + Y₂)
  have h1 := sos_polar_left h2 hw X₁ X₂ Y₁
  have h2' := sos_polar_left h2 hw X₁ X₂ Y₂
  simp only [pauliForm_add_right, Pi.add_apply] at h12
  have e1 : ∑ y, (Y₁ y + Y₂ y) ^ 2 =
      ∑ y, Y₁ y ^ 2 + ∑ y, Y₂ y ^ 2 + 2 * ∑ y, Y₁ y * Y₂ y := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  have e2 : ∑ ν, w ν * ((pauliForm K ν X₁ Y₁ + pauliForm K ν X₁ Y₂) *
        (pauliForm K ν X₂ Y₁ + pauliForm K ν X₂ Y₂)) =
      ∑ ν, w ν * (pauliForm K ν X₁ Y₁ * pauliForm K ν X₂ Y₁) +
        ∑ ν, w ν * (pauliForm K ν X₁ Y₂ * pauliForm K ν X₂ Y₂) +
        ∑ ν, w ν * (pauliForm K ν X₁ Y₁ * pauliForm K ν X₂ Y₂ +
          pauliForm K ν X₁ Y₂ * pauliForm K ν X₂ Y₁) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ν _ => by ring
  rw [e1, e2] at h12
  linear_combination h12 - h1 - h2'

/-- **Tensor identity.** A Pauli sum-of-squares identity over `K` forces
`Σ_ν w_ν (P_ν[x,y] P_ν[u,v] + P_ν[x,v] P_ν[u,y]) = 2 [x = u ∧ y = v]`. -/
theorem sos_tensor_identity (h2 : (2 : K) ≠ 0)
    (hw : ∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2)
    (x y u v : Fin n → Fin 2) :
    ∑ ν, w ν * (pauliWord K ν x y * pauliWord K ν u v + pauliWord K ν x v * pauliWord K ν u y) =
      if x = u ∧ y = v then 2 else 0 := by
  have h := sos_polar h2 hw (Pi.single x 1) (Pi.single u 1) (Pi.single y 1) (Pi.single v 1)
  simp only [pauliForm_single] at h
  rw [h]
  by_cases hxu : x = u <;> by_cases hyv : y = v <;>
    simp [Pi.single_apply, hxu, hyv, @eq_comm _ u x, @eq_comm _ v y]

/-- The tensor identity transported to an extension field `L`. -/
theorem sos_tensor_identity_map (h2 : (2 : K) ≠ 0)
    (hw : ∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2)
    {L : Type*} [Field L] [Algebra K L] (x y u v : Fin n → Fin 2) :
    ∑ ν, algebraMap K L (w ν) *
        (pauliWord L ν x y * pauliWord L ν u v + pauliWord L ν x v * pauliWord L ν u y) =
      if x = u ∧ y = v then 2 else 0 := by
  have hP (ν : Fin n → Fin 4) (a b : Fin n → Fin 2) :
      pauliWord L ν a b = algebraMap K L (pauliWord K ν a b) :=
    (map_pauliWord (algebraMap K L) ν a b).symm
  simp only [hP, ← map_mul, ← map_add, ← map_sum, sos_tensor_identity h2 hw x y u v]
  rw [apply_ite (algebraMap K L), map_ofNat, map_zero]

end Field

/-- Reordering a triple sum. -/
theorem sum_rev3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (g : α → β → γ → M) : ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ b, ∑ a, g a b c := by
  rw [sum_comm]
  refine (sum_congr rfl fun b _ => sum_comm).trans ?_
  exact sum_comm

/-- Moving an outer sum inside a quadruple sum. -/
theorem sum_comm_four {ι α β γ δ M : Type*} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [AddCommMonoid M] (g : ι → α → β → γ → δ → M) :
    ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, g i a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, g i a b c d := by
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_comm]

section Noncommutative

variable {L : Type*} [Field L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {n : ℕ}
  (X Y : (Fin n → Fin 2) → 𝒜)

/-- `f^xy f^xy = Σ_{x,y,u,v} P_ν[x,y] P_ν[u,v] X_x Y_y X_u Y_v`. -/
theorem fxy_mul_fxy (ν : Fin n → Fin 4) :
    fxy (L := L) X Y ν * fxy (L := L) X Y ν =
      ∑ x, ∑ y, ∑ u, ∑ v, (pauliWord L ν x y * pauliWord L ν u v) • (X x * Y y * X u * Y v) := by
  rw [fxy, sum_mul_sum]
  simp_rw [sum_mul_sum, smul_mul_smul_comm, ← mul_assoc]
  exact sum_congr rfl fun x _ => sum_comm

/-- `f ⋆ f^yx = Σ_{x,y,u,v} P_ν[x,v] P_ν[u,y] X_x Y_y X_u Y_v`. -/
theorem fstar_fyx (ν : Fin n → Fin 4) :
    fstar (L := L) X Y ν (fyx (L := L) X Y ν) =
      ∑ x, ∑ y, ∑ u, ∑ v, (pauliWord L ν x v * pauliWord L ν u y) • (X x * Y y * X u * Y v) := by
  rw [fstar, fyx]
  simp_rw [mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc, smul_sum, smul_smul, ← mul_assoc]
  exact sum_congr rfl fun x _ => sum_rev3 _

/-- `f^[2]` in coordinates. -/
theorem f2_eq (ν : Fin n → Fin 4) :
    f2 (L := L) X Y ν =
      ∑ x, ∑ y, ∑ u, ∑ v, ((2 : L)⁻¹ * (pauliWord L ν x y * pauliWord L ν u v +
        pauliWord L ν x v * pauliWord L ν u y)) • (X x * Y y * X u * Y v) := by
  rw [f2, fxy_mul_fxy, fstar_fyx]
  simp only [← sum_add_distrib, ← add_smul, smul_sum, smul_smul]

end Noncommutative

/-- **Hrubeš's Lemma 22, algebraic core.** A Pauli sum-of-squares identity over `K` (with
`2 ≠ 0`) gives `Σ_ν w_ν f_ν^[2] = Σ_{x,y} X_x Y_y X_x Y_y` in every algebra over an extension
field `L` of `K`. -/
theorem sos_f2 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ} (w : (Fin n → Fin 4) → K)
    (hw : ∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2)
    {L : Type*} [Field L] [Algebra K L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜]
    (X Y : (Fin n → Fin 2) → 𝒜) :
    ∑ ν, algebraMap K L (w ν) • f2 (L := L) X Y ν = ∑ x, ∑ y, X x * Y y * X x * Y y := by
  have h2L : (2 : L) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K L)).mpr h2
    rwa [map_ofNat] at h
  have coef (x y u v : Fin n → Fin 2) :
      ∑ ν, algebraMap K L (w ν) * ((2 : L)⁻¹ * (pauliWord L ν x y * pauliWord L ν u v +
        pauliWord L ν x v * pauliWord L ν u y)) = if x = u ∧ y = v then 1 else 0 := by
    calc _ = (2 : L)⁻¹ * ∑ ν, algebraMap K L (w ν) * (pauliWord L ν x y * pauliWord L ν u v +
          pauliWord L ν x v * pauliWord L ν u y) := by
          rw [mul_sum]
          exact sum_congr rfl fun ν _ => mul_left_comm _ _ _
      _ = _ := by
          rw [sos_tensor_identity_map h2 hw x y u v]
          split_ifs <;> simp [h2L]
  simp only [f2_eq, smul_sum, smul_smul]
  rw [sum_comm_four]
  simp only [← sum_smul, coef]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_eq_single x, Fintype.sum_eq_single y]
  · simp
  · intro v hv
    simp [Ne.symm hv]
  · intro u hu
    simp [Ne.symm hu]

end PauliCubes
