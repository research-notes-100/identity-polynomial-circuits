/-
From Fourier conditions on word weights to a weighted sum of squares of Pauli forms.

`fourier w t b = Σ_ν w_ν (−1)^{z_ν·t + x_ν·b}`. If it equals `2^n [t = 0 ∧ b = 0]` whenever `t·b = 0`
(the "symmetric" labels), then `Σ_ν w_ν (Xᵀ P_ν Y)² = (Σ X²)(Σ Y²)` (`sos_of_fourier`).
-/
import IDMM.MajForms
import PauliCubes.NCIdentity

noncomputable section
namespace IDMM
open Finset PauliCubes

variable {n : ℕ} {K : Type*} [Field K] [NeZero (2 : K)]

theorem bits_add_self (v : Bits n) : v + v = 0 := funext fun i => ZMod2_add_self (v i)

theorem bits_eq_add_iff {y x d : Bits n} : y = x + d ↔ d = x + y := by
  constructor <;> intro h <;> subst h
  · rw [← add_assoc, bits_add_self, zero_add]
  · rw [← add_assoc, bits_add_self, zero_add]

theorem sum_zmod2 (f : ZMod 2 → K) : ∑ β, f β = f 0 + f 1 := Fin.sum_univ_two f

/-- **Character orthogonality.** `Σ_b (−1)^{c·b} = 2^n [c = 0]`. -/
theorem sum_sgnB_dot (c : Bits n) : ∑ b : Bits n, (sgnB (dot c b) : K) = if c = 0 then 2 ^ n else 0 := by
  classical
  have hprod : ∀ b : Bits n, (sgnB (dot c b) : K) = ∏ i, (sgnB (c i * b i) : K) := fun b => by
    rw [dot, sgnB_sum]
  simp only [hprod]
  have hps := Fintype.prod_sum (fun (i : Fin n) (β : ZMod 2) => (sgnB (c i * β) : K))
  rw [← hps]
  have hfac : ∀ i, ∑ β : ZMod 2, (sgnB (c i * β) : K) = if c i = 0 then 2 else 0 := by
    intro i
    rw [sum_zmod2, mul_zero, mul_one, sgnB_zero]
    rcases zmod2_cases (c i) with h | h <;> rw [h] <;> simp [sgnB, zmod2_one_ne_zero] <;> norm_num
  simp only [hfac]
  by_cases hc : c = 0
  · rw [if_pos hc]
    simp [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hc]
    have : ∃ i, c i ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    obtain ⟨i, hi⟩ := this
    exact prod_eq_zero (mem_univ i) (by rw [if_neg hi])

/-- **Fourier inversion** on `(ZMod 2)^n`. -/
theorem fourier_inv (H : Bits n → K) (d : Bits n) :
    ∑ b, sgnB (dot d b) * ∑ d', sgnB (dot d' b) * H d' = 2 ^ n * H d := by
  classical
  simp only [mul_sum]
  rw [sum_comm]
  have : ∀ d', ∑ b, sgnB (dot d b) * (sgnB (dot d' b) * H d') =
      (if d + d' = 0 then 2 ^ n else 0) * H d' := by
    intro d'
    rw [← sum_sgnB_dot (d + d'), sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [dot_add_left, sgnB_add]; ring
  simp only [this]
  have hiff : ∀ d', d + d' = 0 ↔ d' = d := fun d' => by
    constructor
    · intro h
      have := congrArg (· + d) h
      simp only [zero_add] at this
      rw [← this, add_comm d d', add_assoc, bits_add_self, add_zero]
    · intro h; rw [h, bits_add_self]
  simp only [hiff, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]

/-- The Fourier transform of word weights at the label `(t, b)`. -/
def fourier (w : (Fin n → Fin 4) → K) (t b : Bits n) : K :=
  ∑ ν, w ν * sgnB (dot (wZ ν) t + dot (wX ν) b)

/-- The partial transform: words with x-part `d`, against the z-character `t`. -/
def gpart (w : (Fin n → Fin 4) → K) (d t : Bits n) : K :=
  ∑ ν, if wX ν = d then w ν * sgnB (dot (wZ ν) t) else 0

theorem prod_term (w : (Fin n → Fin 4) → K) (x y u v : Bits n) :
    ∑ ν, w ν * (pauliWord K ν x y * pauliWord K ν u v) =
      if x + y = u + v then gpart w (x + y) (x + u) else 0 := by
  classical
  simp only [pauliWord_eq, gpart]
  by_cases hxy : x + y = u + v
  · rw [if_pos hxy]
    refine sum_congr rfl fun ν _ => ?_
    by_cases hX : wX ν = x + y
    · have h1 : y = x + wX ν := by rw [hX, ← add_assoc, bits_add_self, zero_add]
      have h2 : v = u + wX ν := by
        rw [hX, hxy, ← add_assoc, bits_add_self, zero_add]
      rw [if_pos h1, if_pos h2, if_pos hX, ← sgnB_add, ← dot_add_right]
    · rw [if_neg hX]
      have : ¬ y = x + wX ν := fun h => hX (bits_eq_add_iff.mp h)
      rw [if_neg this]; ring
  · rw [if_neg hxy]
    refine sum_eq_zero fun ν _ => ?_
    by_cases h1 : y = x + wX ν
    · have h2 : ¬ v = u + wX ν := by
        intro h2; apply hxy
        rw [h1, h2, ← add_assoc, ← add_assoc, bits_add_self, bits_add_self]
      rw [if_neg h2]; ring
    · rw [if_neg h1]; ring

theorem transform_gpart (w : (Fin n → Fin 4) → K) (t b : Bits n) :
    ∑ d, sgnB (dot d b) * gpart w d t = fourier w t b := by
  classical
  simp only [gpart, mul_sum, fourier]
  rw [sum_comm]
  refine sum_congr rfl fun ν _ => ?_
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  rw [sgnB_add]; ring

theorem gpart_relation (w : (Fin n → Fin 4) → K)
    (hF : ∀ t b : Bits n, dot t b = 0 → fourier w t b = if t = 0 ∧ b = 0 then 2 ^ n else 0)
    (d t : Bits n) : gpart w d t + gpart w (d + t) t = if t = 0 then 2 else 0 := by
  classical
  -- the transform of `d ↦ gpart d t + gpart (d + t) t`
  have htr : ∀ b, ∑ d, sgnB (dot d b) * (gpart w d t + gpart w (d + t) t) =
      if t = 0 ∧ b = 0 then 2 ^ (n + 1) else 0 := by
    intro b
    have hshift : ∑ d, sgnB (dot d b) * gpart w (d + t) t =
        sgnB (dot t b) * fourier w t b := by
      rw [← transform_gpart, mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun d => ?_
      simp only [Equiv.coe_addRight, dot_add_left, sgnB_add]
      linear_combination (-(sgnB (dot d b) * gpart w (d + t) t)) * sgnB_sq (R := K) (dot t b)
    simp only [mul_add, sum_add_distrib, hshift, transform_gpart]
    rcases zmod2_cases (dot t b) with h | h
    · rw [h, sgnB_zero, hF t b h]
      split_ifs <;> ring
    · rw [h]
      have ht : ¬ (t = 0 ∧ b = 0) := by
        rintro ⟨rfl, -⟩
        simp [dot] at h
      rw [if_neg ht]
      simp [sgnB, zmod2_one_ne_zero]
  have hinv := fourier_inv (fun d => gpart w d t + gpart w (d + t) t) d
  simp only [htr] at hinv
  have hsum : ∑ b : Bits n, sgnB (dot d b) * (if t = 0 ∧ b = 0 then (2 : K) ^ (n + 1) else 0) =
      if t = 0 then 2 ^ (n + 1) else 0 := by
    by_cases ht : t = 0
    · simp only [ht, true_and, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true, if_pos]
      rw [show dot d 0 = 0 by simp [dot], sgnB_zero, one_mul]
    · simp [ht]
  rw [hsum] at hinv
  have h2n : (2 : K) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2n
  rw [← hinv]
  split_ifs <;> ring

/-- **Fourier conditions give the polarized tensor identity.** -/
theorem tensor_of_fourier (w : (Fin n → Fin 4) → K)
    (hF : ∀ t b : Bits n, dot t b = 0 → fourier w t b = if t = 0 ∧ b = 0 then 2 ^ n else 0)
    (x y u v : Bits n) :
    ∑ ν, w ν * (pauliWord K ν x y * pauliWord K ν u v + pauliWord K ν x v * pauliWord K ν u y) =
      if x = u ∧ y = v then 2 else 0 := by
  classical
  simp only [mul_add, sum_add_distrib, prod_term]
  have hiff : x + y = u + v ↔ x + v = u + y := by
    constructor <;> intro h
    · have := congrArg (· + (y + v)) h
      calc x + v = x + y + (y + v) := by rw [add_assoc, ← add_assoc y, bits_add_self, zero_add]
        _ = u + v + (y + v) := this
        _ = u + y := by rw [add_comm y v, ← add_assoc, add_assoc u, bits_add_self, add_zero]
    · have := congrArg (· + (y + v)) h
      calc x + y = x + v + (y + v) := by
            rw [add_comm y v, ← add_assoc, add_assoc x, bits_add_self, add_zero]
        _ = u + y + (y + v) := this
        _ = u + v := by rw [add_assoc, ← add_assoc y, bits_add_self, zero_add]
  by_cases h : x + y = u + v
  · rw [if_pos h, if_pos (hiff.mp h)]
    have hxv : x + v = (x + y) + (x + u) := by
      rw [hiff.mp h]
      rw [add_comm x y, add_assoc, ← add_assoc x x, bits_add_self, zero_add, add_comm]
    rw [hxv, gpart_relation w hF]
    by_cases hxu : x = u
    · subst hxu
      have hyv : y = v := by
        have := congrArg (x + ·) h
        simpa [← add_assoc, bits_add_self] using this
      rw [if_pos (bits_add_self x), if_pos ⟨rfl, hyv⟩]
    · have : ¬ x + u = 0 := by
        intro h0; apply hxu
        have := congrArg (· + u) h0
        simpa [add_assoc, bits_add_self] using this
      rw [if_neg this, if_neg (fun hh => hxu hh.1)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh)), add_zero]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

/-- **The polarized tensor identity gives the sum of squares.** -/
theorem sos_of_tensor (w : (Fin n → Fin 4) → K)
    (h : ∀ x y u v : Fin n → Fin 2,
      ∑ ν, w ν * (pauliWord K ν x y * pauliWord K ν u v + pauliWord K ν x v * pauliWord K ν u y) =
        if x = u ∧ y = v then 2 else 0)
    (X Y : (Fin n → Fin 2) → K) :
    (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2 := by
  classical
  set m : (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → K :=
    fun x y u v => X x * Y y * X u * Y v with hm
  have hA : ∀ ν, pauliForm K ν X Y ^ 2 =
      ∑ x, ∑ y, ∑ u, ∑ v, pauliWord K ν x y * pauliWord K ν u v * m x y u v := by
    intro ν
    rw [sq, pauliForm]
    simp only [sum_mul, mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun u _ =>
      sum_congr rfl fun v _ => ?_
    simp only [hm]; ring
  have hB : ∀ ν, pauliForm K ν X Y ^ 2 =
      ∑ x, ∑ y, ∑ u, ∑ v, pauliWord K ν x v * pauliWord K ν u y * m x y u v := by
    intro ν
    rw [hA ν]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_rev3]
    refine sum_congr rfl fun y _ => sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    simp only [hm]; ring
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  have hsum : 2 * ∑ ν, w ν * pauliForm K ν X Y ^ 2 =
      ∑ ν, ∑ x, ∑ y, ∑ u, ∑ v, w ν * (pauliWord K ν x y * pauliWord K ν u v +
        pauliWord K ν x v * pauliWord K ν u y) * m x y u v := by
    rw [mul_sum]
    refine sum_congr rfl fun ν _ => ?_
    rw [show (2 : K) * (w ν * pauliForm K ν X Y ^ 2) =
      w ν * pauliForm K ν X Y ^ 2 + w ν * pauliForm K ν X Y ^ 2 by ring]
    nth_rewrite 1 [hA ν]
    rw [hB ν]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun u _ =>
      sum_congr rfl fun v _ => ?_
    ring
  rw [hsum, sum_comm_four]
  simp only [← sum_mul, h]
  have hcol : ∀ x y : Fin n → Fin 2, ∑ u, ∑ v, (if x = u ∧ y = v then (2 : K) else 0) * m x y u v =
      2 * (X x ^ 2 * Y y ^ 2) := by
    intro x y
    rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
    · simp only [hm, and_self, if_true]; ring
    · intro v _ hv; simp [Ne.symm hv]
    · simp
    · intro u _ hu; refine sum_eq_zero fun v _ => ?_; simp [Ne.symm hu]
    · simp
  simp only [hcol, ← mul_sum, sum_mul_sum]

/-- **Fourier conditions give the sum of squares.** -/
theorem sos_of_fourier (w : (Fin n → Fin 4) → K)
    (hF : ∀ t b : Bits n, dot t b = 0 → fourier w t b = if t = 0 ∧ b = 0 then 2 ^ n else 0)
    (X Y : (Fin n → Fin 2) → K) :
    (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * pauliForm K ν X Y ^ 2 :=
  sos_of_tensor w (fun x y u v => tensor_of_fourier w hF x y u v) X Y

end IDMM
