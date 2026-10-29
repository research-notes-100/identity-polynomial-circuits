/-
Character sums over a Majorana class are products of Krawtchouk numbers.

`Σ_{weight v = k} (−1)^{v·c} = [z^k] (1 − z)^{|c|} (1 + z)^{n − |c|}` (`sum_weight_sgnB`), and the commutation
character summed over a class `(a, b)` against a word of class `(c, d)` is
`(−1)^{(a+b)(c+d)} K_a(c) K_b(d)` (`class_sum`).
-/
import IDMM.MajFourier
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace IDMM
open Finset Polynomial

variable {n : ℕ} {K : Type*} [Field K]

theorem sum_zmod2_gen {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ β, f β = f 0 + f 1 :=
  Fin.sum_univ_two f

theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

/-- The Krawtchouk polynomial `(1 − z)^c (1 + z)^{n − c}` over `ℤ`. -/
def krawPoly (n c : ℕ) : ℤ[X] := (1 - X) ^ c * (1 + X) ^ (n - c)

theorem weight_eq_sum (v : Bits n) : weight v = ∑ i, (v i).val := by
  classical
  rw [weight, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  rcases zmod2_cases (v i) with h | h <;> rw [h] <;> simp [zmod2_one_ne_zero.symm]
  · rfl

theorem bsum_eq_weight (v : Bits n) : bsum v = (weight v : ZMod 2) := by
  rw [weight_eq_sum, bsum]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [ZMod.natCast_zmod_val]

/-- The generating polynomial of the characters, by weight. -/
theorem gen_sgnB (c : Bits n) :
    ∑ v : Bits n, C (sgnB (dot v c)) * X ^ weight v =
      ∏ i, (1 + C (sgnB (c i)) * X : K[X]) := by
  classical
  have hfac : ∀ i, (1 + C (sgnB (c i)) * X : K[X]) =
      ∑ β : ZMod 2, C (sgnB (β * c i)) * X ^ β.val := by
    intro i
    rw [sum_zmod2_gen]
    simp [sgnB_zero, zmod2_val_one]
  simp only [hfac]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum, ← weight_eq_sum, dot, sgnB_sum]

theorem prod_one_add (c : Bits n) :
    ∏ i, (1 + C (sgnB (c i)) * X : K[X]) =
      (1 - X) ^ weight c * (1 + X) ^ (n - weight c) := by
  classical
  have hsplit : ∀ i, (1 + C (sgnB (c i)) * X : K[X]) =
      if c i = 1 then 1 - X else 1 + X := by
    intro i
    rcases zmod2_cases (c i) with h | h <;> rw [h] <;> simp [sgnB, sub_eq_add_neg]
  simp only [hsplit, prod_ite, prod_const]
  congr 2
  rw [weight]
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => c i = 1)
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- **Characters summed over a weight class.** -/
theorem sum_weight_sgnB (c : Bits n) (k : ℕ) :
    ∑ v ∈ univ.filter (fun v : Bits n => weight v = k), (sgnB (dot v c) : K) =
      ((krawPoly n (weight c)).coeff k : K) := by
  classical
  have h := congrArg (fun p : K[X] => p.coeff k) ((gen_sgnB c).trans (prod_one_add c))
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero] at h
  rw [sum_filter]
  have hm : (krawPoly n (weight c)).map (Int.castRingHom K) =
      (1 - X) ^ weight c * (1 + X) ^ (n - weight c) := by
    simp [krawPoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add]
  rw [show ((krawPoly n (weight c)).coeff k : K) =
      ((krawPoly n (weight c)).map (Int.castRingHom K)).coeff k by rw [coeff_map]; rfl, hm, ← h]
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : weight v = k
  · rw [if_pos hv, if_pos hv.symm]
  · rw [if_neg hv, if_neg (Ne.symm hv)]

end IDMM
