/-
Class-constant weights: their Fourier transform is the Krawtchouk system, and the transpose parity of a
label depends only on its class.
-/
import IDMM.MajKraw

noncomputable section
namespace IDMM
open Finset Polynomial

variable {n : ℕ} {K : Type*} [Field K]

theorem sgnB_natCast (m : ℕ) : (sgnB (m : ZMod 2) : K) = (-1 : K) ^ m := by
  induction m with
  | zero => simp [sgnB_zero]
  | succ m ih =>
    rw [Nat.cast_succ, sgnB_add, ih, pow_succ]
    simp [sgnB, zmod2_one_ne_zero]

theorem weight_le (v : Bits n) : weight v ≤ n := by
  calc weight v ≤ (univ : Finset (Fin n)).card := card_filter_le _ _
    _ = n := by simp

/-- Group a sum over bit vectors by weight. -/
theorem sum_by_weight {M : Type*} [AddCommMonoid M] (f : Bits n → M) :
    ∑ v, f v = ∑ k ∈ range (n + 1), ∑ v ∈ univ.filter (fun v : Bits n => weight v = k), f v := by
  classical
  rw [sum_fiberwise_of_maps_to (g := weight)]
  intro v _
  simpa [Nat.lt_succ_iff] using weight_le v

/-- **Fourier transform of class-constant weights.** -/
theorem fourier_class (W : ℕ → ℕ → K) (s' a' : Bits n) :
    fourier (fun ν => W (classOf ν).1 (classOf ν).2) (jwX s' a') (jwZ s' a') =
      ∑ a0 ∈ range (n + 1), ∑ b0 ∈ range (n + 1),
        W a0 b0 * (-1 : K) ^ ((a0 + b0) * (weight s' + weight a')) *
          (krawPoly n (weight s')).coeff a0 * (krawPoly n (weight a')).coeff b0 := by
  classical
  rw [fourier, ← jwEquiv.sum_comp, Fintype.sum_prod_type]
  -- the summand in Majorana coordinates
  have hterm : ∀ s a : Bits n,
      W (classOf (jwEquiv (s, a))).1 (classOf (jwEquiv (s, a))).2 *
          sgnB (dot (wZ (jwEquiv (s, a))) (jwX s' a') + dot (wX (jwEquiv (s, a))) (jwZ s' a')) =
        W (weight s) (weight a) * (-1 : K) ^ ((weight s + weight a) * (weight s' + weight a')) *
          (sgnB (dot s s') * sgnB (dot a a')) := by
    intro s a
    have hc : classOf (jwEquiv (s, a)) = (weight s, weight a) := by
      simp [classOf, jwEquiv, majS_jw, majA_jw]
    have hx : wX (jwEquiv (s, a)) = jwX s a := wX_ofXZ _ _
    have hz : wZ (jwEquiv (s, a)) = jwZ s a := wZ_ofXZ _ _
    rw [hc, hx, hz, add_comm, symp_jw, bsum_eq_weight, bsum_eq_weight, bsum_eq_weight,
      bsum_eq_weight, sgnB_add, sgnB_add, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_mul,
      sgnB_natCast]
    ring
  simp only [hterm]
  -- group by the weights of `s` and of `a`
  rw [sum_by_weight]
  refine sum_congr rfl fun a0 _ => ?_
  have hinner : ∀ s ∈ univ.filter (fun v : Bits n => weight v = a0),
      ∑ a : Bits n, W (weight s) (weight a) *
          (-1 : K) ^ ((weight s + weight a) * (weight s' + weight a')) *
          (sgnB (dot s s') * sgnB (dot a a')) =
        sgnB (dot s s') * ∑ b0 ∈ range (n + 1), W a0 b0 *
          (-1 : K) ^ ((a0 + b0) * (weight s' + weight a')) *
          ∑ a ∈ univ.filter (fun v : Bits n => weight v = b0), sgnB (dot a a') := by
    intro s hs
    rw [mem_filter] at hs
    rw [sum_by_weight, mul_sum]
    refine sum_congr rfl fun b0 _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_filter] at ha
    rw [hs.2, ha.2]; ring
  rw [sum_congr rfl hinner, ← sum_mul, sum_weight_sgnB, mul_sum]
  refine sum_congr rfl fun b0 _ => ?_
  rw [sum_weight_sgnB]; ring

/-! ## Transpose parity of a label -/

theorem two_mul_e2_int (v : Bits n) :
    2 * (∑ j, ∑ k ∈ univ.filter (fun k => j < k), ((v j).val : ℤ) * (v k).val) =
      (weight v : ℤ) * weight v - weight v := by
  have hp := pair_split (fun j k => ((v j).val : ℤ) * (v k).val)
  have hsq : ∀ j, ((v j).val : ℤ) * (v j).val = (v j).val := by
    intro j; rcases zmod2_cases (v j) with h | h <;> rw [h] <;> rfl
  have hsym : (∑ j, ∑ k ∈ univ.filter (fun k => j < k), ((v k).val : ℤ) * (v j).val) =
      ∑ j, ∑ k ∈ univ.filter (fun k => j < k), ((v j).val : ℤ) * (v k).val := by
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_comm _ _
  have hw : (weight v : ℤ) = ∑ j, ((v j).val : ℤ) := by rw [weight_eq_sum]; push_cast; rfl
  simp only [hsq, hsym] at hp
  rw [hw, sum_mul_sum, hp]; ring

theorem choose_two_int (w : ℕ) : 2 * ((w.choose 2 : ℕ) : ℤ) = (w : ℤ) * w - w := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- `e₂(v) = C(|v|, 2)` over `ZMod 2`. -/
theorem e2_eq_choose (v : Bits n) : e2 v = ((weight v).choose 2 : ZMod 2) := by
  have hz : (∑ j, ∑ k ∈ univ.filter (fun k => j < k), ((v j).val : ℤ) * (v k).val) =
      ((weight v).choose 2 : ℤ) := by
    have h1 := two_mul_e2_int v
    have h2 := choose_two_int (weight v)
    have : (2 : ℤ) * (∑ j, ∑ k ∈ univ.filter (fun k => j < k), ((v j).val : ℤ) * (v k).val) =
        2 * ((weight v).choose 2 : ℤ) := by rw [h1, h2]
    exact mul_left_cancel₀ two_ne_zero this
  have hcast := congrArg (fun z : ℤ => (z : ZMod 2)) hz
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at hcast
  rw [e2]; exact hcast

theorem add_choose_two (c d : ℕ) : (c + d).choose 2 = c.choose 2 + d.choose 2 + c * d := by
  have h := choose_two_int (c + d)
  have hc := choose_two_int c
  have hd := choose_two_int d
  have : (2 : ℤ) * (((c + d).choose 2 : ℕ) : ℤ) = 2 * ((c.choose 2 + d.choose 2 + c * d : ℕ) : ℤ) := by
    rw [h]; push_cast; linear_combination -hc - hd
  exact_mod_cast mul_left_cancel₀ two_ne_zero this

/-- **Transpose parity in terms of the class.** -/
theorem q_class (s a : Bits n) :
    dot (jwX s a) (jwZ s a) = ((weight a + (weight s + weight a).choose 2 : ℕ) : ZMod 2) := by
  rw [q_jw, bsum_eq_weight, bsum_eq_weight, e2_eq_choose, e2_eq_choose, add_choose_two]
  push_cast; ring

end IDMM
