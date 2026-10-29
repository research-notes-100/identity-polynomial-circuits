/-
The symplectic and quadratic forms in Majorana coordinates.

For words `v = (x, z)`, `w = (x', z')` the commutation form is `x·z' + z·x'` and the transpose sign is
`(−1)^{x·z}`. In Jordan–Wigner coordinates `(s, a)`, with `|A| = |s| + |a|` Majoranas:
`symp = |A||A'| + s·s' + a·a'` (`symp_jw`), and `x·z = |a| + e₂(s) + e₂(a) + |s||a|` (`q_jw`), where
`e₂(v) = Σ_{j<k} v_j v_k` (all over `ZMod 2`).
-/
import IDMM.MajBasic

noncomputable section
namespace IDMM
open Finset

variable {n : ℕ}

/-- The sum of the bits. -/
def bsum (v : Bits n) : ZMod 2 := ∑ i, v i

/-- `e₂(v) = Σ_{j<k} v_j v_k`. -/
def e2 (v : Bits n) : ZMod 2 := ∑ j, ∑ k ∈ univ.filter (fun k => j < k), v j * v k

theorem bsum_add (u v : Bits n) : bsum (u + v) = bsum u + bsum v := by
  simp [bsum, sum_add_distrib]

/-- Split a double sum over `Fin n` by the order of the indices. -/
theorem pair_split {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ j, ∑ k, f j k = (∑ j, ∑ k ∈ univ.filter (fun k => j < k), f j k) +
      (∑ j, ∑ k ∈ univ.filter (fun k => j < k), f k j) + ∑ j, f j j := by
  have h1 : ∀ j, ∑ k, f j k = (∑ k, if j < k then f j k else 0) + (∑ k, if k < j then f j k else 0) +
      ∑ k, if k = j then f j k else 0 := by
    intro j
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_gt h]
    · subst h; simp
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
  have h2 : (∑ j, ∑ k, if k < j then f j k else 0) = ∑ j, ∑ k ∈ univ.filter (fun k => j < k), f k j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_filter]
  simp only [h1, sum_add_distrib, h2, sum_filter, sum_ite_eq', mem_univ, if_true]

theorem dot_add_left (u v w : Bits n) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, sum_add_distrib]

theorem dot_add_right (u v w : Bits n) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, sum_add_distrib]

/-- The double-sum part of the commutation form. -/
private theorem cross_terms (x x' : Bits n) :
    (∑ j, x j * suffix x' j) + (∑ j, suffix x j * x' j) = bsum x * bsum x' + dot x x' := by
  have hp := pair_split (fun j k => x j * x' k)
  have hlhs : (∑ j, ∑ k, x j * x' k) = bsum x * bsum x' := by
    rw [bsum, bsum, sum_mul_sum]
  have h1 : (∑ j, x j * suffix x' j) = ∑ j, ∑ k ∈ univ.filter (fun k => j < k), x j * x' k := by
    simp [suffix, mul_sum]
  have h2 : (∑ j, suffix x j * x' j) = ∑ j, ∑ k ∈ univ.filter (fun k => j < k), x k * x' j := by
    simp [suffix, sum_mul]
  rw [h1, h2]
  have h3 : (∑ j, x j * x' j) = dot x x' := rfl
  rw [hlhs, h3] at hp
  -- over ZMod 2, `A + B + D = S` gives `A + B = S + D`
  have hD : dot x x' + dot x x' = 0 := ZMod2_add_self _
  calc _ = (∑ j, ∑ k ∈ univ.filter (fun k => j < k), x j * x' k) +
        (∑ j, ∑ k ∈ univ.filter (fun k => j < k), x k * x' j) + dot x x' + dot x x' := by
          rw [add_assoc _ (dot x x'), hD, add_zero]
    _ = _ := by rw [← hp]

/-- **Commutation form in Majorana coordinates.** `x·z' + z·x' = |A||A'| + s·s' + a·a'` over `ZMod 2`. -/
theorem symp_jw (s a s' a' : Bits n) :
    dot (jwX s a) (jwZ s' a') + dot (jwZ s a) (jwX s' a') =
      (bsum s + bsum a) * (bsum s' + bsum a') + dot s s' + dot a a' := by
  have hz : ∀ s a : Bits n, jwZ s a = a + fun j => suffix (s + a) j := fun _ _ => rfl
  have hsx : ∀ (u : Bits n) (y : Bits n), dot u (fun j => suffix y j) = ∑ j, u j * suffix y j :=
    fun _ _ => rfl
  have hxs : ∀ (u : Bits n) (y : Bits n), dot (fun j => suffix y j) u = ∑ j, suffix y j * u j :=
    fun _ _ => rfl
  rw [hz, hz, dot_add_right, dot_add_left, hsx, hxs]
  have hc := cross_terms (jwX s a) (jwX s' a')
  simp only [jwX] at hc ⊢
  rw [show dot (s + a) a' + (∑ j, (s + a) j * suffix (s' + a') j) +
      (dot a (s' + a') + ∑ j, suffix (s + a) j * (s' + a') j) =
      dot (s + a) a' + dot a (s' + a') +
      ((∑ j, (s + a) j * suffix (s' + a') j) + ∑ j, suffix (s + a) j * (s' + a') j) by ring, hc,
    bsum_add, bsum_add]
  have hpt : dot (s + a) a' + dot a (s' + a') + dot (s + a) (s' + a') = dot s s' + dot a a' := by
    simp only [dot, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]
    generalize s j = p; generalize a j = q; generalize s' j = p'; generalize a' j = q'
    revert p q p' q'; decide
  linear_combination hpt

/-- `e₂` of a sum. -/
theorem e2_add (u v : Bits n) : e2 (u + v) = e2 u + e2 v + bsum u * bsum v + dot u v := by
  have hp := pair_split (fun j k => u j * v k)
  have hlhs : (∑ j, ∑ k, u j * v k) = bsum u * bsum v := by rw [bsum, bsum, sum_mul_sum]
  rw [hlhs] at hp
  have hD : dot u v + dot u v = 0 := ZMod2_add_self _
  have hexp : e2 (u + v) = e2 u + e2 v + ((∑ j, ∑ k ∈ univ.filter (fun k => j < k), u j * v k) +
      ∑ j, ∑ k ∈ univ.filter (fun k => j < k), u k * v j) := by
    simp only [e2, Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, hp]
  have : dot u v = ∑ j, u j * v j := rfl
  rw [← this]
  linear_combination (-1 : ZMod 2) * hD

/-- **Transpose parity in Majorana coordinates.** `x·z = |a| + e₂(s) + e₂(a) + |s||a|` over `ZMod 2`. -/
theorem q_jw (s a : Bits n) :
    dot (jwX s a) (jwZ s a) = bsum a + e2 s + e2 a + bsum s * bsum a := by
  have hz : jwZ s a = a + fun j => suffix (s + a) j := rfl
  rw [hz, dot_add_right]
  have hx : jwX s a = s + a := rfl
  rw [hx]
  have hsuf : dot (s + a) (fun j => suffix (s + a) j) = e2 (s + a) := by
    simp [dot, e2, suffix, mul_sum]
  rw [hsuf, e2_add]
  have hpt : dot (s + a) a + dot s a = bsum a := by
    simp only [dot, bsum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]
    generalize s j = p; generalize a j = q
    revert p q; decide
  linear_combination hpt

end IDMM
