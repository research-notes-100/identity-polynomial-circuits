/-
Reshaping a Pauli supported on the first `m` qubits (cycle 055 §2).

Split `Bits n ≃ Bits m × Bits (n − m)`. A Pauli `P_{α,β}` with `α, β` zero outside the first `m` qubits has
`Σ_{x,y} P[x,y] F(x,y) = Σ_p (−1)^{β·p} Σ_s F((p,s), (p+α, s))`: the form of a block word is one entry of a
`2^m × 2^(n−m)` by `2^(n−m) × 2^m` matrix product, read along a shifted diagonal with a Walsh sign.
-/
import IDMM.MajCost

noncomputable section
namespace IDMM
open Finset Matrix

variable {n m : ℕ} {K : Type*} [Field K]

/-- Concatenate a block part and a spectator part. -/
def joinB (hm : m ≤ n) (p : Bits m) (s : Bits (n - m)) : Bits n :=
  fun j => if h : j.val < m then p ⟨j.val, h⟩ else s ⟨j.val - m, by omega⟩

/-- The first `m` coordinates. -/
def restr (hm : m ≤ n) (v : Bits n) : Bits m := fun i => v ⟨i.val, by omega⟩

/-- The last `n − m` coordinates. -/
def rest (hm : m ≤ n) (v : Bits n) : Bits (n - m) := fun i => v ⟨i.val + m, by omega⟩

theorem joinB_restr_rest (hm : m ≤ n) (v : Bits n) : joinB hm (restr hm v) (rest hm v) = v := by
  funext j
  by_cases h : j.val < m
  · simp [joinB, restr, h]
  · simp only [joinB, rest, h, dite_false]
    congr 1; ext; simp; omega

theorem restr_joinB (hm : m ≤ n) (p : Bits m) (s : Bits (n - m)) : restr hm (joinB hm p s) = p := by
  funext i; simp [restr, joinB, i.is_lt]

theorem rest_joinB (hm : m ≤ n) (p : Bits m) (s : Bits (n - m)) : rest hm (joinB hm p s) = s := by
  funext i
  simp only [rest, joinB, show ¬ (i.val + m < m) by omega, dite_false]
  congr 1; ext; simp

/-- **The split.** -/
def splitEquiv (hm : m ≤ n) : Bits m × Bits (n - m) ≃ Bits n where
  toFun ps := joinB hm ps.1 ps.2
  invFun v := (restr hm v, rest hm v)
  left_inv ps := by simp [restr_joinB, rest_joinB]
  right_inv v := joinB_restr_rest hm v

/-- Supported on the first `m` qubits. -/
def LowSupp (m : ℕ) (v : Bits n) : Prop := ∀ j : Fin n, m ≤ j.val → v j = 0

theorem joinB_add_low (hm : m ≤ n) {α : Bits n} (hα : LowSupp m α) (p : Bits m) (s : Bits (n - m)) :
    joinB hm p s + α = joinB hm (p + restr hm α) s := by
  funext j
  by_cases h : j.val < m
  · simp [joinB, restr, h]
  · simp [joinB, h, hα j (by omega)]

theorem sum_low {M : Type*} [AddCommMonoid M] (hm : m ≤ n) (f : Fin n → M)
    (hf : ∀ j : Fin n, m ≤ j.val → f j = 0) : ∑ j, f j = ∑ i : Fin m, f (Fin.castLE hm i) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) ?_ (fun i : Fin m => f (Fin.castLE hm i)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin n => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem dot_low_joinB (hm : m ≤ n) {β : Bits n} (hβ : LowSupp m β) (p : Bits m) (s : Bits (n - m)) :
    dot β (joinB hm p s) = dot (restr hm β) p := by
  rw [dot, sum_low hm _ (fun j hj => by simp [hβ j hj])]
  refine sum_congr rfl fun i _ => ?_
  simp [joinB, restr, Fin.castLE, i.is_lt]

/-- **The reshape.** -/
theorem reshape {M : Type*} [AddCommMonoid M] [Module K M] (hm : m ≤ n) {α β : Bits n}
    (hα : LowSupp m α) (hβ : LowSupp m β) (F : Bits n → Bits n → M) :
    ∑ x, ∑ y, pmat K α β x y • F x y =
      ∑ p : Bits m, (sgnB (dot (restr hm β) p) : K) •
        ∑ s : Bits (n - m), F (joinB hm p s) (joinB hm (p + restr hm α) s) := by
  classical
  have h1 : ∀ x, ∑ y, pmat K α β x y • F x y = (sgnB (dot β x) : K) • F x (x + α) := by
    intro x
    simp only [pmat, ite_smul, zero_smul]
    rw [sum_ite_eq']; simp
  simp only [h1]
  rw [← (splitEquiv hm).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun p _ => ?_
  rw [smul_sum]
  refine sum_congr rfl fun s _ => ?_
  simp only [splitEquiv, Equiv.coe_fn_mk]
  rw [dot_low_joinB hm hβ, joinB_add_low hm hα]

/-! ## Low support of a canonical block word -/

theorem lowSupp_jw {A : MV n} (h : SuppIn A (canon n m)) :
    LowSupp m (jwX A.1 A.2) ∧ LowSupp m (jwZ A.1 A.2) :=
  ⟨fun j hj => (jw_supp_canon h j hj).1, fun j hj => (jw_supp_canon h j hj).2⟩

end IDMM
