/-
No cancellation: in a linear combination of distinct normal monomials with nonzero coefficients,
for every linear functional `ℓ` some surviving support point is at least as low as both vertices
`A` and `B` of any one of the monomials.

Route.
* For monotone `ℓ` (`ℓ₀ ≤ ℓ₁ ≤ ℓ₂ ≤ ℓ₃`), compare exponents first by `ℓ` and then (reversed) by the
  tie-break `zA e = 8e₀ + 4e₁ + 2e₂`. This strict order is additive, so leading exponents multiply.
* Each generator has a leading exponent; so `poly m` has leading exponent `A m` when
  `ℓ₀ + ℓ₃ ≤ ℓ₁ + ℓ₂` and `B m` otherwise. Both maps are injective on normal monomials.
* A minimal leading exponent among the monomials of the combination cannot cancel.
* A general `ℓ` is sorted by a permutation; the combination is symmetric, and `A`, `B` are
  antitone, so the rearrangement inequality finishes.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import PauliCubes.Generation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Rearrangement

open Finset MvPolynomial

namespace PauliCubes

/-- The linear functional `e ↦ Σ_a ℓ_a e_a` on exponent vectors. -/
noncomputable def lin (ℓ : Fin 4 → ℝ) (e : Fin 4 →₀ ℕ) : ℝ := ∑ a, ℓ a * (e a : ℝ)

/-! ## The key order -/

/-- The tie-break weight `8e₀ + 4e₁ + 2e₂`. -/
def zA (e : Fin 4 →₀ ℕ) : ℕ := 8 * e 0 + 4 * e 1 + 2 * e 2

/-- The unit exponent vector of variable `i`. -/
noncomputable abbrev E (i : Fin 4) : Fin 4 →₀ ℕ := Finsupp.single i 1

section Order

variable (ℓ : Fin 4 → ℝ)

/-- `p` is strictly below `q`: lower `ℓ`-value, or equal `ℓ`-value and larger tie-break weight. -/
def klt (p q : Fin 4 →₀ ℕ) : Prop :=
  lin ℓ p < lin ℓ q ∨ (lin ℓ p = lin ℓ q ∧ zA q < zA p)

@[simp] lemma lin_add (p q : Fin 4 →₀ ℕ) : lin ℓ (p + q) = lin ℓ p + lin ℓ q := by
  simp only [lin, Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, sum_add_distrib]

@[simp] lemma lin_E (i : Fin 4) : lin ℓ (E i) = ℓ i := by
  simp [lin, Finsupp.single_apply]

@[simp] lemma zA_add (p q : Fin 4 →₀ ℕ) : zA (p + q) = zA p + zA q := by
  simp only [zA, Finsupp.coe_add, Pi.add_apply]
  ring

@[simp] lemma zA_E0 : zA (E 0) = 8 := by simp [zA]
@[simp] lemma zA_E1 : zA (E 1) = 4 := by simp [zA]
@[simp] lemma zA_E2 : zA (E 2) = 2 := by simp [zA]
@[simp] lemma zA_E3 : zA (E 3) = 0 := by simp [zA]

variable {ℓ}

lemma klt_of {p q : Fin 4 →₀ ℕ} (h : lin ℓ p ≤ lin ℓ q) (hz : zA q < zA p) : klt ℓ p q := by
  rcases h.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hz⟩

lemma klt_irrefl {p : Fin 4 →₀ ℕ} : ¬ klt ℓ p p := by
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

lemma klt.lin_le {p q : Fin 4 →₀ ℕ} (h : klt ℓ p q) : lin ℓ p ≤ lin ℓ q := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma klt_trans {p q r : Fin 4 →₀ ℕ} (h₁ : klt ℓ p q) (h₂ : klt ℓ q r) : klt ℓ p r := by
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (h₂ ▸ h₁)
  · exact Or.inl (h₁ ▸ h₂)
  · exact Or.inr ⟨h₁.trans h₂, h₂'.trans h₁'⟩

lemma klt_add {p q x y : Fin 4 →₀ ℕ} (h₁ : klt ℓ p x) (h₂ : q = y ∨ klt ℓ q y) :
    klt ℓ (p + q) (x + y) := by
  unfold klt
  rw [lin_add, lin_add, zA_add, zA_add]
  rcases h₂ with rfl | h₂
  · rcases h₁ with h₁ | ⟨h₁, h₁'⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [h₁], by omega⟩
  · rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [h₁, h₂], by omega⟩

lemma klt_add_left {p q y : Fin 4 →₀ ℕ} (h : klt ℓ q y) : klt ℓ (p + q) (p + y) := by
  rw [add_comm p, add_comm p]
  exact klt_add h (Or.inl rfl)

end Order

/-! ## Leading exponents -/

section Lead

variable {K : Type*} [Field K] {ℓ : Fin 4 → ℝ}

/-- `P` has leading exponent `p`: `p` is in the support and strictly below every other point. -/
def HasLead (ℓ : Fin 4 → ℝ) (P : MvPolynomial (Fin 4) K) (p : Fin 4 →₀ ℕ) : Prop :=
  P.coeff p ≠ 0 ∧ ∀ e ∈ P.support, e ≠ p → klt ℓ p e

/-- Every support point of `Q` is strictly above `p`. -/
def AllAbove (ℓ : Fin 4 → ℝ) (p : Fin 4 →₀ ℕ) (Q : MvPolynomial (Fin 4) K) : Prop :=
  ∀ e ∈ Q.support, klt ℓ p e

lemma HasLead.lin_le {P : MvPolynomial (Fin 4) K} {p e : Fin 4 →₀ ℕ} (h : HasLead ℓ P p)
    (he : e ∈ P.support) : lin ℓ p ≤ lin ℓ e := by
  by_cases hep : e = p
  · rw [hep]
  · exact (h.2 e he hep).lin_le

lemma hasLead_one : HasLead ℓ (1 : MvPolynomial (Fin 4) K) 0 := by
  refine ⟨by simp, fun e he hne => ?_⟩
  rw [support_one, Finset.mem_singleton] at he
  exact absurd he hne

lemma hasLead_X (i : Fin 4) : HasLead ℓ (X i : MvPolynomial (Fin 4) K) (E i) := by
  refine ⟨by simp, fun e he hne => ?_⟩
  rw [support_X, Finset.mem_singleton] at he
  exact absurd he hne

lemma HasLead.neg {P : MvPolynomial (Fin 4) K} {p : Fin 4 →₀ ℕ} (h : HasLead ℓ P p) :
    HasLead ℓ (-P) p :=
  ⟨by rw [coeff_neg, neg_ne_zero]; exact h.1, by rw [support_neg]; exact h.2⟩

lemma HasLead.add {P Q : MvPolynomial (Fin 4) K} {p : Fin 4 →₀ ℕ} (hP : HasLead ℓ P p)
    (hQ : AllAbove ℓ p Q) : HasLead ℓ (P + Q) p := by
  classical
  have hq : Q.coeff p = 0 := by
    by_contra h
    exact klt_irrefl (hQ p (mem_support_iff.2 h))
  refine ⟨by rw [MvPolynomial.coeff_add, hq, add_zero]; exact hP.1, fun e he hne => ?_⟩
  rcases Finset.mem_union.1 (support_add he) with h | h
  · exact hP.2 e h hne
  · exact hQ e h

lemma HasLead.mul {P Q : MvPolynomial (Fin 4) K} {p q : Fin 4 →₀ ℕ} (hP : HasLead ℓ P p)
    (hQ : HasLead ℓ Q q) : HasLead ℓ (P * Q) (p + q) := by
  have key : ∀ x ∈ P.support, ∀ y ∈ Q.support, (x, y) ≠ (p, q) → klt ℓ (p + q) (x + y) := by
    intro x hx y hy hne
    by_cases hxp : x = p
    · subst hxp
      have hyq : y ≠ q := fun h => hne (by rw [h])
      exact klt_add_left (hQ.2 y hy hyq)
    · refine klt_add (hP.2 x hx hxp) ?_
      by_cases hyq : y = q
      · exact Or.inl hyq.symm
      · exact Or.inr (hQ.2 y hy hyq)
  refine ⟨?_, fun e he hne => ?_⟩
  · rw [coeff_mul, Finset.sum_eq_single (p, q)]
    · exact mul_ne_zero hP.1 hQ.1
    · rintro ⟨x, y⟩ hxy hne
      rw [Finset.mem_antidiagonal] at hxy
      by_contra h
      have hk := key x (mem_support_iff.2 (left_ne_zero_of_mul h)) y
        (mem_support_iff.2 (right_ne_zero_of_mul h)) hne
      rw [hxy] at hk
      exact klt_irrefl hk
    · intro h
      exact absurd (by rw [Finset.mem_antidiagonal]) h
  · rw [mem_support_iff, coeff_mul] at he
    obtain ⟨⟨x, y⟩, hxy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [Finset.mem_antidiagonal] at hxy
    subst hxy
    refine key x (mem_support_iff.2 (left_ne_zero_of_mul h)) y
      (mem_support_iff.2 (right_ne_zero_of_mul h)) fun hc => hne ?_
    simp only [Prod.mk.injEq] at hc
    rw [hc.1, hc.2]

lemma HasLead.pow {P : MvPolynomial (Fin 4) K} {p : Fin 4 →₀ ℕ} (h : HasLead ℓ P p) (k : ℕ) :
    HasLead ℓ (P ^ k) (k • p) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact hasLead_one
  | succ k ih => rw [pow_succ, succ_nsmul]; exact ih.mul h

lemma AllAbove.add {p : Fin 4 →₀ ℕ} {P Q : MvPolynomial (Fin 4) K} (hP : AllAbove ℓ p P)
    (hQ : AllAbove ℓ p Q) : AllAbove ℓ p (P + Q) := by
  classical
  intro e he
  rcases Finset.mem_union.1 (support_add he) with h | h
  · exact hP e h
  · exact hQ e h

lemma AllAbove.neg {p : Fin 4 →₀ ℕ} {P : MvPolynomial (Fin 4) K} (hP : AllAbove ℓ p P) :
    AllAbove ℓ p (-P) := by
  rw [AllAbove, support_neg]
  exact hP

lemma HasLead.allAbove {p q : Fin 4 →₀ ℕ} {Q : MvPolynomial (Fin 4) K} (hQ : HasLead ℓ Q q)
    (h : klt ℓ p q) : AllAbove ℓ p Q := by
  intro e he
  by_cases heq : e = q
  · rw [heq]; exact h
  · exact klt_trans h (hQ.2 e he heq)

end Lead

/-! ## Leads of the generators, for monotone `ℓ` -/

section Generators

variable {K : Type*} [Field K] {ℓ : Fin 4 → ℝ}

lemma hasLead_XX (i j : Fin 4) : HasLead ℓ (X i * X j : MvPolynomial (Fin 4) K) (E i + E j) :=
  (hasLead_X i).mul (hasLead_X j)

lemma allAbove_X {p : Fin 4 →₀ ℕ} (i : Fin 4) (h : klt ℓ p (E i)) :
    AllAbove ℓ p (X i : MvPolynomial (Fin 4) K) :=
  (hasLead_X i).allAbove h

lemma allAbove_XX {p : Fin 4 →₀ ℕ} (i j : Fin 4) (h : klt ℓ p (E i + E j)) :
    AllAbove ℓ p (X i * X j : MvPolynomial (Fin 4) K) :=
  (hasLead_XX i j).allAbove h

lemma mono_facts (hℓ : Monotone ℓ) : ℓ 0 ≤ ℓ 1 ∧ ℓ 1 ≤ ℓ 2 ∧ ℓ 2 ≤ ℓ 3 :=
  ⟨hℓ (by decide), hℓ (by decide), hℓ (by decide)⟩

/-- Close `klt ℓ p q` between concrete exponents when `ℓ 0 ≤ ℓ 1 ≤ ℓ 2 ≤ ℓ 3` is in context. -/
macro "klt_tac" : tactic => `(tactic| (apply klt_of <;>
  simp only [lin_add, lin_E, zA_add, zA_E0, zA_E1, zA_E2, zA_E3] <;> first | omega | linarith))

variable (hℓ : Monotone ℓ)
include hℓ

lemma hasLead_q1 : HasLead ℓ (q1 K) (E 0) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  rw [show q1 K = X 0 + (X 1 + X 2 + X 3) by unfold q1; ring]
  exact (hasLead_X 0).add (((allAbove_X 1 (by klt_tac)).add (allAbove_X 2 (by klt_tac))).add
    (allAbove_X 3 (by klt_tac)))

lemma hasLead_q2 : HasLead ℓ (q2 K) (E 0 + E 1) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  rw [show q2 K = X 0 * X 1 + (X 0 * X 2 + X 0 * X 3 + X 1 * X 2 + X 1 * X 3 + X 2 * X 3) by
    unfold q2; ring]
  refine (hasLead_XX 0 1).add ((((((allAbove_XX 0 2 ?_).add (allAbove_XX 0 3 ?_)).add
    (allAbove_XX 1 2 ?_)).add (allAbove_XX 1 3 ?_)).add (allAbove_XX 2 3 ?_))) <;> klt_tac

lemma hasLead_P1 : HasLead ℓ (X 0 * X 1 + X 2 * X 3 : MvPolynomial (Fin 4) K) (E 0 + E 1) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  exact (hasLead_XX 0 1).add (allAbove_XX 2 3 (by klt_tac))

lemma hasLead_P2 : HasLead ℓ (X 0 * X 2 + X 1 * X 3 : MvPolynomial (Fin 4) K) (E 0 + E 2) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  exact (hasLead_XX 0 2).add (allAbove_XX 1 3 (by klt_tac))

lemma hasLead_P3_A (hA : ℓ 0 + ℓ 3 ≤ ℓ 1 + ℓ 2) :
    HasLead ℓ (X 0 * X 3 + X 1 * X 2 : MvPolynomial (Fin 4) K) (E 0 + E 3) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  exact (hasLead_XX 0 3).add (allAbove_XX 1 2 (by klt_tac))

omit hℓ in
lemma hasLead_P3_B (hB : ℓ 1 + ℓ 2 < ℓ 0 + ℓ 3) :
    HasLead ℓ (X 0 * X 3 + X 1 * X 2 : MvPolynomial (Fin 4) K) (E 1 + E 2) := by
  rw [add_comm]
  exact (hasLead_XX 1 2).add (allAbove_XX 0 3 (Or.inl (by simpa using hB)))

lemma hasLead_q4_q6 {l3 : Fin 4 →₀ ℕ}
    (h3 : HasLead ℓ (X 0 * X 3 + X 1 * X 2 : MvPolynomial (Fin 4) K) l3)
    (h13 : klt ℓ (E 0 + E 1) l3) (h23 : klt ℓ (E 0 + E 2) l3) :
    HasLead ℓ (q4 K) (E 0 + E 1 + (E 0 + E 2)) ∧
      HasLead ℓ (q6 K) (E 0 + E 1 + (E 0 + E 2) + l3) := by
  have h1 := hasLead_P1 (K := K) hℓ
  have h2 := hasLead_P2 (K := K) hℓ
  refine ⟨?_, by unfold q6; exact (h1.mul h2).mul h3⟩
  rw [show q4 K = (X 0 * X 1 + X 2 * X 3) * (X 0 * X 2 + X 1 * X 3) +
      ((X 0 * X 1 + X 2 * X 3) * (X 0 * X 3 + X 1 * X 2) +
        (X 0 * X 3 + X 1 * X 2) * (X 0 * X 2 + X 1 * X 3)) by unfold q4; ring]
  exact (h1.mul h2).add (((h1.mul h3).allAbove (klt_add_left h23)).add
    ((h3.mul h2).allAbove (klt_add h13 (Or.inl rfl))))

lemma hasLead_q8 : HasLead ℓ (q8 K) (E 0 + E 1 + E 2 + E 3 + (E 0 + E 0 + E 0 + E 0)) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  have k1 : klt ℓ (E 0) (E 1) := by klt_tac
  have k2 : klt ℓ (E 0) (E 2) := by klt_tac
  have k3 : klt ℓ (E 0) (E 3) := by klt_tac
  have f0 : HasLead ℓ (q1 K - 2 * X 0) (E 0) := by
    rw [show q1 K - 2 * X 0 = -X 0 + (X 1 + X 2 + X 3) by unfold q1; ring]
    exact (hasLead_X 0).neg.add (((allAbove_X 1 k1).add (allAbove_X 2 k2)).add (allAbove_X 3 k3))
  have f1 : HasLead ℓ (q1 K - 2 * X 1) (E 0) := by
    rw [show q1 K - 2 * X 1 = X 0 + (-X 1 + X 2 + X 3) by unfold q1; ring]
    exact (hasLead_X 0).add (((allAbove_X 1 k1).neg.add (allAbove_X 2 k2)).add (allAbove_X 3 k3))
  have f2 : HasLead ℓ (q1 K - 2 * X 2) (E 0) := by
    rw [show q1 K - 2 * X 2 = X 0 + (X 1 + -X 2 + X 3) by unfold q1; ring]
    exact (hasLead_X 0).add (((allAbove_X 1 k1).add (allAbove_X 2 k2).neg).add (allAbove_X 3 k3))
  have f3 : HasLead ℓ (q1 K - 2 * X 3) (E 0) := by
    rw [show q1 K - 2 * X 3 = X 0 + (X 1 + X 2 + -X 3) by unfold q1; ring]
    exact (hasLead_X 0).add (((allAbove_X 1 k1).add (allAbove_X 2 k2)).add (allAbove_X 3 k3).neg)
  unfold q8
  exact ((((hasLead_X 0).mul (hasLead_X 1)).mul (hasLead_X 2)).mul (hasLead_X 3)).mul
    (((f0.mul f1).mul f2).mul f3)

lemma hasLead_poly {l4 l6 l8 : Fin 4 →₀ ℕ} (h4 : HasLead ℓ (q4 K) l4)
    (h6 : HasLead ℓ (q6 K) l6) (h8 : HasLead ℓ (q8 K) l8) (m : NormalMono) :
    HasLead ℓ (m.poly K) (m.u • E 0 + m.v • (E 0 + E 1) + m.w • l4 + m.b • l6 + m.a • l8) :=
  (((((hasLead_q1 hℓ).pow _).mul ((hasLead_q2 hℓ).pow _)).mul (h4.pow _)).mul (h6.pow _)).mul
    (h8.pow _)

end Generators

/-! ## The vertices `A` and `B` as leading exponents -/

section Vertices

/-- The vertex `A m` as an exponent vector. -/
noncomputable def leadA (m : NormalMono) : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm m.A

/-- The vertex `B m` as an exponent vector. -/
noncomputable def leadB (m : NormalMono) : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm m.B

@[simp] lemma coe_leadA (m : NormalMono) : ⇑(leadA m) = m.A :=
  Finsupp.coe_equivFunOnFinite_symm _

@[simp] lemma coe_leadB (m : NormalMono) : ⇑(leadB m) = m.B :=
  Finsupp.coe_equivFunOnFinite_symm _

lemma lin_leadA (ℓ : Fin 4 → ℝ) (m : NormalMono) : lin ℓ (leadA m) = ∑ a, ℓ a * (m.A a : ℝ) := by
  simp [lin]

lemma lin_leadB (ℓ : Fin 4 → ℝ) (m : NormalMono) : lin ℓ (leadB m) = ∑ a, ℓ a * (m.B a : ℝ) := by
  simp [lin]

variable {K : Type*} [Field K] {ℓ : Fin 4 → ℝ}

/-- In chamber A (`ℓ₀ + ℓ₃ ≤ ℓ₁ + ℓ₂`), `poly m` has leading exponent `A m`. -/
theorem hasLead_poly_A (hℓ : Monotone ℓ) (hA : ℓ 0 + ℓ 3 ≤ ℓ 1 + ℓ 2) (m : NormalMono) :
    HasLead ℓ (m.poly K) (leadA m) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  obtain ⟨h4, h6⟩ := hasLead_q4_q6 hℓ (hasLead_P3_A (K := K) hℓ hA) (by klt_tac) (by klt_tac)
  convert hasLead_poly hℓ h4 h6 (hasLead_q8 hℓ) m using 1
  ext i
  fin_cases i <;> simp [NormalMono.A]
  ring

/-- In chamber B (`ℓ₁ + ℓ₂ < ℓ₀ + ℓ₃`), `poly m` has leading exponent `B m`. -/
theorem hasLead_poly_B (hℓ : Monotone ℓ) (hB : ℓ 1 + ℓ 2 < ℓ 0 + ℓ 3) (m : NormalMono) :
    HasLead ℓ (m.poly K) (leadB m) := by
  obtain ⟨h01, h12, h23⟩ := mono_facts hℓ
  obtain ⟨h4, h6⟩ := hasLead_q4_q6 hℓ (hasLead_P3_B (K := K) hB) (by klt_tac) (by klt_tac)
  convert hasLead_poly hℓ h4 h6 (hasLead_q8 hℓ) m using 1
  ext i
  fin_cases i <;> simp [NormalMono.B] <;> ring

lemma leadA_injective : Function.Injective leadA := by
  intro m m' h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  have h2 := DFunLike.congr_fun h 2
  have h3 := DFunLike.congr_fun h 3
  simp only [coe_leadA, NormalMono.A, Matrix.cons_val] at h0 h1 h2 h3
  have := m.normal
  have := m'.normal
  ext <;> omega

lemma leadB_injective : Function.Injective leadB := by
  intro m m' h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  have h2 := DFunLike.congr_fun h 2
  have h3 := DFunLike.congr_fun h 3
  simp only [coe_leadB, NormalMono.B, Matrix.cons_val] at h0 h1 h2 h3
  have := m.normal
  have := m'.normal
  ext <;> omega

lemma leadA_mem_support (m : NormalMono) : leadA m ∈ (m.poly K).support :=
  mem_support_iff.2 (hasLead_poly_A (ℓ := fun _ => 0) (fun _ _ _ => le_rfl) (by simp) m).1

lemma leadB_mem_support (m : NormalMono) : leadB m ∈ (m.poly K).support := by
  have hmono : Monotone (![0, 0, 0, 1] : Fin 4 → ℝ) :=
    Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> simp
  exact mem_support_iff.2 (hasLead_poly_B hmono (by simp) m).1

end Vertices

/-! ## Selection of a minimal leading exponent -/

section Selection

variable {K : Type*} [Field K] {ℓ : Fin 4 → ℝ}

/-- If each `Q i` has leading exponent `L i`, with `L` injective, then in any combination with
nonzero coefficients the leading exponent of some term survives, and it is `ℓ`-minimal among all
the leading exponents. -/
theorem exists_lead_mem_support {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (Q : ι → MvPolynomial (Fin 4) K) (L : ι → Fin 4 →₀ ℕ) (hL : ∀ i ∈ S, HasLead ℓ (Q i) (L i))
    (hinj : Set.InjOn L S) (c : ι → K) (hc : ∀ i ∈ S, c i ≠ 0) :
    ∃ i₁ ∈ S, L i₁ ∈ (∑ i ∈ S, c i • Q i).support ∧ ∀ i ∈ S, lin ℓ (L i₁) ≤ lin ℓ (L i) := by
  classical
  obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image (fun i => lin ℓ (L i)) hS
  obtain ⟨i₁, hi₁, hmax⟩ := (S.filter fun i => lin ℓ (L i) = lin ℓ (L i₀)).exists_max_image
    (fun i => zA (L i)) ⟨i₀, Finset.mem_filter.2 ⟨hi₀, rfl⟩⟩
  rw [Finset.mem_filter] at hi₁
  have hlow : ∀ i ∈ S, lin ℓ (L i₁) ≤ lin ℓ (L i) := fun i hi => hi₁.2 ▸ hmin i hi
  refine ⟨i₁, hi₁.1, ?_, hlow⟩
  have hzero : ∀ i ∈ S, i ≠ i₁ → (Q i).coeff (L i₁) = 0 := by
    intro i hi hne
    by_contra h
    have hne' : L i₁ ≠ L i := fun heq => hne (hinj hi hi₁.1 heq.symm)
    rcases (hL i hi).2 _ (mem_support_iff.2 h) hne' with hlt | ⟨heq, hz⟩
    · exact absurd (hlow i hi) (not_le.2 hlt)
    · exact absurd (hmax i (Finset.mem_filter.2 ⟨hi, heq.trans hi₁.2⟩)) (not_le.2 hz)
  rw [mem_support_iff, coeff_sum, Finset.sum_eq_single i₁]
  · rw [coeff_smul, smul_eq_mul]
    exact mul_ne_zero (hc _ hi₁.1) (hL _ hi₁.1).1
  · intro i hi hne
    rw [coeff_smul, hzero i hi hne, smul_zero]
  · intro h
    exact absurd hi₁.1 h

/-- The statement for monotone `ℓ`. -/
theorem exists_support_le_vertices_of_monotone (S : Finset NormalMono) (c : NormalMono → K)
    (hc : ∀ m ∈ S, c m ≠ 0) {m₀ : NormalMono} (hm₀ : m₀ ∈ S) (hℓ : Monotone ℓ) :
    ∃ e ∈ (∑ m ∈ S, c m • m.poly K).support,
      lin ℓ e ≤ lin ℓ (leadA m₀) ∧ lin ℓ e ≤ lin ℓ (leadB m₀) := by
  by_cases hch : ℓ 0 + ℓ 3 ≤ ℓ 1 + ℓ 2
  · have hL := fun m (_ : m ∈ S) => hasLead_poly_A (K := K) hℓ hch m
    obtain ⟨m₁, -, hm₁, hlow⟩ := exists_lead_mem_support S ⟨m₀, hm₀⟩ _ _ hL
      leadA_injective.injOn c hc
    exact ⟨leadA m₁, hm₁, hlow m₀ hm₀,
      (hlow m₀ hm₀).trans ((hL m₀ hm₀).lin_le (leadB_mem_support m₀))⟩
  · have hL := fun m (_ : m ∈ S) => hasLead_poly_B (K := K) hℓ (not_le.1 hch) m
    obtain ⟨m₁, -, hm₁, hlow⟩ := exists_lead_mem_support S ⟨m₀, hm₀⟩ _ _ hL
      leadB_injective.injOn c hc
    exact ⟨leadB m₁, hm₁, (hlow m₀ hm₀).trans ((hL m₀ hm₀).lin_le (leadA_mem_support m₀)),
      hlow m₀ hm₀⟩

end Selection

/-! ## Removing monotonicity -/

section General

lemma rename_poly {K : Type*} [Field K] (σ : Equiv.Perm (Fin 4)) (m : NormalMono) : rename σ (m.poly K) = m.poly K := by
  simp only [NormalMono.poly, q8_eq, map_mul, map_pow, map_sub, rename_q1, rename_q2, rename_q4,
    rename_q6]

lemma lin_mapDomain (ℓ : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) (e : Fin 4 →₀ ℕ) :
    lin ℓ (Finsupp.mapDomain σ e) = lin (ℓ ∘ σ) e := by
  unfold lin
  rw [← Equiv.sum_comp σ]
  simp [Finsupp.mapDomain_apply_of_injective σ.injective]

lemma antitone_A (m : NormalMono) : Antitone m.A :=
  Fin.antitone_iff_succ_le.2 fun i => by
    fin_cases i <;> simp [NormalMono.A]
    omega

lemma antitone_B (m : NormalMono) : Antitone m.B :=
  Fin.antitone_iff_succ_le.2 fun i => by
    fin_cases i <;> simp [NormalMono.B]
    omega

/-- Rearrangement: an antitone vector paired with a sorted functional. -/
lemma sum_comp_le_sum {ℓ : Fin 4 → ℝ} (σ : Equiv.Perm (Fin 4)) (hσ : Monotone (ℓ ∘ σ))
    {f : Fin 4 → ℕ} (hf : Antitone f) :
    ∑ a, (ℓ ∘ σ) a * (f a : ℝ) ≤ ∑ a, ℓ a * (f a : ℝ) := by
  calc ∑ a, (ℓ ∘ σ) a * (f a : ℝ)
      ≤ ∑ a, (ℓ ∘ σ) a * (f (σ a) : ℝ) :=
        (Monotone.antivary hσ (Nat.mono_cast.comp_antitone hf)).sum_mul_le_sum_mul_comp_perm
    _ = ∑ a, ℓ a * (f a : ℝ) := Equiv.sum_comp σ (fun a => ℓ a * (f a : ℝ))

/-- **No cancellation.** In a linear combination of distinct normal monomials with nonzero
coefficients, for every linear functional `ℓ` some surviving support point is at least as low as
both vertices `A m₀` and `B m₀` of any one of the monomials. -/
theorem exists_support_le_vertices {K : Type*} [Field K] (S : Finset NormalMono)
    (c : NormalMono → K) (hc : ∀ m ∈ S, c m ≠ 0) {m₀ : NormalMono} (hm₀ : m₀ ∈ S) (ℓ : Fin 4 → ℝ) :
    ∃ e ∈ (∑ m ∈ S, c m • m.poly K).support,
      lin ℓ e ≤ ∑ a, ℓ a * (m₀.A a : ℝ) ∧ lin ℓ e ≤ ∑ a, ℓ a * (m₀.B a : ℝ) := by
  set σ := Tuple.sort ℓ
  have hσ : Monotone (ℓ ∘ σ) := Tuple.monotone_sort ℓ
  obtain ⟨e, he, hA, hB⟩ := exists_support_le_vertices_of_monotone S c hc hm₀ hσ
  rw [lin_leadA] at hA
  rw [lin_leadB] at hB
  have hsymm : rename σ (∑ m ∈ S, c m • m.poly K) = ∑ m ∈ S, c m • m.poly K := by
    simp only [map_sum, map_smul, rename_poly]
  refine ⟨Finsupp.mapDomain σ e, ?_, ?_, ?_⟩
  · rw [mem_support_iff, ← hsymm, coeff_rename_mapDomain _ σ.injective]
    exact mem_support_iff.1 he
  · rw [lin_mapDomain]
    exact hA.trans (sum_comp_le_sum σ hσ (antitone_A m₀))
  · rw [lin_mapDomain]
    exact hB.trans (sum_comp_le_sum σ hσ (antitone_B m₀))

end General

end PauliCubes
