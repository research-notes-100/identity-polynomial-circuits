/-
Generation of the invariant ring: every polynomial in four variables that is invariant under the
letter permutations and under `T(x)ᵢ = s/2 − xᵢ`, and homogeneous of degree `d`, is a `K`-linear
combination of the normal monomials `q₁^u q₂^v q₄^w q₆^b q₈^a` (`u < 2 ∨ b = 0`) of degree `d`.
Any field with `2 ≠ 0` works.

Route.
* A symmetric polynomial is a polynomial in `e₁, e₂, e₃, e₄` (Mathlib's fundamental theorem).
* With `E₃ = (a+b−c−d)(a−b+c−d)(a−b−c+d)` one has `8e₃ = E₃ + 4q₁q₂ − q₁³` and
  `32e₄ = (−8q₄ + 4q₁²q₂ − q₁⁴) + q₁E₃`, while `E₃² ∈ K[q₁,q₂,q₄,q₆]`. Hence every symmetric
  polynomial is `α + βE₃` with `α, β ∈ K[q₁,q₂,q₄,q₆]`.
* `T` fixes `q₁` and the three pair sums `ab + cd`, `ac + bd`, `ad + bc` (whose elementary
  symmetric functions are `q₂, q₄, q₆`), and `T E₃ = −E₃`. So `T`-invariance forces `βE₃ = 0`.
* `q₈ = q₄² − q₁²q₆` rewrites every monomial in `q₁, q₂, q₄, q₆` into normal ones, and taking the
  degree-`d` homogeneous component keeps exactly those of degree `d`.
-/
import PauliCubes.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

open MvPolynomial

namespace PauliCubes

variable {K : Type*} [Field K]

/-! ## The elementary symmetric polynomials in four variables -/

section Esymm

variable (K)

lemma esymm_fin4_one : esymm (Fin 4) K 1 = q1 K := by
  rw [esymm, show (Finset.univ : Finset (Fin 4)).powersetCard 1 = {{0}, {1}, {2}, {3}} by decide]
  simp [Finset.sum_insert, q1]
  ring

lemma esymm_fin4_two : esymm (Fin 4) K 2 = q2 K := by
  rw [esymm, show (Finset.univ : Finset (Fin 4)).powersetCard 2 =
    {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} by decide]
  simp +decide [Finset.sum_insert, Finset.prod_insert, q2]
  ring

lemma esymm_fin4_three : esymm (Fin 4) K 3 =
    X 0 * X 1 * X 2 + X 0 * X 1 * X 3 + X 0 * X 2 * X 3 + X 1 * X 2 * X 3 := by
  rw [esymm, show (Finset.univ : Finset (Fin 4)).powersetCard 3 =
    {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} by decide]
  simp +decide [Finset.sum_insert, Finset.prod_insert]
  ring

lemma esymm_fin4_four : esymm (Fin 4) K 4 = X 0 * X 1 * X 2 * X 3 := by
  rw [esymm, show (Finset.univ : Finset (Fin 4)).powersetCard 4 = {{0, 1, 2, 3}} by decide]
  simp
  ring

/-- `q₄ = e₁e₃ − 4e₄`. -/
lemma q4_eq_esymm : q4 K = esymm (Fin 4) K 1 * esymm (Fin 4) K 3 - 4 * esymm (Fin 4) K 4 := by
  rw [esymm_fin4_one, esymm_fin4_three, esymm_fin4_four, q4, q1]
  ring

/-- `q₆ = e₁²e₄ + e₃² − 4e₂e₄`. -/
lemma q6_eq_esymm : q6 K = esymm (Fin 4) K 1 ^ 2 * esymm (Fin 4) K 4 + esymm (Fin 4) K 3 ^ 2 -
    4 * esymm (Fin 4) K 2 * esymm (Fin 4) K 4 := by
  rw [esymm_fin4_one, esymm_fin4_two, esymm_fin4_three, esymm_fin4_four, q6, q1, q2]
  ring

/-- `q₈ = q₄² − q₁²q₆`. -/
lemma q8_eq : q8 K = q4 K ^ 2 - q1 K ^ 2 * q6 K := by
  unfold q8 q4 q1 q6
  ring

end Esymm

/-! ## Symmetry of the generators -/

section Symmetric

variable (K)

lemma rename_esymm_fin4 (σ : Equiv.Perm (Fin 4)) (n : ℕ) :
    rename σ (esymm (Fin 4) K n) = esymm (Fin 4) K n :=
  esymm_isSymmetric (Fin 4) K n σ

lemma rename_q1 (σ : Equiv.Perm (Fin 4)) : rename σ (q1 K) = q1 K := by
  rw [← esymm_fin4_one, rename_esymm_fin4]

lemma rename_q2 (σ : Equiv.Perm (Fin 4)) : rename σ (q2 K) = q2 K := by
  rw [← esymm_fin4_two, rename_esymm_fin4]

lemma rename_q4 (σ : Equiv.Perm (Fin 4)) : rename σ (q4 K) = q4 K := by
  simp only [q4_eq_esymm, map_sub, map_mul, map_ofNat, rename_esymm_fin4]

lemma rename_q6 (σ : Equiv.Perm (Fin 4)) : rename σ (q6 K) = q6 K := by
  simp only [q6_eq_esymm, map_sub, map_add, map_mul, map_pow, map_ofNat, rename_esymm_fin4]

end Symmetric

/-! ## The involution `T` -/

section Involution

variable (K)

/-- The product `uvw` of the three `T`-odd linear forms. -/
noncomputable def oddCubic : MvPolynomial (Fin 4) K :=
  (X 0 + X 1 - X 2 - X 3) * (X 0 - X 1 + X 2 - X 3) * (X 0 - X 1 - X 2 + X 3)

variable {K}

lemma C_inv_mul_ofNat (n : ℕ) [n.AtLeastTwo] (hn : (OfNat.ofNat n : K) ≠ 0) :
    C (OfNat.ofNat n : K)⁻¹ * (OfNat.ofNat n : MvPolynomial (Fin 4) K) = 1 := by
  rw [← map_ofNat C n, ← C_mul, inv_mul_cancel₀ hn, C_1]

lemma bind₁_Tsub_q1 (h2 : (2 : K) ≠ 0) : bind₁ (Tsub K) (q1 K) = q1 K := by
  have h := C_inv_mul_ofNat 2 h2
  simp only [q1, map_add, bind₁_X_right, Tsub]
  linear_combination (2 * (X 0 + X 1 + X 2 + X 3)) * h

/-- `T` fixes `xᵢxⱼ + xₖxₗ` when `{i, j, k, l} = {0, 1, 2, 3}`. -/
lemma bind₁_Tsub_pair (h2 : (2 : K) ≠ 0) (i j k l : Fin 4)
    (hs : (X i + X j + X k + X l : MvPolynomial (Fin 4) K) = X 0 + X 1 + X 2 + X 3) :
    bind₁ (Tsub K) (X i * X j + X k * X l) = X i * X j + X k * X l := by
  have h := C_inv_mul_ofNat 2 h2
  simp only [map_add, map_mul, bind₁_X_right, Tsub]
  linear_combination (C (2 : K)⁻¹ * (X 0 + X 1 + X 2 + X 3) ^ 2) * h -
    (C (2 : K)⁻¹ * (X 0 + X 1 + X 2 + X 3)) * hs

lemma bind₁_Tsub_q2 (h2 : (2 : K) ≠ 0) : bind₁ (Tsub K) (q2 K) = q2 K := by
  have e : q2 K = (X 0 * X 1 + X 2 * X 3) + (X 0 * X 2 + X 1 * X 3) + (X 0 * X 3 + X 1 * X 2) := by
    unfold q2; ring
  rw [e, map_add, map_add, bind₁_Tsub_pair h2 0 1 2 3 (by ring),
    bind₁_Tsub_pair h2 0 2 1 3 (by ring), bind₁_Tsub_pair h2 0 3 1 2 (by ring)]

lemma bind₁_Tsub_q4 (h2 : (2 : K) ≠ 0) : bind₁ (Tsub K) (q4 K) = q4 K := by
  have e : q4 K = (X 0 * X 1 + X 2 * X 3) * (X 0 * X 2 + X 1 * X 3) +
      (X 0 * X 1 + X 2 * X 3) * (X 0 * X 3 + X 1 * X 2) +
      (X 0 * X 2 + X 1 * X 3) * (X 0 * X 3 + X 1 * X 2) := by
    unfold q4; ring
  rw [e, map_add, map_add, map_mul, map_mul, map_mul, bind₁_Tsub_pair h2 0 1 2 3 (by ring),
    bind₁_Tsub_pair h2 0 2 1 3 (by ring), bind₁_Tsub_pair h2 0 3 1 2 (by ring)]

lemma bind₁_Tsub_q6 (h2 : (2 : K) ≠ 0) : bind₁ (Tsub K) (q6 K) = q6 K := by
  rw [q6, map_mul, map_mul, bind₁_Tsub_pair h2 0 1 2 3 (by ring),
    bind₁_Tsub_pair h2 0 2 1 3 (by ring), bind₁_Tsub_pair h2 0 3 1 2 (by ring)]

lemma bind₁_Tsub_oddCubic : bind₁ (Tsub K) (oddCubic K) = -oddCubic K := by
  simp only [oddCubic, map_add, map_sub, map_mul, bind₁_X_right, Tsub]
  ring

end Involution

/-! ## `GInvariant` of the generators -/

section Invariance

lemma ginvariant_q1 (h2 : (2 : K) ≠ 0) : GInvariant K (q1 K) :=
  ⟨rename_q1 K, bind₁_Tsub_q1 h2⟩

lemma ginvariant_q2 (h2 : (2 : K) ≠ 0) : GInvariant K (q2 K) :=
  ⟨rename_q2 K, bind₁_Tsub_q2 h2⟩

lemma ginvariant_q4 (h2 : (2 : K) ≠ 0) : GInvariant K (q4 K) :=
  ⟨rename_q4 K, bind₁_Tsub_q4 h2⟩

lemma ginvariant_q6 (h2 : (2 : K) ≠ 0) : GInvariant K (q6 K) :=
  ⟨rename_q6 K, bind₁_Tsub_q6 h2⟩

lemma ginvariant_q8 (h2 : (2 : K) ≠ 0) : GInvariant K (q8 K) := by
  refine ⟨fun σ => ?_, ?_⟩
  · simp only [q8_eq, map_sub, map_mul, map_pow, rename_q1, rename_q4, rename_q6]
  · simp only [q8_eq, map_sub, map_mul, map_pow, bind₁_Tsub_q1 h2, bind₁_Tsub_q4 h2,
      bind₁_Tsub_q6 h2]

end Invariance

/-! ## The subalgebra `K[q₁, q₂, q₄, q₆]` -/

section Subalgebra

variable (K)

/-- The four generators `q₁, q₂, q₄, q₆`. -/
noncomputable def qGens : Fin 4 → MvPolynomial (Fin 4) K := ![q1 K, q2 K, q4 K, q6 K]

/-- `K[q₁, q₂, q₄, q₆]`, as the range of the evaluation at the generators. -/
noncomputable abbrev qAlg : Subalgebra K (MvPolynomial (Fin 4) K) := (aeval (qGens K)).range

variable {K}

lemma mem_qAlg_iff {x : MvPolynomial (Fin 4) K} : x ∈ qAlg K ↔
    ∃ P : MvPolynomial (Fin 4) K, aeval (qGens K) P = x :=
  AlgHom.mem_range _

lemma bind₁_Tsub_of_mem_qAlg (h2 : (2 : K) ≠ 0) {x : MvPolynomial (Fin 4) K} (hx : x ∈ qAlg K) :
    bind₁ (Tsub K) x = x := by
  obtain ⟨P, rfl⟩ := mem_qAlg_iff.1 hx
  have hg : (fun i => bind₁ (Tsub K) (qGens K i)) = qGens K := by
    funext i
    fin_cases i
    · exact bind₁_Tsub_q1 h2
    · exact bind₁_Tsub_q2 h2
    · exact bind₁_Tsub_q4 h2
    · exact bind₁_Tsub_q6 h2
  rw [comp_aeval_apply, hg]

lemma oddCubic_sq_mem : oddCubic K ^ 2 ∈ qAlg K := by
  refine mem_qAlg_iff.2 ⟨64 * X 3 + 16 * X 0 ^ 2 * X 2 - 64 * X 1 * X 2 + X 0 ^ 6 - 8 * X 0 ^ 4 * X 1 +
    16 * X 0 ^ 2 * X 1 ^ 2, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X, qGens]
  simp only [Matrix.cons_val, oddCubic, q1, q2, q4, q6]
  ring

/-- The elements `α + β E₃` with `α, β ∈ K[q₁, q₂, q₄, q₆]`. -/
def OddSplit (x : MvPolynomial (Fin 4) K) : Prop :=
  ∃ α ∈ qAlg K, ∃ β ∈ qAlg K, x = α + β * oddCubic K

lemma OddSplit.of_mem {x : MvPolynomial (Fin 4) K} (hx : x ∈ qAlg K) : OddSplit x :=
  ⟨x, hx, 0, Subalgebra.zero_mem _, by ring⟩

lemma OddSplit.add {x y : MvPolynomial (Fin 4) K} (hx : OddSplit x) (hy : OddSplit y) :
    OddSplit (x + y) := by
  obtain ⟨α, hα, β, hβ, rfl⟩ := hx
  obtain ⟨α', hα', β', hβ', rfl⟩ := hy
  exact ⟨α + α', Subalgebra.add_mem _ hα hα', β + β', Subalgebra.add_mem _ hβ hβ', by ring⟩

lemma OddSplit.mul {x y : MvPolynomial (Fin 4) K} (hx : OddSplit x) (hy : OddSplit y) :
    OddSplit (x * y) := by
  obtain ⟨α, hα, β, hβ, rfl⟩ := hx
  obtain ⟨α', hα', β', hβ', rfl⟩ := hy
  refine ⟨α * α' + β * β' * oddCubic K ^ 2, ?_, α * β' + β * α', ?_, by ring⟩
  · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hα hα')
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hβ hβ') oddCubic_sq_mem)
  · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hα hβ') (Subalgebra.mul_mem _ hβ hα')

lemma oddSplit_esymm (h2 : (2 : K) ≠ 0) (i : Fin 4) :
    OddSplit (esymm (Fin 4) K ((i : ℕ) + 1)) := by
  fin_cases i
  · show OddSplit (esymm (Fin 4) K 1)
    rw [esymm_fin4_one]
    exact OddSplit.of_mem (mem_qAlg_iff.2 ⟨X 0, by simp [qGens]⟩)
  · show OddSplit (esymm (Fin 4) K 2)
    rw [esymm_fin4_two]
    exact OddSplit.of_mem (mem_qAlg_iff.2 ⟨X 1, by simp [qGens]⟩)
  · show OddSplit (esymm (Fin 4) K 3)
    have h8 : (8 : K) ≠ 0 := by
      have := pow_ne_zero 3 h2
      norm_num at this
      exact this
    have h := C_inv_mul_ofNat 8 h8
    refine ⟨C (8 : K)⁻¹ * (4 * q1 K * q2 K - q1 K ^ 3),
      mem_qAlg_iff.2 ⟨C (8 : K)⁻¹ * (4 * X 0 * X 1 - X 0 ^ 3), by
        simp only [qGens, map_sub, map_mul, map_pow, map_ofNat, aeval_X, aeval_C, algebraMap_eq,
          Matrix.cons_val]⟩,
      C (8 : K)⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [esymm_fin4_three]
    simp only [oddCubic, q1, q2]
    linear_combination (-(X 0 * X 1 * X 2 + X 0 * X 1 * X 3 + X 0 * X 2 * X 3 + X 1 * X 2 * X 3 :
      MvPolynomial (Fin 4) K)) * h
  · show OddSplit (esymm (Fin 4) K 4)
    have h32 : (32 : K) ≠ 0 := by
      have := pow_ne_zero 5 h2
      norm_num at this
      exact this
    have h := C_inv_mul_ofNat 32 h32
    refine ⟨C (32 : K)⁻¹ * (-8 * q4 K + 4 * q1 K ^ 2 * q2 K - q1 K ^ 4),
      mem_qAlg_iff.2 ⟨C (32 : K)⁻¹ * (-8 * X 2 + 4 * X 0 ^ 2 * X 1 - X 0 ^ 4), by
        simp only [qGens, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat, aeval_X, aeval_C,
          algebraMap_eq, Matrix.cons_val]⟩,
      C (32 : K)⁻¹ * q1 K, mem_qAlg_iff.2 ⟨C (32 : K)⁻¹ * X 0, by
        simp only [qGens, map_mul, aeval_X, aeval_C, algebraMap_eq, Matrix.cons_val]⟩, ?_⟩
    rw [esymm_fin4_four]
    simp only [oddCubic, q1, q2, q4]
    linear_combination (-(X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) K)) * h

lemma oddSplit_aeval_esymm (h2 : (2 : K) ≠ 0) (P : MvPolynomial (Fin 4) K) :
    OddSplit (aeval (fun i : Fin 4 => esymm (Fin 4) K ((i : ℕ) + 1)) P) := by
  induction P using MvPolynomial.induction_on with
  | C r => exact OddSplit.of_mem (by rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact hp.mul (oddSplit_esymm h2 i)

/-- Every `G`-invariant polynomial lies in `K[q₁, q₂, q₄, q₆]`. -/
theorem ginv_mem_qAlg (h2 : (2 : K) ≠ 0) {F : MvPolynomial (Fin 4) K} (hF : GInvariant K F) :
    F ∈ qAlg K := by
  obtain ⟨P, hP⟩ := esymmAlgHom_fin_surjective K (le_refl 4)
    (⟨F, (mem_symmetricSubalgebra F).2 hF.1⟩ : symmetricSubalgebra (Fin 4) K)
  have hFP : F = aeval (fun i : Fin 4 => esymm (Fin 4) K ((i : ℕ) + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  obtain ⟨α, hα, β, hβ, hab⟩ := oddSplit_aeval_esymm h2 P
  rw [← hFP] at hab
  have hT := hF.2
  rw [hab, map_add, map_mul, bind₁_Tsub_of_mem_qAlg h2 hα, bind₁_Tsub_of_mem_qAlg h2 hβ,
    bind₁_Tsub_oddCubic] at hT
  have h2' : (2 : MvPolynomial (Fin 4) K) ≠ 0 := by
    rw [← map_ofNat C 2, Ne, C_eq_zero]
    exact h2
  have h0 : (2 : MvPolynomial (Fin 4) K) * (β * oddCubic K) = 0 := by
    linear_combination -hT
  rw [hab, (mul_eq_zero.mp h0).resolve_left h2', add_zero]
  exact hα

end Subalgebra

/-! ## Normal form -/

section NormalForm

variable (K)

/-- The span of the normal monomials of degree `d`. -/
noncomputable abbrev normalSpan (d : ℕ) : Submodule K (MvPolynomial (Fin 4) K) :=
  Submodule.span K ((fun m : NormalMono => m.poly K) '' {m | m.deg = d})

/-- Every monomial in `q₁, q₂, q₄, q₆, q₈` is a combination of normal monomials of its degree. -/
theorem qMonomial_mem_normalSpan (b : ℕ) : ∀ u v w a : ℕ,
    q1 K ^ u * q2 K ^ v * q4 K ^ w * q6 K ^ b * q8 K ^ a ∈
      normalSpan K (u + 2 * v + 4 * w + 6 * b + 8 * a) := by
  induction b with
  | zero =>
    intro u v w a
    exact Submodule.subset_span ⟨⟨u, v, w, 0, a, Or.inr rfl⟩, rfl, rfl⟩
  | succ b ih =>
    intro u v w a
    rcases lt_or_ge u 2 with hu | hu
    · exact Submodule.subset_span ⟨⟨u, v, w, b + 1, a, Or.inl hu⟩, rfl, rfl⟩
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' hu
      have key : q1 K ^ (u + 2) * q2 K ^ v * q4 K ^ w * q6 K ^ (b + 1) * q8 K ^ a =
          q1 K ^ u * q2 K ^ v * q4 K ^ (w + 2) * q6 K ^ b * q8 K ^ a -
            q1 K ^ u * q2 K ^ v * q4 K ^ w * q6 K ^ b * q8 K ^ (a + 1) := by
        linear_combination (q1 K ^ u * q2 K ^ v * q4 K ^ w * q6 K ^ b * q8 K ^ a) * q8_eq K
      rw [key]
      have h1 := ih u v (w + 2) a
      have h2 := ih u v w (a + 1)
      rw [show u + 2 * v + 4 * (w + 2) + 6 * b + 8 * a =
        u + 2 + 2 * v + 4 * w + 6 * (b + 1) + 8 * a by ring] at h1
      rw [show u + 2 * v + 4 * w + 6 * b + 8 * (a + 1) =
        u + 2 + 2 * v + 4 * w + 6 * (b + 1) + 8 * a by ring] at h2
      exact Submodule.sub_mem _ h1 h2

lemma isHomogeneous_q1 : (q1 K).IsHomogeneous 1 := by
  have hX := fun i : Fin 4 => isHomogeneous_X K i
  exact (((hX 0).add (hX 1)).add (hX 2)).add (hX 3)

lemma isHomogeneous_q2 : (q2 K).IsHomogeneous 2 := by
  have hX := fun i : Fin 4 => isHomogeneous_X K i
  exact (((((hX 0).mul (hX 1)).add ((hX 0).mul (hX 2))).add ((hX 0).mul (hX 3))).add
    ((hX 1).mul (hX 2))).add ((hX 1).mul (hX 3)) |>.add ((hX 2).mul (hX 3))

lemma isHomogeneous_q4 : (q4 K).IsHomogeneous 4 := by
  have hX := fun i : Fin 4 => isHomogeneous_X K i
  have p := fun i j : Fin 4 => (hX i).mul (hX j)
  exact (((((hX 0).pow 2).mul (((p 1 2).add (p 1 3)).add (p 2 3))).add
    (((hX 1).pow 2).mul (((p 0 2).add (p 0 3)).add (p 2 3)))).add
    (((hX 2).pow 2).mul (((p 0 1).add (p 0 3)).add (p 1 3)))).add
    (((hX 3).pow 2).mul (((p 0 1).add (p 0 2)).add (p 1 2)))

lemma isHomogeneous_q6 : (q6 K).IsHomogeneous 6 := by
  have hX := fun i : Fin 4 => isHomogeneous_X K i
  have p := fun i j : Fin 4 => (hX i).mul (hX j)
  exact (((p 0 1).add (p 2 3)).mul ((p 0 2).add (p 1 3))).mul ((p 0 3).add (p 1 2))

/-- The degree-`d` component of any element of `K[q₁, q₂, q₄, q₆]` is a combination of normal
monomials of degree `d`. -/
theorem homogeneousComponent_aeval_qGens_mem (d : ℕ) (P : MvPolynomial (Fin 4) K) :
    homogeneousComponent d (aeval (qGens K) P) ∈ normalSpan K d := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
      ← Algebra.smul_def, map_smul]
    refine Submodule.smul_mem _ c ?_
    have hm := qMonomial_mem_normalSpan K (m 3) (m 0) (m 1) (m 2) 0
    simp only [pow_zero, mul_one, mul_zero, add_zero] at hm
    have hhom : (q1 K ^ m 0 * q2 K ^ m 1 * q4 K ^ m 2 * q6 K ^ m 3).IsHomogeneous
        (m 0 + 2 * m 1 + 4 * m 2 + 6 * m 3) := by
      have := ((((isHomogeneous_q1 K).pow (m 0)).mul ((isHomogeneous_q2 K).pow (m 1))).mul
        ((isHomogeneous_q4 K).pow (m 2))).mul ((isHomogeneous_q6 K).pow (m 3))
      convert this using 1
      ring
    simp only [qGens, Matrix.cons_val]
    rw [homogeneousComponent_of_mem hhom]
    split_ifs with h
    · rw [h]; exact hm
    · exact Submodule.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hp hq

/-- A homogeneous element of `K[q₁, q₂, q₄, q₆]` is a combination of normal monomials of its
degree. -/
theorem mem_normalSpan_of_mem_qAlg {F : MvPolynomial (Fin 4) K} (hF : F ∈ qAlg K) {d : ℕ}
    (hd : F.IsHomogeneous d) : F ∈ normalSpan K d := by
  obtain ⟨P, rfl⟩ := mem_qAlg_iff.1 hF
  rw [← homogeneousComponent_eq_self hd]
  exact homogeneousComponent_aeval_qGens_mem K d P

end NormalForm

/-- **Generation.** A `G`-invariant polynomial, homogeneous of degree `d`, is a `K`-linear
combination of the normal monomials of degree `d`. -/
theorem ginv_span {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {F : MvPolynomial (Fin 4) K}
    (hF : GInvariant K F) {d : ℕ} (hd : F.IsHomogeneous d) :
    F ∈ Submodule.span K ((fun m : NormalMono => m.poly K) '' {m | m.deg = d}) :=
  mem_normalSpan_of_mem_qAlg K (ginv_mem_qAlg h2 hF) hd

end PauliCubes
