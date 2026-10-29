/-
From a dual certificate to an invariant polynomial. The certificate `y` gives `certPoly y = Σ_β y_β x^{type β}`;
after the sign change `D = diag(1, 1, 1, -1)` and the substitution `T`, both supports consist of types of
disallowed words, up to a letter permutation. The product over the 48 elements of `S₄ × ⟨T⟩` is then an
invariant polynomial, nonzero at `(1, 1, 1, 1)`, homogeneous of degree `48 n`, whose support points are
sums of 48 permuted types of disallowed words. No averaging is used, so any field with `2 ≠ 0` works.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import PauliCubes.Dual
import PauliCubes.Basic

open Finset MvPolynomial

namespace PauliCubes

variable {K : Type*} [Field K] {n : ℕ}

/-- The exponent vector (type) of a word. -/
noncomputable def wexp (ν : Fin n → Fin 4) : Fin 4 →₀ ℕ := ∑ i, Finsupp.single (ν i) 1

theorem prod_X_eq_monomial (ν : Fin n → Fin 4) :
    (∏ i, (X (ν i) : MvPolynomial (Fin 4) K)) = monomial (wexp ν) 1 := by
  rw [wexp, monomial_sum_one]
  rfl

theorem wexp_apply (ν : Fin n → Fin 4) (a : Fin 4) : wexp ν a = wordType ν a := by
  classical
  simp [wexp, wordType, Finsupp.single_apply, Finset.sum_boole]

/-- The certificate polynomial `Σ_β y_β x^{type β}`. -/
noncomputable def certPoly (y : (Fin n → Fin 4) → K) : MvPolynomial (Fin 4) K :=
  ∑ β, monomial (wexp β) (y β)

theorem certPoly_eq (y : (Fin n → Fin 4) → K) :
    certPoly y = ∑ β, C (y β) * ∏ i, (X (β i) : MvPolynomial (Fin 4) K) := by
  simp [certPoly, prod_X_eq_monomial, C_mul_monomial]

theorem mem_support_certPoly {y : (Fin n → Fin 4) → K} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (certPoly y).support) : ∃ β, y β ≠ 0 ∧ wexp β = e := by
  classical
  have := support_sum (s := univ) (f := fun β => (monomial (wexp β) (y β) : MvPolynomial (Fin 4) K)) he
  obtain ⟨β, -, hβ⟩ := Finset.mem_biUnion.mp this
  by_cases hy : y β = 0
  · simp [hy] at hβ
  · refine ⟨β, hy, ?_⟩
    rw [support_monomial, if_neg hy, Finset.mem_singleton] at hβ
    exact hβ.symm

theorem certPoly_isHomogeneous (y : (Fin n → Fin 4) → K) : (certPoly y).IsHomogeneous n := by
  rw [certPoly_eq]
  apply IsHomogeneous.sum
  intro β _
  have hp := IsHomogeneous.prod (s := univ) (fun i => (X (β i) : MvPolynomial (Fin 4) K)) (fun _ => 1)
    (fun i _ => isHomogeneous_X K (β i))
  simpa using (isHomogeneous_C (Fin 4) (y β)).mul hp

/-- A linear substitution acts on certificate polynomials through the word-level tensor power. -/
theorem bind₁_lin_certPoly (L : Fin 4 → Fin 4 → K) (y : (Fin n → Fin 4) → K) :
    bind₁ (fun b => ∑ a, C (L a b) * X a) (certPoly y) =
      certPoly (fun ν => ∑ β, y β * ∏ i, L (ν i) (β i)) := by
  rw [certPoly_eq, certPoly_eq, map_sum]
  have h : ∀ β : Fin n → Fin 4, bind₁ (fun b => ∑ a, C (L a b) * X a)
      (C (y β) * ∏ i, (X (β i) : MvPolynomial (Fin 4) K)) =
      ∑ ν : Fin n → Fin 4, C (y β * ∏ i, L (ν i) (β i)) * ∏ i, (X (ν i) : MvPolynomial (Fin 4) K) := by
    intro β
    rw [map_mul, bind₁_C_right, map_prod]
    simp only [bind₁_X_right]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod C, map_mul C]
    ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_mul, ← map_sum C]

/-! ## The sign change `D` and the substitution `T` -/

theorem wexp_perm (σ : Equiv.Perm (Fin 4)) (ν : Fin n → Fin 4) :
    wexp (σ ∘ ν) = Finsupp.mapDomain σ (wexp ν) := by
  ext a
  rw [Finsupp.mapDomain_equiv_apply, wexp_apply, wexp_apply]
  simp only [wordType, Function.comp_apply, ← Equiv.eq_symm_apply]

theorem eval_one_certPoly (c : (Fin n → Fin 4) → K) : eval 1 (certPoly c) = ∑ β, c β := by
  simp [certPoly_eq]

variable (K) in
/-- The matrix of `T`: `T(x)_b = Σ_a TL a b · x_a`. -/
noncomputable def TL (a b : Fin 4) : K := 2⁻¹ - if a = b then 1 else 0

variable (K) in
/-- Row signs relating `T` to the change of cut. -/
def sp : Fin 4 → K := ![-1, 1, 1, 1]

/-- The letter reversal `a ↦ 3 - a`. -/
def revP : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem revP_revP (a : Fin 4) : revP (revP a) = a := by
  fin_cases a <;> rfl

theorem Tsub_eq_lin : Tsub K = fun b => ∑ a, C (TL K a b) * X a := by
  funext b
  fin_cases b <;> simp [Tsub, TL, Fin.sum_univ_four] <;> ring

/-- `T` followed by the sign change is a signed change of cut: `T(a,c) s_c = sp(a) M(3 - a, c)`. -/
theorem TL_mul_sgn1 (h2 : (2 : K) ≠ 0) (a c : Fin 4) :
    TL K a c * sgn1 K c = sp K a * cutM K (revP a) c := by
  have h : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  fin_cases a <;> fin_cases c <;> simp [TL, sgn1, sp, cutM, hsign, revP] <;>
    first | ring1 | linear_combination h | linear_combination (-1 : K) * h

theorem T_coeff (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K) (ν : Fin n → Fin 4) :
    ∑ β, y β * tsgn K β * ∏ i, TL K (ν i) (β i) =
      (∏ i, sp K (ν i)) * ∑ β, y β * colVec K (revP ∘ ν) β := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have : tsgn K β * ∏ i, TL K (ν i) (β i) = (∏ i, sp K (ν i)) * colVec K (revP ∘ ν) β := by
    rw [tsgn, colVec, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm]
    exact TL_mul_sgn1 h2 (ν i) (β i)
  rw [mul_assoc, this]
  ring

/-- `g = Σ_β y_β tsgn(β) x^{type β}`, the certificate polynomial after the sign change. -/
noncomputable def gPoly (y : (Fin n → Fin 4) → K) : MvPolynomial (Fin 4) K :=
  certPoly fun β => y β * tsgn K β

theorem bind₁_Tsub_gPoly (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K) :
    bind₁ (Tsub K) (gPoly y) =
      certPoly fun ν => (∏ i, sp K (ν i)) * ∑ β, y β * colVec K (revP ∘ ν) β := by
  rw [gPoly, Tsub_eq_lin, bind₁_lin_certPoly]
  congr 1
  funext ν
  exact T_coeff h2 y ν

theorem rename_Tsub (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    rename σ (Tsub K i) = Tsub K (σ i) := by
  have hs : (X 0 + X 1 + X 2 + X 3 : MvPolynomial (Fin 4) K) = ∑ j, X j := by
    simp [Fin.sum_univ_four]
  simp only [Tsub, hs, map_sub, map_mul, rename_C, map_sum, rename_X]
  rw [Equiv.sum_comp σ (fun j => (X j : MvPolynomial (Fin 4) K))]

theorem bind₁_Tsub_rename (σ : Equiv.Perm (Fin 4)) (p : MvPolynomial (Fin 4) K) :
    bind₁ (Tsub K) (rename σ p) = rename σ (bind₁ (Tsub K) p) := by
  rw [bind₁_rename, rename_bind₁]
  refine congrArg (fun f => bind₁ f p) (funext fun i => ?_)
  exact (rename_Tsub σ i).symm

theorem bind₁_Tsub_Tsub (h2 : (2 : K) ≠ 0) (i : Fin 4) : bind₁ (Tsub K) (Tsub K i) = X i := by
  have h : (C (2 : K)⁻¹ : MvPolynomial (Fin 4) K) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin 4) K) = C 2 from (map_ofNat C 2).symm, ← map_mul,
      inv_mul_cancel₀ h2, map_one]
  simp only [Tsub, map_sub, map_mul, bind₁_C_right, map_add, bind₁_X_right]
  linear_combination (2 * C (2 : K)⁻¹ * (X 0 + X 1 + X 2 + X 3)) * h

theorem bind₁_Tsub_invol (h2 : (2 : K) ≠ 0) (p : MvPolynomial (Fin 4) K) :
    bind₁ (Tsub K) (bind₁ (Tsub K) p) = p := by
  rw [bind₁_bind₁]
  have : (fun i => bind₁ (Tsub K) (Tsub K i)) = X := funext (bind₁_Tsub_Tsub h2)
  rw [this, bind₁_X_left, AlgHom.id_apply]

theorem eval_one_rename (σ : Equiv.Perm (Fin 4)) (p : MvPolynomial (Fin 4) K) :
    eval 1 (rename σ p) = eval 1 p := by
  rw [eval_rename]
  rfl

theorem eval_one_bind₁_Tsub (h2 : (2 : K) ≠ 0) (p : MvPolynomial (Fin 4) K) :
    eval 1 (bind₁ (Tsub K) p) = eval 1 p := by
  have h := eval₂Hom_bind₁ (RingHom.id K) (1 : Fin 4 → K) (Tsub K) p
  have h1 : (fun i => eval₂Hom (RingHom.id K) (1 : Fin 4 → K) (Tsub K i)) = 1 := by
    funext i
    have h' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    simp only [Tsub, coe_eval₂Hom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_add, eval₂_X,
      RingHom.id_apply, Pi.one_apply]
    linear_combination 2 * h'
  rw [h1] at h
  exact h

theorem sum_crossVec (y : (Fin n → Fin 4) → K) :
    ∑ β, y β * crossVec K β = (2⁻¹ : K) ^ n * ∑ β, y β * tsgn K β := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [crossVec, tsgn, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-! ## The product over `S₄ × ⟨T⟩` -/

/-- The 48 factors `rename σ g` and `rename σ (T g)`. -/
noncomputable def factor (y : (Fin n → Fin 4) → K) (j : Equiv.Perm (Fin 4) × Bool) :
    MvPolynomial (Fin 4) K :=
  rename j.1 (if j.2 then bind₁ (Tsub K) (gPoly y) else gPoly y)

/-- `F = Π_{σ ∈ S₄} σ(g) σ(T g)`. -/
noncomputable def bigF (y : (Fin n → Fin 4) → K) : MvPolynomial (Fin 4) K := ∏ j, factor y j

theorem rename_factor (y : (Fin n → Fin 4) → K) (τ : Equiv.Perm (Fin 4))
    (j : Equiv.Perm (Fin 4) × Bool) : rename τ (factor y j) = factor y (τ * j.1, j.2) := by
  simp only [factor, rename_rename, Equiv.Perm.coe_mul]

theorem bind₁_Tsub_factor (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K)
    (j : Equiv.Perm (Fin 4) × Bool) : bind₁ (Tsub K) (factor y j) = factor y (j.1, !j.2) := by
  obtain ⟨σ, b⟩ := j
  cases b <;> simp [factor, bind₁_Tsub_rename, bind₁_Tsub_invol h2]

theorem ginvariant_bigF (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K) : GInvariant K (bigF y) := by
  refine ⟨fun τ => ?_, ?_⟩
  · rw [bigF, map_prod]
    exact Fintype.prod_equiv ((Equiv.mulLeft τ).prodCongr (Equiv.refl Bool)) _ _
      fun j => rename_factor y τ j
  · rw [bigF, map_prod]
    exact Fintype.prod_equiv ((Equiv.refl _).prodCongr (Function.Involutive.toPerm _ Bool.not_not))
      _ _ fun j => bind₁_Tsub_factor h2 y j

theorem isHomogeneous_factor (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K)
    (j : Equiv.Perm (Fin 4) × Bool) : (factor y j).IsHomogeneous n := by
  obtain ⟨σ, b⟩ := j
  apply IsHomogeneous.rename_isHomogeneous
  cases b
  · exact certPoly_isHomogeneous _
  · simp only [if_true]
    rw [bind₁_Tsub_gPoly h2]
    exact certPoly_isHomogeneous _

theorem isHomogeneous_bigF (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K) :
    (bigF y).IsHomogeneous (48 * n) := by
  have h := IsHomogeneous.prod (s := univ) (fun j => factor y j) (fun _ => n)
    (fun j _ => isHomogeneous_factor h2 y j)
  have hc : ∑ _j : Equiv.Perm (Fin 4) × Bool, n = 48 * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm,
      Nat.factorial]
  rwa [hc] at h

theorem eval_one_factor (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K)
    (j : Equiv.Perm (Fin 4) × Bool) : eval 1 (factor y j) = ∑ β, y β * tsgn K β := by
  obtain ⟨σ, b⟩ := j
  cases b <;> simp [factor, eval_one_rename, eval_one_bind₁_Tsub h2, gPoly, eval_one_certPoly]

theorem bigF_ne_zero (h2 : (2 : K) ≠ 0) (y : (Fin n → Fin 4) → K)
    (hy2 : ∑ β, y β * crossVec K β ≠ 0) : bigF y ≠ 0 := by
  intro h0
  have he : eval 1 (bigF y) = 0 := by rw [h0, map_zero]
  rw [bigF, map_prod, Finset.prod_eq_zero_iff] at he
  obtain ⟨j, -, hj⟩ := he
  rw [eval_one_factor h2] at hj
  exact hy2 (by rw [sum_crossVec, hj, mul_zero])

/-! ## Supports -/

open scoped Pointwise in
theorem mem_support_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → MvPolynomial (Fin 4) K)
    {e : Fin 4 →₀ ℕ} (he : e ∈ (∏ j ∈ s, P j).support) :
    ∃ f : ι → (Fin 4 →₀ ℕ), (∀ j ∈ s, f j ∈ (P j).support) ∧ e = ∑ j ∈ s, f j := by
  induction s using Finset.induction_on generalizing e with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at he
    rw [Finset.sum_empty]
    by_contra hne
    exact he (if_neg (Ne.symm hne))
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha] at he
    obtain ⟨x, hx, z, hz, rfl⟩ := Finset.mem_add.mp (support_mul _ _ he)
    obtain ⟨f, hf, rfl⟩ := ih hz
    refine ⟨Function.update f a x, fun j hj => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · simpa using hx
      · rw [Function.update_of_ne (by rintro rfl; exact ha hjs)]
        exact hf j hjs
    · rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun j hjs => ?_
      rw [Function.update_of_ne (by rintro rfl; exact ha hjs)]

theorem factor_support (h2 : (2 : K) ≠ 0) (ch : (Fin n → Fin 4) → Prop) {y : (Fin n → Fin 4) → K}
    (hy0 : ∀ β, ch β → y β = 0) (hy1 : ∀ ν, ch ν → ∑ β, y β * colVec K ν β = 0)
    (j : Equiv.Perm (Fin 4) × Bool) {x : Fin 4 →₀ ℕ} (hx : x ∈ (factor y j).support) :
    ∃ σ : Equiv.Perm (Fin 4), ∃ ν : Fin n → Fin 4, ¬ ch ν ∧ x = Finsupp.mapDomain σ (wexp ν) := by
  obtain ⟨σ, b⟩ := j
  rw [factor, support_rename_of_injective σ.injective, Finset.mem_image] at hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  cases b
  · simp only [Bool.false_eq_true, if_false, gPoly] at hx0
    obtain ⟨β, hβ, rfl⟩ := mem_support_certPoly hx0
    refine ⟨σ, β, fun hc => hβ ?_, rfl⟩
    rw [hy0 β hc, zero_mul]
  · simp only [if_true] at hx0
    rw [bind₁_Tsub_gPoly h2] at hx0
    obtain ⟨ν, hν, rfl⟩ := mem_support_certPoly hx0
    refine ⟨σ * revP, revP ∘ ν, fun hc => hν ?_, ?_⟩
    · rw [hy1 _ hc, mul_zero]
    · have hr : revP ∘ (revP ∘ ν) = ν := by
        funext i
        exact revP_revP (ν i)
      conv_lhs => rw [← hr, wexp_perm]
      rw [Equiv.Perm.coe_mul, Finsupp.mapDomain_comp]

/-- **From a certificate to an invariant.** A dual certificate yields a nonzero polynomial,
invariant under letter permutations and `T`, homogeneous of degree `48 n`, each of whose support
points is a sum of 48 letter-permuted types of disallowed words. -/
theorem cert_invariant (h2 : (2 : K) ≠ 0) (ch : (Fin n → Fin 4) → Prop) (y : (Fin n → Fin 4) → K)
    (hy0 : ∀ β, ch β → y β = 0) (hy1 : ∀ ν, ch ν → ∑ β, y β * colVec K ν β = 0)
    (hy2 : ∑ β, y β * crossVec K β ≠ 0) :
    ∃ F : MvPolynomial (Fin 4) K, GInvariant K F ∧ F.IsHomogeneous (48 * n) ∧ F ≠ 0 ∧
      ∀ e ∈ F.support, ∃ f : Equiv.Perm (Fin 4) × Bool → Equiv.Perm (Fin 4) × (Fin n → Fin 4),
        (∀ j, ¬ ch (f j).2) ∧ e = ∑ j, Finsupp.mapDomain (f j).1 (wexp (f j).2) := by
  classical
  refine ⟨bigF y, ginvariant_bigF h2 y, isHomogeneous_bigF h2 y, bigF_ne_zero h2 y hy2,
    fun e he => ?_⟩
  obtain ⟨g, hg, rfl⟩ := mem_support_prod univ (factor y) he
  have hs : ∀ j, ∃ p : Equiv.Perm (Fin 4) × (Fin n → Fin 4), ¬ ch p.2 ∧
      g j = Finsupp.mapDomain p.1 (wexp p.2) := by
    intro j
    obtain ⟨σ, ν, hν, hx⟩ := factor_support h2 ch hy0 hy1 j (hg j (mem_univ j))
    exact ⟨(σ, ν), hν, hx⟩
  choose f hf using hs
  exact ⟨f, fun j => (hf j).1, Finset.sum_congr rfl fun j _ => (hf j).2⟩

end PauliCubes
