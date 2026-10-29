/-
**Rectangular interpolation at a rational mixing ratio.**

If `ω(k₁) ≤ τ₁` and `ω(k₂) ≤ τ₂` (rectangular admissible exponents for `n × n^k × n`), then for naturals `p, q`
the exponent `(pτ₁ + qτ₂)/(p+q)` is admissible at the aspect `(pk₁ + qk₂)/(p+q)`. No asymptotic spectrum: take
one algorithm at each endpoint (sizes `2^{tp}` and `2^{tq}`), turn each into a bilinear rank bound (`2·cost`),
multiply the ranks under the tensor product, and feed the one fixed rank decomposition to OpenAI's block-step
recursion (`rectangularAdmissibleExponent_of_block_step`).
-/
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.Growth
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity

noncomputable section
namespace IDMM
open OAI.MatrixMultiplication OAI.MatrixMultiplication.Arithmetic OAI.MatrixMultiplication.Foundation

/-! ## Ranks of matrix tensors -/

theorem rank_matrix_equiv {A B C A' B' C' : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] (eA : A' ≃ A) (eB : B' ≃ B) (eC : C' ≃ C) {r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) A B C) r) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) A' B' C') r := by
  have h2 := h.pullback (fun x : A' × B' => (eA x.1, eB x.2)) (fun y : B' × C' => (eB y.1, eC y.2))
    (fun z : C' × A' => (eC z.1, eA z.2))
  convert h2 using 1
  funext x y z
  simp only [Tensor.pullback, Tensor.matrixCoefficients, eA.injective.eq_iff, eB.injective.eq_iff,
    eC.injective.eq_iff]

theorem rank_fin_product {n₁ b₁ c₁ n₂ b₂ c₂ r s : ℕ}
    (h₁ : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin n₁) (Fin b₁) (Fin c₁)) r)
    (h₂ : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin n₂) (Fin b₂) (Fin c₂)) s) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin (n₁ * n₂)) (Fin (b₁ * b₂)) (Fin (c₁ * c₂)))
      (r * s) :=
  rank_matrix_equiv finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm
    (Tensor.matrixCoefficients_product_rank h₁ h₂)

/-! ## Choosing the scale -/

theorem exists_two_rpow_ge (X : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 1 ≤ t ∧ X ≤ (2 : ℝ) ^ ((t : ℝ) * ε) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⌈X / (ε * Real.log 2)⌉₊ + 1, by omega, ?_⟩
  set t : ℕ := ⌈X / (ε * Real.log 2)⌉₊ + 1
  have ht : X / (ε * Real.log 2) ≤ t := by
    have := Nat.le_ceil (X / (ε * Real.log 2)); simp only [t]; push_cast; linarith
  have h1 : X ≤ (t : ℝ) * ε * Real.log 2 := by
    rw [div_le_iff₀ (by positivity)] at ht; linarith
  rw [Real.rpow_def_of_pos (by norm_num)]
  have := Real.add_one_le_exp (Real.log 2 * ((t : ℝ) * ε))
  nlinarith

theorem natCast_two_pow_rpow (N : ℕ) (x : ℝ) : ((2 ^ N : ℕ) : ℝ) ^ x = (2 : ℝ) ^ ((N : ℝ) * x) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-! ## The interpolation -/

/-- **The block-step recursion from one rank decomposition**, over any field. -/
theorem rae_of_scheme {F : Type*} [Field F] {a b R : ℕ}
    (hRk : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R) (ha2 : 2 ≤ a)
    {k τ : ℝ} (hk0 : 0 ≤ k) (hτ : 0 ≤ τ) (hab : (a : ℝ) ^ k ≤ b) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : ((a * b : ℕ) : ℝ) ≤ (a : ℝ) ^ τ) (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_block_step (a := a) (b := b) (R := R)
    (K := 2 * R * (2 * a * b + a ^ 2)) ha2 hk0 hab hτ hR hin hout
  · exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, (scalarAlgorithm_cost F).le⟩
  · -- one block step from the rank decomposition
    intro m p' P hP
    obtain ⟨Q, hQ, hQc⟩ := RecursiveBlock.rank_block_step hRk P hP
    refine ⟨Q, hQ, ?_⟩
    rw [hQc]
    have e : (2 * a * b + a ^ 2) * (m * p' + m ^ 2) =
        (a * b * m * p' + b * a * p' * m + a * a * m * m) + (2 * a * b * m ^ 2 + a ^ 2 * m * p') := by ring
    have : 2 * R * (a * b * m * p' + b * a * p' * m + a * a * m * m) ≤
        2 * R * (2 * a * b + a ^ 2) * (m * p' + m ^ 2) := by
      rw [mul_assoc (2 * R), e]; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    exact Nat.add_le_add_left this _


/-- **The interpolated scheme.** One fixed rank decomposition of `⟨a, b, a⟩` over ℂ with the size conditions of
the block-step recursion at the aspect `(pk₁ + qk₂)/(p+q)` and the exponent `(pτ₁ + qτ₂)/(p+q) + 2ε`. -/
theorem exists_interp_scheme
    (hrank : ∀ {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c), P.Correct →
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) (2 * P.cost))
    {k₁ k₂ τ₁ τ₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₁' : k₁ ≤ 1) (hk₂' : k₂ ≤ 1)
    (hτ₁ : 2 ≤ τ₁) (hτ₂ : 2 ≤ τ₂)
    (h₁ : RectangularAdmissibleExponent ℂ k₁ τ₁) (h₂ : RectangularAdmissibleExponent ℂ k₂ τ₂)
    (p q : ℕ) (hpq : 0 < p + q) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b R : ℕ, Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin a)) R ∧
      2 ≤ a ∧ (a : ℝ) ^ ((p * k₁ + q * k₂) / (p + q)) ≤ b ∧
      (R : ℝ) ≤ (a : ℝ) ^ ((p * τ₁ + q * τ₂) / (p + q) + 2 * ε) ∧
      ((a * b : ℕ) : ℝ) ≤ (a : ℝ) ^ ((p * τ₁ + q * τ₂) / (p + q) + 2 * ε) ∧
      (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ ((p * τ₁ + q * τ₂) / (p + q) + 2 * ε) := by
  set k : ℝ := (p * k₁ + q * k₂) / (p + q) with hkdef
  set τ : ℝ := (p * τ₁ + q * τ₂) / (p + q) with hτdef
  have hpq' : (0 : ℝ) < p + q := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk0 : 0 ≤ k := by rw [hkdef]; positivity
  have hk1 : k ≤ 1 := by rw [hkdef, div_le_one hpq']; nlinarith
  have hτ2 : 2 ≤ τ := by rw [hτdef, le_div_iff₀ hpq']; nlinarith
  obtain ⟨C₁, hC₁, g₁⟩ := h₁ ε hε
  obtain ⟨C₂, hC₂, g₂⟩ := h₂ ε hε
  obtain ⟨t, ht1, hX⟩ := exists_two_rpow_ge (max (4 * C₁ * C₂) 4) hε
  -- the two endpoint algorithms
  set n₁ : ℕ := 2 ^ (t * p) with hn₁
  set n₂ : ℕ := 2 ^ (t * q) with hn₂
  set b₁ : ℕ := innerSize n₁ k₁ with hb₁def
  set b₂ : ℕ := innerSize n₂ k₂ with hb₂def
  set a := n₁ * n₂ with hadef
  set b := b₁ * b₂ with hbdef
  obtain ⟨P₁, hP₁, hc₁⟩ := g₁ n₁ Nat.one_le_two_pow
  obtain ⟨P₂, hP₂, hc₂⟩ := g₂ n₂ Nat.one_le_two_pow
  have hRk := rank_fin_product (hrank P₁ hP₁) (hrank P₂ hP₂)
  set R := 2 * P₁.cost * (2 * P₂.cost) with hRdef
  -- powers of `a`
  have haN : a = 2 ^ (t * (p + q)) := by rw [hadef, hn₁, hn₂, ← pow_add, Nat.mul_add]
  have hapow : ∀ x : ℝ, (a : ℝ) ^ x = (2 : ℝ) ^ (((t : ℝ) * (p + q)) * x) := by
    intro x; rw [haN, natCast_two_pow_rpow]; push_cast; ring_nf
  have hn₁pow : ∀ x : ℝ, (n₁ : ℝ) ^ x = (2 : ℝ) ^ (((t : ℝ) * p) * x) := by
    intro x; rw [hn₁, natCast_two_pow_rpow]; push_cast; ring_nf
  have hn₂pow : ∀ x : ℝ, (n₂ : ℝ) ^ x = (2 : ℝ) ^ (((t : ℝ) * q) * x) := by
    intro x; rw [hn₂, natCast_two_pow_rpow]; push_cast; ring_nf
  have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hsplit : ∀ x₁ x₂ : ℝ, (a : ℝ) ^ ((p * x₁ + q * x₂) / (p + q)) = (n₁ : ℝ) ^ x₁ * (n₂ : ℝ) ^ x₂ := by
    intro x₁ x₂
    rw [hapow, hn₁pow, hn₂pow, ← Real.rpow_add (by norm_num)]
    congr 1; field_simp
  have ha1 : (1 : ℝ) ≤ a := by rw [haN]; exact_mod_cast Nat.one_le_two_pow
  have haε : max (4 * C₁ * C₂) 4 ≤ (a : ℝ) ^ ε := by
    refine hX.trans ?_
    rw [hapow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : (1 : ℝ) ≤ p + q := by exact_mod_cast hpq
    have h2 : (t : ℝ) ≤ t * (p + q) := le_mul_of_one_le_right (by positivity) h1
    exact mul_le_mul_of_nonneg_right h2 hε.le
  have hn₁1 : (1 : ℝ) ≤ (n₁ : ℝ) ^ k₁ := Real.one_le_rpow (by exact_mod_cast Nat.one_le_two_pow) hk₁
  have hn₂1 : (1 : ℝ) ≤ (n₂ : ℝ) ^ k₂ := Real.one_le_rpow (by exact_mod_cast Nat.one_le_two_pow) hk₂
  have hb₁ : (n₁ : ℝ) ^ k₁ ≤ b₁ := by rw [hb₁def]; exact Nat.le_ceil _
  have hb₂ : (n₂ : ℝ) ^ k₂ ≤ b₂ := by rw [hb₂def]; exact Nat.le_ceil _
  have hb₁' : (b₁ : ℝ) ≤ 2 * (n₁ : ℝ) ^ k₁ := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (n₁ : ℝ) ^ k₁ by positivity)
    rw [hb₁def]; unfold innerSize; linarith
  have hb₂' : (b₂ : ℝ) ≤ 2 * (n₂ : ℝ) ^ k₂ := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (n₂ : ℝ) ^ k₂ by positivity)
    rw [hb₂def]; unfold innerSize; linarith
  have hak : (a : ℝ) ^ k = (n₁ : ℝ) ^ k₁ * (n₂ : ℝ) ^ k₂ := hsplit k₁ k₂
  have ha2 : 2 ≤ a := by
    rw [haN]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t * (p + q)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_pos (by omega) hpq)
  refine ⟨a, b, R, hRk, ha2, ?_, ?_, ?_, ?_⟩
  · -- `a^k ≤ b`
    rw [hak, hbdef]; push_cast
    exact mul_le_mul hb₁ hb₂ (by positivity) (by positivity)
  · -- the rank
    have hc₁' : ((2 * P₁.cost : ℕ) : ℝ) ≤ 2 * C₁ * (n₁ : ℝ) ^ (τ₁ + ε) := by push_cast; linarith
    have hc₂' : ((2 * P₂.cost : ℕ) : ℝ) ≤ 2 * C₂ * (n₂ : ℝ) ^ (τ₂ + ε) := by push_cast; linarith
    have hprod : (R : ℝ) ≤ 4 * C₁ * C₂ * (a : ℝ) ^ (τ + ε) := by
      have : (a : ℝ) ^ (τ + ε) = (n₁ : ℝ) ^ (τ₁ + ε) * (n₂ : ℝ) ^ (τ₂ + ε) := by
        rw [← hsplit]; congr 1; rw [hτdef]; field_simp; ring
      rw [this, hRdef]; push_cast
      calc (2 * (P₁.cost : ℝ)) * (2 * P₂.cost) ≤ (2 * C₁ * (n₁ : ℝ) ^ (τ₁ + ε)) * (2 * C₂ * (n₂ : ℝ) ^ (τ₂ + ε)) := by
            push_cast at hc₁' hc₂'
            exact mul_le_mul hc₁' hc₂' (by positivity) (by positivity)
        _ = _ := by ring
    calc (R : ℝ) ≤ 4 * C₁ * C₂ * (a : ℝ) ^ (τ + ε) := hprod
      _ ≤ (a : ℝ) ^ ε * (a : ℝ) ^ (τ + ε) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans haε) (by positivity)
      _ = (a : ℝ) ^ (τ + 2 * ε) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; ring
  · -- `a·b`
    have h1 : ((a * b : ℕ) : ℝ) ≤ 4 * (a : ℝ) ^ (1 + k) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one, hak, hbdef]; push_cast
      have hbb : (b₁ : ℝ) * b₂ ≤ (2 * (n₁ : ℝ) ^ k₁) * (2 * (n₂ : ℝ) ^ k₂) :=
        mul_le_mul hb₁' hb₂' (by positivity) (by positivity)
      calc (a : ℝ) * ((b₁ : ℝ) * b₂) ≤ (a : ℝ) * ((2 * (n₁ : ℝ) ^ k₁) * (2 * (n₂ : ℝ) ^ k₂)) :=
            mul_le_mul_of_nonneg_left hbb (by positivity)
        _ = _ := by ring
    have h2 : (a : ℝ) ^ (1 + k) ≤ (a : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    have h3 : (4 : ℝ) ≤ (a : ℝ) ^ (2 * ε) :=
      ((le_max_right _ _).trans haε).trans (Real.rpow_le_rpow_of_exponent_le ha1 (by linarith))
    calc ((a * b : ℕ) : ℝ) ≤ 4 * (a : ℝ) ^ τ := h1.trans (by linarith)
      _ ≤ (a : ℝ) ^ (2 * ε) * (a : ℝ) ^ τ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (a : ℝ) ^ (τ + 2 * ε) := by rw [← Real.rpow_add (by linarith)]; ring_nf
  · -- `a²`
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ha1 (by push_cast; linarith)

/-- **Interpolation at a rational ratio**, assuming programs give rank bounds. -/
theorem rect_interp_of_rank
    (hrank : ∀ {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c), P.Correct →
      Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) (2 * P.cost))
    {k₁ k₂ τ₁ τ₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₁' : k₁ ≤ 1) (hk₂' : k₂ ≤ 1)
    (hτ₁ : 2 ≤ τ₁) (hτ₂ : 2 ≤ τ₂)
    (h₁ : RectangularAdmissibleExponent ℂ k₁ τ₁) (h₂ : RectangularAdmissibleExponent ℂ k₂ τ₂)
    (p q : ℕ) (hpq : 0 < p + q) :
    RectangularAdmissibleExponent ℂ ((p * k₁ + q * k₂) / (p + q)) ((p * τ₁ + q * τ₂) / (p + q)) := by
  set k : ℝ := (p * k₁ + q * k₂) / (p + q) with hkdef
  set τ : ℝ := (p * τ₁ + q * τ₂) / (p + q) with hτdef
  have hpq' : (0 : ℝ) < p + q := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk0 : 0 ≤ k := by rw [hkdef]; positivity
  have hk1 : k ≤ 1 := by rw [hkdef, div_le_one hpq']; nlinarith
  have hτ2 : 2 ≤ τ := by rw [hτdef, le_div_iff₀ hpq']; nlinarith
  -- it suffices to reach `τ + 2ε` for every `ε`
  suffices hmain : ∀ ε : ℝ, 0 < ε → RectangularAdmissibleExponent ℂ k (τ + 2 * ε) by
    intro ε hε
    obtain ⟨C, hC, hb⟩ := hmain (ε / 4) (by positivity) (ε / 2) (by positivity)
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨P, hP, hc⟩ := hb n hn
    refine ⟨P, hP, hc.trans (le_of_eq ?_)⟩
    congr 2; ring
  intro ε hε
  obtain ⟨a, b, R, hRk, ha2, hab, hR, hin, hout⟩ :=
    exists_interp_scheme hrank hk₁ hk₂ hk₁' hk₂' hτ₁ hτ₂ h₁ h₂ p q hpq hε
  exact rae_of_scheme hRk ha2 hk0 (by linarith) hab hR hin hout

end IDMM
