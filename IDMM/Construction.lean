/-
**The cycle-055 construction bound: `ConditionalTarget`.** For every `μ ∈ (1/2, 1)` and every admissible
rectangular exponent `w` at the aspect `(1−μ)/μ`, `ID_N` has noncommutative circuits with `O(N^{C(μ,w)+ε})`
gates, `C(μ,w) = 2H(1/4) − 2μH(1/(4μ)) + μw`: the Majorana corner sum of squares, blocks of `2m` Majoranas with
`m = ⌈μn⌉`, block covers from the layout bound, and a block matrix-multiplication oracle. The core
(`construction_gen`) works over any field with `2 ≠ 0` and `√−1`; over ℂ the oracle comes from OpenAI's programs.
-/
import IDMM.MajCircuit
import IDMM.BlockCover
import IDMM.Eventual
import IDMM.Layout
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

noncomputable section
namespace IDMM
open Finset PauliCubes OAI.MatrixMultiplication OAI.MatrixMultiplication.Arithmetic Filter

variable {μ : ℝ}

/-! ## The block size -/

theorem le_mOfMu (n : ℕ) : μ * n ≤ mOfMu μ n := Nat.le_ceil _

theorem mOfMu_lt (hμ : 0 ≤ μ) (n : ℕ) : (mOfMu μ n : ℝ) < μ * n + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg hμ (Nat.cast_nonneg n))

theorem mOfMu_le (hμ1 : μ ≤ 1) (n : ℕ) : mOfMu μ n ≤ n := by
  unfold mOfMu
  apply Nat.ceil_le.mpr
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem n_le_two_mOfMu (hμ0 : 1 / 2 < μ) (n : ℕ) : n ≤ 2 * mOfMu μ n := by
  have h : μ * n ≤ mOfMu μ n := le_mOfMu n
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (n : ℝ) ≤ 2 * (mOfMu μ n : ℝ) := by nlinarith
  exact_mod_cast this

/-- The spectator dimension fits inside the inner dimension at the aspect `(1−μ)/μ`. -/
theorem inner_le_mu (hμ0 : 1 / 2 < μ) (hμ1 : μ ≤ 1) (n : ℕ) :
    2 ^ (n - mOfMu μ n) ≤ innerSize (2 ^ mOfMu μ n) ((1 - μ) / μ) := by
  have hμpos : 0 < μ := by linarith
  have hm := mOfMu_le hμ1 n
  have h1 : ((n - mOfMu μ n : ℕ) : ℝ) ≤ (1 - μ) / μ * (mOfMu μ n : ℝ) := by
    rw [Nat.cast_sub hm]
    have h := le_mOfMu (μ := μ) n
    have h2 : (1 - μ) / μ * (μ * n) = (1 - μ) * n := by field_simp
    have h3 : (1 - μ) / μ * (μ * n) ≤ (1 - μ) / μ * (mOfMu μ n : ℝ) :=
      mul_le_mul_of_nonneg_left h (div_nonneg (by linarith) hμpos.le)
    nlinarith
  have h2 : ((2 ^ (n - mOfMu μ n) : ℕ) : ℝ) ≤ ((2 ^ mOfMu μ n : ℕ) : ℝ) ^ ((1 - μ) / μ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  unfold innerSize
  exact_mod_cast h2.trans (Nat.le_ceil _)

/-- **Block algorithms at every length.** -/
theorem algorithms_mu (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {w : ℝ}
    (hw : RectangularAdmissibleExponent ℂ ((1 - μ) / μ) w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∃ P : MatrixAlgorithm ℂ (2 ^ mOfMu μ n) (2 ^ (n - mOfMu μ n)) (2 ^ mOfMu μ n), P.Correct ∧
        (P.cost : ℝ) ≤ C * ((2 : ℝ) ^ mOfMu μ n) ^ (w + ε) := by
  obtain ⟨C, hC, hb⟩ := hw ε hε
  refine ⟨C, hC, fun n => ?_⟩
  obtain ⟨P0, hP0, hc0⟩ := hb (2 ^ mOfMu μ n) Nat.one_le_two_pow
  obtain ⟨P, hP, hcP⟩ :=
    MatrixAlgorithm.exists_restrict le_rfl (inner_le_mu hμ0 hμ1.le n) le_rfl P0 hP0
  refine ⟨P, hP, ?_⟩
  calc (P.cost : ℝ) ≤ P0.cost := by exact_mod_cast hcP
    _ ≤ C * ((2 ^ mOfMu μ n : ℕ) : ℝ) ^ (w + ε) := hc0
    _ = _ := by push_cast; ring

/-- **The oracle family over ℂ**, from programs at the aspect `(1−μ)/μ`. -/
theorem oracles_of_rae (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {w : ℝ}
    (hw : RectangularAdmissibleExponent ℂ ((1 - μ) / μ) w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ M : ℕ,
      BlockMM (ncInputs ℂ ((Fin n → Fin 2) ⊕ (Fin n → Fin 2))) (mOfMu μ n) (n - mOfMu μ n) M ∧
        (M : ℝ) ≤ C * ((2 : ℝ) ^ mOfMu μ n) ^ (w + ε) := by
  obtain ⟨C, hC, hP⟩ := algorithms_mu hμ0 hμ1 hw hε
  refine ⟨960 * C, by positivity, fun n => ?_⟩
  obtain ⟨P, hPc, hPcost⟩ := hP n
  refine ⟨960 * P.cost, blockMM_of_algorithm (𝒜 := FreeAlgebra ℂ ((Fin n → Fin 2) ⊕ (Fin n → Fin 2)))
    (inp := ncInputs ℂ _) (fun z => Or.inr ⟨z, rfl⟩) P hPc, ?_⟩
  push_cast
  linarith

/-! ## Covers -/

theorem choose_min {n a : ℕ} (ha : a ≤ n) : n.choose (min a (n - a)) = n.choose a := by
  rcases le_total a (n - a) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.choose_symm ha]

/-- **Block covers of every corner class.** -/
theorem covers_mu (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {δ : ℝ} (hδ : 0 < δ) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ Ccl : ℕ × ℕ → Finset (Finset (Fin n) × Finset (Fin n)),
      (∀ ab ∈ cornerSet n, ∀ p ∈ Ccl ab, p.1.card + p.2.card = 2 * mOfMu μ n) ∧
      (∀ ab ∈ cornerSet n, ∀ S T : Finset (Fin n), S.card = min ab.1 (n - ab.1) →
        T.card = min ab.2 (n - ab.2) → ∃ p ∈ Ccl ab, S ⊆ p.1 ∧ T ⊆ p.2) ∧
      (∀ ab ∈ cornerSet n,
        ((Ccl ab).card : ℝ) ≤ 1 + 2 * n * (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ))) ∧
      1 ≤ (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ)) := by
  classical
  obtain ⟨n₀, hn₀⟩ := layout_bound_mu hμ0 hμ1 hδ
  refine ⟨n₀, fun n hn => ?_⟩
  have hex : ∀ ab ∈ cornerSet n, ∃ C : Finset (Finset (Fin n) × Finset (Fin n)),
      (∀ p ∈ C, p.1.card + p.2.card = 2 * mOfMu μ n) ∧
      (∀ S T : Finset (Fin n), S.card = min ab.1 (n - ab.1) → T.card = min ab.2 (n - ab.2) →
        ∃ p ∈ C, S ⊆ p.1 ∧ T ⊆ p.2) ∧
      (C.card : ℝ) ≤ 1 + 2 * n * (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ)) := by
    intro ab hab
    obtain ⟨ha, hb, hc⟩ := mem_cornerSet.mp hab
    obtain ⟨us, ua, hsum, hus, hua, has, hbs, hratio⟩ := hn₀ n hn ab.1 ab.2 ha hb hc
    obtain ⟨C, hCs, hCc, hCb⟩ :=
      class_cover n (min ab.1 (n - ab.1)) (min ab.2 (n - ab.2)) us ua has hus hbs hua
    refine ⟨C, fun p hp => by rw [(hCs p hp).1, (hCs p hp).2, hsum], hCc, hCb.trans ?_⟩
    have hden : (0 : ℝ) <
        ((us.choose (min ab.1 (n - ab.1)) * ua.choose (min ab.2 (n - ab.2)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.choose_pos has) (Nat.choose_pos hbs)
    have hrat : ((n.choose (min ab.1 (n - ab.1)) * n.choose (min ab.2 (n - ab.2)) : ℕ) : ℝ) /
        ((us.choose (min ab.1 (n - ab.1)) * ua.choose (min ab.2 (n - ab.2)) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ)) := by
      rw [div_le_iff₀ hden, choose_min ha, choose_min hb]
      exact hratio
    have hn0 : (0 : ℝ) ≤ 2 * n := by positivity
    linarith [mul_le_mul_of_nonneg_left hrat hn0]
  refine ⟨fun ab => if h : ab ∈ cornerSet n then Classical.choose (hex ab h) else ∅, ?_, ?_, ?_, ?_⟩
  · intro ab hab
    simp only [dif_pos hab]
    exact (Classical.choose_spec (hex ab hab)).1
  · intro ab hab
    simp only [dif_pos hab]
    exact (Classical.choose_spec (hex ab hab)).2.1
  · intro ab hab
    simp only [dif_pos hab]
    exact (Classical.choose_spec (hex ab hab)).2.2
  · -- the class `(0, 0)` gives `1 ≤ 2^{n(g+δ)}`
    obtain ⟨us, ua, -, -, -, -, -, h⟩ := hn₀ n hn 0 0 (Nat.zero_le _) (Nat.zero_le _) (by simp)
    simpa using h

theorem card_cornerSet (n : ℕ) : (cornerSet n).card ≤ (n + 1) ^ 2 := by
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_range, sq]

theorem constructionExponent_eq (μ w : ℝ) : constructionExponent μ w = gHalfMu μ + μ * w := by
  unfold constructionExponent gHalfMu; ring

/-! ## The size -/

variable {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K]

/-- **Circuits on `2^n` words** with `≤ K·2^{n(C(μ,w)+ε)}` gates for all large `n`, from an oracle family. -/
theorem eventual_gen (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {w : ℝ} (hw2 : 2 ≤ w)
    (horacle : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ M : ℕ,
      BlockMM (ncInputs K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2))) (mOfMu μ n) (n - mOfMu μ n) M ∧
        (M : ℝ) ≤ C * ((2 : ℝ) ^ mOfMu μ n) ^ (w + ε))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ s : ℕ,
      NCSizeLE (IDw K n) s ∧ (s : ℝ) ≤ K' * (2 : ℝ) ^ ((n : ℝ) * (constructionExponent μ w + ε)) := by
  have hμpos : 0 < μ := by linarith
  obtain ⟨C, hC, hP⟩ := horacle (ε / 4) (by positivity)
  obtain ⟨n₁, hcov⟩ := covers_mu hμ0 hμ1 (δ := ε / 4) (by positivity)
  obtain ⟨n₂, hsucc⟩ := eventually_atTop.mp (eventually_succ_le (ε := ε / 16) (by positivity))
  set K1 : ℝ := 3 * C + 200 with hK1
  refine ⟨(3 + 3 * K1) * (2 : ℝ) ^ (w + ε / 4), max n₁ n₂, fun n hn => ?_⟩
  obtain ⟨M, hMM, hPcost⟩ := hP n
  obtain ⟨Ccl, hsize, hcv, hcard, hR1⟩ := hcov n (le_of_max_le_left hn)
  have hT := hsucc n (le_of_max_le_right hn)
  refine ⟨_, idw_blocks (mOfMu_le hμ1.le n) hMM Ccl hsize hcv, ?_⟩
  -- names
  set R : ℝ := (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + ε / 4)) with hR
  set Q : ℝ := ((2 : ℝ) ^ mOfMu μ n) ^ (w + ε / 4) with hQ
  set T : ℝ := (n : ℝ) + 1 with hTdef
  have hT1 : 1 ≤ T := by simp [T]
  have hnT : (n : ℝ) ≤ T := by simp [T]
  have hmn : (mOfMu μ n : ℝ) ≤ n := by exact_mod_cast mOfMu_le hμ1.le n
  have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ mOfMu μ n := one_le_pow₀ (by norm_num)
  have h4Q : (4 : ℝ) ^ mOfMu μ n ≤ Q := by
    have : ((2 : ℝ) ^ mOfMu μ n) ^ (2 : ℝ) ≤ Q := Real.rpow_le_rpow_of_exponent_le h2m (by linarith)
    rwa [Real.rpow_two, ← pow_mul, mul_comm, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] at this
  have h2n4 : (2 : ℝ) ^ n ≤ (4 : ℝ) ^ mOfMu μ n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (n_le_two_mOfMu hμ0 n)
  have h2nQ : (2 : ℝ) ^ n ≤ Q := h2n4.trans h4Q
  have hQ1 : 1 ≤ Q := (one_le_pow₀ (by norm_num)).trans h2nQ
  have hpc : (M : ℝ) ≤ C * Q := hPcost
  -- one block
  have hbc : ((blockCost n (mOfMu μ n) M : ℕ) : ℝ) + 1 ≤ K1 * (T * Q) := by
    unfold blockCost blockGenCost
    push_cast
    have a1 : (2 : ℝ) ^ n * (4 * (mOfMu μ n : ℝ) + 1) ≤ Q * (4 * T) :=
      mul_le_mul h2nQ (by linarith) (by positivity) (by positivity)
    have a2 : ((mOfMu μ n : ℝ) + 1) * 4 ^ mOfMu μ n ≤ T * Q :=
      mul_le_mul (by linarith) h4Q (by positivity) (by positivity)
    have a3 : C * Q ≤ C * (T * Q) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le
    have a4 : 1 ≤ T * Q := one_le_mul_of_one_le_of_one_le hT1 hQ1
    have a5 : Q ≤ T * Q := by nlinarith
    rw [hK1]
    nlinarith
  -- the number of blocks
  have hsum : ((∑ ab ∈ cornerSet n, (Ccl ab).card : ℕ) : ℝ) ≤ 3 * T ^ 3 * R := by
    push_cast
    have b1 : ∑ ab ∈ cornerSet n, ((Ccl ab).card : ℝ) ≤ (cornerSet n).card * (1 + 2 * n * R) := by
      rw [← nsmul_eq_mul]
      exact sum_le_card_nsmul _ _ _ hcard
    have b2 : ((cornerSet n).card : ℝ) ≤ T ^ 2 := by
      have := card_cornerSet n
      have : ((cornerSet n).card : ℝ) ≤ ((n + 1) ^ 2 : ℕ) := by exact_mod_cast this
      simpa [T] using this
    have b3 : 1 + 2 * (n : ℝ) * R ≤ 3 * T * R := by nlinarith
    have b4 : (0 : ℝ) ≤ 1 + 2 * n * R := by positivity
    calc _ ≤ (cornerSet n).card * (1 + 2 * n * R) := b1
      _ ≤ T ^ 2 * (3 * T * R) := mul_le_mul b2 b3 b4 (by positivity)
      _ = 3 * T ^ 3 * R := by ring
  -- the total
  have htot : ((2 * 2 ^ n + ((∑ ab ∈ cornerSet n, (Ccl ab).card) * (blockCost n (mOfMu μ n) M + 1) + 1) :
      ℕ) : ℝ) ≤ (3 + 3 * K1) * (T ^ 4 * R * Q) := by
    have c1 : ((∑ ab ∈ cornerSet n, (Ccl ab).card : ℕ) : ℝ) *
        (((blockCost n (mOfMu μ n) M : ℕ) : ℝ) + 1) ≤ 3 * T ^ 3 * R * (K1 * (T * Q)) :=
      mul_le_mul hsum hbc (by positivity) (by positivity)
    have c2 : 1 ≤ T ^ 4 * R := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) hR1
    have c3 : Q ≤ T ^ 4 * R * Q := by nlinarith
    push_cast at c1 ⊢
    nlinarith
  -- the exponent
  have e1 : T ^ 4 ≤ (2 : ℝ) ^ ((n : ℝ) * (ε / 4)) := by
    calc T ^ 4 ≤ ((2 : ℝ) ^ ((n : ℝ) * (ε / 16))) ^ 4 := pow_le_pow_left₀ (by positivity) hT 4
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast; ring
  have e2 : Q ≤ (2 : ℝ) ^ ((μ * n + 1) * (w + ε / 4)) := by
    rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (mOfMu_lt hμpos.le n).le (by linarith))
  have e3 : T ^ 4 * R * Q ≤ (2 : ℝ) ^ (w + ε / 4) *
      (2 : ℝ) ^ ((n : ℝ) * (constructionExponent μ w + ε)) := by
    calc T ^ 4 * R * Q ≤ (2 : ℝ) ^ ((n : ℝ) * (ε / 4)) * R * (2 : ℝ) ^ ((μ * n + 1) * (w + ε / 4)) := by
          gcongr
      _ = (2 : ℝ) ^ ((n : ℝ) * (ε / 4) + (n : ℝ) * (gHalfMu μ + ε / 4) + (μ * n + 1) * (w + ε / 4)) := by
          rw [hR, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ ((w + ε / 4) + (n : ℝ) * (constructionExponent μ w + ε)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [constructionExponent_eq]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith [mul_nonneg hn0 hε.le, mul_nonneg (mul_nonneg hn0 hε.le) (by linarith : (0 : ℝ) ≤ 1 - μ)]
      _ = _ := Real.rpow_add (by norm_num) _ _
  calc _ ≤ (3 + 3 * K1) * (T ^ 4 * R * Q) := htot
    _ ≤ (3 + 3 * K1) * ((2 : ℝ) ^ (w + ε / 4) *
          (2 : ℝ) ^ ((n : ℝ) * (constructionExponent μ w + ε))) :=
        mul_le_mul_of_nonneg_left e3 (by rw [hK1]; positivity)
    _ = _ := by ring

/-! ## The bridge -/

/-- **The construction over any field**, from an oracle family. -/
theorem construction_gen (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {w : ℝ} (hw2 : 2 ≤ w)
    (horacle : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ M : ℕ,
      BlockMM (ncInputs K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2))) (mOfMu μ n) (n - mOfMu μ n) M ∧
        (M : ℝ) ≤ C * ((2 : ℝ) ^ mOfMu μ n) ^ (w + ε)) :
    IDBoundF K (constructionExponent μ w) := by
  have hc : 0 ≤ constructionExponent μ w := by
    rw [constructionExponent_eq]
    obtain ⟨n₀, h⟩ := covers_mu hμ0 hμ1 (δ := 1) one_pos
    obtain ⟨-, -, -, -, h1⟩ := h (n₀ + 1) (by omega)
    have hpos : (0 : ℝ) < ((n₀ + 1 : ℕ) : ℝ) := by positivity
    have hprod : 0 ≤ ((n₀ + 1 : ℕ) : ℝ) * (gHalfMu μ + 1) := by
      by_contra hneg
      push Not at hneg
      have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
      linarith
    have hg : 0 ≤ gHalfMu μ + 1 := by
      by_contra hg
      push Not at hg
      have := mul_neg_of_pos_of_neg hpos hg
      linarith
    nlinarith
  exact idBoundF_of_eventual hc fun ε hε => eventual_gen hμ0 hμ1 hw2 horacle hε

/-- **`ConditionalTarget`**: the cycle-055 construction over ℂ, for every `μ ∈ (1/2, 1)` and admissible `w`. -/
theorem construction_target : ConditionalTarget := by
  intro μ w hμ0 hμ1 hw
  exact (idBound_iff _).mpr (construction_gen (K := ℂ) hμ0 hμ1 (rectangularAdmissibleExponent_two_le hw)
    fun ε hε => oracles_of_rae hμ0 hμ1 hw hε)

end IDMM
