/-
Naslund's P(N) and Hurwitz's problem over ℂ from Theorem B (Appendix B of Anthropic's
"A 2^o(n) Time Algorithm for 3-SAT").

Not part of the Anthropic formalization: a corollary built on it. Anthropic's `eth` package is a
Lake dependency pinned to anthropics/formal-math at commit 16a5ce4, and none of its files is
changed. From the root of this repository:

    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean

`#print axioms` on the theorems below gives only propext, Classical.choice and Quot.sound.

P(N) (Naslund, arXiv:1701.04475, Problem 12) is the least number of functions, each of row-wise
rank 1 (g(x,y)·g'(u,v)) or column-wise rank 1 (g(x,u)·g'(y,v)), that sum to the crossing
[x = v][y = u] on an alphabet of N letters. Over ℚ.

* `TheoremB.crossWidth`: pieces with parameters (ρ, c) at λ write d·[x=v][y=u] on λ-bit
  strings as a sum of Σ_{i ∈ 𝓘} 2^{min(c^row_i, c^col_i)} such terms.
* `TheoremB.width_le`: that number is at most (2λ)^c · 2^{2ρλ + (c/2)·log₂(2λ)}.
* `TheoremB.p_le`: with Theorem B (ρ = 1/√2), P(N) ≤ (2N)^{√2} · (2·log₂ N + 2)^{3c/2} for every
  N ≥ 2, for one constant c.
* `TheoremB.p_le_rpow`: for every ε > 0, P(N) ≤ N^{√2 + ε} for all large N.
* `TheoremB.prodLE_of_PLE`: each term of a crossing decomposition gives one product of two
  bilinear forms in (Σ X_i²)(Σ Y_j²) (Hrubeš–Wigderson–Yehudayoff 2011, Lemma 3.5 and
  Proposition 4.1(1), proved here directly).
* `TheoremB.sosLE_of_prodLE`: over ℂ each product is two squares.
* `TheoremB.hurwitz_le`, `TheoremB.hurwitz_le_rpow`: Hurwitz's sum-of-squares problem over ℂ has
  composition formulas of type [N, N, M] with M ≤ N^{√2 + ε} for all large N (Hrubeš, CCC 2024:
  O(N^{1.62})).
-/
import TheoremB.Defs
import PiecesStatement
import PiecesCounted.Basic
import PiecesCounted.Half

open Finset Pieces

namespace TheoremB

/-! ## Sums of row-wise and column-wise rank-1 terms -/

/-- `F` is a sum of `M` terms, each g(x,y)·g'(u,v) (`col j = false`) or g(x,u)·g'(y,v)
(`col j = true`), with integer values. -/
def WidthLE {lam : ℕ} (F : Four lam) (M : ℕ) : Prop :=
  ∃ (g g' : Fin M → Bits lam → Bits lam → ℤ) (col : Fin M → Bool),
    ∀ x y u v, F x y u v = ∑ j, if col j then g j x u * g' j y v else g j x y * g' j u v

variable {lam : ℕ}

theorem WidthLE.zero : WidthLE (fun _ _ _ _ => 0 : Four lam) 0 :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun _ _ _ _ => by simp⟩

theorem WidthLE.add {F G : Four lam} {M N : ℕ} (hF : WidthLE F M) (hG : WidthLE G N) :
    WidthLE (fun x y u v => F x y u v + G x y u v) (M + N) := by
  obtain ⟨g, g', col, h⟩ := hF
  obtain ⟨k, k', col', h'⟩ := hG
  refine ⟨Fin.append g k, Fin.append g' k', Fin.append col col', fun x y u v => ?_⟩
  show F x y u v + G x y u v = _
  rw [Fin.sum_univ_add, h, h']
  simp [Fin.append_left, Fin.append_right]

theorem WidthLE.sum {ι : Type} (s : Finset ι) (F : ι → Four lam) (M : ι → ℕ)
    (h : ∀ i ∈ s, WidthLE (F i) (M i)) :
    WidthLE (fun x y u v => ∑ i ∈ s, F i x y u v) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (WidthLE.zero (lam := lam))
  | @insert a s ha ih =>
    have := (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
    simpa [sum_insert ha] using this

/-- An equivalence between θ ∈ {0,1}^k and `Fin (2^k)`. -/
noncomputable def bitsEquiv (k : ℕ) : Fin (2 ^ k) ≃ Bits k :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- A factorization through k bits as a function of (x,y) and (u,v) gives 2^k row-wise terms. -/
theorem WidthLE.of_row {A : Four lam} {k : ℕ} {b : ℤ} (h : FactorsThrough (rowwise A) k b) :
    WidthLE A (2 ^ k) := by
  obtain ⟨f, f', hf, -, -⟩ := h
  refine ⟨fun j x y => f (x, y) (bitsEquiv k j), fun j u v => f' (u, v) (bitsEquiv k j),
    fun _ => false, fun x y u v => ?_⟩
  simp only [Bool.false_eq_true, if_false]
  rw [show A x y u v = rowwise A (x, y) (u, v) from rfl, hf]
  exact ((bitsEquiv k).sum_comp fun θ => f (x, y) θ * f' (u, v) θ).symm

/-- A factorization through k bits as a function of (x,u) and (y,v) gives 2^k column-wise terms. -/
theorem WidthLE.of_col {A : Four lam} {k : ℕ} {b : ℤ} (h : FactorsThrough (colwise A) k b) :
    WidthLE A (2 ^ k) := by
  obtain ⟨f, f', hf, -, -⟩ := h
  refine ⟨fun j x u => f (x, u) (bitsEquiv k j), fun j y v => f' (y, v) (bitsEquiv k j),
    fun _ => true, fun x y u v => ?_⟩
  simp only [if_true]
  rw [show A x y u v = colwise A (x, u) (y, v) from rfl, hf]
  exact ((bitsEquiv k).sum_comp fun θ => f (x, u) θ * f' (y, v) θ).symm

/-- Each piece in its cheaper direction. -/
theorem WidthLE.of_both {A : Four lam} {k k' : ℕ} {b b' : ℤ} (hr : FactorsThrough (rowwise A) k b)
    (hc : FactorsThrough (colwise A) k' b') : WidthLE A (2 ^ min k k') := by
  rcases le_total k k' with hk | hk
  · rw [min_eq_left hk]; exact .of_row hr
  · rw [min_eq_right hk]; exact .of_col hc

/-! ## Pieces give a narrow crossing -/

/-- Pieces with parameters (ρ, c) at λ write d·[x=v][y=u] as a sum of Σ_{i ∈ 𝓘}
2^{min(c^row_i, c^col_i)} terms of row-wise or column-wise rank 1. -/
theorem crossWidth {lam : ℕ} {P : Family lam} {ρ : ℝ} {c : ℕ} (h : P.Is ρ c) :
    WidthLE (fun x y u v => P.d * cross x y u v : Four lam)
      (∑ i ∈ P.I, 2 ^ min (P.crow i) (P.ccol i)) := by
  have hw := WidthLE.sum P.I P.A (fun i => 2 ^ min (P.crow i) (P.ccol i))
    fun i hi => .of_both (h.row i hi) (h.col i hi)
  have e : (fun x y u v => ∑ i ∈ P.I, P.A i x y u v : Four lam) =
      fun x y u v => P.d * cross x y u v := by
    funext x y u v; exact h.sum_eq x y u v
  rwa [e] at hw

/-- The number of terms: Σ_{i ∈ 𝓘} 2^{min(c^row_i, c^col_i)} ≤ (2λ)^c · 2^{2ρλ + (c/2)·log₂(2λ)},
since min ≤ (c^row_i + c^col_i)/2. -/
theorem width_le {lam : ℕ} {P : Family lam} {ρ : ℝ} {c : ℕ} (h : P.Is ρ c) :
    ((∑ i ∈ P.I, 2 ^ min (P.crow i) (P.ccol i) : ℕ) : ℝ) ≤
      (2 * lam : ℝ) ^ c * (2 : ℝ) ^ (2 * ρ * lam + c / 2 * Real.logb 2 (2 * lam)) := by
  set B : ℝ := (2 : ℝ) ^ (2 * ρ * lam + c / 2 * Real.logb 2 (2 * lam))
  push_cast
  calc ∑ i ∈ P.I, (2 : ℝ) ^ min (P.crow i) (P.ccol i) ≤ ∑ _i ∈ P.I, B := by
        refine sum_le_sum fun i hi => ?_
        have hcap := h.caps i hi
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h1 : ((min (P.crow i) (P.ccol i) : ℕ) : ℝ) ≤ P.crow i := by exact_mod_cast min_le_left _ _
        have h2 : ((min (P.crow i) (P.ccol i) : ℕ) : ℝ) ≤ P.ccol i := by exact_mod_cast min_le_right _ _
        push_cast at hcap h1 h2 ⊢
        linarith
    _ = (#P.I : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * lam : ℝ) ^ c * B := by
        gcongr
        exact_mod_cast h.card_I

/-! ## Theorem B: P(N) ≤ N^{√2 + o(1)} -/

/-- From integer terms for d·crossing to rational terms for the crossing, on any alphabet that
embeds into the λ-bit strings. -/
theorem ple_of_widthLE {lam : ℕ} {α : Type} [DecidableEq α] (e : α → Bits lam) (he : Function.Injective e)
    {d : ℤ} (hd : d ≠ 0) {M : ℕ} (h : WidthLE (fun x y u v => d * cross x y u v : Four lam) M) :
    PLE α M := by
  obtain ⟨g, g', col, hg⟩ := h
  refine ⟨fun j a b => (g j (e a) (e b) : ℚ) / d, fun j a b => (g' j (e a) (e b) : ℚ), col,
    fun x y u v => ?_⟩
  have key := congrArg (fun t : ℤ => (t : ℚ) / d) (hg (e x) (e y) (e u) (e v))
  simp only [cross, he.eq_iff] at key
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [show (if x = v ∧ y = u then 1 else 0 : ℚ) = ((d * (if x = v ∧ y = u then 1 else 0 : ℤ) : ℤ) : ℚ) / d by
    push_cast; field_simp, key]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Theorem B gives, for one constant c and every λ ≥ 1, the crossing on λ-bit strings with at
most 2^{√2·λ} · (2λ)^{3c/2} terms. -/
theorem bits_width : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∃ (d : ℤ) (M : ℕ), 1 ≤ d ∧
    WidthLE (fun x y u v => d * cross x y u v : Four lam) M ∧
    (M : ℝ) ≤ (2 : ℝ) ^ (Real.sqrt 2 * lam) * (2 * lam : ℝ) ^ (3 * c / 2 : ℝ) := by
  obtain ⟨c, D, Alg, hD⟩ := PiecesCounted.halfPiecesExist
  refine ⟨c, fun lam hl => ?_⟩
  have hP := PiecesCounted.toPure D _ c hD.is lam hl
  refine ⟨(D.fam lam).d, _, hP.d_pos, crossWidth hP, (width_le hP).trans (le_of_eq ?_)⟩
  have hlam : (0 : ℝ) < 2 * lam := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : 2 * (1 / Real.sqrt 2) * (lam : ℝ) = Real.sqrt 2 * lam := by
    field_simp; linarith
  rw [Real.rpow_add (by norm_num), h2,
    show (c : ℝ) / 2 * Real.logb 2 (2 * lam) = Real.logb 2 (2 * lam) * (c / 2) by ring,
    Real.rpow_mul (x := 2) (by norm_num) (Real.logb 2 (2 * lam)) (c / 2),
    Real.rpow_logb (by norm_num) (by norm_num) hlam,
    ← Real.rpow_natCast (2 * (lam : ℝ)) c]
  rw [mul_comm ((2 * (lam : ℝ)) ^ (c : ℝ)), mul_assoc, ← Real.rpow_add hlam,
    show (c : ℝ) / 2 + c = 3 * c / 2 by ring]

/-- **P(N) ≤ N^{√2 + o(1)} over ℚ.** For one constant c and every N ≥ 2,
P(N) ≤ (2N)^{√2} · (2·log₂ N + 2)^{3c/2}. -/
theorem p_le : ∃ c : ℕ, ∀ N : ℕ, 2 ≤ N → ∃ M : ℕ, PLE (Fin N) M ∧
    (M : ℝ) ≤ (2 * N : ℝ) ^ Real.sqrt 2 * (2 * Real.logb 2 N + 2) ^ (3 * c / 2 : ℝ) := by
  obtain ⟨c, hc⟩ := bits_width
  refine ⟨c, fun N hN => ?_⟩
  -- λ = ⌈log₂ N⌉, so N ≤ 2^λ < 2N.
  set lam := Nat.clog 2 N
  have hl : 1 ≤ lam := Nat.clog_pos one_lt_two (by omega)
  have hle : N ≤ 2 ^ lam := Nat.le_pow_clog one_lt_two N
  have hpred : 2 ^ (lam - 1) < N := by
    simpa [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < N)
  have h2N : 2 ^ lam ≤ 2 * N := by
    have : 2 ^ lam = 2 * 2 ^ (lam - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  obtain ⟨d, M, hd, hw, hM⟩ := hc lam hl
  -- The N letters as λ-bit strings.
  let e : Fin N → Bits lam := fun a => bitsEquiv lam (Fin.castLE hle a)
  have he : Function.Injective e := (bitsEquiv lam).injective.comp (Fin.castLE_injective hle)
  refine ⟨M, ple_of_widthLE e he (by omega) hw, hM.trans ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hlog : (lam : ℝ) - 1 < Real.logb 2 N := by
    have h1 : (2 : ℝ) ^ ((lam - 1 : ℕ) : ℝ) < N := by
      rw [Real.rpow_natCast]; exact_mod_cast hpred
    have := (Real.lt_logb_iff_rpow_lt one_lt_two hNpos).2 h1
    rwa [Nat.cast_sub hl, Nat.cast_one] at this
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · rw [show Real.sqrt 2 * (lam : ℝ) = lam * Real.sqrt 2 by ring,
      Real.rpow_mul (x := 2) (by norm_num), Real.rpow_natCast]
    refine Real.rpow_le_rpow (by positivity) ?_ (Real.sqrt_nonneg 2)
    exact_mod_cast h2N
  · refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    linarith

/-- **P(N) ≤ N^{√2 + o(1)} over ℚ**, in the form: for every ε > 0, P(N) ≤ N^{√2 + ε} for all large
N. -/
theorem p_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ M : ℕ, PLE (Fin N) M ∧ (M : ℝ) ≤ (N : ℝ) ^ (Real.sqrt 2 + ε) := by
  obtain ⟨c, hc⟩ := p_le
  set r : ℝ := 3 * c / 2
  have hr : 0 ≤ r := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := 2 ^ Real.sqrt 2 * (4 / Real.log 2) ^ r
  have hK : 0 < K := by positivity
  -- (log N)^r ≤ N^ε / K for all large N.
  have ho := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop r hε).def (show (0 : ℝ) < 1 / K by positivity))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 ho
  refine ⟨max N₁ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  obtain ⟨M, hP, hM⟩ := hc N hN2
  refine ⟨M, hP, hM.trans ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have hlogNpos : 0 < Real.log N := hlog2.trans_le hlogN
  have hx := hN₁ N (le_of_max_le_left hN)
  simp only [Real.norm_of_nonneg (Real.rpow_nonneg hlogNpos.le r),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le ε)] at hx
  -- 2·log₂ N + 2 ≤ (4 / log 2)·log N, since log₂ N ≥ 1.
  have hq : 1 ≤ Real.log N / Real.log 2 := (one_le_div hlog2).2 hlogN
  have hb : 2 * Real.logb 2 N + 2 ≤ 4 / Real.log 2 * Real.log N := by
    rw [Real.logb, show 4 / Real.log 2 * Real.log N = 4 * (Real.log N / Real.log 2) by ring]
    linarith
  have h0 : 0 ≤ 2 * Real.logb 2 N + 2 := by rw [Real.logb]; linarith
  calc (2 * N : ℝ) ^ Real.sqrt 2 * (2 * Real.logb 2 N + 2) ^ r
      ≤ (2 * N : ℝ) ^ Real.sqrt 2 * (4 / Real.log 2 * Real.log N) ^ r := by
        gcongr
    _ = K * ((N : ℝ) ^ Real.sqrt 2 * Real.log N ^ r) := by
        rw [Real.mul_rpow (x := 2) (y := N) (by norm_num) hNpos.le,
          Real.mul_rpow (x := 4 / Real.log 2) (y := Real.log N) (by positivity) hlogNpos.le]
        ring
    _ ≤ K * ((N : ℝ) ^ Real.sqrt 2 * (1 / K * (N : ℝ) ^ ε)) := by
        gcongr
    _ = (N : ℝ) ^ (Real.sqrt 2 + ε) := by
        rw [Real.rpow_add hNpos]
        field_simp

/-! ## Hurwitz's problem over ℂ -/

theorem bil_comb {K : Type} [CommRing K] {N : ℕ} (a b : K) (f f' : Fin N → Fin N → K)
    (X Y : Fin N → K) :
    bil (fun i j => a * f i j + b * f' i j) X Y = a * bil f X Y + b * bil f' X Y := by
  simp only [bil, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Σ_{x,y,u,v} A(x,y)·B(u,v) = (Σ A)(Σ B). -/
theorem sum4_mul {K : Type} [CommRing K] {N : ℕ} (A B : Fin N → Fin N → K) :
    ∑ x, ∑ y, ∑ u, ∑ v, A x y * B u v = (∑ x, ∑ y, A x y) * ∑ u, ∑ v, B u v := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]

/-- Σ_{x,y,u,v} (Σ_t T_t)·m = Σ_t Σ_{x,y,u,v} T_t·m. -/
theorem sum4_sum {K : Type} [CommRing K] {N M : ℕ} (T : Fin M → Fin N → Fin N → Fin N → Fin N → K)
    (m : Fin N → Fin N → Fin N → Fin N → K) :
    ∑ x, ∑ y, ∑ u, ∑ v, (∑ t, T t x y u v) * m x y u v =
      ∑ t, ∑ x, ∑ y, ∑ u, ∑ v, T t x y u v * m x y u v := by
  simp only [Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact Finset.sum_comm

/-- Each term of a crossing decomposition becomes one product of two bilinear forms in
(Σ X_i²)(Σ Y_j²) = Σ_{x,y,u,v} [x=v][y=u]·X_x·Y_y·X_v·Y_u. Over ℂ. -/
theorem prodLE_of_PLE {N M : ℕ} (h : PLE (Fin N) M) : ProdLE ℂ N M := by
  obtain ⟨g, g', col, hg⟩ := h
  refine ⟨fun t i j => (g t i j : ℂ), fun t i j => (g' t j i : ℂ), fun X Y => ?_⟩
  have hc : ∀ x y u v : Fin N, (if x = v ∧ y = u then (1 : ℂ) else 0) =
      ∑ t, (((if col t then g t x u * g' t y v else g t x y * g' t u v : ℚ)) : ℂ) := by
    intro x y u v
    rw [← Rat.cast_sum, ← hg x y u v]
    split_ifs <;> simp
  have h1 : ∑ x, ∑ y, ∑ u, ∑ v, (if x = v ∧ y = u then (1 : ℂ) else 0) * (X x * Y y * X v * Y u) =
      (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) := by
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [← h1]
  simp_rw [hc]
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hct : col t = true
  · simp only [hct, ↓reduceIte, Rat.cast_mul]
    calc ∑ x, ∑ y, ∑ u, ∑ v, (g t x u : ℂ) * (g' t y v : ℂ) * (X x * Y y * X v * Y u)
        = ∑ x, ∑ u, ∑ y, ∑ v, ((g t x u : ℂ) * X x * Y u) * ((g' t y v : ℂ) * X v * Y y) :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun v _ => by ring
      _ = (∑ x, ∑ u, (g t x u : ℂ) * X x * Y u) * ∑ y, ∑ v, (g' t y v : ℂ) * X v * Y y :=
          sum4_mul _ _
      _ = _ := by
          simp only [bil]
          congr 1
          exact Finset.sum_comm
  · simp only [hct, Bool.false_eq_true, ↓reduceIte, Rat.cast_mul]
    calc ∑ x, ∑ y, ∑ u, ∑ v, (g t x y : ℂ) * (g' t u v : ℂ) * (X x * Y y * X v * Y u)
        = ∑ x, ∑ y, ∑ u, ∑ v, ((g t x y : ℂ) * X x * Y y) * ((g' t u v : ℂ) * X v * Y u) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      _ = (∑ x, ∑ y, (g t x y : ℂ) * X x * Y y) * ∑ u, ∑ v, (g' t u v : ℂ) * X v * Y u :=
          sum4_mul _ _
      _ = _ := by
          simp only [bil]
          congr 1
          exact Finset.sum_comm

/-- Over ℂ each product is two squares: z·z' = ((z + z')/2)² + (i(z − z')/2)². -/
theorem sosLE_of_prodLE {N M : ℕ} (h : ProdLE ℂ N M) : SOSLE ℂ N (M + M) := by
  obtain ⟨f, f', hf⟩ := h
  refine ⟨Fin.append (fun t i j => (1 / 2 : ℂ) * f t i j + (1 / 2 : ℂ) * f' t i j)
    (fun t i j => (Complex.I / 2) * f t i j + (-Complex.I / 2) * f' t i j), fun X Y => ?_⟩
  rw [Fin.sum_univ_add, hf X Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.append_left, Fin.append_right, bil_comb]
  linear_combination (-(bil (f t) X Y - bil (f' t) X Y) ^ 2 / 4) * Complex.I_sq

/-- **Hurwitz's problem over ℂ**, with Theorem B: for one constant c and every N ≥ 2,
(X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of at most 2·(2N)^{√2}·(2·log₂ N + 2)^{3c/2} squares of
complex bilinear forms. -/
theorem hurwitz_le : ∃ c : ℕ, ∀ N : ℕ, 2 ≤ N → ∃ M : ℕ, SOSLE ℂ N M ∧
    (M : ℝ) ≤ 2 * ((2 * N : ℝ) ^ Real.sqrt 2 * (2 * Real.logb 2 N + 2) ^ (3 * c / 2 : ℝ)) := by
  obtain ⟨c, hc⟩ := p_le
  refine ⟨c, fun N hN => ?_⟩
  obtain ⟨M, hP, hM⟩ := hc N hN
  refine ⟨M + M, sosLE_of_prodLE (prodLE_of_PLE hP), ?_⟩
  push_cast
  linarith

/-- **Hurwitz's problem over ℂ is at most n^{√2 + o(1)}**: for every ε > 0 and all large N, the
product of two sums of N squares is a sum of at most N^{√2 + ε} squares of complex bilinear
forms. Hrubeš (CCC 2024) has O(N^{1.62}). -/
theorem hurwitz_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ M : ℕ, SOSLE ℂ N M ∧ (M : ℝ) ≤ (N : ℝ) ^ (Real.sqrt 2 + ε) := by
  obtain ⟨N₁, hN₁⟩ := p_le_rpow (half_pos hε)
  refine ⟨max N₁ ⌈(2 : ℝ) ^ (2 / ε)⌉₊, fun N hN => ?_⟩
  obtain ⟨M, hP, hM⟩ := hN₁ N (le_of_max_le_left hN)
  refine ⟨M + M, sosLE_of_prodLE (prodLE_of_PLE hP), ?_⟩
  have hN2 : (2 : ℝ) ^ (2 / ε) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN2
  -- N^{ε/2} ≥ 2 once N ≥ 2^{2/ε}.
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by norm_num), show 2 / ε * (ε / 2) = (1 : ℝ) by field_simp,
            Real.rpow_one]
      _ ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hN2 (by positivity)
  calc ((M + M : ℕ) : ℝ) = 2 * M := by push_cast; ring
    _ ≤ 2 * (N : ℝ) ^ (Real.sqrt 2 + ε / 2) := by linarith
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (Real.sqrt 2 + ε / 2) := by
        gcongr
    _ = (N : ℝ) ^ (Real.sqrt 2 + ε) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring

end TheoremB
