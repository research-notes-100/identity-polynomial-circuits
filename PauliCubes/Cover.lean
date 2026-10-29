/-
Covering the words of one type by cubes (the probabilistic method, as an averaging argument).

Pick a pair distribution `μ` nearly attaining `cubeCost` at the type's frequency vector. Drawing one pair
per position independently from `μ` gives a random cube; a fixed word `ν` lies in it with probability
`p(ν) = ∏ᵢ marg μ (νᵢ) ≥ 2^(-n (t - 1 + δ))`. Averaging over `k` independent cubes, the expected number of
uncovered words of the type is `∑_ν (1 - p(ν))^k ≤ 4^n e^(-(2n+2)) < 1`, so some `k`-tuple covers them
all. Expectations are finite weighted sums with weights `∏ μ`.
-/
import PauliCubes.Cost

open Finset

namespace PauliCubes

variable {n : ℕ}

/-! ## Cubes from pair assignments -/

/-- The smaller letters of a pair assignment. -/
def loL (π : Fin n → Pair) : Fin n → Fin 4 := fun i => (π i).1.1

/-- The larger letters of a pair assignment. -/
def hiL (π : Fin n → Pair) : Fin n → Fin 4 := fun i => (π i).1.2

/-- The word `ν` lies in the cube of the pair assignment `π`. -/
def Covers (π : Fin n → Pair) (ν : Fin n → Fin 4) : Prop := ∀ i, (π i).1.1 = ν i ∨ (π i).1.2 = ν i

instance (π : Fin n → Pair) (ν : Fin n → Fin 4) : Decidable (Covers π ν) := by
  unfold Covers; infer_instance

theorem mem_cube_loL_hiL (π : Fin n → Pair) (ν : Fin n → Fin 4) :
    ν ∈ cube (loL π) (hiL π) ↔ Covers π ν := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton, loL, hiL, Covers]
  exact forall_congr' fun i => by rw [eq_comm, @eq_comm _ (ν i)]

theorem isCube_loL_hiL (π : Fin n → Pair) : IsCube (cube (loL π) (hiL π)) :=
  ⟨loL π, hiL π, fun i => (π i).2.ne, rfl⟩

/-! ## Weighted sums over pair assignments -/

section Sums

variable {μ : Pair → ℝ}

theorem sum_prod_weight (hμ : μ ∈ PairDist) (m : ℕ) :
    ∑ π : Fin m → Pair, ∏ i, μ (π i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin m) (p : Pair) => μ p), hμ.2.1]
  simp

/-- Weighted probability that the random cube contains `ν`. -/
theorem sum_weight_covers (ν : Fin n → Fin 4) :
    ∑ π : Fin n → Pair, (if Covers π ν then ∏ i, μ (π i) else 0) = ∏ i, marg μ (ν i) := by
  have h := Fintype.prod_sum
    (fun (i : Fin n) (p : Pair) => if p.1.1 = ν i ∨ p.1.2 = ν i then μ p else 0)
  simp only [marg]
  rw [h]
  refine sum_congr rfl fun π _ => ?_
  rw [prod_ite_zero]
  simp [Covers]

/-- The weight of `π` if its cube misses `ν`, else `0`. -/
noncomputable def missW (μ : Pair → ℝ) (ν : Fin n → Fin 4) (π : Fin n → Pair) : ℝ :=
  if Covers π ν then 0 else ∏ i, μ (π i)

theorem missW_nonneg (hμ : μ ∈ PairDist) (ν : Fin n → Fin 4) (π : Fin n → Pair) :
    0 ≤ missW μ ν π := by
  unfold missW
  split_ifs
  · exact le_rfl
  · exact prod_nonneg fun i _ => hμ.1 _

theorem sum_missW (hμ : μ ∈ PairDist) (ν : Fin n → Fin 4) :
    ∑ π, missW μ ν π = 1 - ∏ i, marg μ (ν i) := by
  have e : ∀ π, missW μ ν π = ∏ i, μ (π i) - (if Covers π ν then ∏ i, μ (π i) else 0) := by
    intro π; unfold missW; split_ifs <;> ring
  simp only [e, sum_sub_distrib, sum_prod_weight hμ, sum_weight_covers]

theorem sum_tuple_missW (hμ : μ ∈ PairDist) (ν : Fin n → Fin 4) (k : ℕ) :
    ∑ ω : Fin k → Fin n → Pair, ∏ j, missW μ ν (ω j) = (1 - ∏ i, marg μ (ν i)) ^ k := by
  rw [← Fintype.prod_sum (fun (_ : Fin k) (π : Fin n → Pair) => missW μ ν π), sum_missW hμ]
  simp

/-- **Averaging.** If the expected number of words of `S` missed by `k` independent random cubes is
below `1`, some `k` cubes cover `S`. -/
theorem exists_cover (hμ : μ ∈ PairDist) (S : Finset (Fin n → Fin 4)) (k : ℕ)
    (hS : ∑ ν ∈ S, (1 - ∏ i, marg μ (ν i)) ^ k < 1) :
    ∃ ω : Fin k → Fin n → Pair, ∀ ν ∈ S, ∃ j, Covers (ω j) ν := by
  by_contra hcon
  push Not at hcon
  have h1 : ∀ ω : Fin k → Fin n → Pair,
      ∏ j, ∏ i, μ (ω j i) ≤ ∑ ν ∈ S, ∏ j, missW μ ν (ω j) := by
    intro ω
    obtain ⟨ν, hν, hnc⟩ := hcon ω
    have e : ∏ j, missW μ ν (ω j) = ∏ j, ∏ i, μ (ω j i) :=
      prod_congr rfl fun j _ => by simp [missW, hnc j]
    rw [← e]
    exact single_le_sum (f := fun ν => ∏ j, missW μ ν (ω j))
      (fun ν _ => prod_nonneg fun j _ => missW_nonneg hμ ν (ω j)) hν
  have h2 : ∑ ω : Fin k → Fin n → Pair, ∏ j, ∏ i, μ (ω j i) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin k) (π : Fin n → Pair) => ∏ i, μ (π i))]
    simp [sum_prod_weight hμ]
  have h3 : ∑ ω : Fin k → Fin n → Pair, ∑ ν ∈ S, ∏ j, missW μ ν (ω j) =
      ∑ ν ∈ S, (1 - ∏ i, marg μ (ν i)) ^ k := by
    rw [sum_comm]
    exact sum_congr rfl fun ν _ => sum_tuple_missW hμ ν k
  have h4 := sum_le_sum fun ω (_ : ω ∈ (univ : Finset (Fin k → Fin n → Pair))) => h1 ω
  linarith

end Sums

/-! ## The probability of a word of a given type -/

theorem prod_marg_eq_of_wordType {μ : Pair → ℝ} (ν : Fin n → Fin 4) :
    ∏ i, marg μ (ν i) = ∏ a, marg μ a ^ wordType ν a := by
  rw [← prod_fiberwise univ ν (fun i => marg μ (ν i))]
  refine prod_congr rfl fun a _ => ?_
  rw [prod_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], prod_const]
  rfl

/-- The words of type `τ` (empty unless `τ` sums to `n`) are covered by
`⌈(2n + 2) 2^(n (t − 1 + δ))⌉` cubes whenever the type's cost is at most `t`. -/
theorem cover_type {n : ℕ} (τ : Fin 4 → ℕ) (hn : 0 < n) {t δ : ℝ}
    (ht : cubeCost (normPt τ n) ≤ t) (hδ : 0 < δ) :
    CubeCovered (Finset.univ.filter fun ν : Fin n → Fin 4 => wordType ν = τ)
      (⌈(2 * (n : ℝ) + 2) * (2 : ℝ) ^ ((n : ℝ) * (t - 1 + δ))⌉₊) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- a pair distribution within `δ` of the infimum
  have hlt : ⨅ μ : PairDist, ∑ a, normPt τ n a * Real.logb 2 (1 / marg μ.1 a) < t - 1 + δ := by
    have : cubeCost (normPt τ n) =
        1 + ⨅ μ : PairDist, ∑ a, normPt τ n a * Real.logb 2 (1 / marg μ.1 a) := rfl
    linarith
  obtain ⟨⟨μ, hμ⟩, hμlt⟩ := exists_lt_of_ciInf_lt hlt
  have hq : ∀ a, 0 < marg μ a := hμ.2.2
  have e : ∑ a, normPt τ n a * Real.logb 2 (1 / marg μ a) =
      -(∑ a, (τ a : ℝ) * Real.log (marg μ a)) / (n * Real.log 2) := by
    rw [← sum_neg_distrib, sum_div]
    refine sum_congr rfl fun a _ => ?_
    simp only [normPt, Real.logb, one_div, Real.log_inv]
    ring
  simp only at hμlt
  rw [e, div_lt_iff₀ (by positivity)] at hμlt
  -- every word of type `τ` lies in the random cube with probability at least `P`
  set k := ⌈(2 * (n : ℝ) + 2) * (2 : ℝ) ^ ((n : ℝ) * (t - 1 + δ))⌉₊ with hkdef
  set S := Finset.univ.filter fun ν : Fin n → Fin 4 => wordType ν = τ with hSdef
  have hP : (0 : ℝ) < 2 ^ (-((n : ℝ) * (t - 1 + δ))) := by positivity
  have hp : ∀ ν : Fin n → Fin 4, wordType ν = τ →
      (2 : ℝ) ^ (-((n : ℝ) * (t - 1 + δ))) ≤ ∏ i, marg μ (ν i) := by
    intro ν hν
    rw [prod_marg_eq_of_wordType, hν]
    have hpos : 0 < ∏ a, marg μ a ^ τ a := prod_pos fun a _ => pow_pos (hq a) _
    rw [← Real.log_le_log_iff hP hpos, Real.log_rpow two_pos,
      Real.log_prod (fun a _ => (pow_pos (hq a) _).ne')]
    simp only [Real.log_pow]
    have : -((n : ℝ) * (t - 1 + δ)) * Real.log 2 = -((t - 1 + δ) * (n * Real.log 2)) := by ring
    rw [this]
    linarith
  -- the expected number of uncovered words is below one
  have hk : (2 * (n : ℝ) + 2) * 2 ^ ((n : ℝ) * (t - 1 + δ)) ≤ k := Nat.le_ceil _
  have hPE : (2 : ℝ) ^ (-((n : ℝ) * (t - 1 + δ))) * 2 ^ ((n : ℝ) * (t - 1 + δ)) = 1 := by
    rw [← Real.rpow_add two_pos]; simp
  have hkP : 2 * (n : ℝ) + 2 ≤ k * 2 ^ (-((n : ℝ) * (t - 1 + δ))) := by
    calc 2 * (n : ℝ) + 2
        = (2 * (n : ℝ) + 2) * 2 ^ ((n : ℝ) * (t - 1 + δ)) * 2 ^ (-((n : ℝ) * (t - 1 + δ))) := by
          rw [mul_assoc, mul_comm (2 ^ ((n : ℝ) * (t - 1 + δ))), hPE, mul_one]
      _ ≤ k * 2 ^ (-((n : ℝ) * (t - 1 + δ))) := mul_le_mul_of_nonneg_right hk hP.le
  have hterm : ∀ ν ∈ S, (1 - ∏ i, marg μ (ν i)) ^ k ≤ Real.exp (-(2 * n + 2)) := by
    intro ν hν
    have hpν := hp ν (mem_filter.mp hν).2
    have hle1 : ∏ i, marg μ (ν i) ≤ 1 :=
      prod_le_one₀ (fun i _ => (hq _).le) (fun i _ => marg_le_one hμ _)
    have hkp : (k : ℝ) * 2 ^ (-((n : ℝ) * (t - 1 + δ))) ≤ k * ∏ i, marg μ (ν i) :=
      mul_le_mul_of_nonneg_left hpν (Nat.cast_nonneg _)
    calc (1 - ∏ i, marg μ (ν i)) ^ k ≤ Real.exp (-∏ i, marg μ (ν i)) ^ k :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) k
      _ = Real.exp (-(k * ∏ i, marg μ (ν i))) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(2 * n + 2)) := Real.exp_le_exp.mpr (by linarith)
  have hcard : (S.card : ℝ) ≤ 4 ^ n := by
    have : S.card ≤ 4 ^ n := (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hexp : (4 : ℝ) ^ n * Real.exp (-(2 * n + 2)) < 1 := by
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 := Real.add_one_le_exp 1
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have e2 : Real.exp (2 * n + 2) = Real.exp 2 ^ (n + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [Real.exp_neg, e2, ← div_eq_mul_inv, div_lt_one (by positivity)]
    calc (4 : ℝ) ^ n < 4 ^ (n + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      _ ≤ Real.exp 2 ^ (n + 1) := pow_le_pow_left₀ (by norm_num) h4 _
  have hbound : ∑ ν ∈ S, (1 - ∏ i, marg μ (ν i)) ^ k < 1 :=
    calc ∑ ν ∈ S, (1 - ∏ i, marg μ (ν i)) ^ k ≤ ∑ _ν ∈ S, Real.exp (-(2 * n + 2)) :=
          sum_le_sum hterm
      _ = S.card * Real.exp (-(2 * n + 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 4 ^ n * Real.exp (-(2 * n + 2)) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ < 1 := hexp
  -- some `k` cubes cover every word of type `τ`
  obtain ⟨ω, hω⟩ := exists_cover hμ S k hbound
  refine ⟨univ.image fun j => cube (loL (ω j)) (hiL (ω j)), ?_, ?_, ?_⟩
  · exact card_image_le.trans (by simp)
  · intro Q hQ
    obtain ⟨j, -, rfl⟩ := mem_image.mp hQ
    exact isCube_loL_hiL _
  · intro ν hν
    obtain ⟨j, hj⟩ := hω ν hν
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ (mem_univ j), (mem_cube_loL_hiL _ _).mpr hj⟩

end PauliCubes
