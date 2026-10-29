/-
Basic properties of the cube-cover cost `cubeCost`: the marginals of a pair distribution are at most 1,
`cubeCost` is bounded by any explicit pair distribution, it is concave on the standard simplex,
invariant under letter permutations, and at least 1 on the simplex.
-/
import PauliCubes.Basic
import Mathlib.Analysis.Convex.Function

open Finset

namespace PauliCubes

/-! ## The six pairs -/

/-- The pair `{0, 1}`. -/
def p01 : Pair := ⟨(0, 1), by decide⟩
/-- The pair `{0, 2}`. -/
def p02 : Pair := ⟨(0, 2), by decide⟩
/-- The pair `{0, 3}`. -/
def p03 : Pair := ⟨(0, 3), by decide⟩
/-- The pair `{1, 2}`. -/
def p12 : Pair := ⟨(1, 2), by decide⟩
/-- The pair `{1, 3}`. -/
def p13 : Pair := ⟨(1, 3), by decide⟩
/-- The pair `{2, 3}`. -/
def p23 : Pair := ⟨(2, 3), by decide⟩

theorem univ_pair : (univ : Finset Pair) = {p01, p02, p03, p12, p13, p23} := by decide

theorem sum_pair {M : Type*} [AddCommMonoid M] (f : Pair → M) :
    ∑ p, f p = f p01 + f p02 + f p03 + f p12 + f p13 + f p23 := by
  rw [univ_pair, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

theorem marg_zero (μ : Pair → ℝ) : marg μ 0 = μ p01 + μ p02 + μ p03 := by
  simp [marg, sum_pair, p01, p02, p03, p12, p13, p23]

theorem marg_one (μ : Pair → ℝ) : marg μ 1 = μ p01 + μ p12 + μ p13 := by
  simp [marg, sum_pair, p01, p02, p03, p12, p13, p23]

theorem marg_two (μ : Pair → ℝ) : marg μ 2 = μ p02 + μ p12 + μ p23 := by
  simp [marg, sum_pair, p01, p02, p03, p12, p13, p23]

theorem marg_three (μ : Pair → ℝ) : marg μ 3 = μ p03 + μ p13 + μ p23 := by
  simp [marg, sum_pair, p01, p02, p03, p12, p13, p23]

/-! ## Marginals -/

theorem marg_le_one {μ : Pair → ℝ} (hμ : μ ∈ PairDist) (a : Fin 4) : marg μ a ≤ 1 := by
  rw [← hμ.2.1, marg]
  refine sum_le_sum fun p _ => ?_
  split_ifs
  · exact le_rfl
  · exact hμ.1 p

/-- The uniform distribution on the six pairs. -/
noncomputable def unifPair : Pair → ℝ := fun _ => 1 / 6

theorem unifPair_mem : unifPair ∈ PairDist := by
  refine ⟨fun _ => by norm_num [unifPair], ?_, ?_⟩
  · simp only [unifPair, sum_pair]; norm_num
  · intro a
    fin_cases a <;> simp [marg_zero, marg_one, marg_two, marg_three, unifPair] <;> norm_num

instance : Nonempty PairDist := ⟨⟨unifPair, unifPair_mem⟩⟩

/-- Each weight `log₂ (1 / marg μ a)` is nonnegative. -/
theorem logb_one_div_marg_nonneg {μ : Pair → ℝ} (hμ : μ ∈ PairDist) (a : Fin 4) :
    0 ≤ Real.logb 2 (1 / marg μ a) :=
  Real.logb_nonneg one_lt_two ((one_le_div (hμ.2.2 a)).mpr (marg_le_one hμ a))

/-- The objective inside the infimum defining `cubeCost` is nonnegative at a nonnegative point. -/
theorem costSum_nonneg {μ : Pair → ℝ} (hμ : μ ∈ PairDist) {x : Fin 4 → ℝ} (hx : ∀ a, 0 ≤ x a) :
    0 ≤ ∑ a, x a * Real.logb 2 (1 / marg μ a) :=
  sum_nonneg fun a _ => mul_nonneg (hx a) (logb_one_div_marg_nonneg hμ a)

theorem costSum_bddBelow {x : Fin 4 → ℝ} (hx : ∀ a, 0 ≤ x a) :
    BddBelow (Set.range fun μ : PairDist => ∑ a, x a * Real.logb 2 (1 / marg μ.1 a)) :=
  ⟨0, by rintro _ ⟨μ, rfl⟩; exact costSum_nonneg μ.2 hx⟩

/-! ## Bounds on `cubeCost` -/

theorem cubeCost_le {μ : Pair → ℝ} (hμ : μ ∈ PairDist) {x : Fin 4 → ℝ} (hx : ∀ a, 0 ≤ x a) :
    cubeCost x ≤ 1 + ∑ a, x a * Real.logb 2 (1 / marg μ a) := by
  unfold cubeCost
  gcongr
  exact ciInf_le (costSum_bddBelow hx) ⟨μ, hμ⟩

theorem one_le_cubeCost {x : Fin 4 → ℝ} (hx : x ∈ stdSimplex ℝ (Fin 4)) : 1 ≤ cubeCost x := by
  unfold cubeCost
  have : 0 ≤ ⨅ μ : PairDist, ∑ a, x a * Real.logb 2 (1 / marg μ.1 a) :=
    le_ciInf fun μ => costSum_nonneg μ.2 hx.1
  linarith

theorem cubeCost_concave : ConcaveOn ℝ (stdSimplex ℝ (Fin 4)) cubeCost := by
  refine ⟨convex_stdSimplex ℝ (Fin 4), fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, cubeCost]
  have key : a * (⨅ μ : PairDist, ∑ c, x c * Real.logb 2 (1 / marg μ.1 c)) +
      b * (⨅ μ : PairDist, ∑ c, y c * Real.logb 2 (1 / marg μ.1 c)) ≤
      ⨅ μ : PairDist, ∑ c, (a • x + b • y) c * Real.logb 2 (1 / marg μ.1 c) := by
    refine le_ciInf fun μ => ?_
    have h1 := ciInf_le (costSum_bddBelow hx.1) μ
    have h2 := ciInf_le (costSum_bddBelow hy.1) μ
    have e : ∑ c, (a • x + b • y) c * Real.logb 2 (1 / marg μ.1 c) =
        a * ∑ c, x c * Real.logb 2 (1 / marg μ.1 c) +
          b * ∑ c, y c * Real.logb 2 (1 / marg μ.1 c) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun c _ => by ring
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  linarith

/-! ## Permutation invariance -/

/-- The pair `{σ i, σ j}` as an increasing pair. -/
def pmap (σ : Equiv.Perm (Fin 4)) (p : Pair) : Pair :=
  if h : σ p.1.1 < σ p.1.2 then ⟨(σ p.1.1, σ p.1.2), h⟩
  else ⟨(σ p.1.2, σ p.1.1),
    lt_of_le_of_ne (not_lt.mp h) fun e => p.2.ne (σ.injective e).symm⟩

theorem pmap_mem (σ : Equiv.Perm (Fin 4)) (p : Pair) (c : Fin 4) :
    ((pmap σ p).1.1 = c ∨ (pmap σ p).1.2 = c) ↔ (σ p.1.1 = c ∨ σ p.1.2 = c) := by
  unfold pmap
  split_ifs
  · exact Iff.rfl
  · exact or_comm

theorem pmap_inv_pmap (σ : Equiv.Perm (Fin 4)) (p : Pair) : pmap σ⁻¹ (pmap σ p) = p := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  unfold pmap
  by_cases h : σ i < σ j
  · simp [h, hij]
  · simp [h, not_lt.mpr hij.le]

/-- The permutation of pairs induced by a permutation of letters. -/
def pequiv (σ : Equiv.Perm (Fin 4)) : Pair ≃ Pair where
  toFun := pmap σ
  invFun := pmap σ⁻¹
  left_inv := pmap_inv_pmap σ
  right_inv p := by simpa using pmap_inv_pmap σ⁻¹ p

theorem marg_comp_pmap (σ : Equiv.Perm (Fin 4)) (μ : Pair → ℝ) (c : Fin 4) :
    marg (μ ∘ pmap σ) c = marg μ (σ c) := by
  have h := (pequiv σ).sum_comp (fun q : Pair => if q.1.1 = σ c ∨ q.1.2 = σ c then μ q else 0)
  beta_reduce at h
  unfold marg
  rw [← h]
  refine sum_congr rfl fun p _ => ?_
  simp only [Function.comp_apply, show pequiv σ p = pmap σ p from rfl, pmap_mem,
    σ.apply_eq_iff_eq]

theorem comp_pmap_mem (σ : Equiv.Perm (Fin 4)) {μ : Pair → ℝ} (hμ : μ ∈ PairDist) :
    μ ∘ pmap σ ∈ PairDist := by
  refine ⟨fun p => hμ.1 _, ?_, fun c => ?_⟩
  · exact ((pequiv σ).sum_comp μ).trans hμ.2.1
  · rw [marg_comp_pmap]
    exact hμ.2.2 _

theorem cubeCost_comp_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → ℝ) :
    cubeCost (x ∘ σ) = cubeCost x := by
  unfold cubeCost
  congr 1
  show sInf (Set.range _) = sInf (Set.range _)
  congr 1
  ext r
  simp only [Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ ∘ pmap σ⁻¹, comp_pmap_mem σ⁻¹ hμ, ?_⟩
    rw [← Equiv.sum_comp σ (fun c => x c * Real.logb 2 (1 / marg (μ ∘ pmap σ⁻¹) c))]
    simp only [marg_comp_pmap, Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨μ ∘ pmap σ, comp_pmap_mem σ hμ, ?_⟩
    simp only [marg_comp_pmap, Function.comp_apply]
    exact Equiv.sum_comp σ (fun c => x c * Real.logb 2 (1 / marg μ c))

end PauliCubes
