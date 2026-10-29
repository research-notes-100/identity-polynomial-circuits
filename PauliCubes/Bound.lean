/-
The cost of a normal monomial: at least one of its two leading exponent vectors (chambers A and B) has
cube-cover cost at most `1.727899`.

Write `λ = deg`, `t = a / λ` and `t₀ = 0.0407474`. Two explicit pair distributions bound `cubeCost`
linearly (`cubeCost_le`):
* chamber A, `t ≥ t₀`: mass `1/3` on each of `{0,1}, {0,2}, {0,3}` (marginals `(1, 1/3, 1/3, 1/3)`) gives
  `cubeCost ≤ 1 + (x₁ + x₂ + x₃) log₂ 3 ≤ 1 + (1/2 − t₀) log₂ 3`;
* chamber B, `t ≤ t₀`: the distribution whose marginals are twice `B(t₀) = ((1+7t₀)/3, (1−5t₀)/3,
  (1−5t₀)/3, t₀)` gives a bound that is affine and nondecreasing in `t`, and equals the entropy of
  `B(t₀)` at `t = t₀`.
The logarithms are bounded with the Taylor series of `log (1 − x)` (`Real.abs_log_sub_add_sum_range_le`).
-/
import PauliCubes.Cost
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset

namespace PauliCubes

/-! ## Numerical bounds on logarithms -/

theorem log_one_sub_bounds {x : ℝ} (h : |x| < 1) (n : ℕ) :
    -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - |x| ^ (n + 1) / (1 - |x|) ≤ Real.log (1 - x) ∧
      Real.log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + |x| ^ (n + 1) / (1 - |x|) := by
  have := abs_le.mp (Real.abs_log_sub_add_sum_range_le h n)
  constructor <;> linarith [this.1, this.2]

/-- `m₀ = 2 (1 + 7 t₀) / 3`. -/
theorem log_m0_bounds : (-0.1545260175 : ℝ) ≤ Real.log (2142053 / 2500000) ∧
    Real.log (2142053 / 2500000) ≤ -0.1545260162 := by
  have h := log_one_sub_bounds (x := 357947 / 2500000)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  rw [abs_of_pos (show (0 : ℝ) < 357947 / 2500000 by norm_num),
    show (1 : ℝ) - 357947 / 2500000 = 2142053 / 2500000 by norm_num] at h
  set ℓ := Real.log (2142053 / 2500000)
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `m₁ = 2 (1 − 5 t₀) / 3`. -/
theorem log_m1_bounds : (-0.6332908543 : ℝ) ≤ Real.log (265421 / 500000) ∧
    Real.log (265421 / 500000) ≤ -0.6332908532 := by
  have h := log_one_sub_bounds (x := -15421 / 250000)
    (by rw [abs_of_neg (by norm_num)]; norm_num) 7
  rw [abs_of_neg (show (-15421 / 250000 : ℝ) < 0 by norm_num),
    show (1 : ℝ) - -15421 / 250000 = 265421 / 250000 by norm_num] at h
  have e : Real.log (265421 / 500000) = Real.log (265421 / 250000) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set ℓ := Real.log (265421 / 250000)
  norm_num [Finset.sum_range_succ] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

/-- `m₃ = 2 t₀`. -/
theorem log_m3_bounds : (-2.5072160662 : ℝ) ≤ Real.log (203737 / 2500000) ∧
    Real.log (203737 / 2500000) ≤ -2.5072160626 := by
  have h := log_one_sub_bounds (x := -47487 / 156250)
    (by rw [abs_of_neg (by norm_num)]; norm_num) 17
  rw [abs_of_neg (show (-47487 / 156250 : ℝ) < 0 by norm_num),
    show (1 : ℝ) - -47487 / 156250 = 203737 / 156250 by norm_num] at h
  have e16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have e : Real.log (203737 / 2500000) = Real.log (203737 / 156250) - 4 * Real.log 2 := by
    rw [← e16, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e]
  set ℓ := Real.log (203737 / 156250)
  norm_num [Finset.sum_range_succ] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

/-! ## Pair distributions given by tables -/

/-- The pair distribution reading `μ {i, j} = M i j` (`i < j`) off a table. -/
def tab (M : Fin 4 → Fin 4 → ℝ) : Pair → ℝ := fun p => M p.1.1 p.1.2

theorem forall_pair {P : Pair → Prop} (h01 : P p01) (h02 : P p02) (h03 : P p03) (h12 : P p12)
    (h13 : P p13) (h23 : P p23) : ∀ p, P p := by
  intro p
  have hp := Finset.mem_univ p
  rw [univ_pair] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Chamber A: mass `1/3` on each pair containing letter 0. -/
noncomputable def μA : Pair → ℝ :=
  tab ![![0, 1 / 3, 1 / 3, 1 / 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

theorem μA_marg0 : marg μA 0 = 1 := by
  rw [marg_zero]; simp [μA, tab, p01, p02, p03]; norm_num

theorem μA_marg1 : marg μA 1 = 1 / 3 := by
  rw [marg_one]; simp [μA, tab, p01, p12, p13]

theorem μA_marg2 : marg μA 2 = 1 / 3 := by
  rw [marg_two]; simp [μA, tab, p02, p12, p23]

theorem μA_marg3 : marg μA 3 = 1 / 3 := by
  rw [marg_three]; simp [μA, tab, p03, p13, p23]

theorem μA_mem : μA ∈ PairDist := by
  refine ⟨forall_pair (by simp [μA, tab, p01]) (by simp [μA, tab, p02]) (by simp [μA, tab, p03])
    (by simp [μA, tab, p12]) (by simp [μA, tab, p13]) (by simp [μA, tab, p23]), ?_, fun c => ?_⟩
  · rw [sum_pair]; simp [μA, tab, p01, p02, p03, p12, p13, p23]; norm_num
  · fin_cases c
    · simp [μA_marg0]
    · simp [μA_marg1]
    · simp [μA_marg2]
    · simp [μA_marg3]

/-- Chamber B: `μ{0,1} = μ{0,2} = (1+4t₀)/3`, `μ{1,2} = (1−14t₀)/3`, `μ{0,3} = 2t₀`. -/
noncomputable def μB : Pair → ℝ :=
  tab ![![0, 484579 / 1250000, 484579 / 1250000, 203737 / 2500000], ![0, 0, 357947 / 2500000, 0],
    ![0, 0, 0, 0], ![0, 0, 0, 0]]

theorem μB_marg0 : marg μB 0 = 2142053 / 2500000 := by
  rw [marg_zero]; simp [μB, tab, p01, p02, p03]; norm_num

theorem μB_marg1 : marg μB 1 = 265421 / 500000 := by
  rw [marg_one]; simp [μB, tab, p01, p12, p13]; norm_num

theorem μB_marg2 : marg μB 2 = 265421 / 500000 := by
  rw [marg_two]; simp [μB, tab, p02, p12, p23]; norm_num

theorem μB_marg3 : marg μB 3 = 203737 / 2500000 := by
  rw [marg_three]; simp [μB, tab, p03, p13, p23]

theorem μB_mem : μB ∈ PairDist := by
  refine ⟨forall_pair (by simp [μB, tab, p01]; norm_num) (by simp [μB, tab, p02]; norm_num)
    (by simp [μB, tab, p03]; norm_num) (by simp [μB, tab, p12]; norm_num)
    (by simp [μB, tab, p13]) (by simp [μB, tab, p23]), ?_, fun c => ?_⟩
  · rw [sum_pair]; simp [μB, tab, p01, p02, p03, p12, p13, p23]; norm_num
  · fin_cases c
    · simp [μB_marg0]
    · simp [μB_marg1]
    · simp [μB_marg2]
    · simp [μB_marg3]

/-! ## The two chambers -/

theorem normPt_nonneg (n : Fin 4 → ℕ) (d : ℕ) (a : Fin 4) : 0 ≤ normPt n d a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem scaled_bound {d K : ℝ} (hd : 0 < d) (X W : Fin 4 → ℝ) (h : ∑ c, X c * W c ≤ (K - 1) * d) :
    1 + ∑ c, X c / d * W c ≤ K := by
  have e : ∑ c, X c / d * W c = (∑ c, X c * W c) / d := by
    rw [sum_div]; exact sum_congr rfl fun c _ => by ring
  rw [e]
  have := (div_le_iff₀ hd).mpr h
  linarith

theorem normal_vertex_cost (m : NormalMono) (hm : 0 < m.deg) :
    min (cubeCost (normPt m.A m.deg)) (cubeCost (normPt m.B m.deg)) ≤ 1727899 / 1000000 := by
  have hd : (0 : ℝ) < m.deg := by exact_mod_cast hm
  have hdeg : (m.deg : ℝ) = m.u + 2 * m.v + 4 * m.w + 6 * m.b + 8 * m.a := by
    simp [NormalMono.deg]
  have hu : (0 : ℝ) ≤ m.u := Nat.cast_nonneg _
  have hv : (0 : ℝ) ≤ m.v := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ m.w := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ m.b := Nat.cast_nonneg _
  have ha : (0 : ℝ) ≤ m.a := Nat.cast_nonneg _
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hL : 0 < Real.log 2 := by linarith
  by_cases ht : (m.a : ℝ) ≤ 407474 / 10000000 * m.deg
  · -- chamber B
    refine (min_le_right _ _).trans ?_
    refine (cubeCost_le μB_mem (normPt_nonneg _ _)).trans ?_
    refine scaled_bound hd (fun c => (m.B c : ℝ)) (fun c => Real.logb 2 (1 / marg μB c)) ?_
    simp only [Fin.sum_univ_four, μB_marg0, μB_marg1, μB_marg2, μB_marg3]
    have e0 : (m.B 0 : ℝ) = m.u + m.v + 2 * m.w + 2 * m.b + 5 * m.a := by simp [NormalMono.B]
    have e1 : (m.B 1 : ℝ) = m.v + m.w + 2 * m.b + m.a := by simp [NormalMono.B]
    have e2 : (m.B 2 : ℝ) = m.w + 2 * m.b + m.a := by simp [NormalMono.B]
    have e3 : (m.B 3 : ℝ) = m.a := by simp [NormalMono.B]
    rw [e0, e1, e2, e3]
    have hW : ∀ y : ℝ, Real.logb 2 (1 / y) = -Real.log y / Real.log 2 := fun y => by
      rw [Real.logb, one_div, Real.log_inv]
    rw [hW, hW, hW]
    obtain ⟨h0lo, h0hi⟩ := log_m0_bounds
    obtain ⟨h1lo, h1hi⟩ := log_m1_bounds
    obtain ⟨h3lo, h3hi⟩ := log_m3_bounds
    set ℓ0 := Real.log (2142053 / 2500000)
    set ℓ1 := Real.log (265421 / 500000)
    set ℓ3 := Real.log (203737 / 2500000)
    set L := Real.log 2
    have F1 : -ℓ0 / L ≤ -ℓ1 / L := div_le_div_of_nonneg_right (by linarith) hL.le
    have F2 : 0 ≤ 7 * (-ℓ0 / L) - 10 * (-ℓ1 / L) + 3 * (-ℓ3 / L) := by
      have e : 7 * (-ℓ0 / L) - 10 * (-ℓ1 / L) + 3 * (-ℓ3 / L) = (-7 * ℓ0 + 10 * ℓ1 - 3 * ℓ3) / L := by
        ring
      rw [e]
      exact div_nonneg (by linarith) hL.le
    have F3 : 2142053 / 5000000 * (-ℓ0 / L) + 265421 / 500000 * (-ℓ1 / L) +
        203737 / 5000000 * (-ℓ3 / L) ≤ 1727899 / 1000000 - 1 := by
      have e : 2142053 / 5000000 * (-ℓ0 / L) + 265421 / 500000 * (-ℓ1 / L) +
          203737 / 5000000 * (-ℓ3 / L) =
          (2142053 / 5000000 * (-ℓ0) + 265421 / 500000 * (-ℓ1) + 203737 / 5000000 * (-ℓ3)) / L := by
        ring
      rw [e, div_le_iff₀ hL]
      linarith
    set W0 := -ℓ0 / L
    set W1 := -ℓ1 / L
    set W3 := -ℓ3 / L
    rw [hdeg] at ht ⊢
    nlinarith [mul_le_mul_of_nonneg_left F3
        (show (0 : ℝ) ≤ m.u + 2 * m.v + 4 * m.w + 6 * m.b + 8 * m.a by positivity),
      mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ) ≤ 2 * m.u + m.v + 2 * m.w by positivity)
        (show W0 - W1 ≤ 0 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 407474 / 10000000 * (m.u + 2 * m.v + 4 * m.w + 6 * m.b + 8 * m.a)
        - m.a by linarith) F2]
  · -- chamber A
    rw [not_le] at ht
    refine (min_le_left _ _).trans ?_
    refine (cubeCost_le μA_mem (normPt_nonneg _ _)).trans ?_
    refine scaled_bound hd (fun c => (m.A c : ℝ)) (fun c => Real.logb 2 (1 / marg μA c)) ?_
    simp only [Fin.sum_univ_four, μA_marg0, μA_marg1, μA_marg2, μA_marg3]
    have e0 : (m.A 0 : ℝ) = m.u + m.v + 2 * m.w + 3 * m.b + 5 * m.a := by simp [NormalMono.A]
    have e1 : (m.A 1 : ℝ) = m.v + m.w + m.b + m.a := by simp [NormalMono.A]
    have e2 : (m.A 2 : ℝ) = m.w + m.b + m.a := by simp [NormalMono.A]
    have e3 : (m.A 3 : ℝ) = m.b + m.a := by simp [NormalMono.A]
    rw [e0, e1, e2, e3]
    rw [div_one, Real.logb_one, one_div_one_div]
    have h3hi := Real.log_three_lt_d9
    have hL3 : 0 ≤ Real.logb 2 3 := Real.logb_nonneg one_lt_two (by norm_num)
    have FA : (1 / 2 - 407474 / 10000000) * Real.logb 2 3 ≤ 1727899 / 1000000 - 1 := by
      rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hL]
      linarith
    rw [hdeg] at ht ⊢
    nlinarith [mul_le_mul_of_nonneg_left FA
        (show (0 : ℝ) ≤ m.u + 2 * m.v + 4 * m.w + 6 * m.b + 8 * m.a by positivity),
      mul_le_mul_of_nonneg_right
        (show (m.v + m.w + m.b + m.a : ℝ) + (m.w + m.b + m.a) + (m.b + m.a) ≤
          (1 / 2 - 407474 / 10000000) * (m.u + 2 * m.v + 4 * m.w + 6 * m.b + 8 * m.a) by linarith)
        hL3]

end PauliCubes
