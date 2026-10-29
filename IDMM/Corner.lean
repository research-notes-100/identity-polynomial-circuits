import Mathlib

/-!
# Corner feasibility for the class-constant SOS system

`corner_feasible n`: for every length `n`, the class-constant linear system
`∑_{a,b} W a b · (-1)^((a+b)(c+d)) · K_a(c) · K_b(d) = [c = d = 0]` (one equation for each
`c, d ≤ n` with `qpar c d = 0`) has a solution `W` supported on corner classes.

Proof outline.
* Duality (`Submodule.exists_dual_map_eq_bot_of_notMem`): if no corner-supported solution
  exists, there is `y` on admissible `(c, d)` with `y 0 0 ≠ 0` annihilating every corner column.
* `kraw_homog`: `∑_a K_a(c) s^a t^(n-a) = (t - s)^c (t + s)^(n-c)` in any commutative ring.
* `dual_vanish`: pair the column relations with `P a · P b`, where
  `P a = (1-X)^a (1+X)^(n-a) + (1+X)^a (1-X)^(n-a)` (the four reflections `a ↦ n - a`,
  `b ↦ n - b`). Non-corner columns make every term divisible by `(1 - X^2)^m`, `m = n/2 + 1`;
  `kraw_homog` evaluates the pairing to `4 · 2^(2n) · G`, `G = ∑_{c,d even} y c d X^(c+d)`.
  `qpar = 0` forces `4 ∣ c + d` on the even part, so `G(iX) = G(X)` and `(1 + X^2)^m ∣ G` too.
  Coprimality gives `(1 - X^4)^m ∣ G`, and `deg G ≤ 2n < 4m` forces `G = 0`, so `y 0 0 = 0`.
-/

namespace IDMM

open Polynomial Finset

/-- Binary Krawtchouk number K_a(c) for length n. -/
noncomputable def kraw (n a c : ℕ) : ℤ := ((1 - Polynomial.X) ^ c * (1 + Polynomial.X) ^ (n - c) : Polynomial ℤ).coeff a
def qpar (c d : ℕ) : ℕ := (d + (c + d).choose 2) % 2
def InCorner (n a b : ℕ) : Prop := min a (n - a) + min b (n - b) ≤ n / 2

namespace Corner

section Homog

variable {R : Type*} [CommRing R]

/-- Degree-`N` homogenization of an integer polynomial, evaluated at `(s, t)`. -/
def homog (N : ℕ) (p : ℤ[X]) (s t : R) : R :=
  ∑ a ∈ range (N + 1), (p.coeff a : R) * s ^ a * t ^ (N - a)

lemma homog_add (N : ℕ) (p q : ℤ[X]) (s t : R) :
    homog N (p + q) s t = homog N p s t + homog N q s t := by
  simp only [homog, coeff_add, Int.cast_add, add_mul, sum_add_distrib]

lemma homog_sub (N : ℕ) (p q : ℤ[X]) (s t : R) :
    homog N (p - q) s t = homog N p s t - homog N q s t := by
  simp only [homog, coeff_sub, Int.cast_sub, sub_mul, sum_sub_distrib]

lemma homog_X_mul (N : ℕ) (p : ℤ[X]) (s t : R) :
    homog (N + 1) (X * p) s t = s * homog N p s t := by
  unfold homog
  rw [sum_range_succ', mul_sum]
  simp only [coeff_X_mul, coeff_X_mul_zero, Int.cast_zero, zero_mul, add_zero]
  refine sum_congr rfl fun a _ => ?_
  rw [Nat.add_sub_add_right, pow_succ]
  ring

lemma homog_succ (N : ℕ) (p : ℤ[X]) (s t : R) (hp : p.natDegree ≤ N) :
    homog (N + 1) p s t = t * homog N p s t := by
  unfold homog
  rw [sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero, zero_mul,
    zero_mul, add_zero, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha : a ≤ N := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [Nat.succ_sub ha, pow_succ]
  ring

lemma natDegree_kpoly (c k : ℕ) :
    ((1 - X : ℤ[X]) ^ c * (1 + X) ^ k).natDegree ≤ c + k := by
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · refine natDegree_pow_le.trans ?_
    have : (1 - X : ℤ[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  · refine natDegree_pow_le.trans ?_
    have : (1 + X : ℤ[X]).natDegree ≤ 1 := by compute_degree
    nlinarith

lemma homog_kpoly (c k : ℕ) (s t : R) :
    homog (c + k) ((1 - X : ℤ[X]) ^ c * (1 + X) ^ k) s t = (t - s) ^ c * (t + s) ^ k := by
  induction k with
  | zero =>
    induction c with
    | zero => simp [homog]
    | succ c ih =>
      have hdeg := natDegree_kpoly c 0
      simp only [pow_zero, mul_one, add_zero] at ih hdeg ⊢
      rw [pow_succ', sub_mul, one_mul, homog_sub, homog_succ _ _ _ _ hdeg, homog_X_mul, ih]
      ring
  | succ k ih =>
    have hdeg := natDegree_kpoly c k
    rw [← add_assoc, pow_succ', mul_left_comm, add_mul, one_mul, homog_add,
      homog_succ _ _ _ _ hdeg, homog_X_mul, ih]
    ring

/-- The homogenized Krawtchouk generating function. -/
lemma kraw_homog {n c : ℕ} (hc : c ≤ n) (s t : R) :
    ∑ a ∈ range (n + 1), (kraw n a c : R) * s ^ a * t ^ (n - a) =
      (t - s) ^ c * (t + s) ^ (n - c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  rw [Nat.add_sub_cancel_left, ← homog_kpoly]
  simp only [homog, kraw, Nat.add_sub_cancel_left]

end Homog

section Key

variable {K : Type*} [Field K]

/-- The reflection-symmetrized, sign-twisted Krawtchouk generating polynomial. -/
noncomputable def S (n c e : ℕ) : K[X] :=
  ∑ a ∈ range (n + 1), C ((-1 : K) ^ (a * e) * (kraw n a c : K)) *
    ((1 - X) ^ a * (1 + X) ^ (n - a) + (1 + X) ^ a * (1 - X) ^ (n - a))

lemma S_eq {n c : ℕ} (hc : c ≤ n) (e : ℕ) :
    S (K := K) n c e = ((1 + X) - (-1) ^ e * (1 - X)) ^ c * ((1 + X) + (-1) ^ e * (1 - X)) ^ (n - c) +
      ((1 - X) - (-1) ^ e * (1 + X)) ^ c * ((1 - X) + (-1) ^ e * (1 + X)) ^ (n - c) := by
  rw [← kraw_homog hc ((-1) ^ e * (1 - X)) (1 + X), ← kraw_homog hc ((-1) ^ e * (1 + X)) (1 - X),
    ← sum_add_distrib]
  unfold S
  refine sum_congr rfl fun a _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_intCast, mul_pow, ← pow_mul]
  ring

lemma S_even {n c e : ℕ} (hc : c ≤ n) (he : Even e) :
    S (K := K) n c e = ((2 * X) ^ c + (-(2 * X)) ^ c) * 2 ^ (n - c) := by
  rw [S_eq hc, he.neg_one_pow]
  have h1 : (1 + X : K[X]) - 1 * (1 - X) = 2 * X := by ring
  have h2 : (1 + X : K[X]) + 1 * (1 - X) = 2 := by ring
  have h3 : (1 - X : K[X]) - 1 * (1 + X) = -(2 * X) := by ring
  have h4 : (1 - X : K[X]) + 1 * (1 + X) = 2 := by ring
  rw [h1, h2, h3, h4]
  ring

lemma S_odd {n c e : ℕ} (hc : c ≤ n) (he : Odd e) :
    S (K := K) n c e = 2 ^ c * ((2 * X) ^ (n - c) + (-(2 * X)) ^ (n - c)) := by
  rw [S_eq hc, he.neg_one_pow]
  have h1 : (1 + X : K[X]) - -1 * (1 - X) = 2 := by ring
  have h2 : (1 + X : K[X]) + -1 * (1 - X) = 2 * X := by ring
  have h3 : (1 - X : K[X]) - -1 * (1 + X) = 2 := by ring
  have h4 : (1 - X : K[X]) + -1 * (1 + X) = -(2 * X) := by ring
  rw [h1, h2, h3, h4]
  ring

lemma Q_odd {k : ℕ} (hk : Odd k) : (2 * X : K[X]) ^ k + (-(2 * X)) ^ k = 0 := by
  rw [hk.neg_pow]; ring

lemma S_mul_S {n c d : ℕ} (hc : c ≤ n) (hd : d ≤ n) :
    S (K := K) n c (c + d) * S (K := K) n d (c + d) =
      if Even c ∧ Even d then 4 * 2 ^ (2 * n) * X ^ (c + d) else 0 := by
  have e1 : (2 : K[X]) ^ c * 2 ^ (n - c) = 2 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hc]
  have e2 : (2 : K[X]) ^ d * 2 ^ (n - d) = 2 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hd]
  rcases Nat.even_or_odd c with hc2 | hc2 <;> rcases Nat.even_or_odd d with hd2 | hd2
  · rw [S_even hc (hc2.add hd2), S_even hd (hc2.add hd2), ite_eq_left ⟨hc2, hd2⟩, hc2.neg_pow,
      hd2.neg_pow]
    linear_combination (4 * X ^ c * X ^ d * (2 ^ d * 2 ^ (n - d))) * e1 +
      (4 * X ^ c * X ^ d * 2 ^ n) * e2
  · rw [S_odd hc (hc2.add_odd hd2), ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr hd2) h.2)]
    rcases Nat.even_or_odd n with hn | hn
    · rw [S_odd hd (hc2.add_odd hd2), Q_odd (k := n - d) (Nat.odd_iff.mpr (by
        have := Nat.even_iff.mp hn; have := Nat.odd_iff.mp hd2; omega))]
      ring
    · rw [Q_odd (k := n - c) (Nat.odd_iff.mpr (by
        have := Nat.odd_iff.mp hn; have := Nat.even_iff.mp hc2; omega))]
      ring
  · rw [S_odd hc (hc2.add_even hd2), ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr hc2) h.1)]
    rcases Nat.even_or_odd n with hn | hn
    · rw [Q_odd (k := n - c) (Nat.odd_iff.mpr (by
        have := Nat.even_iff.mp hn; have := Nat.odd_iff.mp hc2; omega))]
      ring
    · rw [S_odd hd (hc2.add_even hd2), Q_odd (k := n - d) (Nat.odd_iff.mpr (by
        have := Nat.odd_iff.mp hn; have := Nat.even_iff.mp hd2; omega))]
      ring
  · rw [S_even hc (hc2.add_odd hd2), ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr hc2) h.1),
      Q_odd hc2]
    ring

lemma four_dvd_of_qpar {c d : ℕ} (hc : Even c) (hd : Even d) (hq : qpar c d = 0) :
    4 ∣ c + d := by
  obtain ⟨i, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := hd
  have hk : i + i + (j + j) = 2 * (i + j) := by ring
  have hch : (2 * (i + j)).choose 2 = (i + j) * (2 * (i + j) - 1) := by
    rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  unfold qpar at hq
  rw [hk, hch] at hq
  rcases Nat.even_or_odd (i + j) with ⟨l, hl⟩ | hodd
  · exact ⟨l, by omega⟩
  · exfalso
    have h1 : Odd (2 * (i + j) - 1) := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hodd; omega)
    have h2 := Nat.odd_iff.mp (hodd.mul h1)
    generalize (i + j) * (2 * (i + j) - 1) = z at hq h2
    omega

end Key

section Key2

variable {K : Type*} [Field K] [NeZero (2 : K)]

lemma P_dvd {n a α : ℕ} (h1 : α ≤ a) (h2 : α ≤ n - a) :
    ((1 - X : K[X]) * (1 + X)) ^ α ∣
      (1 - X) ^ a * (1 + X) ^ (n - a) + (1 + X) ^ a * (1 - X) ^ (n - a) := by
  rw [mul_pow]
  refine dvd_add (mul_dvd_mul (pow_dvd_pow _ h1) (pow_dvd_pow _ h2)) ?_
  rw [mul_comm ((1 - X : K[X]) ^ α)]
  exact mul_dvd_mul (pow_dvd_pow _ h1) (pow_dvd_pow _ h2)

/-- The dual certificate cannot exist: any `y` annihilating every corner column
(and supported on `qpar = 0`) has `y 0 0 = 0`. -/
theorem dual_vanish (i : K) (hi : i * i = -1) (n : ℕ) (y : ℕ → ℕ → K)
    (hq : ∀ c ≤ n, ∀ d ≤ n, y c d ≠ 0 → qpar c d = 0)
    (hcorner : ∀ a ≤ n, ∀ b ≤ n, InCorner n a b →
      ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
        y c d * ((-1 : K) ^ ((a + b) * (c + d)) * (kraw n a c : K) * (kraw n b d : K)) = 0) :
    y 0 0 = 0 := by
  classical
  set m := n / 2 + 1 with hm
  set P : ℕ → K[X] := fun a =>
    (1 - X) ^ a * (1 + X) ^ (n - a) + (1 + X) ^ a * (1 - X) ^ (n - a) with hP
  set coef : ℕ → ℕ → K := fun a b => ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
    y c d * ((-1 : K) ^ ((a + b) * (c + d)) * (kraw n a c : K) * (kraw n b d : K)) with hcoef
  set ybar : ℕ → ℕ → K := fun c d => if Even c ∧ Even d then y c d else 0 with hybar
  set G : K[X] := ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1), C (ybar c d) * X ^ (c + d) with hG
  set Ψ : K[X] := ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), C (coef a b) * (P a * P b) with hΨ
  -- Step A: Ψ is a nonzero multiple of G.
  have hA1 : ∀ a b, C (coef a b) * (P a * P b) =
      ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1), C (y c d) *
        ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
          (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) := by
    intro a b
    simp only [hcoef, map_sum, sum_mul]
    refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
    simp only [map_mul, map_pow]
    ring
  have hS : ∀ c d, C (y c d) * (S (K := K) n c (c + d) * S (K := K) n d (c + d)) =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), C (y c d) *
        ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
          (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) := by
    intro c d
    rw [S, S, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun a _ => by rw [mul_sum]
  have hA2 : Ψ = ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      C (y c d) * (S (K := K) n c (c + d) * S (K := K) n d (c + d)) := by
    calc Ψ = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
          ∑ d ∈ range (n + 1), C (y c d) *
            ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
              (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) := by
          rw [hΨ]; exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => hA1 a b
      _ = ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ b ∈ range (n + 1),
          ∑ d ∈ range (n + 1), C (y c d) *
            ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
              (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) :=
          sum_congr rfl fun a _ => sum_comm
      _ = ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
          ∑ b ∈ range (n + 1), C (y c d) *
            ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
              (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) :=
          sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
      _ = ∑ c ∈ range (n + 1), ∑ a ∈ range (n + 1), ∑ d ∈ range (n + 1),
          ∑ b ∈ range (n + 1), C (y c d) *
            ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
              (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) := sum_comm
      _ = ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1), ∑ a ∈ range (n + 1),
          ∑ b ∈ range (n + 1), C (y c d) *
            ((C ((-1 : K) ^ (a * (c + d)) * (kraw n a c : K)) * P a) *
              (C ((-1 : K) ^ (b * (c + d)) * (kraw n b d : K)) * P b)) :=
          sum_congr rfl fun c _ => sum_comm
      _ = _ := sum_congr rfl fun c _ => sum_congr rfl fun d _ => (hS c d).symm
  have hA : Ψ = 4 * 2 ^ (2 * n) * G := by
    rw [hA2, hG, mul_sum]
    refine sum_congr rfl fun c hc => ?_
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    rw [S_mul_S (Nat.lt_succ_iff.mp (mem_range.mp hc)) (Nat.lt_succ_iff.mp (mem_range.mp hd))]
    simp only [hybar]
    split_ifs
    · ring
    · simp
  -- Step B: corner vanishing makes Ψ divisible by ((1 - X)(1 + X))^m.
  have hB : ((1 - X : K[X]) * (1 + X)) ^ m ∣ Ψ := by
    refine dvd_sum fun a ha => dvd_sum fun b hb => ?_
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hb' : b ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hb)
    by_cases hab : InCorner n a b
    · have : coef a b = 0 := hcorner a ha' b hb' hab
      rw [this, map_zero, zero_mul]
      exact dvd_zero _
    · refine Dvd.dvd.mul_left ?_ _
      have hm' : m ≤ min a (n - a) + min b (n - b) := by
        unfold InCorner at hab; omega
      refine (pow_dvd_pow _ hm').trans ?_
      rw [pow_add]
      exact mul_dvd_mul (P_dvd (min_le_left _ _) (min_le_right _ _))
        (P_dvd (min_le_left _ _) (min_le_right _ _))
  -- Step C: G is invariant under X ↦ i X.
  have hi2 : i ^ 2 = -1 := by rw [sq, hi]
  have hi4 : i ^ 4 = 1 := by rw [show i ^ 4 = (i * i) * (i * i) by ring, hi]; ring
  have hC : G.comp (C i * X) = G := by
    simp only [hG, Polynomial.sum_comp, mul_comp, C_comp, X_pow_comp]
    refine sum_congr rfl fun c hc => sum_congr rfl fun d hd => ?_
    simp only [hybar]
    split_ifs with h
    · by_cases hy : y c d = 0
      · simp [hy]
      obtain ⟨k, hk⟩ := four_dvd_of_qpar h.1 h.2
        (hq c (Nat.lt_succ_iff.mp (mem_range.mp hc)) d (Nat.lt_succ_iff.mp (mem_range.mp hd)) hy)
      rw [mul_pow, ← C_pow, hk, pow_mul, hi4, one_pow, C_1, one_mul]
    · simp
  -- Step D: degree count.
  have hu : IsUnit (4 * 2 ^ (2 * n) : K[X]) := by
    have : (4 * 2 ^ (2 * n) : K[X]) = C (4 * 2 ^ (2 * n)) := by
      simp only [map_mul, map_pow, C_ofNat]
    rw [this]
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    exact isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero (by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) (pow_ne_zero _ h2)))
  have h1 : (1 - X ^ 2 : K[X]) ^ m ∣ G := by
    have e : (1 - X ^ 2 : K[X]) = (1 - X) * (1 + X) := by ring
    rw [e, ← hu.dvd_mul_left, ← hA]
    exact hB
  have h2 : (1 + X ^ 2 : K[X]) ^ m ∣ G := by
    obtain ⟨Q, hQ⟩ := h1
    refine ⟨Q.comp (C i * X), ?_⟩
    have e : ((1 - X ^ 2 : K[X]) ^ m).comp (C i * X) = (1 + X ^ 2) ^ m := by
      simp only [pow_comp, sub_comp, one_comp, X_comp, mul_pow, ← C_pow, hi2, map_neg,
        map_one]
      ring
    rw [← hC, hQ, mul_comp, e]
  have hcop : IsCoprime ((1 - X ^ 2 : K[X]) ^ m) ((1 + X ^ 2) ^ m) := by
    refine IsCoprime.pow ⟨C (1 / 2), C (1 / 2), ?_⟩
    have h2 : C (1 / 2 : K) * (2 : K[X]) = 1 := by
      rw [show (2 : K[X]) = C 2 by rw [C_ofNat], ← C_mul, one_div, inv_mul_cancel₀ two_ne_zero, C_1]
    linear_combination h2
  have h3 := hcop.mul_dvd h1 h2
  have hGdeg : G.natDegree ≤ 2 * n := by
    refine natDegree_sum_le_of_forall_le _ _ fun c hc => natDegree_sum_le_of_forall_le _ _
      fun d hd => (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := mem_range.mp hc; have := mem_range.mp hd; omega
  have hG0 : G = 0 := by
    by_contra hG0
    have hdeg := natDegree_le_of_dvd h3 hG0
    have hD : ((1 - X ^ 2 : K[X]) ^ m * (1 + X ^ 2) ^ m).natDegree = m * 4 := by
      rw [← mul_pow, natDegree_pow]
      congr 1
      have : (1 - X ^ 2 : K[X]) * (1 + X ^ 2) = -(X ^ 4 - C 1) := by simp; ring
      rw [this, natDegree_neg, natDegree_X_pow_sub_C]
    omega
  have hcoeff : G.coeff 0 = y 0 0 := by
    simp only [hG, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [sum_eq_single 0 (fun c _ hc => sum_eq_zero fun d _ => by rw [ite_eq_right (by omega)])
      (by simp), sum_eq_single 0 (fun d _ hd => by rw [ite_eq_right (by omega)]) (by simp)]
    simp [hybar]
  rw [← hcoeff, hG0, coeff_zero]

end Key2

lemma sum_fin_prod {K : Type*} [Field K] (n : ℕ) (f : ℕ → ℕ → K) :
    ∑ p : Fin (n + 1) × Fin (n + 1), f p.1 p.2 =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), f a b := by
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range (n + 1), f a b)]
  exact sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (f a) (n + 1)

end Corner

open Corner in
/-- **Corner feasibility.** For every length `n`, the class-constant linear system has a
solution supported on corner classes. -/
theorem corner_feasible {K : Type*} [Field K] [NeZero (2 : K)] (i : K) (hi : i * i = -1) (n : ℕ) :
    ∃ W : ℕ → ℕ → K,
    (∀ a b, W a b ≠ 0 → a ≤ n ∧ b ≤ n ∧ InCorner n a b) ∧
    ∀ c ≤ n, ∀ d ≤ n, qpar c d = 0 →
      (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
        W a b * (-1) ^ ((a + b) * (c + d)) * kraw n a c * kraw n b d) =
      if c = 0 ∧ d = 0 then 1 else 0 := by
  classical
  let M : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) K := fun p q =>
    if qpar p.1 p.2 = 0 ∧ InCorner n q.1 q.2 then
      (-1 : K) ^ (((q.1 : ℕ) + q.2) * ((p.1 : ℕ) + p.2)) * (kraw n q.1 p.1 : K) *
        (kraw n q.2 p.2 : K)
    else 0
  let e : Fin (n + 1) × Fin (n + 1) → Fin (n + 1) × Fin (n + 1) → K :=
    fun i j => if i = j then 1 else 0
  have hMe : ∀ p q, (M.mulVecLin (e q)) p = M p q := by
    intro p q
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, e, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hmem : e (0, 0) ∈ LinearMap.range M.mulVecLin
  · obtain ⟨w, hw⟩ := hmem
    refine ⟨fun a b => if h : a < n + 1 ∧ b < n + 1 then
      (if InCorner n a b then w (⟨a, h.1⟩, ⟨b, h.2⟩) else 0) else 0, ?_, ?_⟩
    · intro a b h
      by_cases h1 : a < n + 1 ∧ b < n + 1
      · beta_reduce at h
        rw [dite_eq_left h1] at h
        by_cases h2 : InCorner n a b
        · exact ⟨by omega, by omega, h2⟩
        · rw [ite_eq_right h2] at h; exact absurd rfl h
      · beta_reduce at h
        rw [dite_eq_right h1] at h; exact absurd rfl h
    · intro c hc d hd hq
      have hcd := congrFun hw (⟨c, by omega⟩, ⟨d, by omega⟩)
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at hcd
      have hδ : e (0, 0) (⟨c, by omega⟩, ⟨d, by omega⟩) = if c = 0 ∧ d = 0 then 1 else 0 := by
        simp only [e, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, eq_comm]
      rw [← hδ, ← hcd, ← sum_fin_prod]
      refine sum_congr rfl fun q _ => ?_
      beta_reduce
      rw [dite_eq_left ⟨q.1.2, q.2.2⟩]
      simp only [M, Fin.eta, Prod.mk.eta, hq, true_and]
      split_ifs <;> ring
  · exfalso
    obtain ⟨φ, hφδ, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
    have hφM : ∀ x, φ (M.mulVecLin x) = 0 := fun x => by
      have : φ (M.mulVecLin x) ∈ (LinearMap.range M.mulVecLin).map φ :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x)
      rw [hφ] at this
      exact (Submodule.mem_bot K).mp this
    let y : ℕ → ℕ → K := fun c d => if h : c < n + 1 ∧ d < n + 1 then
      (if qpar c d = 0 then φ (e (⟨c, h.1⟩, ⟨d, h.2⟩)) else 0) else 0
    have hy0 : y 0 0 = φ (e (0, 0)) := by
      simp only [y, dite_eq_left (⟨Nat.succ_pos n, Nat.succ_pos n⟩ : 0 < n + 1 ∧ 0 < n + 1),
        show qpar 0 0 = 0 from rfl, ite_true]
      rfl
    apply hφδ
    rw [← hy0]
    refine dual_vanish i hi n y ?_ ?_
    · intro c _ d _ hy
      by_contra hq
      apply hy
      simp only [y, hq, ite_false, dite_eq_ite, ite_self]
    · intro a ha b hb hab
      have h := hφM (e (⟨a, by omega⟩, ⟨b, by omega⟩))
      rw [LinearMap.pi_apply_eq_sum_univ] at h
      rw [← sum_fin_prod, ← h]
      refine sum_congr rfl fun p _ => ?_
      rw [hMe]
      simp only [y, dite_eq_left (⟨p.1.2, p.2.2⟩ : (p.1 : ℕ) < n + 1 ∧ (p.2 : ℕ) < n + 1)]
      simp only [M, Fin.eta, Prod.mk.eta, hab, and_true, smul_eq_mul]
      split_ifs
      · ring
      · simp

end IDMM
