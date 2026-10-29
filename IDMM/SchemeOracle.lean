/-
**Block oracles from one rank decomposition**, over any field.

A rank-`R` decomposition of `⟨a, b, a⟩` with `a^k ≤ b`, `k = (1−μ)/μ`, and `R, ab, a² ≤ a^τ` gives, for every
length `n`, a block matrix-multiplication oracle for `2^m × 2^(n−m)` inputs (`m = ⌈μn⌉`) with
`O((2^m)^{τ+ε})` gates: recurse `t = ⌈log_a 2^m⌉` levels (`rank_products_reach`, `rank_middle_reach`).
-/
import IDMM.Construction
import IDMM.RankCircuits

noncomputable section
namespace IDMM
open Finset PauliCubes OAI.MatrixMultiplication.Foundation Filter

/-- `m + 1 ≤ C₀ (2^m)^ε` for all `m`. -/
theorem exists_succ_le_two_pow_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, (m : ℝ) + 1 ≤ C₀ * ((2 : ℝ) ^ m) ^ ε := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (eventually_succ_le hε)
  refine ⟨m₀ + 1, by positivity, fun m => ?_⟩
  have h1 : (1 : ℝ) ≤ ((2 : ℝ) ^ m) ^ ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
  have hpow : ((2 : ℝ) ^ m) ^ ε = (2 : ℝ) ^ ((m : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rcases le_or_gt m₀ m with h | h
  · have := hm₀ m h
    rw [← hpow] at this
    nlinarith
  · have : (m : ℝ) + 1 ≤ m₀ := by exact_mod_cast h
    nlinarith

variable {K : Type*} [Field K] {μ : ℝ}

/-- **The oracle family from one rank decomposition.** -/
theorem oracles_of_scheme (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {a b R : ℕ}
    (hT : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a)) R) (ha2 : 2 ≤ a)
    {τ : ℝ} (hab : (a : ℝ) ^ ((1 - μ) / μ) ≤ b) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : ((a * b : ℕ) : ℝ) ≤ (a : ℝ) ^ τ) (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ M : ℕ,
      BlockMM (ncInputs K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2))) (mOfMu μ n) (n - mOfMu μ n) M ∧
        (M : ℝ) ≤ C * ((2 : ℝ) ^ mOfMu μ n) ^ (τ + ε) := by
  have hμpos : 0 < μ := by linarith
  have ha1 : (1 : ℝ) < a := by exact_mod_cast ha2
  have haR : (0 : ℝ) < a := by linarith
  have hk0 : 0 ≤ (1 - μ) / μ := div_nonneg (by linarith) hμpos.le
  obtain ⟨C₀, hC₀, hsucc⟩ := exists_succ_le_two_pow_rpow hε
  set D : ℕ := 7 * (a * b + b * a + a * a) + 6 with hD
  refine ⟨D * (a : ℝ) ^ τ * C₀, by positivity, fun n => ?_⟩
  set m := mOfMu μ n with hm
  set r := n - m with hr
  set t := Nat.clog a (2 ^ m) with ht
  -- the sizes
  have hat : 2 ^ m ≤ a ^ t := Nat.le_pow_clog (by omega) _
  have hatR : ((2 : ℝ) ^ m) ≤ (a : ℝ) ^ t := by exact_mod_cast hat
  have hrk : (r : ℝ) ≤ (1 - μ) / μ * m := by
    have hmn := mOfMu_le hμ1.le n
    rw [hr, Nat.cast_sub hmn]
    have h := le_mOfMu (μ := μ) n
    have h2 : (1 - μ) / μ * (μ * n) = (1 - μ) * n := by field_simp
    have h3 : (1 - μ) / μ * (μ * n) ≤ (1 - μ) / μ * (mOfMu μ n : ℝ) :=
      mul_le_mul_of_nonneg_left h hk0
    nlinarith
  have hbt : 2 ^ r ≤ b ^ t := by
    have : ((2 : ℝ) ^ r) ≤ (b : ℝ) ^ t := by
      calc ((2 : ℝ) ^ r) = (2 : ℝ) ^ (r : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ ((1 - μ) / μ * m) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hrk
        _ = ((2 : ℝ) ^ m) ^ ((1 - μ) / μ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
        _ ≤ ((a : ℝ) ^ t) ^ ((1 - μ) / μ) := Real.rpow_le_rpow (by positivity) hatR hk0
        _ = ((a : ℝ) ^ ((1 - μ) / μ)) ^ t := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul haR.le,
              ← Real.rpow_mul haR.le, mul_comm]
        _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (by positivity) hab t
    exact_mod_cast this
  have hcI : Fintype.card (Bits m) ≤ a ^ t := by simpa [card_bits] using hat
  have hcJ : Fintype.card (Bits r) ≤ b ^ t := by simpa [card_bits] using hbt
  let V := (Fin n → Fin 2) ⊕ (Fin n → Fin 2)
  have hc : ∀ z : K, algebraMap K (FreeAlgebra K V) z ∈ ncInputs K V := fun z => Or.inr ⟨z, rfl⟩
  refine ⟨rankCost a b a R t, ⟨fun B X Y hX hY => ?_, fun B X Y Q hX hY hQ => ?_⟩, ?_⟩
  · exact rank_products_reach hc hT t hcI hcJ hcI (fun i j => X (i, j)) (fun j l => Y (l, j))
      (fun i j => hX _) (fun j l => hY _)
  · exact rank_middle_reach hc hT t hcI hcJ hcI (fun i j => X (i, j)) Q (fun j l => Y (l, j))
      (fun i j => hX _) hQ (fun j l => hY _)
  · -- the cost
    set Mx := max R (max (a * b) (max (b * a) (a * a))) with hMx
    have hMx1 : 1 ≤ Mx := le_trans (by nlinarith) (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans
      (le_max_right _ _))
    have hcost := rankCost_le a b a R t hMx1
    have hMxR : (Mx : ℝ) ≤ (a : ℝ) ^ τ := by
      have e1 : ((b * a : ℕ) : ℝ) ≤ (a : ℝ) ^ τ := by rw [mul_comm]; exact hin
      have e2 : ((a * a : ℕ) : ℝ) ≤ (a : ℝ) ^ τ := by push_cast; rw [← sq]; exact_mod_cast hout
      rw [hMx]; push_cast
      exact max_le hR (max_le (by exact_mod_cast hin) (max_le (by exact_mod_cast e1) (by exact_mod_cast e2)))
    -- `a^t ≤ a · 2^m`
    have hat2 : (a : ℝ) ^ t ≤ a * (2 : ℝ) ^ m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · have : t = 0 := by rw [ht, hm0, pow_zero, Nat.clog_one_right]
        rw [this, hm0]; simp; linarith
      · have hx : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
        have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < a) hx
        have htpos : 0 < t := Nat.clog_pos (by omega) hx
        have : a ^ t ≤ a * 2 ^ m := by
          calc a ^ t = a * a ^ t.pred := by
                rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos htpos).symm
            _ ≤ a * 2 ^ m := Nat.mul_le_mul_left _ hlt.le
        exact_mod_cast this
    have htm : (t : ℝ) + 1 ≤ m + 1 := by
      have : t ≤ m := Nat.clog_le_of_le_pow (by
        calc 2 ^ m ≤ a ^ m := Nat.pow_le_pow_left ha2 m
          _ = a ^ m := rfl)
      exact_mod_cast Nat.add_le_add_right this 1
    have hτ0 : 0 ≤ τ := by
      by_contra hneg
      push Not at hneg
      have h1 : (a : ℝ) ^ τ < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha1 hneg
      have h2 : (1 : ℝ) ≤ (a : ℝ) ^ (2 : ℕ) := one_le_pow₀ ha1.le
      linarith
    have hpow : (Mx : ℝ) ^ t ≤ (a : ℝ) ^ τ * ((2 : ℝ) ^ m) ^ τ := by
      calc (Mx : ℝ) ^ t ≤ ((a : ℝ) ^ τ) ^ t := pow_le_pow_left₀ (by positivity) hMxR t
        _ = ((a : ℝ) ^ t) ^ τ := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul haR.le,
              ← Real.rpow_mul haR.le, mul_comm]
        _ ≤ ((a : ℝ) * (2 : ℝ) ^ m) ^ τ := Real.rpow_le_rpow (by positivity) hat2 hτ0
        _ = (a : ℝ) ^ τ * ((2 : ℝ) ^ m) ^ τ := Real.mul_rpow haR.le (by positivity)
    have hcostR : (rankCost a b a R t : ℝ) ≤ D * ((t : ℝ) + 1) * (Mx : ℝ) ^ t := by
      have := hcost
      rw [hD]; exact_mod_cast this
    have hsplit : ((2 : ℝ) ^ m) ^ (τ + ε) = ((2 : ℝ) ^ m) ^ τ * ((2 : ℝ) ^ m) ^ ε :=
      Real.rpow_add (by positivity) _ _
    calc (rankCost a b a R t : ℝ) ≤ D * ((t : ℝ) + 1) * (Mx : ℝ) ^ t := hcostR
      _ ≤ D * ((m : ℝ) + 1) * ((a : ℝ) ^ τ * ((2 : ℝ) ^ m) ^ τ) := by gcongr
      _ ≤ D * (C₀ * ((2 : ℝ) ^ m) ^ ε) * ((a : ℝ) ^ τ * ((2 : ℝ) ^ m) ^ τ) := by
          gcongr; exact hsucc m
      _ = D * (a : ℝ) ^ τ * C₀ * ((2 : ℝ) ^ m) ^ (τ + ε) := by rw [hsplit]; ring

end IDMM
