/-
**The Majorana corner sum of squares.** For every `n` there are weights on the `4^n` Pauli words, supported on
the corner Majorana classes `min(a, n−a) + min(b, n−b) ≤ n/2`, with
`(Σ X²)(Σ Y²) = Σ_ν w_ν (Xᵀ P_ν Y)²` over every field with `2 ≠ 0` and a square root of `−1` (cycle 055, §1).
-/
import IDMM.MajClass
import IDMM.Corner

noncomputable section
namespace IDMM
open Finset

variable {n : ℕ} {K : Type*} [Field K]

theorem weight_eq_zero_iff (v : Bits n) : weight v = 0 ↔ v = 0 := by
  classical
  rw [weight, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h; funext i
    rcases zmod2_cases (v i) with hv | hv
    · exact hv
    · exact absurd hv (h (mem_univ i))
  · rintro rfl i _; simp [zmod2_one_ne_zero.symm]

theorem kraw_eq_coeff (n a c : ℕ) : kraw n a c = (krawPoly n c).coeff a := rfl

theorem fourier_smul (c : K) (w : (Fin n → Fin 4) → K) (t b : Bits n) :
    fourier (fun ν => c * w ν) t b = c * fourier w t b := by
  simp [fourier, mul_sum, mul_assoc]

/-- **The Majorana corner sum of squares.** -/
theorem majorana_sos [NeZero (2 : K)] [SqrtNegOne K] (n : ℕ) : ∃ w : (Fin n → Fin 4) → K,
    (∀ X Y : (Fin n → Fin 2) → K,
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, w ν * PauliCubes.pauliForm K ν X Y ^ 2) ∧
    (∀ ν, w ν ≠ 0 → InCorner n (classOf ν).1 (classOf ν).2) := by
  classical
  obtain ⟨W, hWsupp, hWeq⟩ := corner_feasible (SqrtNegOne.i : K) SqrtNegOne.i_mul_i n
  refine ⟨fun ν => (2 : K) ^ n * W (classOf ν).1 (classOf ν).2, ?_, ?_⟩
  · intro X Y
    refine sos_of_fourier _ (fun t b htb => ?_) X Y
    -- write the label `(t, b)` in Majorana coordinates
    set ν₀ : Fin n → Fin 4 := ofXZ t b
    set s' := majS ν₀
    set a' := majA ν₀
    have hj := jw_maj ν₀
    have ht : jwX s' a' = t := by
      have := congrArg wX hj; rwa [jw, wX_ofXZ, wX_ofXZ] at this
    have hb : jwZ s' a' = b := by
      have := congrArg wZ hj; rwa [jw, wZ_ofXZ, wZ_ofXZ] at this
    rw [fourier_smul, ← ht, ← hb, fourier_class]
    have hq : qpar (weight s') (weight a') = 0 := by
      have h := q_class s' a'
      rw [ht, hb, htb] at h
      have h2 := (ZMod.natCast_eq_zero_iff _ 2).mp h.symm
      simp only [qpar]
      omega
    have hc := hWeq (weight s') (weight_le s') (weight a') (weight_le a') hq
    simp only [← kraw_eq_coeff]
    rw [hc]
    have hiff : (weight s' = 0 ∧ weight a' = 0) ↔ (jwX s' a' = 0 ∧ jwZ s' a' = 0) := by
      rw [weight_eq_zero_iff, weight_eq_zero_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by simp [jwX, h1, h2], ?_⟩
        funext j; simp [jwZ, h1, h2, suffix]
      · rintro ⟨h1, h2⟩
        rw [ht] at h1; rw [hb] at h2
        have hν : ν₀ = ofXZ 0 0 := by simp only [ν₀, h1, h2]
        have hs : majS ν₀ = 0 := by
          funext j; simp [hν, majS, majA, wX_ofXZ, wZ_ofXZ, suffix]
        have ha : majA ν₀ = 0 := by
          funext j; simp [hν, majA, wX_ofXZ, wZ_ofXZ, suffix]
        exact ⟨hs, ha⟩
    by_cases h0 : weight s' = 0 ∧ weight a' = 0
    · rw [if_pos h0, if_pos (hiff.mp h0), mul_one]
    · rw [if_neg h0, if_neg (fun h => h0 (hiff.mpr h)), mul_zero]
  · intro ν hν
    have : W (classOf ν).1 (classOf ν).2 ≠ 0 := by
      intro h0; apply hν; simp [h0]
    exact (hWsupp _ _ this).2.2

end IDMM
