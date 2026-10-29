/-
Input transforms for one Majorana block (cycle 055 §2).

Every word of a shifted block `σ + A` (`A` supported in the block `U`) has matrix
`P = λ · C⁻¹ · P_{A'} · (C · P_σ)` with `A'` supported on the first `m` qubits (`block_word_mat`), and bilinear
forms transform accordingly in all three orders (`bilin_xy`, `bilin_yx`, `bilin_star`).
-/
import IDMM.MajMove

noncomputable section
namespace IDMM
open Finset Matrix

variable {n : ℕ} {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K]

theorem pmatM_add (A σ : MV n) :
    pmatM K (A + σ) = (sgnB (dot (jwZ σ.1 σ.2) (jwX A.1 A.2)) : K) • (pmatM K A * pmatM K σ) := by
  rw [pmatM, pmatM, pmatM, pmat_mul, smul_smul, sgnB_sq, one_smul, ← jwX_add, ← jwZ_add]

/-- **The matrix of a block word.** -/
theorem block_word_mat (L : List (MIdx n × MIdx n)) (hL : ∀ p ∈ L, p.1 ≠ p.2) (σ A : MV n) :
    ∃ lam : K, lam ≠ 0 ∧
      pmatM K (A + σ) = lam • (compI K L * pmatM K (mswapList L A) * (compM K L * pmatM K σ)) := by
  obtain ⟨l1, hl1, h1⟩ := comp_conj (K := K) L hL A
  have hA : pmatM K A = l1 • (compI K L * pmatM K (mswapList L A) * compM K L) := by
    calc pmatM K A = compI K L * (compM K L * pmatM K A * compI K L) * compM K L := by
          rw [show compI K L * (compM K L * pmatM K A * compI K L) * compM K L =
            (compI K L * compM K L) * pmatM K A * (compI K L * compM K L) by noncomm_ring, compI_compM]; simp
      _ = _ := by rw [h1, mul_smul_comm, smul_mul_assoc]
  have hs : (sgnB (dot (jwZ σ.1 σ.2) (jwX A.1 A.2)) : K) ≠ 0 := by unfold sgnB; split_ifs <;> norm_num
  refine ⟨sgnB (dot (jwZ σ.1 σ.2) (jwX A.1 A.2)) * l1, mul_ne_zero hs hl1, ?_⟩
  rw [pmatM_add, hA, smul_mul_assoc, smul_smul]
  congr 1; noncomm_ring

/-! ## Bilinear forms under a change of basis -/

section bilin
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜]

/-- `X'_{x'} = Σ_x L[x, x'] X_x`. -/
def leftT (Lm : Matrix ι ι K) (X : ι → 𝒜) (x' : ι) : 𝒜 := ∑ x, Lm x x' • X x
/-- `Y'_{y'} = Σ_y R[y', y] Y_y`. -/
def rightT (Rm : Matrix ι ι K) (Y : ι → 𝒜) (y' : ι) : 𝒜 := ∑ y, Rm y' y • Y y

theorem mul3_apply (Lm N Rm : Matrix ι ι K) (x y : ι) :
    (Lm * N * Rm) x y = ∑ x', ∑ y', Lm x x' * N x' y' * Rm y' y := by
  simp only [mul_apply, sum_mul]
  rw [sum_comm]

theorem sum_swap_pairs {M : Type*} [AddCommMonoid M] (F : ι → ι → ι → ι → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm

theorem bilin_xy (Lm N Rm : Matrix ι ι K) (X Y : ι → 𝒜) :
    ∑ x, ∑ y, (Lm * N * Rm) x y • (X x * Y y) =
      ∑ x', ∑ y', N x' y' • (leftT Lm X x' * rightT Rm Y y') := by
  have rhs : ∀ x' y', N x' y' • (leftT Lm X x' * rightT Rm Y y') =
      ∑ x, ∑ y, (Lm x x' * N x' y' * Rm y' y) • (X x * Y y) := by
    intro x' y'
    simp only [leftT, rightT, sum_mul, mul_sum, smul_sum, smul_mul_smul_comm, smul_smul]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    congr 1; ring
  simp only [rhs, mul3_apply, sum_smul]
  exact sum_swap_pairs _

theorem bilin_yx (Lm N Rm : Matrix ι ι K) (X Y : ι → 𝒜) :
    ∑ x, ∑ y, (Lm * N * Rm) x y • (Y y * X x) =
      ∑ x', ∑ y', N x' y' • (rightT Rm Y y' * leftT Lm X x') := by
  have rhs : ∀ x' y', N x' y' • (rightT Rm Y y' * leftT Lm X x') =
      ∑ x, ∑ y, (Lm x x' * N x' y' * Rm y' y) • (Y y * X x) := by
    intro x' y'
    simp only [leftT, rightT, sum_mul, mul_sum, smul_sum, smul_mul_smul_comm, smul_smul]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    congr 1; ring
  simp only [rhs, mul3_apply, sum_smul]
  exact sum_swap_pairs _

theorem bilin_star (Lm N Rm : Matrix ι ι K) (X Y : ι → 𝒜) (z : 𝒜) :
    ∑ x, ∑ y, (Lm * N * Rm) x y • (X x * z * Y y) =
      ∑ x', ∑ y', N x' y' • (leftT Lm X x' * z * rightT Rm Y y') := by
  have rhs : ∀ x' y', N x' y' • (leftT Lm X x' * z * rightT Rm Y y') =
      ∑ x, ∑ y, (Lm x x' * N x' y' * Rm y' y) • (X x * z * Y y) := by
    intro x' y'
    simp only [leftT, rightT, sum_mul, mul_sum, smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    congr 1; ring
  simp only [rhs, mul3_apply, sum_smul]
  exact sum_swap_pairs _

end bilin

end IDMM
