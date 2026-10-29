/-
The forms of one block word after the input change of basis and reshape (cycle 055 §2).

For a block `(L, σ)` with `L` moving the block onto the first `m` qubits, each word `ν` with Majorana vector
`A + σ` has `f^xy_ν = λ · Σ_p (−1)^{β·p} Σ_s X''(p,s) Y''(p+α,s)`, and likewise for `f^yx` and `f ⋆ z`, where
`X''`, `Y''` are the transformed inputs shared by the whole block and `(α, β)` is the canonical word.
-/
import IDMM.MajReshape
import PauliCubes.NCForms

noncomputable section
namespace IDMM
open Finset Matrix PauliCubes

variable {n m : ℕ} {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K] {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜]

/-! ## Block forms -/

section forms
variable {r : ℕ} (X'' Y'' : Bits m × Bits r → 𝒜) (α β : Bits m)

variable (K) in
/-- `Σ_p (−1)^{β·p} Σ_s X''(p,s) Y''(p+α,s)`. -/
def bxy : 𝒜 := ∑ p, (sgnB (dot β p) : K) • ∑ s, X'' (p, s) * Y'' (p + α, s)
variable (K) in
/-- `Σ_p (−1)^{β·p} Σ_s Y''(p+α,s) X''(p,s)`. -/
def byx : 𝒜 := ∑ p, (sgnB (dot β p) : K) • ∑ s, Y'' (p + α, s) * X'' (p, s)
variable (K) in
/-- `Σ_p (−1)^{β·p} Σ_s X''(p,s) z Y''(p+α,s)`. -/
def bstar (z : 𝒜) : 𝒜 := ∑ p, (sgnB (dot β p) : K) • ∑ s, X'' (p, s) * z * Y'' (p + α, s)

end forms

theorem pauliWord_maj (ν : Fin n → Fin 4) (x y : Bits n) :
    pauliWord K ν x y = pmatM K (majS ν, majA ν) x y := by
  conv_lhs => rw [← jw_maj ν]
  rw [jw, pauliWord_ofXZ]; rfl

/-! ## One block -/

section block
variable (hm : m ≤ n) (L : List (MIdx n × MIdx n)) (σ A : MV n)

variable (K) in
/-- The transformed `X`, reshaped. -/
def Xblk (X : Bits n → 𝒜) : Bits m × Bits (n - m) → 𝒜 :=
  fun ps => leftT (compI K L) X (joinB hm ps.1 ps.2)
variable (K) in
/-- The transformed `Y`, reshaped. -/
def Yblk (Y : Bits n → 𝒜) : Bits m × Bits (n - m) → 𝒜 :=
  fun qs => rightT (compM K L * pmatM K σ) Y (joinB hm qs.1 qs.2)
/-- The canonical word's shift. -/
def αblk : Bits m := restr hm (jwX (mswapList L A).1 (mswapList L A).2)
/-- The canonical word's sign vector. -/
def βblk : Bits m := restr hm (jwZ (mswapList L A).1 (mswapList L A).2)

variable {hm L σ A} {lam : K}
  (hlam : pmatM K (A + σ) = lam • (compI K L * pmatM K (mswapList L A) * (compM K L * pmatM K σ)))
  (hA : SuppIn (mswapList L A) (canon n m))
include hlam hA

theorem fxy_block (ν : Fin n → Fin 4) (hν : (majS ν, majA ν) = A + σ) (X Y : Bits n → 𝒜) :
    fxy (L := K) X Y ν = lam • bxy K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A) := by
  have hl := lowSupp_jw hA
  change ∑ x : Bits n, ∑ y : Bits n, pauliWord K ν x y • (X x * Y y) = _
  simp only [pauliWord_maj, hν, hlam, Matrix.smul_apply, smul_eq_mul, mul_smul, ← smul_sum]
  rw [bilin_xy, pmatM, reshape hm hl.1 hl.2]
  rfl

theorem fyx_block (ν : Fin n → Fin 4) (hν : (majS ν, majA ν) = A + σ) (X Y : Bits n → 𝒜) :
    fyx (L := K) X Y ν = lam • byx K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A) := by
  have hl := lowSupp_jw hA
  change ∑ x : Bits n, ∑ y : Bits n, pauliWord K ν x y • (Y y * X x) = _
  simp only [pauliWord_maj, hν, hlam, Matrix.smul_apply, smul_eq_mul, mul_smul, ← smul_sum]
  rw [bilin_yx, pmatM, reshape hm hl.1 hl.2]
  rfl

theorem fstar_block (ν : Fin n → Fin 4) (hν : (majS ν, majA ν) = A + σ) (X Y : Bits n → 𝒜) (z : 𝒜) :
    fstar (L := K) X Y ν z =
      lam • bstar K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A) z := by
  have hl := lowSupp_jw hA
  change ∑ x : Bits n, ∑ y : Bits n, pauliWord K ν x y • (X x * z * Y y) = _
  simp only [pauliWord_maj, hν, hlam, Matrix.smul_apply, smul_eq_mul, mul_smul, ← smul_sum]
  rw [bilin_star, pmatM, reshape hm hl.1 hl.2]
  rfl

/-- **`f^[2]` of a block word.** -/
theorem f2_block (ν : Fin n → Fin 4) (hν : (majS ν, majA ν) = A + σ) (X Y : Bits n → 𝒜) :
    f2 (L := K) X Y ν =
      (2 : K)⁻¹ • ((lam • bxy K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A)) *
          (lam • bxy K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A)) +
        lam • bstar K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A)
          (lam • byx K (Xblk K hm L X) (Yblk K hm L σ Y) (αblk hm L A) (βblk hm L A))) := by
  unfold f2
  rw [fxy_block hlam hA ν hν, fstar_block hlam hA ν hν, fyx_block hlam hA ν hν]

end block

end IDMM
