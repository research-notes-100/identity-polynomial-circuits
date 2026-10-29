/-
Circuit cost of the input transforms, and the reshape of a Pauli supported on the first `m` qubits.
-/
import IDMM.MajInput
import IDMM.SourceAccounting

noncomputable section
namespace IDMM
open Finset Matrix PauliCubes

variable {n : ℕ} {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K]

/-- A gate factor `c₁ · 1 + c₂ · P_{α,β}`. -/
def factor (c₁ c₂ : K) (α β : Bits n) : Matrix (Bits n) (Bits n) K := c₁ • 1 + c₂ • pmat K α β

section transforms
variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜]

theorem leftT_mul (A B : Matrix (Bits n) (Bits n) K) (Z : Bits n → 𝒜) :
    leftT (A * B) Z = leftT B (leftT A Z) := by
  funext x'
  simp only [leftT, mul_apply, sum_smul, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => sum_congr rfl fun x _ => ?_
  rw [mul_comm]

theorem rightT_mul (A B : Matrix (Bits n) (Bits n) K) (Z : Bits n → 𝒜) :
    rightT (A * B) Z = rightT A (rightT B Z) := by
  funext y'
  simp only [rightT, mul_apply, sum_smul, smul_sum, smul_smul]
  rw [sum_comm]

theorem leftT_one (Z : Bits n → 𝒜) : leftT (1 : Matrix (Bits n) (Bits n) K) Z = Z := by
  funext x'; simp [leftT, one_apply]

theorem rightT_one (Z : Bits n → 𝒜) : rightT (1 : Matrix (Bits n) (Bits n) K) Z = Z := by
  funext y'; simp [rightT, one_apply]

theorem factor_apply (c₁ c₂ : K) (α β : Bits n) (x y : Bits n) :
    factor c₁ c₂ α β x y = (if x = y then c₁ else 0) + (if y = x + α then c₂ * sgnB (dot β x) else 0) := by
  simp only [factor, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, pmat, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

theorem leftT_factor (c₁ c₂ : K) (α β : Bits n) (Z : Bits n → 𝒜) (x' : Bits n) :
    leftT (factor c₁ c₂ α β) Z x' = c₁ • Z x' + (c₂ * sgnB (dot β (x' + α))) • Z (x' + α) := by
  classical
  have key : ∀ x : Bits n, (x' = x + α) ↔ (x = x' + α) := fun x => by
    constructor <;> rintro rfl <;> rw [add_assoc, bits_add_self, add_zero]
  simp only [leftT, factor_apply, add_smul, sum_add_distrib, ite_smul, zero_smul, key, sum_ite_eq,
    sum_ite_eq', mem_univ, if_true]

theorem rightT_factor (c₁ c₂ : K) (α β : Bits n) (Z : Bits n → 𝒜) (y' : Bits n) :
    rightT (factor c₁ c₂ α β) Z y' = c₁ • Z y' + (c₂ * sgnB (dot β y')) • Z (y' + α) := by
  classical
  simp only [rightT, factor_apply, add_smul, sum_add_distrib, ite_smul, zero_smul, sum_ite_eq,
    sum_ite_eq', mem_univ, if_true]

end transforms

section cost
variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜}

/-- Two-term linear combinations of available values cost 7 gates. -/
theorem reach_lin2 (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) {B : Set 𝒜} {u v : 𝒜}
    (hu : u ∈ B) (hv : v ∈ B) (a b : K) : Reach inp B {a • u + b • v} 7 := by
  have h0 : (0 : 𝒜) ∈ inp := by simpa using hconst 0
  have h := Reach.linComb (inp := inp) h0 (univ : Finset (Fin 2))
    (c := ![algebraMap K 𝒜 a, algebraMap K 𝒜 b]) (p := ![u, v])
    (by intro i _; fin_cases i <;> exact hconst _) (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two, Algebra.smul_def] using h

/-- **One factor applied to an available vector, on the left.** -/
theorem reach_leftT_factor (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) {B : Set 𝒜}
    {Z : Bits n → 𝒜} (hZ : ∀ x, Z x ∈ B) (c₁ c₂ : K) (α β : Bits n) :
    Reach inp B (Set.range (leftT (factor c₁ c₂ α β) Z)) (7 * 2 ^ n) := by
  classical
  have h := Reach.biUnion (inp := inp) (B := B) (univ : Finset (Bits n))
    (S := fun x' => {leftT (factor c₁ c₂ α β) Z x'}) (t := fun _ => 7)
    (fun x' _ => by rw [leftT_factor]; exact reach_lin2 hconst (hZ _) (hZ _) _ _)
  refine h.mono le_rfl (fun z ⟨x', hx'⟩ => Set.mem_biUnion (mem_univ x') (by simp [hx'])) ?_
  simp [card_univ, mul_comm]

theorem reach_rightT_factor (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) {B : Set 𝒜}
    {Z : Bits n → 𝒜} (hZ : ∀ x, Z x ∈ B) (c₁ c₂ : K) (α β : Bits n) :
    Reach inp B (Set.range (rightT (factor c₁ c₂ α β) Z)) (7 * 2 ^ n) := by
  classical
  have h := Reach.biUnion (inp := inp) (B := B) (univ : Finset (Bits n))
    (S := fun y' => {rightT (factor c₁ c₂ α β) Z y'}) (t := fun _ => 7)
    (fun y' _ => by rw [rightT_factor]; exact reach_lin2 hconst (hZ _) (hZ _) _ _)
  refine h.mono le_rfl (fun z ⟨y', hy'⟩ => Set.mem_biUnion (mem_univ y') (by simp [hy'])) ?_
  simp [card_univ, mul_comm]

end cost

/-! ## The gates as factors -/

theorem gateM_factor (k l : MIdx n) :
    gateM K k l = factor 1 (gscal K (mpair k l)) (jwX (mpair k l).1 (mpair k l).2)
      (jwZ (mpair k l).1 (mpair k l).2) := by
  simp [gateM, gK, factor, pmatM]

theorem gateI_factor (k l : MIdx n) :
    gateI K k l = factor (2 : K)⁻¹ (-((2 : K)⁻¹ * gscal K (mpair k l))) (jwX (mpair k l).1 (mpair k l).2)
      (jwZ (mpair k l).1 (mpair k l).2) := by
  simp only [gateI, gK, factor, pmatM, sub_eq_add_neg, neg_smul]
  rw [smul_add, smul_neg, smul_smul]

theorem pmatM_factor (σ : MV n) : pmatM K σ = factor 0 1 (jwX σ.1 σ.2) (jwZ σ.1 σ.2) := by
  simp [factor, pmatM]

section composite
variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜}

/-- **The left transform by `C⁻¹`, gate by gate.** -/
theorem reach_leftT_compI (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) :
    ∀ (L : List (MIdx n × MIdx n)) {B : Set 𝒜} {Z : Bits n → 𝒜}, (∀ x, Z x ∈ B) →
      Reach inp B (Set.range (leftT (compI K L) Z)) (7 * 2 ^ n * L.length)
  | [], B, Z, hZ => by
    rw [compI, leftT_one]
    exact (Reach.refl (S := Set.range Z) (by rintro z ⟨x, rfl⟩; exact hZ x)).mono le_rfl le_rfl (by simp)
  | p :: L, B, Z, hZ => by
    rw [compI, leftT_mul, gateI_factor]
    set F := factor (2 : K)⁻¹ (-((2 : K)⁻¹ * gscal K (mpair p.1 p.2)))
      (jwX (mpair p.1 p.2).1 (mpair p.1 p.2).2) (jwZ (mpair p.1 p.2).1 (mpair p.1 p.2).2)
    have h1 := reach_leftT_factor (inp := inp) hconst hZ (2 : K)⁻¹ (-((2 : K)⁻¹ * gscal K (mpair p.1 p.2)))
      (jwX (mpair p.1 p.2).1 (mpair p.1 p.2).2) (jwZ (mpair p.1 p.2).1 (mpair p.1 p.2).2)
    have h2 := reach_leftT_compI hconst L (B := B ∪ Set.range (leftT F Z)) (Z := leftT F Z)
      (fun x => Set.mem_union_right _ (Set.mem_range_self x))
    refine (h1.seq h2).mono le_rfl le_rfl ?_
    simp only [List.length_cons]; exact le_of_eq (by ring)

/-- **The right transform by `C`, gate by gate.** -/
theorem reach_rightT_compM (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) :
    ∀ (L : List (MIdx n × MIdx n)) {B : Set 𝒜} {Z : Bits n → 𝒜}, (∀ x, Z x ∈ B) →
      Reach inp B (Set.range (rightT (compM K L) Z)) (7 * 2 ^ n * L.length)
  | [], B, Z, hZ => by
    rw [compM, rightT_one]
    exact (Reach.refl (S := Set.range Z) (by rintro z ⟨x, rfl⟩; exact hZ x)).mono le_rfl le_rfl (by simp)
  | p :: L, B, Z, hZ => by
    rw [compM, rightT_mul, gateM_factor]
    set F := factor 1 (gscal K (mpair p.1 p.2))
      (jwX (mpair p.1 p.2).1 (mpair p.1 p.2).2) (jwZ (mpair p.1 p.2).1 (mpair p.1 p.2).2)
    have h1 := reach_rightT_factor (inp := inp) hconst hZ 1 (gscal K (mpair p.1 p.2))
      (jwX (mpair p.1 p.2).1 (mpair p.1 p.2).2) (jwZ (mpair p.1 p.2).1 (mpair p.1 p.2).2)
    have h2 := reach_rightT_compM hconst L (B := B ∪ Set.range (rightT F Z)) (Z := rightT F Z)
      (fun x => Set.mem_union_right _ (Set.mem_range_self x))
    refine (h1.seq h2).mono le_rfl le_rfl ?_
    simp only [List.length_cons]; exact le_of_eq (by ring)

end composite

end IDMM
