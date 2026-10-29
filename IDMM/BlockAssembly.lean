/-
The evaluation of one Majorana block (cycle 055 §2 and §5), given transformed inputs, over any field.

After the input change of basis, every Pauli form of a block word is `λ · Σ_p (−1)^{β·p} M[p, p+α]`
with `M[p, q] = Σ_s X'(p, s) Y'(q, s)`, one rectangular matrix product. The block sum of squares
`Σ_i c_i · ½ (f^xy_i f^xy_i + f^*_i(f^yx_i))` is then evaluated by

* the two products `M` and `M'`, and one middle insertion, from a block matrix-multiplication
  oracle `BlockMM` (every `2^m × 2^r` product and middle insertion within `M` gates),
* Walsh–Hadamard transforms over `β` for every `α` (`walsh_family_reach`),
* regrouping the block by its labels `(α_i, β_i)` (`sum_smul_regroup`), so the squares are one
  linear combination of `4^m` products and the middle-insertion terms collapse to one matrix
  `Q[p, q]` inserted between `X'` and `Y'` (`midForm_sum`).

Everything here works over a field `K` acting on a `K`-algebra `𝒜`; the scalar `½` is carried
along, never cancelled. Main result: `block_assembly_gen`, at `3 M + 15 (m + 1) 4^m + 2` gates
(`blockGenCost`), with no dependence on the size of the block.

Over `ℂ`, a correct program `P` is such an oracle (`blockMM_of_algorithm`, at `960 · cost(P)`
gates): products and swapped products are `products_reach`, `products_reach_swapped`, and the
middle insertion is `middle_subst_reach`. Its cost carries a term `2^m 2^r`, absorbed in `P.cost`
by the input lower bound `b c ≤ 2 · cost` (`inner_mul_le_two_mul_cost`): a correct program reads
every entry of `B` directly from an input register, and each charged gate reads at most two.
Hence `block_assembly`, at `2880 · cost(P) + 15 (m + 1) 4^m + 2` gates.
-/
import IDMM.MMToolkit
import IDMM.MajBasic
import PauliCubes.CubeCircuit

noncomputable section
namespace IDMM
open PauliCubes Finset MvPolynomial
open OAI.MatrixMultiplication.Arithmetic

/-! ## Every correct program reads all of `B` -/

section InputBound

variable {F I : Type*}

/-- The input loaded by a gate, if it is an input gate. -/
def gateInput {R : Type*} : Gate F I R → Option I
  | .input u => some u
  | _ => none

/-- The input loaded by a register, if its gate is an input gate. -/
def inputReg : {r : ℕ} → Program F I r → Fin r → Option I
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases (gateInput g) (inputReg p)

variable [DecidableEq I]

/-- The inputs a charged gate reads directly from input registers. -/
def gateReads {r : ℕ} (p : Program F I r) : Gate F I (Fin r) → Finset I
  | .add i j | .sub i j | .mul i j => (inputReg p i).toFinset ∪ (inputReg p j).toFinset
  | _ => ∅

/-- The inputs some charged gate of the program reads directly from an input register. -/
def reads : {r : ℕ} → Program F I r → Finset I
  | 0, .nil => ∅
  | _ + 1, .step p g => reads p ∪ gateReads p g

theorem card_gateReads {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    (gateReads p g).card ≤ 2 * g.cost := by
  have h : ∀ i j : Fin r, ((inputReg p i).toFinset ∪ (inputReg p j).toFinset).card ≤ 2 := by
    intro i j
    refine (card_union_le _ _).trans ?_
    cases inputReg p i <;> cases inputReg p j <;> simp
  cases g with
  | constant z => simp [gateReads]
  | input u => simp [gateReads]
  | add i j => simpa [gateReads, Gate.cost] using h i j
  | sub i j => simpa [gateReads, Gate.cost] using h i j
  | mul i j => simpa [gateReads, Gate.cost] using h i j

/-- Each charged gate reads at most two inputs. -/
theorem card_reads {r : ℕ} (p : Program F I r) : (reads p).card ≤ 2 * p.cost := by
  induction p with
  | nil => simp [reads]
  | step p g ih =>
    have h₁ := card_gateReads p g
    have h₂ := card_union_le (reads p) (gateReads p g)
    simp only [reads, Program.cost]
    omega

/-- Every register is a polynomial in the inputs read by charged gates, or is itself an input
register. -/
theorem polynomialProgram_mem_reads [Field F] {r : ℕ} (p : Program F I r) (t : Fin r) :
    polynomialProgram p t ∈ supported F (↑(reads p) : Set I) ∨
      ∃ u, inputReg p t = some u ∧ polynomialProgram p t = X u := by
  induction p with
  | nil => exact Fin.elim0 t
  | @step r p g ih =>
    have hsub : (↑(reads p) : Set I) ⊆ ↑(reads (p.step g)) := by
      simp only [reads, coe_union]; exact Set.subset_union_left
    have hop : ∀ i : Fin r, (inputReg p i).toFinset ⊆ gateReads p g →
        polynomialProgram p i ∈ supported F (↑(reads (p.step g)) : Set I) := by
      intro i hi
      rcases ih i with h | ⟨u, hu, h⟩
      · exact supported_mono hsub h
      · rw [h, X_mem_supported]
        simp only [reads, coe_union, Set.mem_union, mem_coe]
        exact Or.inr (hi (by simp [hu]))
    refine Fin.cases ?_ (fun t => ?_) t
    · rw [polynomialProgram_step_zero]
      cases g with
      | constant z =>
        exact Or.inl (Subalgebra.algebraMap_mem _ z)
      | input u => exact Or.inr ⟨u, rfl, rfl⟩
      | add i j =>
        exact Or.inl (add_mem (hop i (by simp [gateReads])) (hop j (by simp [gateReads])))
      | sub i j =>
        exact Or.inl (sub_mem (hop i (by simp [gateReads])) (hop j (by simp [gateReads])))
      | mul i j =>
        exact Or.inl (mul_mem (hop i (by simp [gateReads])) (hop j (by simp [gateReads])))
    · rw [polynomialProgram_step_succ]
      rcases ih t with h | ⟨u, hu, h⟩
      · exact Or.inl (supported_mono hsub h)
      · exact Or.inr ⟨u, hu, h⟩

end InputBound

/-- **Input lower bound.** A correct algorithm for an `a × b` by `b × c` product with `a ≥ 1` reads
every entry of the right factor, so `b c ≤ 2 · cost`. -/
theorem inner_mul_le_two_mul_cost {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct)
    (ha : 1 ≤ a) : b * c ≤ 2 * P.cost := by
  classical
  let i₀ : Fin a := ⟨0, ha⟩
  have hread : ∀ jk : Fin b × Fin c, (Sum.inr jk : MatrixInput a b c) ∈ reads P.program := by
    rintro ⟨j, k⟩
    have hmem := polynomialProgram_mem_reads P.program (P.output i₀ k)
    rw [correct_polynomial P hP] at hmem
    rcases hmem with hmem | ⟨u, -, hu⟩
    · by_contra hn
      let x : MatrixInput a b c → ℂ :=
        Sum.elim (fun ij => if ij = (i₀, j) then 1 else 0) (fun _ => 0)
      let y : MatrixInput a b c → ℂ :=
        Sum.elim (fun ij => if ij = (i₀, j) then 1 else 0) (fun jk => if jk = (j, k) then 1 else 0)
      have hxy := hom_congr_vars (f₁ := MvPolynomial.eval x) (f₂ := MvPolynomial.eval y)
        (p₁ := ∑ j' : Fin b, X (Sum.inl (i₀, j')) * X (Sum.inr (j', k)))
        (RingHom.ext fun z => by simp) (fun v hv _ => ?_) rfl
      · simp [x, y] at hxy
      · have hv' : v ∈ reads P.program := (mem_supported.mp hmem) hv
        rcases v with ij | jk
        · simp [x, y]
        · have hne : jk ≠ (j, k) := by rintro rfl; exact hn hv'
          simp [x, y, hne]
    · rcases u with ij | jk
      · have h' := congrArg (MvPolynomial.eval (Sum.elim (fun _ => (1 : ℂ)) (fun _ => 0))) hu
        simp at h'
      · have h' := congrArg (MvPolynomial.eval (Sum.elim (fun _ => (0 : ℂ)) (fun _ => 1))) hu
        simp at h'
  have hsub : (univ : Finset (Fin b × Fin c)).image (fun jk => (Sum.inr jk : MatrixInput a b c)) ⊆
      reads P.program := by
    intro v hv
    obtain ⟨jk, -, rfl⟩ := mem_image.mp hv
    exact hread jk
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin] at hcard
  exact hcard.trans (card_reads P.program)

/-! ## Walsh–Hadamard transforms -/

theorem card_bits (m : ℕ) : Fintype.card (Bits m) = 2 ^ m := by
  simp [Bits]

private theorem bits_add_self {m : ℕ} (p : Bits m) : p + p = 0 :=
  funext fun j => ZMod2_add_self (p j)

theorem bits_add_add_cancel {m : ℕ} (p a : Bits m) : p + (p + a) = a := by
  rw [← add_assoc, bits_add_self, zero_add]

private theorem dot_comm {m : ℕ} (u v : Bits m) : dot u v = dot v u :=
  sum_congr rfl fun _ _ => mul_comm _ _

section Walsh

variable {K : Type*} [Field K]

variable (K) in
/-- The Hadamard matrix `[[1, 1], [1, −1]]` in every coordinate (`ZMod 2` is `Fin 2`). -/
def hadamard (m : ℕ) : Fin m → Fin 2 → Fin 2 → K := fun _ (a b : ZMod 2) => sgnB (a * b)

theorem hadamard_prod {m : ℕ} (k p : Bits m) :
    ∏ j, hadamard K m j (k j) (p j) = (sgnB (dot k p) : K) := by
  rw [dot, sgnB_sum]
  rfl

variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜}

/-- **Fast Walsh–Hadamard transform.** All `2^m` values `Σ_p (−1)^{k·p} v_p` of available values
`v`, with `5 m 2^m` gates. -/
theorem walsh_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp) {B : Set 𝒜} {m : ℕ} (v : Bits m → 𝒜)
    (hv : ∀ p, v p ∈ B) :
    Reach inp B (Set.range fun k : Bits m => ∑ p, (sgnB (dot k p) : K) • v p) (5 * m * 2 ^ m) := by
  refine (kron_reach hc (hadamard K m) v hv).mono le_rfl ?_ le_rfl
  rintro _ ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  unfold kronTransform
  exact Fintype.sum_equiv (Equiv.refl _) _ _ fun x => by rw [hadamard_prod k x]; rfl

/-- Walsh transforms of a family of `2^m` vectors: `5 m 4^m` gates. -/
theorem walsh_family_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp) {B : Set 𝒜} {m : ℕ}
    (v : Bits m → Bits m → 𝒜) (hv : ∀ a p, v a p ∈ B) :
    Reach inp B (Set.range fun ak : Bits m × Bits m => ∑ p, (sgnB (dot ak.2 p) : K) • v ak.1 p)
      (5 * m * 4 ^ m) := by
  classical
  have h := Reach.biUnion (inp := inp) (B := B) (univ : Finset (Bits m))
    (S := fun a => Set.range fun k : Bits m => ∑ p, (sgnB (dot k p) : K) • v a p)
    (t := fun _ => 5 * m * 2 ^ m) (fun a _ => walsh_reach hc (v a) (hv a))
  refine h.mono le_rfl ?_ (le_of_eq ?_)
  · rintro _ ⟨⟨a, k⟩, rfl⟩
    exact Set.mem_biUnion (mem_univ a) ⟨k, rfl⟩
  · rw [sum_const, card_univ, card_bits, smul_eq_mul,
      show (4 : ℕ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
    ring

end Walsh

/-! ## Matrix products and the middle term at given values -/

section Subst

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜] {inp B : Set 𝒜}
  {a b c : ℕ} {I J K : Type*}

/-- All products `Σ_j X(i, j) Y(k, j)`, from a correct algorithm, at any available values. -/
theorem products_reach [Fintype J] (hc : ∀ z : ℂ, algebraMap ℂ 𝒜 z ∈ inp)
    (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b)
    (eI : Fin a ≃ I) (eJ : Fin b ≃ J) (eK : Fin c ≃ K)
    (X : I × J → 𝒜) (Y : K × J → 𝒜) (hX : ∀ x, X x ∈ B) (hY : ∀ y, Y y ∈ B) :
    Reach inp B (Set.range fun ik : I × K => ∑ j, X (ik.1, j) * Y (ik.2, j)) (91 * P.cost) := by
  let φ : FreeAlgebra ℂ (MatrixInput a b c) →ₐ[ℂ] 𝒜 := FreeAlgebra.lift ℂ
    (Sum.elim (fun ij => X (eI ij.1, eJ ij.2)) (fun jk => Y (eK jk.2, eJ jk.1)))
  have hφ : ∀ v, φ (FreeAlgebra.ι ℂ v) ∈ inp ∪ B := by
    rintro (ij | jk)
    · exact Or.inr (by simpa [φ] using hX _)
    · exact Or.inr (by simpa [φ] using hY _)
  refine ((matrixAlgorithm_reach_linear P hP hb).subst φ hφ hc).mono le_rfl ?_ le_rfl
  rintro _ ⟨⟨i, k⟩, rfl⟩
  refine ⟨_, ⟨(eI.symm i, eK.symm k), rfl⟩, ?_⟩
  simp only [φ, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr,
    Equiv.apply_symm_apply]
  exact eJ.sum_comp (fun j => X (i, j) * Y (k, j))

/-- All reversed products `Σ_j Y(k, j) X(i, j)`. -/
theorem products_reach_swapped [Fintype J] (hc : ∀ z : ℂ, algebraMap ℂ 𝒜 z ∈ inp)
    (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b)
    (eI : Fin a ≃ I) (eJ : Fin b ≃ J) (eK : Fin c ≃ K)
    (X : I × J → 𝒜) (Y : K × J → 𝒜) (hX : ∀ x, X x ∈ B) (hY : ∀ y, Y y ∈ B) :
    Reach inp B (Set.range fun ik : I × K => ∑ j, Y (ik.2, j) * X (ik.1, j)) (91 * P.cost) := by
  let φ : FreeAlgebra ℂ (MatrixInput a b c) →ₐ[ℂ] 𝒜 := FreeAlgebra.lift ℂ
    (Sum.elim (fun ij => X (eI ij.1, eJ ij.2)) (fun jk => Y (eK jk.2, eJ jk.1)))
  have hφ : ∀ v, φ (FreeAlgebra.ι ℂ v) ∈ inp ∪ B := by
    rintro (ij | jk)
    · exact Or.inr (by simpa [φ] using hX _)
    · exact Or.inr (by simpa [φ] using hY _)
  refine ((matrixAlgorithm_reach_swapped P hP hb).subst φ hφ hc).mono le_rfl ?_ le_rfl
  rintro _ ⟨⟨i, k⟩, rfl⟩
  refine ⟨_, ⟨(eI.symm i, eK.symm k), rfl⟩, ?_⟩
  simp only [φ, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr,
    Equiv.apply_symm_apply]
  exact eJ.sum_comp (fun j => Y (k, j) * X (i, j))

/-- The middle-insertion term `Σ_{i,j,k} X(i, j) Q(i, k) Y(k, j)` at any available values. -/
theorem middle_subst_reach [Fintype I] [Fintype J] [Fintype K]
    (hc : ∀ z : ℂ, algebraMap ℂ 𝒜 z ∈ inp)
    (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) (hc' : 1 ≤ c)
    (eI : Fin a ≃ I) (eJ : Fin b ≃ J) (eK : Fin c ≃ K)
    (X : I × J → 𝒜) (Y : K × J → 𝒜) (Q : I → K → 𝒜) (hX : ∀ x, X x ∈ B) (hY : ∀ y, Y y ∈ B)
    (hQ : ∀ i k, Q i k ∈ B) :
    Reach inp B {∑ i, ∑ j, ∑ k, X (i, j) * Q i k * Y (k, j)}
      (696 * P.cost + 88 * (a * c + b * c)) := by
  let φ : FreeAlgebra ℂ (MatrixInput a b c ⊕ (Fin a × Fin c)) →ₐ[ℂ] 𝒜 := FreeAlgebra.lift ℂ
    (Sum.elim (Sum.elim (fun ij => X (eI ij.1, eJ ij.2)) (fun jk => Y (eK jk.2, eJ jk.1)))
      (fun ik => Q (eI ik.1) (eK ik.2)))
  have hφ : ∀ v, φ (FreeAlgebra.ι ℂ v) ∈ inp ∪ B := by
    rintro ((ij | jk) | ik)
    · exact Or.inr (by simpa [φ] using hX _)
    · exact Or.inr (by simpa [φ] using hY _)
    · exact Or.inr (by simpa [φ] using hQ _ _)
  have h := (middle_reach P hP hb hc').subst φ hφ hc
  rw [Set.image_singleton] at h
  convert h using 2
  simp only [φ, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr]
  symm
  refine Fintype.sum_equiv eI _ (fun i => ∑ j, ∑ k, X (i, j) * Q i k * Y (k, j)) fun i => ?_
  refine Fintype.sum_equiv eJ _ (fun j => ∑ k, X (eI i, j) * Q (eI i) k * Y (k, j)) fun j => ?_
  exact Equiv.sum_comp eK (fun k => X (eI i, eJ j) * Q (eI i) k * Y (k, eJ j))

end Subst

/-! ## Regrouping a block by its labels -/

theorem sum_smul_regroup {ι κ S M : Type*} [Fintype κ] [DecidableEq κ] [Semiring S]
    [AddCommMonoid M] [Module S M] (s : Finset ι) (w : ι → S) (lab : ι → κ) (F : κ → M) :
    ∑ i ∈ s, w i • F (lab i) = ∑ k, (∑ i ∈ s, if lab i = k then w i else 0) • F k := by
  simp only [sum_smul, ite_smul, zero_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_ite_eq]
  simp

/-! ## The block matrix-multiplication oracle -/

/-- A block matrix-multiplication oracle: every product matrix and every middle insertion of
`2^m × 2^r` inputs, each within `M` gates. -/
structure BlockMM {𝒜 : Type*} [Ring 𝒜] (inp : Set 𝒜) (m r M : ℕ) : Prop where
  prod : ∀ (B : Set 𝒜) (X Y : Bits m × Bits r → 𝒜), (∀ x, X x ∈ B) → (∀ y, Y y ∈ B) →
    Reach inp B (Set.range fun pq : Bits m × Bits m => ∑ s, X (pq.1, s) * Y (pq.2, s)) M
  mid : ∀ (B : Set 𝒜) (X Y : Bits m × Bits r → 𝒜) (Q : Bits m → Bits m → 𝒜),
    (∀ x, X x ∈ B) → (∀ y, Y y ∈ B) → (∀ p q, Q p q ∈ B) →
    Reach inp B {∑ p, ∑ s, ∑ q, X (p, s) * Q p q * Y (q, s)} M

/-! ## The block -/

section Block

variable {K : Type*} [Field K] {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {m r : ℕ} {ι : Type*}

/-- `f^xy_i = λ_i Σ_p (−1)^{β_i·p} Σ_s X'(p, s) Y'(p + α_i, s)`. -/
def fxyT (X' Y' : Bits m × Bits r → 𝒜) (lam : ι → K) (α β : ι → Bits m) (i : ι) : 𝒜 :=
  lam i • ∑ p : Bits m, (sgnB (dot (β i) p) : K) • ∑ s : Bits r, X' (p, s) * Y' (p + α i, s)

/-- `f^yx_i = λ_i Σ_p (−1)^{β_i·p} Σ_s Y'(p + α_i, s) X'(p, s)`. -/
def fyxT (X' Y' : Bits m × Bits r → 𝒜) (lam : ι → K) (α β : ι → Bits m) (i : ι) : 𝒜 :=
  lam i • ∑ p : Bits m, (sgnB (dot (β i) p) : K) • ∑ s : Bits r, Y' (p + α i, s) * X' (p, s)

/-- `f^*_i(z) = λ_i Σ_p (−1)^{β_i·p} Σ_s X'(p, s) z Y'(p + α_i, s)`. -/
def fstarT (X' Y' : Bits m × Bits r → 𝒜) (lam : ι → K) (α β : ι → Bits m) (i : ι) (z : 𝒜) : 𝒜 :=
  lam i • ∑ p : Bits m, (sgnB (dot (β i) p) : K) • ∑ s : Bits r, X' (p, s) * z * Y' (p + α i, s)

variable (K) in
/-- The Walsh coefficient of `M[p, q] = Σ_s X'(p, s) Y'(q, s)` at the label `(a, b)`. -/
def walshXY (X' Y' : Bits m × Bits r → 𝒜) (a b : Bits m) : 𝒜 :=
  ∑ p : Bits m, (sgnB (dot b p) : K) • ∑ s : Bits r, X' (p, s) * Y' (p + a, s)

variable (K) in
/-- The Walsh coefficient of `M'[p, q] = Σ_s Y'(q, s) X'(p, s)` at the label `(a, b)`. -/
def walshYX (X' Y' : Bits m × Bits r → 𝒜) (a b : Bits m) : 𝒜 :=
  ∑ p : Bits m, (sgnB (dot b p) : K) • ∑ s : Bits r, Y' (p + a, s) * X' (p, s)

variable (K) in
/-- The middle-insertion form at the label `(a, b)`. -/
def midForm (X' Y' : Bits m × Bits r → 𝒜) (a b : Bits m) (z : 𝒜) : 𝒜 :=
  ∑ p : Bits m, (sgnB (dot b p) : K) • ∑ s : Bits r, X' (p, s) * z * Y' (p + a, s)

/-- The block's coefficient at the label `κ`: `Σ_{i ∈ blk, (α_i, β_i) = κ} c_i λ_i² / 2`. -/
def blockCoeff (blk : Finset ι) (c lam : ι → K) (α β : ι → Bits m) (κ : Bits m × Bits m) : K :=
  ∑ i ∈ blk, if (α i, β i) = κ then c i * (2⁻¹ * (lam i * lam i)) else 0

theorem midForm_smul (X' Y' : Bits m × Bits r → 𝒜) (a b : Bits m) (w : K) (z : 𝒜) :
    midForm K X' Y' a b (w • z) = w • midForm K X' Y' a b z := by
  simp only [midForm, smul_sum, mul_smul_comm, smul_mul_assoc]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => smul_comm _ _ _

theorem block_term (X' Y' : Bits m × Bits r → 𝒜) (c lam : ι → K) (α β : ι → Bits m) (i : ι) :
    c i • ((2 : K)⁻¹ • (fxyT X' Y' lam α β i * fxyT X' Y' lam α β i +
      fstarT X' Y' lam α β i (fyxT X' Y' lam α β i))) =
    (c i * (2⁻¹ * (lam i * lam i))) •
      (walshXY K X' Y' (α i) (β i) * walshXY K X' Y' (α i) (β i) +
        midForm K X' Y' (α i) (β i) (walshYX K X' Y' (α i) (β i))) := by
  have h₁ : fxyT X' Y' lam α β i = lam i • walshXY K X' Y' (α i) (β i) := rfl
  have h₂ : fyxT X' Y' lam α β i = lam i • walshYX K X' Y' (α i) (β i) := rfl
  have h₃ : ∀ z, fstarT X' Y' lam α β i z = lam i • midForm K X' Y' (α i) (β i) z := fun _ => rfl
  rw [h₃, h₂, h₁, midForm_smul, smul_mul_assoc, mul_smul_comm]
  module

/-- **The block regrouped by labels.** The squares become one linear combination of `W_κ W_κ`,
and the middle terms one middle form per label. -/
theorem block_sum_eq (X' Y' : Bits m × Bits r → 𝒜) (blk : Finset ι) (c lam : ι → K)
    (α β : ι → Bits m) :
    ∑ i ∈ blk, c i • ((2 : K)⁻¹ • (fxyT X' Y' lam α β i * fxyT X' Y' lam α β i +
      fstarT X' Y' lam α β i (fyxT X' Y' lam α β i))) =
    ∑ κ : Bits m × Bits m, blockCoeff blk c lam α β κ •
        (walshXY K X' Y' κ.1 κ.2 * walshXY K X' Y' κ.1 κ.2) +
      ∑ κ : Bits m × Bits m, midForm K X' Y' κ.1 κ.2
        (blockCoeff blk c lam α β κ • walshYX K X' Y' κ.1 κ.2) := by
  classical
  refine (sum_congr rfl fun i _ => block_term X' Y' c lam α β i).trans ?_
  refine (sum_smul_regroup blk (fun i => c i * (2⁻¹ * (lam i * lam i))) (fun i => (α i, β i))
    (fun κ => walshXY K X' Y' κ.1 κ.2 * walshXY K X' Y' κ.1 κ.2 +
      midForm K X' Y' κ.1 κ.2 (walshYX K X' Y' κ.1 κ.2))).trans ?_
  simp only [smul_add, sum_add_distrib, ← midForm_smul]
  rfl

/-- **One middle matrix.** The middle forms of all labels are a single middle insertion
`Σ_{p,s,q} X'(p, s) Q[p, q] Y'(q, s)` with `Q[p, q] = Σ_b (−1)^{p·b} g(p + q, b)`. -/
theorem midForm_sum (X' Y' : Bits m × Bits r → 𝒜) (g : Bits m × Bits m → 𝒜) :
    ∑ κ : Bits m × Bits m, midForm K X' Y' κ.1 κ.2 (g κ) =
      ∑ p : Bits m, ∑ s : Bits r, ∑ q : Bits m,
        X' (p, s) * (∑ b : Bits m, (sgnB (dot p b) : K) • g (p + q, b)) * Y' (q, s) := by
  have hR : ∀ p s, ∑ q : Bits m,
      X' (p, s) * (∑ b, (sgnB (dot p b) : K) • g (p + q, b)) * Y' (q, s) =
      ∑ a : Bits m, ∑ b : Bits m, (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s)) := by
    intro p s
    refine (Equiv.sum_comp (Equiv.addLeft p)
      (fun q => X' (p, s) * (∑ b, (sgnB (dot p b) : K) • g (p + q, b)) * Y' (q, s))).symm.trans ?_
    refine sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_addLeft, bits_add_add_cancel, mul_sum, sum_mul, mul_smul_comm,
      smul_mul_assoc, dot_comm p]
  simp only [hR, Fintype.sum_prod_type, midForm, smul_sum]
  calc ∑ a : Bits m, ∑ b : Bits m, ∑ p : Bits m, ∑ s : Bits r,
        (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s))
      = ∑ a : Bits m, ∑ p : Bits m, ∑ b : Bits m, ∑ s : Bits r,
        (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s)) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ p : Bits m, ∑ a : Bits m, ∑ b : Bits m, ∑ s : Bits r,
        (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s)) := sum_comm
    _ = ∑ p : Bits m, ∑ a : Bits m, ∑ s : Bits r, ∑ b : Bits m,
        (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s)) :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ p : Bits m, ∑ s : Bits r, ∑ a : Bits m, ∑ b : Bits m,
        (sgnB (dot b p) : K) • (X' (p, s) * g (a, b) * Y' (p + a, s)) :=
        sum_congr rfl fun _ _ => sum_comm

end Block

/-- The gate count of `block_assembly_gen`: three oracle calls plus `15 (m + 1) 4^m + 2`. -/
def blockGenCost (m M : ℕ) : ℕ := 3 * M + 15 * (m + 1) * 4 ^ m + 2

/-- **Block assembly over any field.** From transformed inputs `X'`, `Y'` and a block
matrix-multiplication oracle with `M` gates per call, the block sum of squares
`Σ_{i ∈ blk} c_i · ½ (f^xy_i f^xy_i + f^*_i(f^yx_i))` takes `3 M + 15 (m + 1) 4^m + 2` gates,
whatever the size of the block. -/
theorem block_assembly_gen {K : Type*} [Field K] {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜]
    {inp B : Set 𝒜} (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp) {m r M : ℕ}
    (X' Y' : Bits m × Bits r → 𝒜) (hX : ∀ x, X' x ∈ B) (hY : ∀ y, Y' y ∈ B) (hMM : BlockMM inp m r M)
    {ι : Type*} (blk : Finset ι) (c lam : ι → K) (α β : ι → Bits m) :
    Reach inp B {∑ i ∈ blk, c i • ((2 : K)⁻¹ • (fxyT X' Y' lam α β i * fxyT X' Y' lam α β i +
        fstarT X' Y' lam α β i (fyxT X' Y' lam α β i)))} (blockGenCost m M) := by
  classical
  have h4 : (2 : ℕ) ^ m * 2 ^ m = 4 ^ m := by rw [← mul_pow]; norm_num
  have hcard : Fintype.card (Bits m × Bits m) = 4 ^ m := by
    rw [Fintype.card_prod, card_bits, h4]
  let d := blockCoeff blk c lam α β
  -- the values computed along the way
  let Mv : Bits m × Bits m → 𝒜 := fun pq => ∑ s, X' (pq.1, s) * Y' (pq.2, s)
  let Nv : Bits m × Bits m → 𝒜 := fun pq => ∑ s, Y' (pq.1, s) * X' (pq.2, s)
  let Wv : Bits m × Bits m → 𝒜 := fun κ => walshXY K X' Y' κ.1 κ.2
  let Vv : Bits m × Bits m → 𝒜 := fun κ => walshYX K X' Y' κ.1 κ.2
  let Sv : Bits m × Bits m → 𝒜 := fun κ => Wv κ * Wv κ
  let Gv : Bits m × Bits m → 𝒜 := fun κ => d κ • Vv κ
  let Qv : Bits m × Bits m → 𝒜 := fun ak => ∑ b, (sgnB (dot ak.2 b) : K) • Gv (ak.1, b)
  let sq : 𝒜 := ∑ κ, d κ • Sv κ
  let mid : 𝒜 := ∑ p, ∑ s, ∑ q, X' (p, s) * Qv (p + q, p) * Y' (q, s)
  have key : ∑ i ∈ blk, c i • ((2 : K)⁻¹ • (fxyT X' Y' lam α β i * fxyT X' Y' lam α β i +
      fstarT X' Y' lam α β i (fyxT X' Y' lam α β i))) = sq + mid := by
    rw [block_sum_eq]
    congr 1
    exact midForm_sum X' Y' Gv
  rw [key]
  -- the circuits
  have hM : Reach inp B (Set.range Mv) M := hMM.prod B X' Y' hX hY
  have hN : Reach inp B (Set.range Nv) M := hMM.prod B Y' X' hY hX
  have hW : Reach inp (B ∪ Set.range Mv) (Set.range Wv) (5 * m * 4 ^ m) :=
    walsh_family_reach hc (fun a p => Mv (p, p + a)) fun _ _ => Or.inr ⟨_, rfl⟩
  have hV : Reach inp (B ∪ Set.range Nv) (Set.range Vv) (5 * m * 4 ^ m) :=
    walsh_family_reach hc (fun a p => Nv (p + a, p)) fun _ _ => Or.inr ⟨_, rfl⟩
  have hS : Reach inp (Set.range Wv) (Set.range Sv) (4 ^ m * 1) := by
    rw [← hcard]
    exact reach_range (f := Sv) fun κ =>
      Reach.mul (B := Set.range Wv) (p := Wv κ) (q := Wv κ) ⟨κ, rfl⟩ ⟨κ, rfl⟩
  have hG : Reach inp (Set.range Vv) (Set.range Gv) (4 ^ m * 2) := by
    rw [← hcard]
    exact reach_range (f := Gv) fun κ =>
      reach_smul hc (B := Set.range Vv) (u := Vv κ) ⟨κ, rfl⟩ (d κ)
  have hQ : Reach inp (Set.range Gv) (Set.range Qv) (5 * m * 4 ^ m) :=
    walsh_family_reach hc (fun a b => Gv (a, b)) fun _ _ => ⟨_, rfl⟩
  have hsq : Reach inp (Set.range Sv) {sq} (3 * 4 ^ m + 1) := by
    have h := reach_smulSum hc (univ : Finset (Bits m × Bits m)) (B := Set.range Sv) (c := d)
      (p := Sv) fun κ _ => ⟨κ, rfl⟩
    rwa [card_univ, hcard] at h
  have hmid : Reach inp (B ∪ Set.range Qv) {mid} M :=
    hMM.mid (B ∪ Set.range Qv) X' Y' (fun p q => Qv (p + q, p))
      (fun x => Or.inl (hX x)) (fun y => Or.inl (hY y)) (fun _ _ => Or.inr ⟨_, rfl⟩)
  -- composition
  have hall := (((((hM.union hN).trans
      ((hW.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl).union
        (hV.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl))).trans
      ((hS.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl).union
        (hG.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl))).trans
      (hQ.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl)).trans
      ((hsq.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl).union
        (hmid.mono (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto) le_rfl le_rfl))).seq
      (Reach.add (p := sq) (q := mid) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))))
  refine hall.mono le_rfl le_rfl ?_
  unfold blockGenCost
  nlinarith [Nat.zero_le (4 ^ m)]

/-! ## Over `ℂ`: a correct program is a block oracle -/

section Complex

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜] {inp : Set 𝒜}

/-- **A correct program is a block oracle.** A correct algorithm `P` for the `2^m × 2^r` by
`2^r × 2^m` product gives every block product and middle insertion within `960 · cost(P)` gates:
`91 · cost(P)` for products, and `696 · cost(P) + 88 (4^m + 2^r 2^m)` for the middle insertion,
with `4^m ≤ cost(P)` (output size) and `2^r 2^m ≤ 2 · cost(P)` (`inner_mul_le_two_mul_cost`). -/
theorem blockMM_of_algorithm (hc : ∀ z : ℂ, algebraMap ℂ 𝒜 z ∈ inp) {m r : ℕ}
    (P : MatrixAlgorithm ℂ (2 ^ m) (2 ^ r) (2 ^ m)) (hP : P.Correct) :
    BlockMM inp m r (960 * P.cost) := by
  classical
  let eM : Fin (2 ^ m) ≃ Bits m := (Fintype.equivFinOfCardEq (card_bits m)).symm
  let eR : Fin (2 ^ r) ≃ Bits r := (Fintype.equivFinOfCardEq (card_bits r)).symm
  have hr1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hout : 2 ^ m * 2 ^ m ≤ P.cost := P.output_size_le_cost hr1 hP
  have hlow : 2 ^ r * 2 ^ m ≤ 2 * P.cost := inner_mul_le_two_mul_cost P hP hm1
  refine ⟨fun B X Y hX hY => ?_, fun B X Y Q hX hY hQ => ?_⟩
  · exact (products_reach hc P hP hr1 eM eR eM X Y hX hY).mono le_rfl le_rfl (by omega)
  · refine (middle_subst_reach hc P hP hr1 hm1 eM eR eM X Y Q hX hY hQ).mono le_rfl le_rfl ?_
    nlinarith [hout, hlow]

/-- **Block assembly over `ℂ`.** From transformed inputs `X'`, `Y'` and a correct algorithm `P`
for the `2^m × 2^r` by `2^r × 2^m` product, the block sum of squares
`Σ_{i ∈ blk} c_i · ½ (f^xy_i f^xy_i + f^*_i(f^yx_i))` takes
`2880 · cost(P) + 15 (m + 1) 4^m + 2` gates, whatever the size of the block. -/
theorem block_assembly {m r : ℕ} {ι : Type*} {B : Set 𝒜} (hc : ∀ z : ℂ, algebraMap ℂ 𝒜 z ∈ inp)
    (X' Y' : Bits m × Bits r → 𝒜) (hX : ∀ x, X' x ∈ B) (hY : ∀ y, Y' y ∈ B)
    (P : MatrixAlgorithm ℂ (2 ^ m) (2 ^ r) (2 ^ m)) (hP : P.Correct)
    (blk : Finset ι) (c lam : ι → ℂ) (α β : ι → Bits m) :
    Reach inp B {∑ i ∈ blk, c i • ((2 : ℂ)⁻¹ • (fxyT X' Y' lam α β i * fxyT X' Y' lam α β i +
        fstarT X' Y' lam α β i (fyxT X' Y' lam α β i)))}
      (2880 * P.cost + 15 * (m + 1) * 4 ^ m + 2) :=
  (block_assembly_gen hc X' Y' hX hY (blockMM_of_algorithm hc P hP) blk c lam α β).mono
    le_rfl le_rfl (le_of_eq (by unfold blockGenCost; ring))

end Complex

end IDMM
