import IDMM.BilinearExtraction
import IDMM.SourceAccounting
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

noncomputable section
namespace IDMM
open PauliCubes Finset
open OAI.MatrixMultiplication.Arithmetic
variable {A B : Type*} [Fintype A] [Fintype B]

/-- The three nonconstant components tracked for each register. -/
def parts (p : Poly A B) : Set (NC A B) :=
  {leftPart p} ∪ {rightPart p} ∪ {orderedPart p}

private theorem const_input (z : ℂ) :
    algebraMap ℂ (NC A B) z ∈ ncInputs ℂ (A ⊕ B) := Or.inr ⟨z,rfl⟩

private theorem zero_input : (0 : NC A B) ∈ ncInputs ℂ (A ⊕ B) := by
  simpa using const_input (A := A) (B := B) 0

private theorem reach_two {D : Set (NC A B)} {x y : NC A B}
    (hx : x ∈ D) (hy : y ∈ D) (a b : ℂ) :
    Reach (ncInputs ℂ (A ⊕ B)) D {a • x + b • y} 7 := by
  have h := Reach.linComb (inp := ncInputs ℂ (A ⊕ B)) zero_input
    (univ : Finset (Fin 2)) (c := ![algebraMap ℂ (NC A B) a, algebraMap ℂ (NC A B) b])
    (p := ![x,y]) (by intro i _; fin_cases i <;> exact const_input _)
    (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two, Algebra.smul_def] using h

private theorem parts_add {D : Set (NC A B)} (p q : Poly A B)
    (hp : parts p ⊆ D) (hq : parts q ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D (parts (p+q)) 3 := by
  have h₁ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := leftPart p) (q := leftPart q)
  have h₂ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := rightPart p) (q := rightPart q)
  have h₃ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := orderedPart p) (q := orderedPart q)
  simpa [parts] using (h₁.union h₂).union h₃

private theorem parts_sub {D : Set (NC A B)} (p q : Poly A B)
    (hp : parts p ⊆ D) (hq : parts q ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D (parts (p-q)) 21 := by
  have h₁ := reach_two (hp (by simp [parts])) (hq (by simp [parts])) 1 (-1)
    (x := leftPart p) (y := leftPart q)
  have h₂ := reach_two (hp (by simp [parts])) (hq (by simp [parts])) 1 (-1)
    (x := rightPart p) (y := rightPart q)
  have h₃ := reach_two (hp (by simp [parts])) (hq (by simp [parts])) 1 (-1)
    (x := orderedPart p) (y := orderedPart q)
  change Reach _ D ({leftPart (p-q)} ∪ {rightPart (p-q)} ∪ {orderedPart (p-q)}) 21
  rw [leftPart_sub, rightPart_sub, orderedPart_sub]
  simpa only [one_smul, neg_smul, sub_eq_add_neg] using (h₁.union h₂).union h₃

private theorem parts_mul {D : Set (NC A B)} (p q : Poly A B)
    (hp : parts p ⊆ D) (hq : parts q ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D (parts (p*q)) 29 := by
  have h₁ := reach_two (hp (by simp [parts])) (hq (by simp [parts]))
    (scalarPart q) (scalarPart p) (x := leftPart p) (y := leftPart q)
  have h₂ := reach_two (hp (by simp [parts])) (hq (by simp [parts]))
    (scalarPart q) (scalarPart p) (x := rightPart p) (y := rightPart q)
  have hc₁ := Reach.mul (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := leftPart p) (q := rightPart q)
  have hc₂ := Reach.mul (inp := ncInputs ℂ (A ⊕ B))
    (hq (by simp [parts])) (hp (by simp [parts])) (p := leftPart q) (q := rightPart p)
  let T : Set (NC A B) := {leftPart p * rightPart q} ∪ {leftPart q * rightPart p}
  have hc : Reach (ncInputs ℂ (A ⊕ B)) D T 2 := hc₁.union hc₂
  have hs := Reach.linComb (inp := ncInputs ℂ (A ⊕ B)) (B := D ∪ T) zero_input
    (univ : Finset (Fin 4))
    (c := ![algebraMap ℂ (NC A B) (scalarPart q), 1, 1, algebraMap ℂ (NC A B) (scalarPart p)])
    (p := ![orderedPart p, leftPart p * rightPart q, leftPart q * rightPart p, orderedPart q])
    (by intro i _; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons];
        all_goals first | exact const_input _ | simpa using const_input (A := A) (B := B) 1)
    (by
      intro i _
      fin_cases i
      · exact Or.inl (hp (by simp [parts]))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (hq (by simp [parts])))
  have h₃ : Reach (ncInputs ℂ (A ⊕ B)) D {orderedPart (p*q)} 15 := by
    convert hc.seq hs using 1 <;>
      simp [Fin.sum_univ_succ, orderedPart_mul, Algebra.smul_def, add_assoc]
  have h₁' : Reach (ncInputs ℂ (A ⊕ B)) D {leftPart (p*q)} 7 := by
    simpa [leftPart_mul] using h₁
  have h₂' : Reach (ncInputs ℂ (A ⊕ B)) D {rightPart (p*q)} 7 := by
    simpa [rightPart_mul] using h₂
  exact (h₁'.union h₂').union h₃

/-- All register components remain available with at most 30 gates per charged source gate.
Constants are precomputed scalar parts, not variable-dependent work. -/
theorem program_parts {r : ℕ} (p : Program ℂ (A ⊕ B) r) :
    Reach (ncInputs ℂ (A ⊕ B)) (ncInputs ℂ (A ⊕ B))
      (⋃ j, parts (polynomialProgram p j)) (30*p.cost) := by
  induction p with
  | nil => exact Reach.refl (by simp)
  | @step r p g ih =>
    let S := ⋃ j, parts (polynomialProgram p j)
    let D := ncInputs ℂ (A ⊕ B) ∪ S
    have hp (j : Fin r) : parts (polynomialProgram p j) ⊆ D := by
      intro x hx; exact Or.inr (Set.mem_iUnion.mpr ⟨j,hx⟩)
    have hg : Reach (ncInputs ℂ (A ⊕ B)) D
        (parts (polynomialGate g (polynomialProgram p))) (30*g.cost) := by
      cases g with
      | constant c =>
        apply Reach.refl
        intro x hx
        have hx0 : x = 0 := by simpa [parts, polynomialGate] using hx
        subst x
        exact Or.inl zero_input
      | input i =>
        apply Reach.refl
        intro x hx
        cases i with
        | inl i =>
          simp only [parts, polynomialGate, leftPart_X_left, rightPart_X_left, orderedPart_X,
            Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with (rfl | rfl) | rfl
          · exact Or.inl (Or.inl ⟨.inl i,rfl⟩)
          · exact Or.inl zero_input
          · exact Or.inl zero_input
        | inr i =>
          simp only [parts, polynomialGate, leftPart_X_right, rightPart_X_right, orderedPart_X,
            Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with (rfl | rfl) | rfl
          · exact Or.inl zero_input
          · exact Or.inl (Or.inl ⟨.inr i,rfl⟩)
          · exact Or.inl zero_input
      | add i j => exact (parts_add _ _ (hp i) (hp j)).mono le_rfl le_rfl (by simp [Gate.cost])
      | sub i j => exact (parts_sub _ _ (hp i) (hp j)).mono le_rfl le_rfl (by simp [Gate.cost])
      | mul i j => exact (parts_mul _ _ (hp i) (hp j)).mono le_rfl le_rfl (by simp [Gate.cost])
    refine (ih.trans hg).mono le_rfl ?_ ?_
    · intro x hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
      refine Fin.cases ?_ (fun j => ?_) j hj
      · intro hj; exact Or.inr hj
      · intro hj; exact Or.inl (Set.mem_iUnion.mpr ⟨j,hj⟩)
    · simp only [Program.cost]
      omega

/-- The requested bridge, preserving sharing across all matrix-product entries. -/
theorem matrixAlgorithm_reach {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) :
    Reach (ncInputs ℂ (MatrixInput a b c)) ∅
      (Set.range (fun ik : Fin a × Fin c =>
        ∑ j : Fin b, FreeAlgebra.ι ℂ (.inl (ik.1,j)) * FreeAlgebra.ι ℂ (.inr (j,ik.2))))
      (90*P.cost + a*c) := by
  have h := reach_charge_sources (program_parts P.program)
    (fun ik : Fin a × Fin c => orderedPart (polynomialProgram P.program (P.output ik.1 ik.2)))
    (by intro ik; apply Set.mem_iUnion.mpr; exact ⟨P.output ik.1 ik.2, by simp [parts]⟩)
  simpa [orderedPart_correct P hP, Fintype.card_prod, MatrixAlgorithm.cost, ← Nat.mul_assoc] using h
/-- A genuine constant-factor bridge when the inner dimension is positive. -/
theorem matrixAlgorithm_reach_linear {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c)
    (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (ncInputs ℂ (MatrixInput a b c)) ∅
      (Set.range (fun ik : Fin a × Fin c =>
        ∑ j : Fin b, FreeAlgebra.ι ℂ (.inl (ik.1,j)) * FreeAlgebra.ι ℂ (.inr (j,ik.2))))
      (91*P.cost) := by
  have hout := P.output_size_le_cost hb hP
  exact (matrixAlgorithm_reach P hP).mono le_rfl le_rfl (by omega)

/-- Individual `NCSizeLE` corollary, obtained from the shared multi-output circuit. -/
theorem matrixAlgorithm_ncSizeLE {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c)
    (hP : P.Correct) (hb : 1 ≤ b) (i : Fin a) (k : Fin c) :
    NCSizeLE (∑ j : Fin b,
      FreeAlgebra.ι ℂ (Sum.inl (i,j) : MatrixInput a b c) *
      FreeAlgebra.ι ℂ (Sum.inr (j,k) : MatrixInput a b c)) (91*P.cost) := by
  apply Reach.ncSizeLE
  exact (matrixAlgorithm_reach_linear P hP hb).mono le_rfl
    (Set.singleton_subset_iff.mpr ⟨(i,k),rfl⟩) le_rfl
end IDMM
