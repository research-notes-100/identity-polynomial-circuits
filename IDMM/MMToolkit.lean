/-
Matrix-multiplication toolkit for the middle-insertion term of Hrubeš's Lemma 22.

* `Reach.subst`: plug available values into the variables of a noncommutative circuit.
* `matrixAlgorithm_reach_swapped`: the reversed products `Σ_j B_jk A_ij` at `O(P.cost)`.
* `middle_reach`: `Σ_{i,j,k} A_ij Q_ik B_jk` (Q in the middle) at `696 P.cost + 88 (ac + bc)`,
  for `1 ≤ b` and `1 ≤ c` (`middle_reach_needs_c`: the second hypothesis cannot be dropped;
  `middle_reach_add_one` drops it at the price of `+ 1`).

The middle term is obtained by reverse-mode differentiation (Baur–Strassen) of
`F = Σ_{i,k} Q_ik (AB)_ik`, carried out on commutative circuits (`Reach` over `MvPolynomial`,
`adjoint_reach`): `∂F/∂B_jk = Σ_i A_ij Q_ik`. Those derivatives are then transported to
noncommutative circuits by the ordered bilinear extraction of `IDMM.BilinearExtraction`
(`reach_parts`), with the `A` variables before the `B` and `Q` variables, and finally
`G = Σ_{j,k} g_jk B_jk`.
-/
import IDMM.BridgeCost
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
namespace IDMM
open PauliCubes Finset MvPolynomial
open OAI.MatrixMultiplication.Arithmetic

/-! ## Available values and substitution -/

/-- Values already available never need to be listed. -/
theorem reach_of_subset_avail {R : Type*} [Ring R] {inp B S S' : Set R} {s : ℕ}
    (h : Reach inp B S s) (hS : S' ⊆ B ∪ S) : Reach inp B S' s := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  refine ⟨gs, hb, hl, fun x hx => ?_⟩
  rcases hS hx with h | h
  · exact Or.inl h
  · exact hc h

section Subst

variable {K V 𝒜 : Type*} [CommRing K] [Ring 𝒜] [Algebra K 𝒜] {inp B : Set 𝒜}

theorem builds_subst (φ : FreeAlgebra K V →ₐ[K] 𝒜) (hin : φ '' ncInputs K V ⊆ inp ∪ B) :
    ∀ {gs : List (FreeAlgebra K V)} {D : Set (FreeAlgebra K V)}, Builds (ncInputs K V) D gs →
      Reach inp (B ∪ φ '' D) (φ '' {x | x ∈ gs}) gs.length
  | [], _, _ => Reach.refl (by simp)
  | g :: gs, D, ⟨hg, hgs⟩ => by
    have h₁ : Reach inp (B ∪ φ '' D) {φ g} 1 := by
      rcases hg with hg | ⟨p, hp, q, hq, rfl | rfl⟩
      · apply IDMM.reach_source
        rcases hin ⟨g, hg, rfl⟩ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rw [map_add]; exact Reach.add (Or.inr ⟨p, hp, rfl⟩) (Or.inr ⟨q, hq, rfl⟩)
      · rw [map_mul]; exact Reach.mul (Or.inr ⟨p, hp, rfl⟩) (Or.inr ⟨q, hq, rfl⟩)
    have h₂ := (builds_subst φ hin hgs).mono (B' := (B ∪ φ '' D) ∪ {φ g})
      (by rw [Set.image_insert_eq]; intro x hx; aesop) le_rfl le_rfl
    refine (h₁.trans h₂).mono le_rfl ?_ (by simp; omega)
    rintro _ ⟨x, hx, rfl⟩
    simp only [List.mem_cons, Set.mem_ofPred_eq] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx, rfl⟩

/-- **Substitution.** A noncommutative circuit over the free algebra can be evaluated at any values:
if every variable is sent to an input or an available value, and every constant is an input, the
image of the circuit has no more gates than the circuit itself. -/
theorem _root_.PauliCubes.Reach.subst {S : Set (FreeAlgebra K V)} {s : ℕ}
    (h : Reach (ncInputs K V) ∅ S s) (φ : FreeAlgebra K V →ₐ[K] 𝒜)
    (hφ : ∀ v, φ (FreeAlgebra.ι K v) ∈ inp ∪ B) (hconst : ∀ c : K, algebraMap K 𝒜 c ∈ inp) :
    Reach inp B (φ '' S) s := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  have hin : φ '' ncInputs K V ⊆ inp ∪ B := by
    rintro _ ⟨x, ⟨v, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · exact hφ v
    · exact Or.inl (by rw [AlgHom.commutes]; exact hconst c)
  refine ((builds_subst φ hin hb).mono (by simp) le_rfl hl).mono le_rfl ?_ le_rfl
  rintro _ ⟨x, hx, rfl⟩
  rcases hc hx with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact ⟨x, h, rfl⟩

end Subst

/-- Renaming variables carries circuits along, gate for gate. -/
theorem reach_relabel {K V V' : Type*} [CommRing K] (σ : V → V') {S : Set (FreeAlgebra K V)}
    {s : ℕ} (h : Reach (ncInputs K V) ∅ S s) :
    Reach (ncInputs K V') ∅ (FreeAlgebra.lift K (fun v => FreeAlgebra.ι K (σ v)) '' S) s := by
  have h' := h.subst (FreeAlgebra.lift K (fun v => FreeAlgebra.ι K (σ v)))
    (inp := ncInputs K V') (B := ∅) (fun v => Or.inl (Or.inl ⟨σ v, by simp⟩))
    (fun c => Or.inr ⟨c, rfl⟩)
  exact h'

/-! ## Relabeling the inputs of an OpenAI program -/

section Relabel

variable {F I J : Type*} [Field F]

/-- Rename the input variables read by a gate. -/
def relabelGate {r : ℕ} (e : I → J) : Gate F I (Fin r) → Gate F J (Fin r)
  | .constant z => .constant z
  | .input i => .input (e i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

/-- Rename the input variables read by a program. -/
def relabelProgram (e : I → J) : {r : ℕ} → Program F I r → Program F J r
  | 0, .nil => .nil
  | _ + 1, .step p g => .step (relabelProgram e p) (relabelGate e g)

theorem polynomialProgram_step_zero {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    polynomialProgram (p.step g) 0 = polynomialGate g (polynomialProgram p) := rfl

theorem polynomialProgram_step_succ {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r))
    (t : Fin r) : polynomialProgram (p.step g) t.succ = polynomialProgram p t := rfl

theorem polynomialProgram_relabel (e : I → J) {r : ℕ} (p : Program F I r) (t : Fin r) :
    polynomialProgram (relabelProgram e p) t = rename e (polynomialProgram p t) := by
  induction p with
  | nil => exact Fin.elim0 t
  | step p g ih =>
    refine Fin.cases ?_ (fun t => ?_) t
    · change polynomialGate (relabelGate e g) (polynomialProgram (relabelProgram e p)) =
        rename e (polynomialGate g (polynomialProgram p))
      rw [funext ih]
      cases g <;> simp [polynomialGate, relabelGate]
    · exact ih t

omit [Field F] in
theorem cost_relabel (e : I → J) {r : ℕ} (p : Program F I r) :
    (relabelProgram e p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih =>
    change (relabelProgram e p).cost + (relabelGate e g).cost = p.cost + g.cost
    rw [ih]
    cases g <;> rfl

end Relabel

/-! ## The reversed products `Σ_j B_jk A_ij` -/

theorem orderedPart_swapped {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct)
    (i : Fin a) (k : Fin c) :
    orderedPart (polynomialProgram (relabelProgram Sum.swap P.program) (P.output i k)) =
      ∑ j : Fin b, FreeAlgebra.ι ℂ (.inl (j,k)) * FreeAlgebra.ι ℂ (.inr (i,j)) := by
  rw [polynomialProgram_relabel, correct_polynomial P hP, map_sum, orderedPart_sum]
  simp [orderedPart_mul]

/-- The reversed matrix product, `B` before `A`, with one shared circuit for all entries. -/
theorem matrixAlgorithm_reach_swapped_add {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c)
    (hP : P.Correct) :
    Reach (ncInputs ℂ (MatrixInput a b c)) ∅
      (Set.range (fun ik : Fin a × Fin c =>
        ∑ j : Fin b, FreeAlgebra.ι ℂ (.inr (j,ik.2)) * FreeAlgebra.ι ℂ (.inl (ik.1,j))))
      (90*P.cost + a*c) := by
  have h := reach_charge_sources (program_parts (relabelProgram Sum.swap P.program))
    (fun ik : Fin a × Fin c =>
      orderedPart (polynomialProgram (relabelProgram Sum.swap P.program) (P.output ik.1 ik.2)))
    (by intro ik; apply Set.mem_iUnion.mpr; exact ⟨P.output ik.1 ik.2, by simp [parts]⟩)
  have h' := reach_relabel (K := ℂ) (Sum.swap : (Fin b × Fin c) ⊕ (Fin a × Fin b) → _) h
  rw [← Set.range_comp] at h'
  refine h'.mono le_rfl ?_ ?_
  · rintro _ ⟨ik, rfl⟩
    refine ⟨ik, ?_⟩
    simp [orderedPart_swapped P hP]
  · simp [cost_relabel, Fintype.card_prod, MatrixAlgorithm.cost, ← Nat.mul_assoc]

/-- **Swapped bridge.** The same bound as `matrixAlgorithm_reach_linear`, for `Σ_j B_jk A_ij`. -/
theorem matrixAlgorithm_reach_swapped {a b c : ℕ} (P : MatrixAlgorithm ℂ a b c)
    (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (ncInputs ℂ (MatrixInput a b c)) ∅
      (Set.range (fun ik : Fin a × Fin c =>
        ∑ j : Fin b, FreeAlgebra.ι ℂ (.inr (j,ik.2)) * FreeAlgebra.ι ℂ (.inl (ik.1,j))))
      (91*P.cost) := by
  have hout := P.output_size_le_cost hb hP
  exact (matrixAlgorithm_reach_swapped_add P hP).mono le_rfl le_rfl (by omega)

/-! ## Commutative circuits -/

section Commutative

variable {I : Type*}

/-- The inputs of a commutative circuit: the variables and the constants. -/
def cInputs (I : Type*) : Set (MvPolynomial I ℂ) := Set.range X ∪ Set.range C

theorem X_mem_cInputs (i : I) : (X i : MvPolynomial I ℂ) ∈ cInputs I := Or.inl ⟨i, rfl⟩

theorem C_mem_cInputs (z : ℂ) : (C z : MvPolynomial I ℂ) ∈ cInputs I := Or.inr ⟨z, rfl⟩

theorem zero_mem_cInputs : (0 : MvPolynomial I ℂ) ∈ cInputs I := by
  simpa using C_mem_cInputs (I := I) 0

/-- A difference costs two gates: `x - y = x + (-1) y`. -/
theorem reach_sub {D : Set (MvPolynomial I ℂ)} (hD : cInputs I ⊆ D) {x y : MvPolynomial I ℂ}
    (hx : x ∈ D) (hy : y ∈ D) : Reach (cInputs I) D {x - y} 2 := by
  have h₁ : Reach (cInputs I) D {C (-1) * y} 1 := Reach.mul (hD (C_mem_cInputs _)) hy
  have h₂ : Reach (cInputs I) (D ∪ {C (-1) * y}) {x + C (-1) * y} 1 :=
    Reach.add (Or.inl hx) (Or.inr rfl)
  have h := h₁.seq h₂
  rwa [show x + C (-1) * y = x - y by simp [sub_eq_add_neg]] at h

/-- **Forward pass.** Every register of a program, with the inputs and constants available. -/
theorem forward_reach {r : ℕ} (p : Program ℂ I r) :
    Reach (cInputs I) (cInputs I) (Set.range (polynomialProgram p)) (2 * p.cost) := by
  induction p with
  | nil => exact Reach.refl (by rintro _ ⟨t, _⟩; exact Fin.elim0 t)
  | @step r p g ih =>
    let D := cInputs I ∪ Set.range (polynomialProgram p)
    have hv (t : Fin r) : polynomialProgram p t ∈ D := Or.inr ⟨t, rfl⟩
    have hg : Reach (cInputs I) D {polynomialGate g (polynomialProgram p)} (2 * g.cost) := by
      cases g with
      | constant z =>
        exact Reach.refl (Set.singleton_subset_iff.mpr (Or.inl (C_mem_cInputs z)))
      | input i =>
        exact Reach.refl (Set.singleton_subset_iff.mpr (Or.inl (X_mem_cInputs i)))
      | add i j => exact (Reach.add (hv i) (hv j)).mono le_rfl le_rfl (by simp [Gate.cost])
      | sub i j =>
        exact (reach_sub Set.subset_union_left (hv i) (hv j)).mono le_rfl le_rfl
          (by simp [Gate.cost])
      | mul i j => exact (Reach.mul (hv i) (hv j)).mono le_rfl le_rfl (by simp [Gate.cost])
    refine (ih.trans hg).mono le_rfl ?_ (by simp only [Program.cost_step]; omega)
    rintro _ ⟨t, rfl⟩
    refine Fin.cases ?_ (fun t => ?_) t
    · exact Or.inr rfl
    · exact Or.inl ⟨t, rfl⟩

/-! ### Reverse mode (Baur–Strassen) -/

/-- The reverse-mode invariant for a program `p`: weights `w` on its registers (nonzero only on
`T`) and accumulators `acc` on its inputs, all available, give every
`acc z + Σ_t w_t ∂v_t/∂z` with `6` gates per charged gate and one per weighted register. -/
def AdjGoal {r : ℕ} (p : Program ℂ I r) : Prop :=
  ∀ (w : Fin r → MvPolynomial I ℂ) (T : Finset (Fin r)) (acc : I → MvPolynomial I ℂ)
    (E : Set (MvPolynomial I ℂ)),
    cInputs I ⊆ E → (∀ t, polynomialProgram p t ∈ E) → (∀ t, w t ∈ E) → (∀ t ∉ T, w t = 0) →
    (∀ z, acc z ∈ E) →
    Reach (cInputs I) E
      (Set.range fun z => acc z + ∑ t, w t * pderiv z (polynomialProgram p t))
      (6 * p.cost + T.card)

/-- The indices `t` with `t.succ ∈ T`. -/
def tailSet {r : ℕ} (T : Finset (Fin (r + 1))) : Finset (Fin r) :=
  univ.filter fun t => t.succ ∈ T

theorem tailSet_card {r : ℕ} (T : Finset (Fin (r + 1))) :
    (tailSet T).card + (if (0 : Fin (r + 1)) ∈ T then 1 else 0) ≤ T.card := by
  have hmap : (tailSet T).map (Fin.succEmb r) ⊆ T.erase 0 := by
    intro x hx
    simp only [tailSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_succEmb] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero t, ht⟩
  have h := Finset.card_le_card hmap
  rw [Finset.card_map] at h
  split_ifs with h0
  · rw [Finset.card_erase_of_mem h0] at h
    have : 1 ≤ T.card := Finset.card_pos.mpr ⟨0, h0⟩
    omega
  · rw [Finset.erase_eq_of_notMem h0] at h
    omega

/-- One charged gate of the reverse pass: the registers `i` and `j` receive `α` and `β`. -/
theorem adj_bump {r : ℕ} (p : Program ℂ I r) (ih : AdjGoal p)
    (w : Fin r → MvPolynomial I ℂ) (T : Finset (Fin r)) (acc : I → MvPolynomial I ℂ)
    (E : Set (MvPolynomial I ℂ)) (hE : cInputs I ⊆ E) (hv : ∀ t, polynomialProgram p t ∈ E)
    (hw : ∀ t, w t ∈ E) (hT : ∀ t ∉ T, w t = 0) (hacc : ∀ z, acc z ∈ E)
    (i j : Fin r) (α β : MvPolynomial I ℂ) {k : ℕ} (hαβ : Reach (cInputs I) E ({α} ∪ {β}) k) :
    Reach (cInputs I) E
      (Set.range fun z => acc z + ((α * pderiv z (polynomialProgram p i) +
        β * pderiv z (polynomialProgram p j)) + ∑ t, w t * pderiv z (polynomialProgram p t)))
      (k + 2 + (6 * p.cost + (T.card + 2))) := by
  classical
  set v := polynomialProgram p
  let w' : Fin r → MvPolynomial I ℂ := fun t =>
    w t + (if t = i then α else 0) + (if t = j then β else 0)
  have h₂ : Reach (cInputs I) (E ∪ ({α} ∪ {β})) ({w' i} ∪ {w' j}) 2 := by
    by_cases hij : i = j
    · subst hij
      have ha : Reach (cInputs I) (E ∪ ({α} ∪ {β})) {w i + α} 1 :=
        Reach.add (Or.inl (hw i)) (Or.inr (Or.inl rfl))
      have hb : Reach (cInputs I) ((E ∪ ({α} ∪ {β})) ∪ {w i + α}) {w i + α + β} 1 :=
        Reach.add (Or.inr rfl) (Or.inl (Or.inr (Or.inr rfl)))
      have hw' : w' i = w i + α + β := by simp [w']
      rw [hw', Set.union_self]
      exact (ha.seq hb).mono le_rfl le_rfl le_rfl
    · have ha : Reach (cInputs I) (E ∪ ({α} ∪ {β})) {w' i} 1 := by
        have : w' i = w i + α := by simp [w', hij]
        rw [this]; exact Reach.add (Or.inl (hw i)) (Or.inr (Or.inl rfl))
      have hb : Reach (cInputs I) (E ∪ ({α} ∪ {β})) {w' j} 1 := by
        have : w' j = w j + β := by simp [w', Ne.symm hij]
        rw [this]; exact Reach.add (Or.inl (hw j)) (Or.inr (Or.inr rfl))
      exact ha.union hb
  have hw₂ : ∀ t, w' t ∈ E ∪ (({α} ∪ {β}) ∪ ({w' i} ∪ {w' j})) := by
    intro t
    by_cases hi : t = i
    · subst hi; exact Or.inr (Or.inr (Or.inl rfl))
    by_cases hj : t = j
    · subst hj; exact Or.inr (Or.inr (Or.inr rfl))
    have : w' t = w t := by simp [w', hi, hj]
    rw [this]; exact Or.inl (hw t)
  have hT₂ : ∀ t ∉ T ∪ {i, j}, w' t = 0 := by
    intro t ht
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [w', ht.2.1, ht.2.2, hT t ht.1]
  have h₃ := ih w' (T ∪ {i, j}) acc _ (hE.trans Set.subset_union_left)
    (fun t => Or.inl (hv t)) hw₂ hT₂ (fun z => Or.inl (hacc z))
  have hsum : ∀ z, ∑ t, w' t * pderiv z (v t) =
      (α * pderiv z (v i) + β * pderiv z (v j)) + ∑ t, w t * pderiv z (v t) := by
    intro z
    simp only [w', add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have hcard : (T ∪ {i, j}).card ≤ T.card + 2 :=
    (Finset.card_union_le _ _).trans (by have := Finset.card_le_two (a := i) (b := j); omega)
  refine ((hαβ.trans h₂).seq h₃).mono le_rfl ?_ (by omega)
  rintro _ ⟨z, rfl⟩
  exact ⟨z, congrArg (fun s => acc z + s) (hsum z)⟩

/-- **Reverse mode.** The invariant holds for every program. -/
theorem adjoint_reach {r : ℕ} (p : Program ℂ I r) : AdjGoal p := by
  classical
  induction p with
  | nil =>
    intro w T acc E hE hv hw hT hacc
    exact (Reach.refl (by rintro _ ⟨z, rfl⟩; simpa using hacc z)).mono le_rfl le_rfl
      (Nat.zero_le _)
  | @step r p g ih =>
    intro w T acc E hE hv hw hT hacc
    have hsplit : ∀ z, ∑ t, w t * pderiv z (polynomialProgram (p.step g) t) =
        w 0 * pderiv z (polynomialGate g (polynomialProgram p)) + ∑ t : Fin r, w t.succ * pderiv z (polynomialProgram p t) := by
      intro z; rw [Fin.sum_univ_succ]; rfl
    have hv' : ∀ t, polynomialProgram p t ∈ E := fun t => hv t.succ
    have hw' : ∀ t : Fin r, w t.succ ∈ E := fun t => hw t.succ
    have hT' : ∀ t ∉ tailSet T, w t.succ = 0 := by
      intro t ht; exact hT _ (by simpa [tailSet] using ht)
    have hcard := tailSet_card T
    have hw0 : w 0 ∈ E := hw 0
    have bump : ∀ (i j : Fin r) (α β : MvPolynomial I ℂ) (k : ℕ), k ≤ 2 →
        Reach (cInputs I) E ({α} ∪ {β}) k →
        (∀ z, w 0 * pderiv z (polynomialGate g (polynomialProgram p)) =
          α * pderiv z (polynomialProgram p i) + β * pderiv z (polynomialProgram p j)) → g.cost = 1 →
        Reach (cInputs I) E
          (Set.range fun z => acc z + ∑ t, w t * pderiv z (polynomialProgram (p.step g) t))
          (6 * (p.step g).cost + T.card) := by
      intro i j α β k hk hαβ hid hg
      have h := adj_bump p ih (fun t => w t.succ) (tailSet T) acc E hE hv' hw' hT' hacc
        i j α β hαβ
      refine h.mono le_rfl ?_ ?_
      · rintro _ ⟨z, rfl⟩; exact ⟨z, by simp only [hsplit, hid]⟩
      · simp only [Program.cost_step, hg]; split_ifs at hcard <;> omega
    cases g with
    | constant z =>
      have h := ih (fun t => w t.succ) (tailSet T) acc E hE hv' hw' hT' hacc
      refine h.mono le_rfl ?_ ?_
      · rintro _ ⟨z, rfl⟩; exact ⟨z, by simp [hsplit, polynomialGate]⟩
      · simp only [Program.cost_step, Gate.cost]; split_ifs at hcard <;> omega
    | input i =>
      by_cases h0 : (0 : Fin (r + 1)) ∈ T
      · have h₁ : Reach (cInputs I) E {acc i + w 0} 1 := Reach.add (hacc i) hw0
        let acc' : I → MvPolynomial I ℂ := fun z => acc z + w 0 * pderiv z (X i)
        have hacc' : ∀ z, acc' z ∈ E ∪ {acc i + w 0} := by
          intro z
          by_cases hz : z = i
          · subst hz; exact Or.inr (by simp [acc'])
          · refine Or.inl ?_
            simp only [acc']
            rw [pderiv_X_of_ne (Ne.symm hz), mul_zero, add_zero]
            exact hacc z
        have h₂ := ih (fun t => w t.succ) (tailSet T) acc' (E ∪ {acc i + w 0})
          (hE.trans Set.subset_union_left) (fun t => Or.inl (hv' t)) (fun t => Or.inl (hw' t))
          hT' hacc'
        refine (h₁.seq h₂).mono le_rfl ?_ ?_
        · rintro _ ⟨z, rfl⟩; exact ⟨z, by simp only [hsplit, polynomialGate, acc']; ring⟩
        · simp only [Program.cost_step, Gate.cost]; simp only [h0, ↓reduceIte] at hcard; omega
      · have hw0' : w 0 = 0 := hT 0 h0
        have h := ih (fun t => w t.succ) (tailSet T) acc E hE hv' hw' hT' hacc
        refine h.mono le_rfl ?_ ?_
        · rintro _ ⟨z, rfl⟩; exact ⟨z, by simp [hsplit, hw0']⟩
        · simp only [Program.cost_step, Gate.cost]; simp only [h0, ↓reduceIte] at hcard; omega
    | add i j =>
      exact bump i j (w 0) (w 0) 0 (by omega)
        (Reach.refl (by simp [hw0])) (fun z => by simp [polynomialGate, mul_add]) rfl
    | sub i j =>
      exact bump i j (w 0) (C (-1) * w 0) 1 (by omega)
        (((Reach.refl (Set.singleton_subset_iff.mpr hw0)).union
          (Reach.mul (hE (C_mem_cInputs _)) hw0)).mono le_rfl le_rfl (by omega))
        (fun z => by simp [polynomialGate]; ring) rfl
    | mul i j =>
      exact bump i j (w 0 * polynomialProgram p j) (w 0 * polynomialProgram p i) 2 le_rfl
        ((Reach.mul hw0 (hv' j)).union (Reach.mul hw0 (hv' i)))
        (fun z => by simp [polynomialGate, Derivation.leibniz]; ring) rfl

end Commutative

/-! ## Ordered extraction of commutative circuits

The register-by-register compiler of `IDMM.BridgeCost` (`program_parts`), restated for arbitrary
commutative circuits (`Reach` over `MvPolynomial`), whose gates are sums and products. The two
gate lemmas are private there and are repeated here. -/

section Parts

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
private theorem const_input' (z : ℂ) :
    algebraMap ℂ (NC A B) z ∈ ncInputs ℂ (A ⊕ B) := Or.inr ⟨z,rfl⟩

omit [Fintype A] [Fintype B] in
private theorem zero_input' : (0 : NC A B) ∈ ncInputs ℂ (A ⊕ B) := by
  simpa using const_input' (A := A) (B := B) 0

omit [Fintype A] [Fintype B] in
private theorem reach_two' {D : Set (NC A B)} {x y : NC A B}
    (hx : x ∈ D) (hy : y ∈ D) (a b : ℂ) :
    Reach (ncInputs ℂ (A ⊕ B)) D {a • x + b • y} 7 := by
  have h := Reach.linComb (inp := ncInputs ℂ (A ⊕ B)) zero_input'
    (univ : Finset (Fin 2)) (c := ![algebraMap ℂ (NC A B) a, algebraMap ℂ (NC A B) b])
    (p := ![x,y]) (by intro i _; fin_cases i <;> exact const_input' _)
    (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two, Algebra.smul_def] using h

private theorem parts_add' {D : Set (NC A B)} (p q : Poly A B)
    (hp : parts p ⊆ D) (hq : parts q ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D (parts (p+q)) 3 := by
  have h₁ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := leftPart p) (q := leftPart q)
  have h₂ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := rightPart p) (q := rightPart q)
  have h₃ := Reach.add (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := orderedPart p) (q := orderedPart q)
  simpa [parts] using (h₁.union h₂).union h₃

private theorem parts_mul' {D : Set (NC A B)} (p q : Poly A B)
    (hp : parts p ⊆ D) (hq : parts q ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D (parts (p*q)) 29 := by
  have h₁ := reach_two' (hp (by simp [parts])) (hq (by simp [parts]))
    (scalarPart q) (scalarPart p) (x := leftPart p) (y := leftPart q)
  have h₂ := reach_two' (hp (by simp [parts])) (hq (by simp [parts]))
    (scalarPart q) (scalarPart p) (x := rightPart p) (y := rightPart q)
  have hc₁ := Reach.mul (inp := ncInputs ℂ (A ⊕ B))
    (hp (by simp [parts])) (hq (by simp [parts])) (p := leftPart p) (q := rightPart q)
  have hc₂ := Reach.mul (inp := ncInputs ℂ (A ⊕ B))
    (hq (by simp [parts])) (hp (by simp [parts])) (p := leftPart q) (q := rightPart p)
  let T : Set (NC A B) := {leftPart p * rightPart q} ∪ {leftPart q * rightPart p}
  have hc : Reach (ncInputs ℂ (A ⊕ B)) D T 2 := hc₁.union hc₂
  have hs := Reach.linComb (inp := ncInputs ℂ (A ⊕ B)) (B := D ∪ T) zero_input'
    (univ : Finset (Fin 4))
    (c := ![algebraMap ℂ (NC A B) (scalarPart q), 1, 1, algebraMap ℂ (NC A B) (scalarPart p)])
    (p := ![orderedPart p, leftPart p * rightPart q, leftPart q * rightPart p, orderedPart q])
    (by intro i _; fin_cases i <;> exact const_input' _)
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

theorem parts_input {x : Poly A B} (hx : x ∈ cInputs (A ⊕ B)) :
    parts x ⊆ ncInputs ℂ (A ⊕ B) := by
  rcases hx with ⟨v, rfl⟩ | ⟨z, rfl⟩
  · cases v with
    | inl i =>
      simp only [parts, leftPart_X_left, rightPart_X_left, orderedPart_X, Set.union_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨⟨Or.inl ⟨_, rfl⟩, zero_input'⟩, zero_input'⟩
    | inr j =>
      simp only [parts, leftPart_X_right, rightPart_X_right, orderedPart_X, Set.union_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨⟨zero_input', Or.inl ⟨_, rfl⟩⟩, zero_input'⟩
  · simp only [parts, leftPart_C, rightPart_C, orderedPart_C, Set.union_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨⟨zero_input', zero_input'⟩, zero_input'⟩

theorem builds_parts : ∀ {gs : List (Poly A B)} {D₀ : Set (Poly A B)} {D : Set (NC A B)},
    Builds (cInputs (A ⊕ B)) D₀ gs → ncInputs ℂ (A ⊕ B) ⊆ D → (∀ p ∈ D₀, parts p ⊆ D) →
    Reach (ncInputs ℂ (A ⊕ B)) D {y | ∃ x ∈ gs, y ∈ parts x} (29 * gs.length)
  | [], _, _, _, _, _ => Reach.refl (by simp)
  | g :: gs, D₀, D, ⟨hg, hgs⟩, hD, hD₀ => by
    have h₁ : Reach (ncInputs ℂ (A ⊕ B)) D (parts g) 29 := by
      rcases hg with hg | ⟨p, hp, q, hq, rfl | rfl⟩
      · exact (Reach.refl ((parts_input hg).trans hD)).mono le_rfl le_rfl (by omega)
      · exact (parts_add' p q (hD₀ p hp) (hD₀ q hq)).mono le_rfl le_rfl (by omega)
      · exact parts_mul' p q (hD₀ p hp) (hD₀ q hq)
    have h₂ := builds_parts (D := D ∪ parts g) hgs (hD.trans Set.subset_union_left)
      (by
        intro p hp
        rcases hp with rfl | hp
        · exact Set.subset_union_right
        · exact (hD₀ p hp).trans Set.subset_union_left)
    refine (h₁.trans h₂).mono le_rfl ?_ (by simp only [List.length_cons]; omega)
    rintro y ⟨x, hx, hy⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl hy
    · exact Or.inr ⟨x, hx, hy⟩

/-- **Ordered extraction of a commutative circuit.** Every component (`leftPart`, `rightPart`,
`orderedPart`) of every computed polynomial, with at most 29 gates per commutative gate. -/
theorem reach_parts {D₀ S : Set (Poly A B)} {D : Set (NC A B)} {s : ℕ}
    (h : Reach (cInputs (A ⊕ B)) D₀ S s) (hD : ncInputs ℂ (A ⊕ B) ⊆ D)
    (hD₀ : ∀ p ∈ D₀, parts p ⊆ D) :
    Reach (ncInputs ℂ (A ⊕ B)) D {y | ∃ x ∈ S, y ∈ parts x} (29 * s) := by
  obtain ⟨gs, hb, hl, hc⟩ := h
  refine reach_of_subset_avail ((builds_parts hb hD hD₀).mono le_rfl le_rfl
    (Nat.mul_le_mul_left 29 hl)) ?_
  rintro y ⟨x, hx, hy⟩
  rcases hc hx with h | h
  · exact Or.inl (hD₀ x h hy)
  · exact Or.inr ⟨x, h, hy⟩

end Parts

/-! ## The middle-insertion term -/

section Middle

variable {a b c : ℕ}

/-- Commutative variables for the middle term: `A` on the left; `B` and `Q` on the right. -/
abbrev MidVar (a b c : ℕ) := (Fin a × Fin b) ⊕ ((Fin b × Fin c) ⊕ (Fin a × Fin c))

/-- The matrix inputs `A, B` among the middle-term variables. -/
def midEmbed : MatrixInput a b c → MidVar a b c := Sum.map id Sum.inl

/-- The seed of the reverse pass: the output register of `(AB)_ik` carries `Q_ik`, so that the
weighted sum of the registers is `F = Σ_{i,k} Q_ik (AB)_ik`. -/
def midWeight (P : MatrixAlgorithm ℂ a b c) (t : Fin P.registers) :
    MvPolynomial (MidVar a b c) ℂ :=
  ∑ ik : Fin a × Fin c, if P.output ik.1 ik.2 = t then X (Sum.inr (Sum.inr ik)) else 0

/-- `∂F/∂B_jk = Σ_i A_ij Q_ik`. -/
theorem middle_derivative (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (j : Fin b) (k : Fin c) :
    ∑ t, midWeight P t * pderiv (Sum.inr (Sum.inl (j,k)) : MidVar a b c)
      (polynomialProgram (relabelProgram midEmbed P.program) t) =
    ∑ i : Fin a, X (Sum.inl (i,j)) * X (Sum.inr (Sum.inr (i,k))) := by
  classical
  have hM : ∀ (i : Fin a) (k' : Fin c), pderiv (Sum.inr (Sum.inl (j,k)) : MidVar a b c)
      (polynomialProgram (relabelProgram midEmbed P.program) (P.output i k')) =
      if k' = k then X (Sum.inl (i,j)) else 0 := by
    intro i k'
    rw [polynomialProgram_relabel, correct_polynomial P hP]
    simp [midEmbed, Pi.single_apply, ite_and]
  simp only [midWeight, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hM, Fintype.sum_prod_type, mul_ite,
    mul_zero, Finset.sum_ite_eq']
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Commutative middle term.** All `∂F/∂B_jk = Σ_i A_ij Q_ik`, by the forward pass of `P`
followed by the reverse pass. -/
theorem middle_commutative (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (cInputs (MidVar a b c)) (cInputs (MidVar a b c))
      (Set.range fun jk : Fin b × Fin c =>
        ∑ i : Fin a, (X (Sum.inl (i,jk.1)) * X (Sum.inr (Sum.inr (i,jk.2))) :
          MvPolynomial (MidVar a b c) ℂ))
      (8 * P.cost + a * c) := by
  classical
  have hinj := P.output_injective hb hP
  let p := relabelProgram midEmbed P.program
  let E := cInputs (MidVar a b c) ∪ Set.range (polynomialProgram p)
  let T : Finset (Fin P.registers) := univ.image fun ik : Fin a × Fin c => P.output ik.1 ik.2
  have hw : ∀ t, midWeight P t ∈ E := by
    intro t
    by_cases h : ∃ ik : Fin a × Fin c, P.output ik.1 ik.2 = t
    · obtain ⟨ik, rfl⟩ := h
      have : midWeight P (P.output ik.1 ik.2) = X (Sum.inr (Sum.inr ik)) := by
        rw [midWeight, Finset.sum_eq_single ik]
        · simp
        · intro ik' _ hne
          exact ite_eq_right (fun heq => hne (hinj heq))
        · simp
      rw [this]; exact Or.inl (X_mem_cInputs _)
    · have : midWeight P t = 0 :=
        Finset.sum_eq_zero (fun ik _ => ite_eq_right (fun heq => h ⟨ik, heq⟩))
      rw [this]; exact Or.inl zero_mem_cInputs
  have hT : ∀ t ∉ T, midWeight P t = 0 := by
    intro t ht
    refine Finset.sum_eq_zero (fun ik _ => ite_eq_right (fun heq => ht ?_))
    exact Finset.mem_image.mpr ⟨ik, Finset.mem_univ _, heq⟩
  have hTc : T.card ≤ a * c := by
    have := Finset.card_image_le (s := (univ : Finset (Fin a × Fin c)))
      (f := fun ik => P.output ik.1 ik.2)
    simpa [T, Fintype.card_prod] using this
  have hback := adjoint_reach p (midWeight P) T (fun _ => 0) E Set.subset_union_left
    (fun t => Or.inr ⟨t, rfl⟩) hw hT (fun _ => Or.inl zero_mem_cInputs)
  have hcost : p.cost = P.cost := cost_relabel _ _
  refine ((forward_reach p).seq hback).mono le_rfl ?_ (by omega)
  rintro _ ⟨jk, rfl⟩
  exact ⟨Sum.inr (Sum.inl jk), (zero_add _).trans (middle_derivative P hP jk.1 jk.2)⟩

/-- The factors `g_jk = Σ_i A_ij Q_ik` as noncommutative circuits, `A` before `Q`. -/
theorem middle_factors_nc (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (ncInputs ℂ (MidVar a b c)) ∅
      (Set.range fun jk : Fin b × Fin c =>
        ∑ i : Fin a, (FreeAlgebra.ι ℂ (Sum.inl (i,jk.1)) *
          FreeAlgebra.ι ℂ (Sum.inr (Sum.inr (i,jk.2))) : FreeAlgebra ℂ (MidVar a b c)))
      (696 * P.cost + 87 * (a * c) + b * c) := by
  have h := reach_parts (A := Fin a × Fin b) (B := (Fin b × Fin c) ⊕ (Fin a × Fin c))
    (middle_commutative P hP hb) le_rfl (fun p hp => parts_input hp)
  have h' := reach_charge_sources h (fun jk : Fin b × Fin c => orderedPart
    (∑ i : Fin a, (X (Sum.inl (i,jk.1)) * X (Sum.inr (Sum.inr (i,jk.2))) :
      MvPolynomial (MidVar a b c) ℂ)))
    (fun jk => ⟨_, ⟨jk, rfl⟩, Or.inr rfl⟩)
  refine h'.mono le_rfl ?_ ?_
  · rintro _ ⟨jk, rfl⟩
    refine ⟨jk, ?_⟩
    simp [orderedPart_sum, orderedPart_mul]
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega

/-- Back from the middle-term variables to `MatrixInput a b c ⊕ (Fin a × Fin c)`. -/
def midOut : MidVar a b c → MatrixInput a b c ⊕ (Fin a × Fin c)
  | .inl ij => .inl (.inl ij)
  | .inr (.inl jk) => .inl (.inr jk)
  | .inr (.inr ik) => .inr ik

/-- **Middle factors.** `g_jk = Σ_i A_ij Q_ik` for all `(j,k)`, one shared circuit. -/
theorem middle_factors_reach (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (ncInputs ℂ (MatrixInput a b c ⊕ (Fin a × Fin c))) ∅
      (Set.range fun jk : Fin b × Fin c =>
        ∑ i : Fin a,
          FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,jk.1)) : MatrixInput a b c ⊕ (Fin a × Fin c)) *
          FreeAlgebra.ι ℂ (Sum.inr (i,jk.2)))
      (696 * P.cost + 87 * (a * c) + b * c) := by
  have h := reach_relabel midOut (middle_factors_nc P hP hb)
  rw [← Set.range_comp] at h
  refine h.mono le_rfl ?_ le_rfl
  rintro _ ⟨jk, rfl⟩
  exact ⟨jk, by simp [midOut]⟩

/-- The middle term with no hypothesis on `c`; the `+ 1` is needed when `c = 0` (see
`middle_reach`). -/
theorem middle_reach_add_one (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) :
    Reach (ncInputs ℂ (MatrixInput a b c ⊕ (Fin a × Fin c))) ∅
      {∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,j)) : MatrixInput a b c ⊕ (Fin a × Fin c)) *
          FreeAlgebra.ι ℂ (Sum.inr (i,k)) * FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (j,k)))}
      (696 * P.cost + 87 * (a * c) + 4 * (b * c) + 1) := by
  classical
  let V := MatrixInput a b c ⊕ (Fin a × Fin c)
  let g : Fin b × Fin c → FreeAlgebra ℂ V := fun jk =>
    ∑ i : Fin a, FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,jk.1))) * FreeAlgebra.ι ℂ (Sum.inr (i,jk.2))
  let y : Fin b × Fin c → FreeAlgebra ℂ V := fun jk => FreeAlgebra.ι ℂ (Sum.inl (Sum.inr jk))
  have h₁ : Reach (ncInputs ℂ V) ∅ (Set.range g) (696 * P.cost + 87 * (a * c) + b * c) :=
    middle_factors_reach P hP hb
  let Ys : Set (FreeAlgebra ℂ V) := ⋃ jk ∈ (univ : Finset (Fin b × Fin c)), {y jk}
  let Ps : Set (FreeAlgebra ℂ V) := ⋃ jk ∈ (univ : Finset (Fin b × Fin c)), {g jk * y jk}
  have h₂ : Reach (ncInputs ℂ V) (∅ ∪ Set.range g) Ys (∑ _jk : Fin b × Fin c, 1) :=
    Reach.biUnion univ fun jk _ => Reach.input (Or.inl ⟨_, rfl⟩)
  have h₃ : Reach (ncInputs ℂ V) (∅ ∪ (Set.range g ∪ Ys)) Ps (∑ _jk : Fin b × Fin c, 1) :=
    Reach.biUnion univ fun jk _ => Reach.mul (Or.inr (Or.inl ⟨jk, rfl⟩))
      (Or.inr (Or.inr (Set.mem_biUnion (mem_univ jk) (Set.mem_singleton _))))
  have h₄ := Reach.sum (inp := ncInputs ℂ V) (B := ∅ ∪ ((Set.range g ∪ Ys) ∪ Ps))
    (Or.inr ⟨0, map_zero _⟩) univ (p := fun jk => g jk * y jk)
    (fun jk _ => Or.inr (Or.inr (Set.mem_biUnion (mem_univ jk) (Set.mem_singleton _))))
  have h := ((h₁.trans h₂).trans h₃).seq h₄
  have hG : ∑ jk ∈ (univ : Finset (Fin b × Fin c)), g jk * y jk =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,j)) : V) *
          FreeAlgebra.ι ℂ (Sum.inr (i,k)) * FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (j,k))) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [g, y, Finset.sum_mul]
    calc _ = ∑ j : Fin b, ∑ i : Fin a, ∑ k : Fin c,
          FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,j)) : V) *
            FreeAlgebra.ι ℂ (Sum.inr (i,k)) * FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (j,k))) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hG] at h
  refine h.mono le_rfl le_rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
    mul_one]
  omega

/-- **Middle insertion (Hrubeš's Lemma 22, matrix-multiplication case).**
`Σ_{i,j,k} A_ij Q_ik B_jk`, with `Q` inserted between the two factors of `(AB)_ik`, has a
noncommutative circuit of size `696 · cost(P) + 88 (ac + bc)`.

The hypothesis `1 ≤ c` is necessary for a bound of this shape: when `c = 0` the empty program is a
correct algorithm of cost `0`, the bound is `0`, and `Reach _ ∅ {0} 0` is false (even `0` takes an
input node). `middle_reach_add_one` drops it at the price of `+ 1`. -/
theorem middle_reach (P : MatrixAlgorithm ℂ a b c) (hP : P.Correct) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    Reach (ncInputs ℂ (MatrixInput a b c ⊕ (Fin a × Fin c))) ∅
      {∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,j)) : MatrixInput a b c ⊕ (Fin a × Fin c)) *
          FreeAlgebra.ι ℂ (Sum.inr (i,k)) * FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (j,k)))}
      (696 * P.cost + 88 * (a * c + b * c)) := by
  have hbc : 1 ≤ b * c := by simpa using Nat.mul_le_mul hb hc
  exact (middle_reach_add_one P hP hb).mono le_rfl le_rfl (by omega)

/-- `middle_reach` needs `1 ≤ c`: for `c = 0` there is a correct algorithm of cost `0`, and then no
bound `C₁ · cost + C₂ (ac + bc) = 0` can hold. -/
theorem middle_reach_needs_c : ∃ P : MatrixAlgorithm ℂ 1 1 0, P.Correct ∧ ∀ C₁ C₂ : ℕ,
    ¬ Reach (ncInputs ℂ (MatrixInput 1 1 0 ⊕ (Fin 1 × Fin 0))) ∅
      {∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin 0,
        FreeAlgebra.ι ℂ (Sum.inl (Sum.inl (i,j)) : MatrixInput 1 1 0 ⊕ (Fin 1 × Fin 0)) *
          FreeAlgebra.ι ℂ (Sum.inr (i,k)) * FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (j,k)))}
      (C₁ * P.cost + C₂ * (1 * 0 + 1 * 0)) := by
  refine ⟨⟨0, .nil, fun _ k => k.elim0⟩, fun _ _ => funext fun _ => funext fun k => k.elim0, ?_⟩
  rintro C₁ C₂ ⟨gs, -, hl, hc⟩
  have hgs : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp
    (hl.trans (by simp [MatrixAlgorithm.cost, Program.cost])))
  subst hgs
  simpa using hc (Set.mem_singleton _)

end Middle

end IDMM
