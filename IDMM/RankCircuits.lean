/-
Rank decompositions give noncommutative circuits, over any field. A decomposition
`⟨a,b,c⟩ = Σ_{q<R} u_q ⊗ v_q ⊗ w_q` over `K` drives the classical recursive bilinear algorithm in any
`K`-algebra (scalars are central, and left factors stay on the left): block products recurse on the
`R` products `(Σ u_q X)(Σ v_q Y)`, and the middle form `Σ X_ij Q_il Y_jl` recurses on the `R` forms
`Mid(Σ u_q X, Σ w_q Q^T, Σ v_q Y)`. Index sets of size at most `a^t`, `b^t`, `c^t` are padded with
zeros into words `Fin t → Fin a`, etc., and the recursion peels off the first letter (`Fin.cons`).
No infinite-field or characteristic assumption is used.
-/
import PauliCubes.Circuit
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

open OAI.MatrixMultiplication.Foundation PauliCubes Finset

namespace IDMM

section Identities

variable {K : Type*} [Field K] {a b c : ℕ}

/-- Contracting with the matrix-multiplication tensor at a fixed third index. -/
theorem sum_matrixCoefficients_smul {M : Type*} [AddCommMonoid M] [Module K M] (z : Fin c × Fin a)
    (G : Fin a × Fin b → Fin b × Fin c → M) :
    ∑ x, ∑ y, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z • G x y =
      ∑ j, G (z.2, j) (j, z.1) := by
  simp only [Tensor.matrixCoefficients, ite_smul, one_smul, zero_smul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single z.2]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (j, z.1)]
    · simp
    · rintro ⟨y1, y2⟩ _ hy
      rw [ite_eq_right_iff]
      rintro ⟨h1, h2, -⟩
      exact absurd (by simp_all) hy
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => ?_
    rw [ite_eq_right_iff]
    rintro ⟨-, -, h⟩
    exact absurd h.symm hi
  · simp

variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {R : ℕ} {u : Fin R → Fin a × Fin b → K}
  {v : Fin R → Fin b × Fin c → K} {w : Fin R → Fin c × Fin a → K}

/-- One level of the bilinear algorithm: block products from a rank decomposition. -/
theorem bilinear_identity
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z)
    (f : Fin a × Fin b → 𝒜) (g : Fin b × Fin c → 𝒜) (z : Fin c × Fin a) :
    ∑ q, w q z • ((∑ x, u q x • f x) * (∑ y, v q y • g y)) = ∑ j, f (z.2, j) * g (j, z.1) := by
  rw [← sum_matrixCoefficients_smul (K := K) z (fun x y => f x * g y)]
  simp only [huvw, Finset.sum_smul, Fintype.sum_mul_sum, smul_mul_smul_comm, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun q _ => ?_
  congr 1
  ring

/-- One level of the middle form: the trilinear form `Σ X_ij Q_il Y_jl` from a rank decomposition. -/
theorem trilinear_identity
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z)
    (f : Fin a × Fin b → 𝒜) (h : Fin c × Fin a → 𝒜) (g : Fin b × Fin c → 𝒜) :
    ∑ q, (∑ x, u q x • f x) * (∑ z, w q z • h z) * (∑ y, v q y • g y) =
      ∑ i, ∑ j, ∑ l, f (i, j) * h (l, i) * g (j, l) := by
  have hz : ∀ z : Fin c × Fin a, ∑ x, ∑ y,
      Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z • (f x * h z * g y) =
        ∑ j, f (z.2, j) * h z * g (j, z.1) :=
    fun z => sum_matrixCoefficients_smul (K := K) z (fun x y => f x * h z * g y)
  have hr : ∑ i, ∑ j, ∑ l, f (i, j) * h (l, i) * g (j, l) =
      ∑ z : Fin c × Fin a, ∑ j, f (z.2, j) * h z * g (j, z.1) := by
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hq : ∀ q, (∑ x, u q x • f x) * (∑ z, w q z • h z) * (∑ y, v q y • g y) =
      ∑ x, ∑ z, ∑ y, (u q x * v q y * w q z) • (f x * h z * g y) := by
    intro q
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm]
    congr 1
    ring
  rw [hr]
  simp_rw [← hz, huvw, Finset.sum_smul, hq]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_comm

end Identities

/-! ## Reindexing sums -/

theorem sum_fin_cons {β M : Type*} [Fintype β] [AddCommMonoid M] {t : ℕ}
    (F : (Fin (t + 1) → β) → M) : ∑ j, F j = ∑ j₁, ∑ j' : Fin t → β, F (Fin.cons j₁ j') := by
  rw [← (Fin.consEquiv fun _ : Fin (t + 1) => β).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_six {α α' β β' γ γ' M : Type*} [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    [Fintype γ] [Fintype γ'] [AddCommMonoid M] (F : α → α' → β → β' → γ → γ' → M) :
    ∑ i₁, ∑ i', ∑ j₁, ∑ j', ∑ l₁, ∑ l', F i₁ i' j₁ j' l₁ l' =
      ∑ i', ∑ j', ∑ l', ∑ i₁, ∑ j₁, ∑ l₁, F i₁ i' j₁ j' l₁ l' :=
  calc ∑ i₁, ∑ i', ∑ j₁, ∑ j', ∑ l₁, ∑ l', F i₁ i' j₁ j' l₁ l'
      = ∑ i', ∑ i₁, ∑ j₁, ∑ j', ∑ l₁, ∑ l', F i₁ i' j₁ j' l₁ l' := Finset.sum_comm
    _ = ∑ i', ∑ i₁, ∑ j', ∑ j₁, ∑ l₁, ∑ l', F i₁ i' j₁ j' l₁ l' :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i₁, ∑ j₁, ∑ l₁, ∑ l', F i₁ i' j₁ j' l₁ l' :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i₁, ∑ j₁, ∑ l', ∑ l₁, F i₁ i' j₁ j' l₁ l' :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i₁, ∑ l', ∑ j₁, ∑ l₁, F i₁ i' j₁ j' l₁ l' :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ l', ∑ i₁, ∑ j₁, ∑ l₁, F i₁ i' j₁ j' l₁ l' :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- A sum over `κ` of a function vanishing off the image of an injection `e : ι → κ`. -/
theorem sum_of_injective {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M] {e : ι → κ}
    (he : Function.Injective e) (F : κ → M) (hF : ∀ k, (∀ i, e i ≠ k) → F k = 0) :
    ∑ k, F k = ∑ i, F (e i) := by
  classical
  calc ∑ k, F k = ∑ k ∈ univ.map ⟨e, he⟩, F k :=
        (Finset.sum_subset (subset_univ _) fun k _ hk =>
          hF k fun i hi => hk (Finset.mem_map.2 ⟨i, mem_univ i, hi⟩)).symm
    _ = ∑ i, F (e i) := Finset.sum_map univ ⟨e, he⟩ F

/-! ## One level of the recursion -/

section Step

variable {K 𝒜 : Type*} [Field K] [Ring 𝒜] [Algebra K 𝒜] {a b c R t : ℕ}
  {u : Fin R → Fin a × Fin b → K} {v : Fin R → Fin b × Fin c → K} {w : Fin R → Fin c × Fin a → K}

theorem products_step
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z)
    (X : (Fin (t + 1) → Fin a) → (Fin (t + 1) → Fin b) → 𝒜)
    (Y : (Fin (t + 1) → Fin b) → (Fin (t + 1) → Fin c) → 𝒜) (i : Fin (t + 1) → Fin a)
    (l : Fin (t + 1) → Fin c) :
    ∑ q, w q (l 0, i 0) • ∑ j' : Fin t → Fin b,
      (∑ x, u q x • X (Fin.cons x.1 (Fin.tail i)) (Fin.cons x.2 j')) *
        (∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 (Fin.tail l))) =
      ∑ j, X i j * Y j l := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm, sum_fin_cons, Finset.sum_comm (s := univ (α := Fin b))]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [bilinear_identity huvw (fun x => X (Fin.cons x.1 (Fin.tail i)) (Fin.cons x.2 j'))
    (fun y => Y (Fin.cons y.1 j') (Fin.cons y.2 (Fin.tail l))) (l 0, i 0)]
  simp only [Fin.cons_self_tail]

theorem middle_step
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z)
    (X : (Fin (t + 1) → Fin a) → (Fin (t + 1) → Fin b) → 𝒜)
    (Q : (Fin (t + 1) → Fin a) → (Fin (t + 1) → Fin c) → 𝒜)
    (Y : (Fin (t + 1) → Fin b) → (Fin (t + 1) → Fin c) → 𝒜) :
    ∑ q, ∑ i' : Fin t → Fin a, ∑ j' : Fin t → Fin b, ∑ l' : Fin t → Fin c,
      (∑ x, u q x • X (Fin.cons x.1 i') (Fin.cons x.2 j')) *
        (∑ z, w q z • Q (Fin.cons z.2 i') (Fin.cons z.1 l')) *
          (∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 l')) =
      ∑ i, ∑ j, ∑ l, X i j * Q i l * Y j l := by
  simp only [sum_fin_cons (β := Fin a), sum_fin_cons (β := Fin b), sum_fin_cons (β := Fin c)]
  rw [sum_six (fun i₁ i' j₁ j' l₁ l' => X (Fin.cons i₁ i') (Fin.cons j₁ j') *
    Q (Fin.cons i₁ i') (Fin.cons l₁ l') * Y (Fin.cons j₁ j') (Fin.cons l₁ l'))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  exact trilinear_identity huvw (fun x => X (Fin.cons x.1 i') (Fin.cons x.2 j'))
    (fun z => Q (Fin.cons z.2 i') (Fin.cons z.1 l')) (fun y => Y (Fin.cons y.1 j') (Fin.cons y.2 l'))

end Step

/-! ## Circuit helpers -/

section Reach

variable {𝒜 : Type*} [Ring 𝒜] {inp : Set 𝒜}

/-- Every member of a finite family, each reachable with `s` gates. -/
theorem reach_range {ι : Type*} [Fintype ι] {B : Set 𝒜} (f : ι → 𝒜) {s : ℕ}
    (h : ∀ i, Reach inp B {f i} s) : Reach inp B (Set.range f) (Fintype.card ι * s) := by
  classical
  refine (Reach.biUnion univ fun i _ => h i).mono le_rfl ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact Set.mem_biUnion (mem_univ i) rfl
  · simp

/-- A finite union of sets, each reachable with `s` gates. -/
theorem reach_iUnion {ι : Type*} [Fintype ι] {B : Set 𝒜} (S : ι → Set 𝒜) {s : ℕ}
    (h : ∀ i, Reach inp B (S i) s) : Reach inp B (⋃ i, S i) (Fintype.card ι * s) := by
  classical
  refine (Reach.biUnion univ fun i _ => h i).mono le_rfl ?_ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_biUnion (mem_univ i) hi
  · simp

variable {K : Type*} [Field K] [Algebra K 𝒜]

/-- A `K`-linear combination of available values, the scalars being inputs. -/
theorem reach_smul_sum (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp) {ι : Type*} [Fintype ι]
    {B : Set 𝒜} (k : ι → K) (p : ι → 𝒜) (hp : ∀ i, p i ∈ B) :
    Reach inp B {∑ i, k i • p i} (3 * Fintype.card ι + 1) := by
  classical
  have h0 : (0 : 𝒜) ∈ inp := by simpa using hc 0
  simpa [Algebra.smul_def] using Reach.linComb (B := B) h0 univ
    (c := fun i => algebraMap K 𝒜 (k i)) (p := p) (fun i _ => hc _) (fun i _ => hp i)

end Reach

/-! ## The recursion on words -/

/-- Gates used by the recursive algorithms on words of length `t`: `R` recursive calls, the block
linear combinations, the output combinations (products) and the final sum (middle form). -/
def wordCost (a b c R : ℕ) : ℕ → ℕ
  | 0 => 2
  | t + 1 => R * wordCost a b c R t + R * (a ^ t * b ^ t) * (3 * (a * b) + 1) +
      R * (b ^ t * c ^ t) * (3 * (b * c) + 1) + R * (a ^ t * c ^ t) * (3 * (c * a) + 1) +
      a ^ (t + 1) * c ^ (t + 1) * (3 * R + 1) + (R + 1)

/-- Gates for products and middle forms of size up to `a^t × b^t × c^t` from a rank-`R`
decomposition of `⟨a,b,c⟩`: the word recursion plus one gate for the padding zero. -/
def rankCost (a b c R t : ℕ) : ℕ := wordCost a b c R t + 1

section Words

variable {K 𝒜 : Type*} [Field K] [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜} {a b c R : ℕ}
  {u : Fin R → Fin a × Fin b → K} {v : Fin R → Fin b × Fin c → K} {w : Fin R → Fin c × Fin a → K}

theorem word_products_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp)
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z) (t : ℕ) :
    ∀ (B : Set 𝒜) (X : (Fin t → Fin a) → (Fin t → Fin b) → 𝒜)
      (Y : (Fin t → Fin b) → (Fin t → Fin c) → 𝒜), (∀ i j, X i j ∈ B) → (∀ j l, Y j l ∈ B) →
      Reach inp B (Set.range fun il : (Fin t → Fin a) × (Fin t → Fin c) =>
        ∑ j, X il.1 j * Y j il.2) (wordCost a b c R t) := by
  induction t with
  | zero =>
    intro B X Y hX hY
    refine (Reach.mul (hX default default) (hY default default)).mono le_rfl ?_ (by simp [wordCost])
    rintro _ ⟨il, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [Fintype.sum_unique, Subsingleton.elim il.1 default, Subsingleton.elim il.2 default]
  | succ t ih =>
    intro B X Y hX hY
    set SP : Set 𝒜 := Set.range fun e : Fin R × (Fin t → Fin a) × (Fin t → Fin b) =>
      ∑ x, u e.1 x • X (Fin.cons x.1 e.2.1) (Fin.cons x.2 e.2.2) with hSP
    set SQ : Set 𝒜 := Set.range fun e : Fin R × (Fin t → Fin b) × (Fin t → Fin c) =>
      ∑ y, v e.1 y • Y (Fin.cons y.1 e.2.1) (Fin.cons y.2 e.2.2) with hSQ
    set SM : Set 𝒜 := ⋃ q : Fin R, Set.range fun il : (Fin t → Fin a) × (Fin t → Fin c) =>
      ∑ j', (∑ x, u q x • X (Fin.cons x.1 il.1) (Fin.cons x.2 j')) *
        (∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 il.2)) with hSM
    have h1 : Reach inp B SP _ := reach_range _ fun e => reach_smul_sum hc _ _ fun x => hX _ _
    have h2 : Reach inp B SQ _ := reach_range _ fun e => reach_smul_sum hc _ _ fun y => hY _ _
    have h3 : Reach inp (B ∪ (SP ∪ SQ)) SM (Fintype.card (Fin R) * wordCost a b c R t) :=
      reach_iUnion _ fun q => ih _
        (fun i' j' => ∑ x, u q x • X (Fin.cons x.1 i') (Fin.cons x.2 j'))
        (fun j' l' => ∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 l'))
        (fun i' j' => Or.inr (Or.inl ⟨(q, i', j'), rfl⟩))
        (fun j' l' => Or.inr (Or.inr ⟨(q, j', l'), rfl⟩))
    have h4 : Reach inp (B ∪ ((SP ∪ SQ) ∪ SM))
        (Set.range fun il : (Fin (t + 1) → Fin a) × (Fin (t + 1) → Fin c) =>
          ∑ q, w q (il.2 0, il.1 0) • ∑ j' : Fin t → Fin b,
            (∑ x, u q x • X (Fin.cons x.1 (Fin.tail il.1)) (Fin.cons x.2 j')) *
              (∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 (Fin.tail il.2)))) _ :=
      reach_range _ fun il => reach_smul_sum hc _ _ fun q =>
        Or.inr (Or.inr (Set.mem_iUnion.2 ⟨q, (Fin.tail il.1, Fin.tail il.2), rfl⟩))
    refine (((h1.union h2).trans h3).seq h4).mono le_rfl ?_ ?_
    · rintro _ ⟨il, rfl⟩
      exact ⟨il, products_step huvw X Y il.1 il.2⟩
    · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, prod_const, card_univ,
        wordCost]
      omega

theorem word_middle_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp)
    (huvw : ∀ x y z, Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
      ∑ q, u q x * v q y * w q z) (t : ℕ) :
    ∀ (B : Set 𝒜) (X : (Fin t → Fin a) → (Fin t → Fin b) → 𝒜)
      (Q : (Fin t → Fin a) → (Fin t → Fin c) → 𝒜) (Y : (Fin t → Fin b) → (Fin t → Fin c) → 𝒜),
      (∀ i j, X i j ∈ B) → (∀ i l, Q i l ∈ B) → (∀ j l, Y j l ∈ B) →
      Reach inp B {∑ i, ∑ j, ∑ l, X i j * Q i l * Y j l} (wordCost a b c R t) := by
  have h0 : (0 : 𝒜) ∈ inp := by simpa using hc 0
  induction t with
  | zero =>
    intro B X Q Y hX hQ hY
    have h₁ : Reach inp B {X default default * Q default default} 1 :=
      Reach.mul (hX default default) (hQ default default)
    have h₂ : Reach inp (B ∪ {X default default * Q default default})
        {X default default * Q default default * Y default default} 1 :=
      Reach.mul (Or.inr rfl) (Or.inl (hY default default))
    refine (h₁.seq h₂).mono le_rfl ?_ (by simp [wordCost])
    simp only [Fintype.sum_unique]
    rfl
  | succ t ih =>
    intro B X Q Y hX hQ hY
    set SP : Set 𝒜 := Set.range fun e : Fin R × (Fin t → Fin a) × (Fin t → Fin b) =>
      ∑ x, u e.1 x • X (Fin.cons x.1 e.2.1) (Fin.cons x.2 e.2.2) with hSP
    set SH : Set 𝒜 := Set.range fun e : Fin R × (Fin t → Fin a) × (Fin t → Fin c) =>
      ∑ z, w e.1 z • Q (Fin.cons z.2 e.2.1) (Fin.cons z.1 e.2.2) with hSH
    set SV : Set 𝒜 := Set.range fun e : Fin R × (Fin t → Fin b) × (Fin t → Fin c) =>
      ∑ y, v e.1 y • Y (Fin.cons y.1 e.2.1) (Fin.cons y.2 e.2.2) with hSV
    set mid : Fin R → 𝒜 := fun q => ∑ i' : Fin t → Fin a, ∑ j' : Fin t → Fin b,
      ∑ l' : Fin t → Fin c, (∑ x, u q x • X (Fin.cons x.1 i') (Fin.cons x.2 j')) *
        (∑ z, w q z • Q (Fin.cons z.2 i') (Fin.cons z.1 l')) *
          (∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 l')) with hmid
    have h1 : Reach inp B SP _ := reach_range _ fun e => reach_smul_sum hc _ _ fun x => hX _ _
    have h2 : Reach inp B SH _ := reach_range _ fun e => reach_smul_sum hc _ _ fun z => hQ _ _
    have h3 : Reach inp B SV _ := reach_range _ fun e => reach_smul_sum hc _ _ fun y => hY _ _
    have h4 : Reach inp (B ∪ ((SP ∪ SH) ∪ SV)) (⋃ q, {mid q})
        (Fintype.card (Fin R) * wordCost a b c R t) :=
      reach_iUnion _ fun q => ih _
        (fun i' j' => ∑ x, u q x • X (Fin.cons x.1 i') (Fin.cons x.2 j'))
        (fun i' l' => ∑ z, w q z • Q (Fin.cons z.2 i') (Fin.cons z.1 l'))
        (fun j' l' => ∑ y, v q y • Y (Fin.cons y.1 j') (Fin.cons y.2 l'))
        (fun i' j' => Or.inr (Or.inl (Or.inl ⟨(q, i', j'), rfl⟩)))
        (fun i' l' => Or.inr (Or.inl (Or.inr ⟨(q, i', l'), rfl⟩)))
        (fun j' l' => Or.inr (Or.inr ⟨(q, j', l'), rfl⟩))
    have h5 : Reach inp (B ∪ (((SP ∪ SH) ∪ SV) ∪ ⋃ q, {mid q})) {∑ q ∈ univ, mid q}
        ((univ : Finset (Fin R)).card + 1) :=
      Reach.sum h0 univ fun q _ => Or.inr (Or.inr (Set.mem_iUnion.2 ⟨q, rfl⟩))
    refine ((((h1.union h2).union h3).trans h4).seq h5).mono le_rfl ?_ ?_
    · exact Set.singleton_subset_iff.2 (Set.mem_singleton_iff.2 (middle_step huvw X Q Y).symm)
    · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, prod_const, card_univ,
        wordCost]
      omega

end Words

/-! ## Padding arbitrary index sets into words -/

section Pad

variable {𝒜 : Type*} [Ring 𝒜] {I J I' J' : Type*} {eI : I → I'} {eJ : J → J'}

/-- Extend a matrix along injections of its index sets, by zeros. -/
noncomputable def pad (eI : I → I') (eJ : J → J') (X : I → J → 𝒜) : I' → J' → 𝒜 :=
  fun w w' => Function.extend eI (fun i => Function.extend eJ (X i) 0 w') 0 w

theorem pad_apply (hI : Function.Injective eI) (hJ : Function.Injective eJ) (X : I → J → 𝒜)
    (i : I) (j : J) : pad eI eJ X (eI i) (eJ j) = X i j := by
  simp only [pad, hI.extend_apply, hJ.extend_apply]

theorem pad_left (X : I → J → 𝒜) {w : I'} (hw : ∀ i, eI i ≠ w) (w' : J') :
    pad eI eJ X w w' = 0 := by
  simp only [pad]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hw i hi]
  rfl

theorem pad_right (hI : Function.Injective eI) (X : I → J → 𝒜) (w : I') {w' : J'}
    (hw' : ∀ j, eJ j ≠ w') : pad eI eJ X w w' = 0 := by
  by_cases h : ∃ i, eI i = w
  · obtain ⟨i, rfl⟩ := h
    simp only [pad, hI.extend_apply]
    rw [Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hw' j hj]
    rfl
  · exact pad_left X (fun i hi => h ⟨i, hi⟩) w'

theorem pad_mem (hI : Function.Injective eI) (hJ : Function.Injective eJ) {B : Set 𝒜}
    {X : I → J → 𝒜} (hX : ∀ i j, X i j ∈ B) (w : I') (w' : J') :
    pad eI eJ X w w' ∈ B ∪ {0} := by
  by_cases h : ∃ i, eI i = w
  · obtain ⟨i, rfl⟩ := h
    by_cases h' : ∃ j, eJ j = w'
    · obtain ⟨j, rfl⟩ := h'
      rw [pad_apply hI hJ]
      exact Or.inl (hX i j)
    · rw [pad_right hI X _ fun j hj => h' ⟨j, hj⟩]
      exact Or.inr rfl
  · rw [pad_left X fun i hi => h ⟨i, hi⟩]
    exact Or.inr rfl

end Pad

/-! ## Main statements -/

variable {K 𝒜 : Type*} [Field K] [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜}

theorem coeffs_of_rankAtMost {a b c R : ℕ}
    (hT : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) R) :
    ∃ (u : Fin R → Fin a × Fin b → K) (v : Fin R → Fin b × Fin c → K)
      (w : Fin R → Fin c × Fin a → K), ∀ x y z,
        Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) x y z =
          ∑ q, u q x * v q y * w q z := by
  obtain ⟨u, v, w, huvw⟩ := hT
  exact ⟨u, v, w, fun x y z => by rw [huvw]; rfl⟩

/-- **Products from a rank decomposition.** If `⟨a,b,c⟩` has rank at most `R` over `K`, then for any
`I × J` and `J × L` matrices over a `K`-algebra with `|I| ≤ a^t`, `|J| ≤ b^t`, `|L| ≤ c^t`, all entries
of the product (in this order) are reached with `rankCost a b c R t` gates. -/
theorem rank_products_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp)
    {a b c R : ℕ}
    (hT : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) R)
    (t : ℕ) {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    (hI : Fintype.card I ≤ a ^ t) (hJ : Fintype.card J ≤ b ^ t) (hL : Fintype.card L ≤ c ^ t)
    {B : Set 𝒜} (X : I → J → 𝒜) (Y : J → L → 𝒜) (hX : ∀ i j, X i j ∈ B)
    (hY : ∀ j l, Y j l ∈ B) :
    Reach inp B (Set.range fun il : I × L => ∑ j, X il.1 j * Y j il.2) (rankCost a b c R t) := by
  obtain ⟨u, v, w, huvw⟩ := coeffs_of_rankAtMost hT
  obtain ⟨eI⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin a) (by simpa using hI)
  obtain ⟨eJ⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin b) (by simpa using hJ)
  obtain ⟨eL⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin c) (by simpa using hL)
  have h0 : Reach inp B {0} 1 := Reach.input (by simpa using hc 0)
  have hw := word_products_reach hc huvw t (B ∪ {0}) (pad eI eJ X) (pad eJ eL Y)
    (pad_mem eI.injective eJ.injective hX) (pad_mem eJ.injective eL.injective hY)
  refine (h0.seq hw).mono le_rfl ?_ (by unfold rankCost; omega)
  rintro _ ⟨⟨i, l⟩, rfl⟩
  refine ⟨(eI i, eL l), ?_⟩
  simp only
  rw [sum_of_injective eJ.injective _ fun w' hw' => by
    rw [pad_right eI.injective X _ hw', zero_mul]]
  simp only [pad_apply eI.injective eJ.injective, pad_apply eJ.injective eL.injective]

/-- **The middle form from a rank decomposition.** Under the same hypotheses,
`Σ_{i,j,l} X_ij Q_il Y_jl` is reached with `rankCost a b c R t` gates. -/
theorem rank_middle_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp)
    {a b c R : ℕ}
    (hT : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)) R)
    (t : ℕ) {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    (hI : Fintype.card I ≤ a ^ t) (hJ : Fintype.card J ≤ b ^ t) (hL : Fintype.card L ≤ c ^ t)
    {B : Set 𝒜} (X : I → J → 𝒜) (Q : I → L → 𝒜) (Y : J → L → 𝒜) (hX : ∀ i j, X i j ∈ B)
    (hQ : ∀ i l, Q i l ∈ B) (hY : ∀ j l, Y j l ∈ B) :
    Reach inp B {∑ i, ∑ j, ∑ l, X i j * Q i l * Y j l} (rankCost a b c R t) := by
  obtain ⟨u, v, w, huvw⟩ := coeffs_of_rankAtMost hT
  obtain ⟨eI⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin a) (by simpa using hI)
  obtain ⟨eJ⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin b) (by simpa using hJ)
  obtain ⟨eL⟩ := Function.Embedding.nonempty_of_card_le (β := Fin t → Fin c) (by simpa using hL)
  have h0 : Reach inp B {0} 1 := Reach.input (by simpa using hc 0)
  have hw := word_middle_reach hc huvw t (B ∪ {0}) (pad eI eJ X) (pad eI eL Q) (pad eJ eL Y)
    (pad_mem eI.injective eJ.injective hX) (pad_mem eI.injective eL.injective hQ)
    (pad_mem eJ.injective eL.injective hY)
  refine (h0.seq hw).mono le_rfl ?_ (by unfold rankCost; omega)
  rw [Set.singleton_subset_iff, Set.mem_singleton_iff]
  symm
  rw [sum_of_injective eI.injective _ fun w hw => Finset.sum_eq_zero fun w' _ =>
    Finset.sum_eq_zero fun w'' _ => by rw [pad_left X hw, zero_mul, zero_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_of_injective eJ.injective _ fun w' hw' => Finset.sum_eq_zero fun w'' _ => by
    rw [pad_right eI.injective X _ hw', zero_mul, zero_mul]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_of_injective eL.injective _ fun w'' hw'' => by
    rw [pad_right eI.injective Q _ hw'', mul_zero, zero_mul]]
  simp only [pad_apply eI.injective eJ.injective, pad_apply eI.injective eL.injective,
    pad_apply eJ.injective eL.injective]

/-! ## The cost bound -/

/-- Reaching `0` from no available values takes at least one gate. With `a = b = c = R = 0` and
`t = 1`, `rank_middle_reach` (for `B = ∅`) therefore forces `rankCost 0 0 0 0 1 ≥ 1`, while
`D · (t + 1) · max(R, ab, bc, ca)^t = 0`: this is why `rankCost_le` assumes `1 ≤ max(R, ab, bc, ca)`. -/
theorem one_le_of_reach_empty {𝒜 : Type*} [Ring 𝒜] {inp : Set 𝒜} {s : ℕ}
    (h : Reach inp (∅ : Set 𝒜) {0} s) : 1 ≤ s := by
  obtain ⟨gs, -, hl, hc⟩ := h
  rcases hc rfl with h | h
  · exact absurd h (Set.notMem_empty _)
  · exact (List.length_pos_of_mem h).trans_le hl

theorem wordCost_le {a b c R M : ℕ} (hM : 1 ≤ M) (hR : R ≤ M) (hab : a * b ≤ M) (hbc : b * c ≤ M)
    (hca : c * a ≤ M) (t : ℕ) :
    wordCost a b c R t ≤ (7 * (a * b + b * c + c * a) + 5) * (t + 1) * M ^ t := by
  induction t with
  | zero => simp only [wordCost, zero_add, pow_zero, mul_one]; omega
  | succ t ih =>
    have hP : 1 ≤ M ^ t := Nat.one_le_pow _ _ hM
    have e1 : a ^ t * b ^ t ≤ M ^ t := by rw [← mul_pow]; exact Nat.pow_le_pow_left hab t
    have e2 : b ^ t * c ^ t ≤ M ^ t := by rw [← mul_pow]; exact Nat.pow_le_pow_left hbc t
    have e3 : a ^ t * c ^ t ≤ M ^ t := by
      rw [← mul_pow, mul_comm a c]; exact Nat.pow_le_pow_left hca t
    have e4 : a ^ (t + 1) * c ^ (t + 1) ≤ c * a * M ^ t := by
      rw [← mul_pow, pow_succ, mul_comm a c, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hca t)
    have f1 : R * wordCost a b c R t ≤ M * ((7 * (a * b + b * c + c * a) + 5) * (t + 1) * M ^ t) :=
      Nat.mul_le_mul hR ih
    have f2 : R * (a ^ t * b ^ t) * (3 * (a * b) + 1) ≤ M * M ^ t * (3 * (a * b) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR e1) le_rfl
    have f3 : R * (b ^ t * c ^ t) * (3 * (b * c) + 1) ≤ M * M ^ t * (3 * (b * c) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR e2) le_rfl
    have f4 : R * (a ^ t * c ^ t) * (3 * (c * a) + 1) ≤ M * M ^ t * (3 * (c * a) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR e3) le_rfl
    have f5 : a ^ (t + 1) * c ^ (t + 1) * (3 * R + 1) ≤ c * a * M ^ t * (3 * M + 1) :=
      Nat.mul_le_mul e4 (by omega)
    have f6 : M ≤ M * M ^ t := Nat.le_mul_of_pos_right _ hP
    have f7 : c * a * M ^ t ≤ c * a * (M * M ^ t) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hM)
    have f8 : 1 ≤ M * M ^ t := Nat.one_le_iff_ne_zero.2 (by positivity)
    have f9 := Nat.zero_le (a * b * (M * M ^ t))
    have f10 := Nat.zero_le (b * c * (M * M ^ t))
    rw [show M ^ (t + 1) = M * M ^ t by ring]
    simp only [wordCost]
    linarith

/-- **The cost bound.** `rankCost a b c R t ≤ D · (t+1) · M^t` with `M = max(R, ab, bc, ca)` and
`D = 7(ab + bc + ca) + 6`, provided `M ≥ 1`. (If `M = 0` and `t ≥ 1`, the middle form is the empty
sum `0`, which costs one gate from `B = ∅`, so no bound `D · (t+1) · 0^t` can hold.) -/
theorem rankCost_le (a b c R t : ℕ) (hM : 1 ≤ max R (max (a * b) (max (b * c) (c * a)))) :
    rankCost a b c R t ≤
      (7 * (a * b + b * c + c * a) + 6) * (t + 1) * max R (max (a * b) (max (b * c) (c * a))) ^ t := by
  set M := max R (max (a * b) (max (b * c) (c * a))) with hMdef
  have h := wordCost_le (a := a) (b := b) (c := c) (R := R) hM (by omega) (by omega) (by omega)
    (by omega) t
  have hP : 1 ≤ M ^ t := Nat.one_le_pow _ _ hM
  have := Nat.zero_le (t * M ^ t)
  unfold rankCost
  nlinarith

end IDMM
