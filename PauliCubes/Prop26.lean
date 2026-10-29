/-
**Hrubeš's Proposition 26 for `k = 4`.** `S_{4,N}` costs at most the cost of `ID*_N` plus `O(N)`
gates: `32 N + 46` of them (`reach_S4`), so `ncSizeLE_S4_of_IDstar` holds with `s + 100 N + 100`.

Write `x_i` for the variables and `p_m = Σ_i x_i^m`. With
  `s₂ = p₁p₁ - p₂`,  `q₁ = Σ_i x_i p₁ x_i`,  `q₂ = Σ_i x_i x_i p₁ x_i`,  `q₃ = Σ_i x_i s₂ x_i`,
  `q₄ = Σ_i x_i p₁ x_i x_i`,  `s₃ = p₁s₂ - p₂p₁ - q₁ + 2p₃`,
  `A = p₂s₂ - p₃p₁ - q₂ + 2p₄`,  `B = q₃ - q₂ - q₄ + 2p₄`,  `C = q₁p₁ - p₃p₁ - q₄ - ID* + 2p₄`,
inclusion–exclusion gives `S₄ = p₁s₃ - A - B - C` (`S4_eq`): `p₁s₃` sums `x_a x_b x_c x_d` over
arbitrary `a` and pairwise distinct `b, c, d`, and `A`, `B`, `C` are its terms with `a = b`, `a = d`
and `a = c`. Every side is written as `M4 c = Σ_{i,j,k,l} c i j k l • x_i x_j x_k x_l`, so the
identity reduces to one of coefficients, checked by cases on the six index equalities.

Each `p_m` and `q_m` is a sum of `N` words of length at most four, so `O(N)` gates; the rest is
`O(1)` gates, with `a - b = a + (-1)·b` and `2·p` from the constant inputs `-1` and `2`.
-/
import PauliCubes.IDStar
import Mathlib.Tactic.NoncommRing

open Finset

namespace PauliCubes

namespace Prop26

/-! ## Gate helpers -/

section Circ

variable {R : Type*} [Ring R] {inp B S : Set R} {s t : ℕ}

theorem isGate_mul {p q : R} (hp : p ∈ B) (hq : q ∈ B) : IsGate inp B (p * q) :=
  Or.inr ⟨p, hp, q, hq, Or.inr rfl⟩

theorem isGate_add {p q : R} (hp : p ∈ B) (hq : q ∈ B) : IsGate inp B (p + q) :=
  Or.inr ⟨p, hp, q, hq, Or.inl rfl⟩

/-- `-p` is the product of the available constant `-1` with `p`. -/
theorem isGate_neg {p : R} (hm : (-1 : R) ∈ B) (hp : p ∈ B) : IsGate inp B (-p) :=
  Or.inr ⟨-1, hm, p, hp, Or.inr (neg_one_mul p).symm⟩

/-- `p - q` is the sum of `p` and the available `-q`. -/
theorem isGate_sub {p q : R} (hp : p ∈ B) (hq : -q ∈ B) : IsGate inp B (p - q) :=
  Or.inr ⟨p, hp, -q, hq, Or.inl (sub_eq_add_neg p q)⟩

/-- One gate, then the rest of the circuit over the enlarged set of values. -/
theorem reach_cons_gate {g : R} (hg : IsGate inp B g) (h : Reach inp (insert g B) S s) :
    Reach inp B S (s + 1) :=
  ((Reach.gate hg).seq (h.mono Set.union_singleton.ge le_rfl le_rfl)).mono le_rfl le_rfl
    (by omega)

/-- The circuit so far, then one more gate, keeping every value. -/
theorem reach_snoc {g : R} (h : Reach inp B S s) (hg : IsGate inp (B ∪ S) g) :
    Reach inp B (S ∪ {g}) (s + 1) :=
  h.trans (Reach.gate hg)

/-- A sum of `|u|` values, each computed with `t` gates. -/
theorem reach_sum_each {ι : Type*} [DecidableEq ι] (h0 : (0 : R) ∈ inp) (u : Finset ι)
    {f : ι → R} (h : ∀ i ∈ u, Reach inp B {f i} t) :
    Reach inp B {∑ i ∈ u, f i} (u.card * t + u.card + 1) := by
  have h1 := Reach.biUnion (t := fun _ => t) u h
  have h2 := Reach.sum (B := B ∪ ⋃ i ∈ u, {f i}) h0 u (p := f) fun i hi =>
    Or.inr (Set.mem_biUnion hi (Set.mem_singleton _))
  refine (h1.seq h2).mono le_rfl le_rfl ?_
  simp only [Finset.sum_const, smul_eq_mul]
  omega

end Circ

/-! ## Degree-four forms -/

variable {K : Type*} [CommRing K] {N : ℕ}

local notation "𝕩" => FreeAlgebra.ι K

/-- `Σ_i a_i x_i`. -/
noncomputable def M1 (a : Fin N → K) : FreeAlgebra K (Fin N) := ∑ i, a i • 𝕩 i

/-- `Σ_{i,j} b_{ij} x_i x_j`. -/
noncomputable def M2 (b : Fin N → Fin N → K) : FreeAlgebra K (Fin N) :=
  ∑ i, ∑ j, b i j • (𝕩 i * 𝕩 j)

/-- `Σ_{i,j,k} c_{ijk} x_i x_j x_k`. -/
noncomputable def M3 (c : Fin N → Fin N → Fin N → K) : FreeAlgebra K (Fin N) :=
  ∑ i, ∑ j, ∑ k, c i j k • (𝕩 i * 𝕩 j * 𝕩 k)

/-- `Σ_{i,j,k,l} d_{ijkl} x_i x_j x_k x_l`. -/
noncomputable def M4 (d : Fin N → Fin N → Fin N → Fin N → K) : FreeAlgebra K (Fin N) :=
  ∑ i, ∑ j, ∑ k, ∑ l, d i j k l • (𝕩 i * 𝕩 j * 𝕩 k * 𝕩 l)

theorem M1_mul_M1 (a b : Fin N → K) : M1 a * M1 b = M2 fun i j => a i * b j := by
  simp only [M1, M2, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm]

theorem M1_mul_M2 (a : Fin N → K) (b : Fin N → Fin N → K) :
    M1 a * M2 b = M3 fun i j k => a i * b j k := by
  simp only [M1, M2, M3, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, mul_assoc]

theorem M2_mul_M1 (b : Fin N → Fin N → K) (a : Fin N → K) :
    M2 b * M1 a = M3 fun i j k => b i j * a k := by
  simp only [M1, M2, M3, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, mul_assoc]

theorem M1_mul_M3 (a : Fin N → K) (c : Fin N → Fin N → Fin N → K) :
    M1 a * M3 c = M4 fun i j k l => a i * c j k l := by
  simp only [M1, M3, M4, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, mul_assoc]

theorem M3_mul_M1 (c : Fin N → Fin N → Fin N → K) (a : Fin N → K) :
    M3 c * M1 a = M4 fun i j k l => c i j k * a l := by
  simp only [M1, M3, M4, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, mul_assoc]

theorem M2_mul_M2 (b c : Fin N → Fin N → K) :
    M2 b * M2 c = M4 fun i j k l => b i j * c k l := by
  simp only [M2, M4, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, mul_assoc]

theorem conj_M1 (a : Fin N → K) :
    ∑ m, 𝕩 m * M1 a * 𝕩 m = M3 fun i j k => if i = k then a j else 0 := by
  simp only [M1, M3, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

theorem conj_M2 (b : Fin N → Fin N → K) :
    ∑ m, 𝕩 m * M2 b * 𝕩 m = M4 fun i j k l => if i = l then b j k else 0 := by
  simp only [M2, M4, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

theorem M4_add (c d : Fin N → Fin N → Fin N → Fin N → K) :
    M4 c + M4 d = M4 fun i j k l => c i j k l + d i j k l := by
  simp only [M4, add_smul, Finset.sum_add_distrib]

theorem M4_sub (c d : Fin N → Fin N → Fin N → Fin N → K) :
    M4 c - M4 d = M4 fun i j k l => c i j k l - d i j k l := by
  simp only [M4, sub_smul, Finset.sum_sub_distrib]

/-! ## The polynomials of Proposition 26 -/

variable (K N)

/-- `p₁ = Σ_i x_i`. -/
noncomputable def p1 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i
/-- `p₂ = Σ_i x_i²`. -/
noncomputable def p2 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * 𝕩 i
/-- `p₃ = Σ_i x_i³`. -/
noncomputable def p3 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * 𝕩 i * 𝕩 i
/-- `p₄ = Σ_i x_i⁴`. -/
noncomputable def p4 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * 𝕩 i * 𝕩 i * 𝕩 i
/-- `q₁ = Σ_i x_i p₁ x_i`. -/
noncomputable def q1 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * p1 K N * 𝕩 i
/-- `q₂ = Σ_i x_i x_i p₁ x_i`. -/
noncomputable def q2 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * 𝕩 i * p1 K N * 𝕩 i
/-- `q₄ = Σ_i x_i p₁ x_i x_i`. -/
noncomputable def q4 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * p1 K N * 𝕩 i * 𝕩 i
/-- `s₂ = p₁p₁ - p₂`, the noncommutative `S_{2,N}`. -/
noncomputable def s2 : FreeAlgebra K (Fin N) := p1 K N * p1 K N - p2 K N
/-- `q₃ = Σ_i x_i s₂ x_i`. -/
noncomputable def q3 : FreeAlgebra K (Fin N) := ∑ i, 𝕩 i * s2 K N * 𝕩 i
/-- `s₃ = p₁s₂ - p₂p₁ - q₁ + 2p₃`, the noncommutative `S_{3,N}`. -/
noncomputable def s3 : FreeAlgebra K (Fin N) :=
  p1 K N * s2 K N - p2 K N * p1 K N - q1 K N + 2 * p3 K N
/-- `A = p₂s₂ - p₃p₁ - q₂ + 2p₄ = Σ_{(j,k,l) distinct} x_j x_j x_k x_l`. -/
noncomputable def tA : FreeAlgebra K (Fin N) :=
  p2 K N * s2 K N - p3 K N * p1 K N - q2 K N + 2 * p4 K N
/-- `B = q₃ - q₂ - q₄ + 2p₄ = Σ_{(j,k,l) distinct} x_l x_j x_k x_l`. -/
noncomputable def tB : FreeAlgebra K (Fin N) := q3 K N - q2 K N - q4 K N + 2 * p4 K N
/-- `C = q₁p₁ - p₃p₁ - q₄ - ID* + 2p₄ = Σ_{(j,k,l) distinct} x_k x_j x_k x_l`. -/
noncomputable def tC : FreeAlgebra K (Fin N) :=
  q1 K N * p1 K N - p3 K N * p1 K N - q4 K N - IDstar K N + 2 * p4 K N

variable {K N}

/-! ## The identity -/

theorem p1_eq : p1 K N = M1 fun _ => 1 := by simp [p1, M1]

theorem p2_eq : p2 K N = M2 fun i j => if i = j then 1 else 0 := by
  simp only [p2, M2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem p3_eq : p3 K N = M3 fun i j k => if j = k then if i = j then 1 else 0 else 0 := by
  simp only [p3, M3, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem p4_eq : p4 K N =
    M4 fun i j k l => if k = l then if j = k then if i = j then 1 else 0 else 0 else 0 := by
  simp only [p4, M4, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem q1_eq : q1 K N = M3 fun i _ k => if i = k then 1 else 0 := by
  rw [q1, p1_eq, conj_M1]

theorem q2_eq : q2 K N = M4 fun i j _ l => if j = l then if i = j then 1 else 0 else 0 := by
  simp only [q2, p1, M4, Finset.mul_sum, Finset.sum_mul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, if_true]

theorem q4_eq : q4 K N = M4 fun i _ k l => if k = l then if i = k then 1 else 0 else 0 := by
  simp only [q4, p1, M4, Finset.mul_sum, Finset.sum_mul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem q3_eq : q3 K N = M4 (fun i _ _ l => if i = l then (1 * 1 : K) else 0) -
    M4 fun i j k l => if i = l then (if j = k then 1 else 0) else 0 := by
  have h1 : ∑ m, 𝕩 m * (p1 K N * p1 K N) * 𝕩 m =
      M4 fun i _ _ l => if i = l then (1 * 1 : K) else 0 := by
    rw [p1_eq, M1_mul_M1, conj_M2]
  have h2 : ∑ m, 𝕩 m * p2 K N * 𝕩 m =
      M4 fun i j k l => if i = l then (if j = k then 1 else 0) else 0 := by
    rw [p2_eq, conj_M2]
  rw [← h1, ← h2, q3, s2, ← Finset.sum_sub_distrib]
  simp only [mul_sub, sub_mul]

theorem IDstar_eq :
    IDstar K N = M4 fun i j k l => if j = l then if i = k then 1 else 0 else 0 := by
  simp only [IDstar, M4, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem S4_eq_M4 : S4 K N = M4 fun i j k l =>
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then 1 else 0 := by
  simp only [S4, M4, ite_smul, one_smul, zero_smul]

/-- `p₁s₃ - A - B - C` expanded into products of the basic sums. -/
theorem expand : p1 K N * s3 K N - tA K N - tB K N - tC K N =
    (p1 K N * p1 K N * p1 K N * p1 K N - p1 K N * p1 K N * p2 K N - p1 K N * p2 K N * p1 K N
      - p1 K N * q1 K N + (p1 K N * p3 K N + p1 K N * p3 K N))
    - (p2 K N * p1 K N * p1 K N - p2 K N * p2 K N - p3 K N * p1 K N - q2 K N + (p4 K N + p4 K N))
    - (q3 K N - q2 K N - q4 K N + (p4 K N + p4 K N))
    - (q1 K N * p1 K N - p3 K N * p1 K N - q4 K N - IDstar K N + (p4 K N + p4 K N)) := by
  simp only [s3, tA, tB, tC, s2]
  noncomm_ring

/-- **The identity of Proposition 26.** `S_{4,N} = p₁s₃ - A - B - C`. -/
theorem S4_eq : S4 K N = p1 K N * s3 K N - tA K N - tB K N - tC K N := by
  rw [S4_eq_M4, expand, q3_eq, q1_eq, q2_eq, q4_eq, IDstar_eq, p1_eq, p2_eq, p3_eq, p4_eq]
  simp only [M1_mul_M1, M1_mul_M2, M2_mul_M1, M1_mul_M3, M3_mul_M1, M2_mul_M2, M4_add, M4_sub]
  congr 1
  funext i j k l
  rcases eq_or_ne i j with h1 | h1 <;> rcases eq_or_ne i k with h2 | h2 <;>
  rcases eq_or_ne i l with h3 | h3 <;> rcases eq_or_ne j k with h4 | h4 <;>
  rcases eq_or_ne j l with h5 | h5 <;> rcases eq_or_ne k l with h6 | h6 <;>
  simp_all

/-! ## The circuit -/

/-- Membership in a set built up by `insert` and `∪`, using the hypotheses in context. -/
local macro "mem" : tactic =>
  `(tactic| simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
    *])

section Build

variable {B : Set (FreeAlgebra K (Fin N))}

theorem input_mem (i : Fin N) : 𝕩 i ∈ ncInputs K (Fin N) := Or.inl ⟨i, rfl⟩

/-- A sum of `N` values indexed by `Fin N`, each computed with `t` gates. -/
theorem reach_sum_fin {f : Fin N → FreeAlgebra K (Fin N)} {t : ℕ}
    (h : ∀ i, Reach (ncInputs K (Fin N)) B {f i} t) :
    Reach (ncInputs K (Fin N)) B {∑ i, f i} (N * t + N + 1) := by
  have := reach_sum_each (inp := ncInputs K (Fin N)) (Or.inr ⟨0, map_zero _⟩) univ fun i _ => h i
  rwa [Finset.card_univ, Fintype.card_fin] at this

theorem reach_p1 : Reach (ncInputs K (Fin N)) B {p1 K N} (N * 1 + N + 1) :=
  reach_sum_fin fun i => Reach.input (input_mem i)

theorem reach_p2 : Reach (ncInputs K (Fin N)) B {p2 K N} (N * 2 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_p3 : Reach (ncInputs K (Fin N)) B {p3 K N} (N * 3 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_p4 : Reach (ncInputs K (Fin N)) B {p4 K N} (N * 4 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i * 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_q1 (hp : p1 K N ∈ B) : Reach (ncInputs K (Fin N)) B {q1 K N} (N * 3 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * p1 K N) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * p1 K N * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_q2 (hp : p1 K N ∈ B) : Reach (ncInputs K (Fin N)) B {q2 K N} (N * 4 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i * p1 K N) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * 𝕩 i * p1 K N * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_q4 (hp : p1 K N ∈ B) : Reach (ncInputs K (Fin N)) B {q4 K N} (N * 4 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * p1 K N) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * p1 K N * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * p1 K N * 𝕩 i * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem reach_q3 (hs : s2 K N ∈ B) : Reach (ncInputs K (Fin N)) B {q3 K N} (N * 3 + N + 1) :=
  reach_sum_fin fun i => by
    refine reach_cons_gate (Or.inl (input_mem i)) ?_
    refine reach_cons_gate (g := 𝕩 i * s2 K N) (isGate_mul (by mem) (by mem)) ?_
    refine reach_cons_gate (g := 𝕩 i * s2 K N * 𝕩 i) (isGate_mul (by mem) (by mem)) ?_
    exact Reach.refl (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/-- From any values containing `ID*_N`, `32 N + 46` more gates compute `S_{4,N}`. -/
theorem reach_S4 (hI : IDstar K N ∈ B) :
    Reach (ncInputs K (Fin N)) B {S4 K N} (32 * N + 46) := by
  have hm : (-1 : FreeAlgebra K (Fin N)) ∈ ncInputs K (Fin N) := Or.inr ⟨-1, by simp⟩
  have h2 : (2 : FreeAlgebra K (Fin N)) ∈ ncInputs K (Fin N) := Or.inr ⟨2, map_ofNat _ 2⟩
  rw [S4_eq]
  -- the power sums and the sums `q₁, q₂, q₄`: `27 N + 7` gates
  have h := ((((reach_p1 (B := B)).trans reach_p2).trans reach_p3).trans reach_p4)
  have h := h.trans (reach_q1 (by mem))
  have h := h.trans (reach_q2 (by mem))
  have h := h.trans (reach_q4 (by mem))
  -- the constants `-1, 2`, then `s₂ = p₁p₁ - p₂` and `q₃`: `4 N + 6` gates
  have h := reach_snoc h (g := -1) (Or.inl hm)
  have h := reach_snoc h (g := 2) (Or.inl h2)
  have h := reach_snoc h (g := p1 K N * p1 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := -p2 K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := s2 K N)
    (isGate_sub (p := p1 K N * p1 K N) (q := p2 K N) (by mem) (by mem))
  have h := h.trans (reach_q3 (by mem))
  -- `s₃ = p₁s₂ - p₂p₁ - q₁ + 2p₃`: 8 gates
  have h := reach_snoc h (g := p1 K N * s2 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := p2 K N * p1 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := -(p2 K N * p1 K N)) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p1 K N * s2 K N - p2 K N * p1 K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -q1 K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p1 K N * s2 K N - p2 K N * p1 K N - q1 K N)
    (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := 2 * p3 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := s3 K N)
    (isGate_add (p := p1 K N * s2 K N - p2 K N * p1 K N - q1 K N) (q := 2 * p3 K N)
      (by mem) (by mem))
  -- `A = p₂s₂ - p₃p₁ - q₂ + 2p₄`: 8 gates
  have h := reach_snoc h (g := p2 K N * s2 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := p3 K N * p1 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := -(p3 K N * p1 K N)) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p2 K N * s2 K N - p3 K N * p1 K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -q2 K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p2 K N * s2 K N - p3 K N * p1 K N - q2 K N)
    (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := 2 * p4 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := tA K N)
    (isGate_add (p := p2 K N * s2 K N - p3 K N * p1 K N - q2 K N) (q := 2 * p4 K N)
      (by mem) (by mem))
  -- `B = q₃ - q₂ - q₄ + 2p₄`: 4 gates
  have h := reach_snoc h (g := q3 K N - q2 K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -q4 K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := q3 K N - q2 K N - q4 K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := tB K N)
    (isGate_add (p := q3 K N - q2 K N - q4 K N) (q := 2 * p4 K N) (by mem) (by mem))
  -- `C = q₁p₁ - p₃p₁ - q₄ - ID* + 2p₄`: 6 gates
  have h := reach_snoc h (g := q1 K N * p1 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := q1 K N * p1 K N - p3 K N * p1 K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := q1 K N * p1 K N - p3 K N * p1 K N - q4 K N)
    (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -IDstar K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := q1 K N * p1 K N - p3 K N * p1 K N - q4 K N - IDstar K N)
    (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := tC K N)
    (isGate_add (p := q1 K N * p1 K N - p3 K N * p1 K N - q4 K N - IDstar K N) (q := 2 * p4 K N)
      (by mem) (by mem))
  -- `S₄ = p₁s₃ - A - B - C`: 7 gates
  have h := reach_snoc h (g := p1 K N * s3 K N) (isGate_mul (by mem) (by mem))
  have h := reach_snoc h (g := -tA K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p1 K N * s3 K N - tA K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -tB K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p1 K N * s3 K N - tA K N - tB K N) (isGate_sub (by mem) (by mem))
  have h := reach_snoc h (g := -tC K N) (isGate_neg (by mem) (by mem))
  have h := reach_snoc h (g := p1 K N * s3 K N - tA K N - tB K N - tC K N)
    (isGate_sub (by mem) (by mem))
  exact h.mono le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)

end Build

end Prop26

/-- **Hrubeš's Proposition 26, sharp count.** `S_{4,N}` costs at most the cost of `ID*_N` plus
`32 N + 46` gates. -/
theorem ncSizeLE_S4_of_IDstar_sharp {K : Type*} [CommRing K] {N s : ℕ}
    (h : NCSizeLE (IDstar K N) s) : NCSizeLE (S4 K N) (s + 32 * N + 46) :=
  ((h.reach.seq (Prop26.reach_S4 (Or.inr rfl))).mono le_rfl le_rfl (by omega)).ncSizeLE

/-- **Hrubeš's Proposition 26.** `S_{4,N}` costs at most the cost of `ID*_N` plus `O(N)` gates. -/
theorem ncSizeLE_S4_of_IDstar {K : Type*} [CommRing K] {N s : ℕ}
    (h : NCSizeLE (IDstar K N) s) : NCSizeLE (S4 K N) (s + 100 * N + 100) :=
  (ncSizeLE_S4_of_IDstar_sharp h).mono (by omega)

end PauliCubes
