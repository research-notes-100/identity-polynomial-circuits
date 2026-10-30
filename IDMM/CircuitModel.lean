/-
Two checks on the circuit model `PauliCubes.NCSizeLE`.

**Hrubeš's model, read strictly.** `NCSizeLE` lets a gate use one earlier value twice (`p * p`, `p + p`).
Hrubeš defines a circuit as a graph in which every non-input node has two incoming edges; read strictly,
these come from two *different* nodes. `StrictNCSizeLE` is that reading, stated by node positions.
`ncSizeLE_strict` turns a circuit with `s` nodes into a strict one with at most `2s + 1` nodes: one extra
constant node `1`, and after every node `g` a copy `1 * g`. Conversely every strict circuit is a circuit
(`StrictNCSizeLE.ncSizeLE`). The bound predicates transfer for every exponent `c ≥ 0` (`strict_of_bound`).

**Non-vacuity.** Every circuit computing `ID_N` has at least `2N` nodes, one for each variable
(`two_mul_le_of_ncSizeLE_ID`). Hence `IDBoundF F c` is false for every `c < 1` (`not_idBoundF_of_lt_one`):
the bound predicates are not satisfied trivially.
-/
import IDMM.Eventual
import PauliCubes.Sanity

namespace IDMM
open PauliCubes

universe u

/-! ### The strict model -/

section Strict

variable {R : Type*} [Ring R]

/-- **Strict circuits.** Node `k` of `gs` is an input, or the sum or the product (left factor first) of
the values at two *different* earlier nodes `i ≠ j`. -/
def StrictBuilds (inp : Set R) (gs : List R) : Prop :=
  ∀ (k : ℕ) (g : R), gs[k]? = some g → g ∈ inp ∨
    ∃ (i j : ℕ) (a b : R), i < k ∧ j < k ∧ i ≠ j ∧ gs[i]? = some a ∧ gs[j]? = some b ∧
      (g = a + b ∨ g = a * b)

theorem isGate_mono {inp B B' : Set R} {g : R} (h : IsGate inp B g) (hB : B ⊆ B') : IsGate inp B' g := by
  rcases h with h | ⟨p, hp, q, hq, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hB hp, q, hB hq, h⟩

/-- `Builds` in position form: every listed value is a gate over the start set and the values before it. -/
theorem builds_index {inp : Set R} :
    ∀ {B : Set R} {gs : List R}, Builds inp B gs →
      ∀ (k : ℕ) (g : R), gs[k]? = some g → IsGate inp (B ∪ {x | ∃ i : ℕ, i < k ∧ gs[i]? = some x}) g
  | _, [], _, k, g, hk => by simp at hk
  | B, g0 :: gs, ⟨h0, hrest⟩, k, g, hk => by
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact isGate_mono h0 Set.subset_union_left
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      refine isGate_mono (builds_index hrest k g hk) ?_
      rintro x (hx | ⟨i, hi, hx⟩)
      · rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact Or.inr ⟨0, Nat.succ_pos k, rfl⟩
        · exact Or.inl hx
      · exact Or.inr ⟨i + 1, Nat.succ_lt_succ hi, by simpa using hx⟩

/-- The converse: position-form gates give `Builds`. -/
theorem builds_of_index {inp : Set R} :
    ∀ {B : Set R} {gs : List R},
      (∀ (k : ℕ) (g : R), gs[k]? = some g → IsGate inp (B ∪ {x | ∃ i : ℕ, i < k ∧ gs[i]? = some x}) g) →
        Builds inp B gs
  | _, [], _ => trivial
  | B, g0 :: gs, h => by
    refine ⟨isGate_mono (h 0 g0 rfl) ?_, builds_of_index fun k g hk => ?_⟩
    · rintro x (hx | ⟨i, hi, -⟩)
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
    · refine isGate_mono (h (k + 1) g (by simpa using hk)) ?_
      rintro x (hx | ⟨i, hi, hx⟩)
      · exact Or.inl (Set.mem_insert_of_mem g0 hx)
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          exact Or.inl (hx ▸ Set.mem_insert g0 B)
        | succ i =>
          exact Or.inr ⟨i, Nat.lt_of_succ_lt_succ hi, by simpa using hx⟩

/-- Every node followed by its copy `1 * g`. -/
def twinAux : List R → List R
  | [] => []
  | g :: gs => g :: (1 * g) :: twinAux gs

theorem twinAux_length : ∀ gs : List R, (twinAux gs).length = 2 * gs.length
  | [] => rfl
  | _ :: gs => by simp [twinAux, twinAux_length gs]; ring

theorem twinAux_even : ∀ (gs : List R) (k : ℕ), (twinAux gs)[2 * k]? = gs[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: gs, k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simpa [twinAux] using twinAux_even gs k

theorem twinAux_odd : ∀ (gs : List R) (k : ℕ), (twinAux gs)[2 * k + 1]? = (gs[k]?).map (1 * ·)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: gs, k + 1 => by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring]
    simpa [twinAux] using twinAux_odd gs k

end Strict

variable {K V : Type*} [CommRing K]

/-- **Strict circuit size**: `f` is computed by a strict circuit over `K` with at most `s` nodes. -/
def StrictNCSizeLE (f : FreeAlgebra K V) (s : ℕ) : Prop :=
  ∃ gs : List (FreeAlgebra K V), StrictBuilds (ncInputs K V) gs ∧ gs.length ≤ s ∧ f ∈ gs

theorem StrictNCSizeLE.mono {f : FreeAlgebra K V} {s t : ℕ} (h : StrictNCSizeLE f s) (hst : s ≤ t) :
    StrictNCSizeLE f t := by
  obtain ⟨gs, hb, hl, hf⟩ := h
  exact ⟨gs, hb, hl.trans hst, hf⟩

/-- **Strict circuits are circuits.** -/
theorem StrictNCSizeLE.ncSizeLE {f : FreeAlgebra K V} {s : ℕ} (h : StrictNCSizeLE f s) : NCSizeLE f s := by
  obtain ⟨gs, hb, hl, hf⟩ := h
  refine ⟨gs, builds_of_index fun k g hk => ?_, hl, hf⟩
  rcases hb k g hk with hin | ⟨i, j, a, b, hi, hj, -, ha, hb', hg⟩
  · exact Or.inl hin
  · exact Or.inr ⟨a, Or.inr ⟨i, hi, ha⟩, b, Or.inr ⟨j, hj, hb'⟩, hg⟩

/-- **From circuits to strict circuits**: `s` nodes become at most `2s + 1`. -/
theorem ncSizeLE_strict {f : FreeAlgebra K V} {s : ℕ} (h : NCSizeLE f s) : StrictNCSizeLE f (2 * s + 1) := by
  classical
  obtain ⟨gs, hb, hl, hf⟩ := h
  have hidx := builds_index hb
  set one : FreeAlgebra K V := 1
  refine ⟨one :: twinAux gs, fun m g hm => ?_, ?_, ?_⟩
  · cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      exact Or.inl (Or.inr ⟨1, by rw [← hm, map_one]⟩)
    | succ n =>
      simp only [List.getElem?_cons_succ] at hm
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
      · -- the original node `gs[k]`, now at position `2k + 1`
        rw [twinAux_even] at hm
        rcases hidx k g hm with hin | ⟨p, hp, q, hq, hg⟩
        · exact Or.inl hin
        · simp only [Set.empty_union, Set.mem_ofPred_eq] at hp hq
          obtain ⟨i, hi, hpi⟩ := hp
          obtain ⟨j, hj, hqj⟩ := hq
          right
          by_cases hij : i = j
          · subst hij
            have hq' : q = p := Option.some.inj (hqj.symm.trans hpi)
            subst hq'
            refine ⟨2 * i + 1, 2 * i + 1 + 1, q, 1 * q, by omega, by omega, by omega, ?_, ?_, ?_⟩
            · simpa [twinAux_even] using hpi
            · simp [twinAux_odd, hpi]
            · rw [one_mul]; exact hg
          · refine ⟨2 * i + 1, 2 * j + 1, p, q, by omega, by omega, by omega, ?_, ?_, hg⟩
            · simpa [twinAux_even] using hpi
            · simpa [twinAux_even] using hqj
      · -- the copy `1 * gs[k]`, at position `2k + 2`
        rw [twinAux_odd] at hm
        obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.mp hm
        right
        refine ⟨0, 2 * k + 1, one, g0, by omega, by omega, by omega, rfl, ?_, Or.inr rfl⟩
        simpa [twinAux_even] using hg0
  · simp only [List.length_cons, twinAux_length]; omega
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hf
    have : (one :: twinAux gs)[2 * k + 1]? = some gs[k] := by
      simp [twinAux_even, List.getElem?_eq_getElem hk]
    exact List.mem_of_getElem? this

theorem not_strictNCSizeLE_zero (f : FreeAlgebra K V) : ¬ StrictNCSizeLE f 0 := by
  rintro ⟨gs, -, hl, hf⟩
  rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hf
  exact List.not_mem_nil hf

/-! ### Bound predicates in the strict model -/

/-- The strict version of a bound: `f N` has strict circuits with `⌊C·N^{c+ε}⌋` nodes. -/
def StrictBound {F : Type u} [Field F] {W : ℕ → Type} (f : ∀ N, FreeAlgebra F (W N)) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → StrictNCSizeLE (f N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊

/-- `IDBoundF` in the strict model. -/
def StrictIDBoundF (F : Type u) [Field F] (c : ℝ) : Prop := StrictBound (ID F) c
/-- `S4BoundF` in the strict model. -/
def StrictS4BoundF (F : Type u) [Field F] (c : ℝ) : Prop := StrictBound (S4 F) c
/-- `Perm4BoundF` in the strict model. -/
def StrictPerm4BoundF (F : Type u) [Field F] (c : ℝ) : Prop := StrictBound (perm4 F) c

/-- **Bounds transfer to the strict model**, for every exponent `c ≥ 0`, with constant `2C + 1`. -/
theorem strict_of_bound {F : Type u} [Field F] {W : ℕ → Type} {f : ∀ N, FreeAlgebra F (W N)} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → NCSizeLE (f N) ⌊C * (N : ℝ) ^ (c + ε)⌋₊) :
    StrictBound f c := by
  intro ε hε
  obtain ⟨C, hC, hN⟩ := h ε hε
  refine ⟨2 * C + 1, by positivity, fun N hN1 => ?_⟩
  refine (ncSizeLE_strict (hN N hN1)).mono (Nat.le_floor ?_)
  set x : ℝ := (N : ℝ) ^ (c + ε)
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  have hfl : (⌊C * x⌋₊ : ℝ) ≤ C * x := Nat.floor_le (by positivity)
  push_cast
  nlinarith

theorem StrictIDBoundF.of {F : Type u} [Field F] {c : ℝ} (hc : 0 ≤ c) (h : IDBoundF F c) :
    StrictIDBoundF F c := strict_of_bound hc h
theorem StrictS4BoundF.of {F : Type u} [Field F] {c : ℝ} (hc : 0 ≤ c) (h : S4BoundF F c) :
    StrictS4BoundF F c := strict_of_bound hc h
theorem StrictPerm4BoundF.of {F : Type u} [Field F] {c : ℝ} (hc : 0 ≤ c) (h : Perm4BoundF F c) :
    StrictPerm4BoundF F c := strict_of_bound hc h

/-! ### Non-vacuity: `ID_N` needs at least `2N` nodes -/

/-- Every value of a circuit lies in the subalgebra generated by the variables it uses as nodes. -/
theorem mem_adjoin_of_builds {F : Type u} [Field F] {V : Type} {gs : List (FreeAlgebra F V)}
    (hb : Builds (ncInputs F V) ∅ gs) :
    ∀ g ∈ gs, g ∈ Algebra.adjoin F (FreeAlgebra.ι F '' {v | FreeAlgebra.ι F v ∈ gs}) := by
  set A := Algebra.adjoin F (FreeAlgebra.ι F '' {v | FreeAlgebra.ι F v ∈ gs})
  have hidx := builds_index hb
  suffices ∀ (k : ℕ) (g : FreeAlgebra F V), gs[k]? = some g → g ∈ A by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    exact this k _ (List.getElem?_eq_getElem hk)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    rcases hidx k g hg with (⟨v, rfl⟩ | ⟨r, rfl⟩) | ⟨p, hp, q, hq, hpq⟩
    · exact Algebra.subset_adjoin ⟨v, List.mem_of_getElem? hg, rfl⟩
    · exact Subalgebra.algebraMap_mem A r
    · simp only [Set.empty_union, Set.mem_ofPred_eq] at hp hq
      obtain ⟨i, hi, hpi⟩ := hp
      obtain ⟨j, hj, hqj⟩ := hq
      rcases hpq with rfl | rfl
      · exact add_mem (ih i hi p hpi) (ih j hj q hqj)
      · exact mul_mem (ih i hi p hpi) (ih j hj q hqj)

/-- `ID_N` evaluated at a point of the commutative field `F`. -/
theorem eval_ID {F : Type u} [Field F] (N : ℕ) (val : Fin N ⊕ Fin N → F) :
    FreeAlgebra.lift F val (ID F N) =
      ∑ i : Fin N, ∑ j : Fin N, (val (Sum.inl i) * val (Sum.inr j)) ^ 2 := by
  simp only [ID, map_sum, map_mul, FreeAlgebra.lift_ι_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Every circuit computing `ID_N` has at least `2N` nodes**: each of the `2N` variables is a node. -/
theorem two_mul_le_of_ncSizeLE_ID {F : Type u} [Field F] {N s : ℕ} (h : NCSizeLE (ID F N) s) :
    2 * N ≤ s := by
  classical
  obtain ⟨gs, hb, hl, hf⟩ := h
  set S := {v | FreeAlgebra.ι F v ∈ gs}
  have hID := mem_adjoin_of_builds hb _ hf
  -- two evaluations that agree on the variables in `S` agree on `ID_N`
  have agree : ∀ val val' : Fin N ⊕ Fin N → F, (∀ v ∈ S, val v = val' v) →
      FreeAlgebra.lift F val (ID F N) = FreeAlgebra.lift F val' (ID F N) := by
    intro val val' hvv
    have hle : Algebra.adjoin F (FreeAlgebra.ι F '' S) ≤
        AlgHom.equalizer (FreeAlgebra.lift F val) (FreeAlgebra.lift F val') := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AlgHom.mem_equalizer, FreeAlgebra.lift_ι_apply]
      exact hvv v hv
    exact hle hID
  have hall : ∀ v : Fin N ⊕ Fin N, v ∈ S := by
    intro v
    by_contra hv
    -- a partner variable on the other side
    have hN : 0 < N := by rcases v with i | i <;> exact Fin.pos i
    let w : Fin N ⊕ Fin N := match v with
      | Sum.inl _ => Sum.inr ⟨0, hN⟩
      | Sum.inr _ => Sum.inl ⟨0, hN⟩
    have hwv : w ≠ v := by rcases v with i | i <;> simp [w]
    let val : Fin N ⊕ Fin N → F := fun u => if u = v ∨ u = w then 1 else 0
    let val' : Fin N ⊕ Fin N → F := fun u => if u = w then 1 else 0
    have heq := agree val val' fun u hu => by
      have : u ≠ v := fun h => hv (h ▸ hu)
      simp [val, val', this]
    rw [eval_ID, eval_ID] at heq
    -- the left side is 1 (only the monomial of `v` and `w` survives), the right side is 0
    have lhs : ∑ i : Fin N, ∑ j : Fin N, (val (Sum.inl i) * val (Sum.inr j)) ^ 2 = 1 := by
      rcases v with i0 | j0
      · rw [Finset.sum_eq_single i0, Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
        · simp [val, w]
        · intro j _ hj; simp [val, w, hj]
        · simp
        · intro i _ hi; simp [val, w, hi]
        · simp
      · rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N), Finset.sum_eq_single j0]
        · simp [val, w]
        · intro j _ hj; simp [val, w, hj]
        · simp
        · intro i _ hi; simp [val, w, hi]
        · simp
    have rhs : ∑ i : Fin N, ∑ j : Fin N, (val' (Sum.inl i) * val' (Sum.inr j)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rcases v with i0 | j0 <;> simp [val', w]
    rw [lhs, rhs] at heq
    exact one_ne_zero heq
  -- the `2N` variable nodes are distinct elements of `gs`
  have hsub : (Finset.univ.image (FreeAlgebra.ι F : Fin N ⊕ Fin N → FreeAlgebra F (Fin N ⊕ Fin N))) ⊆
      gs.toFinset := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (hall v)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (FreeAlgebra.ι_injective (R := F)), Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin] at hcard
  calc 2 * N = N + N := by ring
    _ ≤ gs.toFinset.card := hcard
    _ ≤ gs.length := List.toFinset_card_le gs
    _ ≤ s := hl

/-- **The bound predicate is not vacuous**: no exponent below 1 is achievable for `ID_N`. -/
theorem not_idBoundF_of_lt_one {F : Type u} [Field F] {c : ℝ} (hc : c < 1) : ¬ IDBoundF F c := by
  intro h
  obtain ⟨C, hC, hN⟩ := h ((1 - c) / 2) (by linarith)
  set a : ℝ := c + (1 - c) / 2
  have ha : 0 < 1 - a := by simp only [a]; linarith
  -- `N^(1-a)` eventually exceeds `C`
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hbig, hN1⟩ := ((ht.eventually_gt_atTop C).and (Filter.eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsize := two_mul_le_of_ncSizeLE_ID (hN N hN1)
  have h1 : (2 * N : ℝ) ≤ C * (N : ℝ) ^ a := by
    calc (2 * N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ⌊C * (N : ℝ) ^ a⌋₊ := by exact_mod_cast hsize
      _ ≤ C * (N : ℝ) ^ a := Nat.floor_le (by positivity)
  have hsplit : (N : ℝ) = (N : ℝ) ^ (1 - a) * (N : ℝ) ^ a := by
    rw [← Real.rpow_add hNpos]; simp
  have hNa : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos a
  nlinarith

/-- The strict model is not vacuous either. -/
theorem not_strictIDBoundF_of_lt_one {F : Type u} [Field F] {c : ℝ} (hc : c < 1) :
    ¬ StrictIDBoundF F c := fun h =>
  not_idBoundF_of_lt_one hc fun ε hε => (h ε hε).imp fun _C hC =>
    ⟨hC.1, fun N hN => (hC.2 N hN).ncSizeLE⟩

/-- The strict model is satisfiable: `ID_N` has strict circuits with `2(4N² + 2N + 1) + 1` nodes. -/
theorem strict_id_trivial (F : Type u) [Field F] (N : ℕ) :
    StrictNCSizeLE (ID F N) (2 * (4 * N ^ 2 + 2 * N + 1) + 1) :=
  ncSizeLE_strict (PauliCubes.id_trivial F N)

end IDMM
