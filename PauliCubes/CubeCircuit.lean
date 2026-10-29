/-
A circuit for one cube's weighted noncommutative squares. Over a field with `2 ≠ 0` and
`i * i = -1`, the local two-multiplication algorithms tensor to
`P_ν[x, y] = Σ_k c(ν, k) Ā(k, x) B̄(k, y)` with Kronecker products `Ā`, `B̄`,
`c`. With `α_k = (Ā X)_k`, `β_k = (B̄ Y)_k` and
`λ_k = Σ_ν w_ν c(ν, k) f^yx_ν`,
`Σ_{ν ∈ Q} w_ν f_ν^[2] = ½ (Σ_ν w_ν f^xy_ν f^xy_ν + Σ_k α_k λ_k β_k)` (`sum_f2_eq`).
Every Kronecker transform costs `5 n 2^n` gates (`kron_reach`), so the sum costs
`(25 n + 13) 2^n + 5` gates (`cube_circuit_count`, `cube_circuit`).
-/
import PauliCubes.CubeRank
import PauliCubes.Circuit
import PauliCubes.NCForms

open Finset

namespace PauliCubes

/-! ## Generic gate counts -/

section Generic

variable {R : Type*} [Ring R] {inp : Set R}

/-- A family of values, each reachable with `t` gates, is reachable with `card * t` gates. -/
theorem reach_range {ι : Type*} [Fintype ι] {B : Set R} {f : ι → R} {t : ℕ}
    (h : ∀ i, Reach inp B {f i} t) : Reach inp B (Set.range f) (Fintype.card ι * t) := by
  classical
  refine (Reach.biUnion univ fun i _ => h i).mono le_rfl ?_ (by simp)
  rintro _ ⟨i, rfl⟩
  exact Set.mem_biUnion (mem_univ i) rfl

/-- Sequential composition keeping all values, from a smaller base. -/
theorem Reach.then {B B' S T : Set R} {s t : ℕ} (h₁ : Reach inp B S s) (h₂ : Reach inp B' T t)
    (hB : B' ⊆ B ∪ S) : Reach inp B (S ∪ T) (s + t) :=
  h₁.trans (h₂.mono hB le_rfl le_rfl)

end Generic

section Algebra

variable {L : Type*} [Field L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {inp : Set 𝒜}

/-- A scalar multiple of an available value: one constant and one product. -/
theorem reach_smul (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {B : Set 𝒜} {u : 𝒜} (hu : u ∈ B)
    (c : L) : Reach inp B {c • u} 2 := by
  rw [Algebra.smul_def]
  exact (Reach.input (hc c)).seq (Reach.mul (Or.inr rfl) (Or.inl hu))

/-- A two-term linear combination of available values: five gates. -/
theorem reach_lin2 (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {B : Set 𝒜} {u₀ u₁ : 𝒜} (h₀ : u₀ ∈ B)
    (h₁ : u₁ ∈ B) (c₀ c₁ : L) : Reach inp B {c₀ • u₀ + c₁ • u₁} 5 :=
  ((reach_smul hc h₀ c₀).union (reach_smul hc h₁ c₁)).seq
    (Reach.add (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))

/-- A linear combination of available values with coefficients in `L`. -/
theorem reach_smulSum (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {ι : Type*} (s : Finset ι)
    {B : Set 𝒜} {c : ι → L} {p : ι → 𝒜} (hp : ∀ i ∈ s, p i ∈ B) :
    Reach inp B {∑ i ∈ s, c i • p i} (3 * s.card + 1) := by
  classical
  have h0 : (0 : 𝒜) ∈ inp := by simpa using hc 0
  simp only [Algebra.smul_def]
  exact Reach.linComb h0 s (fun i _ => hc (c i)) hp

/-! ## The fast Kronecker transform -/

/-- The Kronecker transform `(T_M v)(k) = Σ_x (∏_j M_j[k_j, x_j]) v_x`. -/
noncomputable def kronTransform {n : ℕ} (M : Fin n → Fin 2 → Fin 2 → L) (v : (Fin n → Fin 2) → 𝒜)
    (k : Fin n → Fin 2) : 𝒜 :=
  ∑ x, (∏ j, M j (k j) (x j)) • v x

/-- Splitting off the first coordinate. -/
theorem kronTransform_succ {n : ℕ} (M : Fin (n + 1) → Fin 2 → Fin 2 → L)
    (v : (Fin (n + 1) → Fin 2) → 𝒜) (k : Fin (n + 1) → Fin 2) :
    kronTransform M v k =
      M 0 (k 0) 0 • kronTransform (fun j => M j.succ) (fun x => v (Fin.cons 0 x)) (Fin.tail k) +
      M 0 (k 0) 1 • kronTransform (fun j => M j.succ) (fun x => v (Fin.cons 1 x)) (Fin.tail k) := by
  simp only [kronTransform]
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul,
    Finset.smul_sum, Fin.tail]
  rfl

/-- **Fast Kronecker transform.** All `2^n` values of a Kronecker transform of available values are
reachable with `5 n 2^n` gates. -/
theorem kron_reach (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {B : Set 𝒜} :
    ∀ {n : ℕ} (M : Fin n → Fin 2 → Fin 2 → L) (v : (Fin n → Fin 2) → 𝒜), (∀ x, v x ∈ B) →
      Reach inp B (Set.range (kronTransform M v)) (5 * n * 2 ^ n)
  | 0, M, v, hv => Reach.refl (by rintro _ ⟨k, rfl⟩; simp [kronTransform, hv])
  | n + 1, M, v, hv => by
    have h₁ := (kron_reach hc (fun j => M j.succ) (fun x => v (Fin.cons 0 x)) fun _ => hv _).union
      (kron_reach hc (fun j => M j.succ) (fun x => v (Fin.cons 1 x)) fun _ => hv _)
    have h₂ : Reach inp (B ∪ (Set.range (kronTransform (fun j => M j.succ)
          (fun x => v (Fin.cons 0 x))) ∪ Set.range (kronTransform (fun j => M j.succ)
          (fun x => v (Fin.cons 1 x))))) (Set.range (kronTransform M v)) (2 ^ (n + 1) * 5) := by
      refine (reach_range (t := 5) fun k => ?_).mono le_rfl le_rfl (by simp)
      rw [kronTransform_succ]
      exact reach_lin2 hc (Or.inr (Or.inl ⟨_, rfl⟩)) (Or.inr (Or.inr ⟨_, rfl⟩)) _ _
    refine (h₁.seq h₂).mono le_rfl le_rfl (le_of_eq ?_)
    ring

end Algebra

/-! ## The words of a cube -/

/-- The word of the cube `a, b` selected by `σ`: the letter `a j` where `σ j = 0`, else `b j`. -/
def cubeWord {n : ℕ} (a b : Fin n → Fin 4) (σ : Fin n → Fin 2) : Fin n → Fin 4 :=
  fun j => if σ j = 0 then a j else b j

theorem cubeWord_mem {n : ℕ} (a b : Fin n → Fin 4) (σ : Fin n → Fin 2) :
    cubeWord a b σ ∈ cube a b := by
  refine Fintype.mem_piFinset.mpr fun j => ?_
  unfold cubeWord
  split_ifs <;> simp

/-- A sum over a cube is a sum over its selectors. -/
theorem sum_cube {M : Type*} [AddCommMonoid M] {n : ℕ} {a b : Fin n → Fin 4}
    (hab : ∀ j, a j ≠ b j) (f : (Fin n → Fin 4) → M) :
    ∑ ν ∈ cube a b, f ν = ∑ σ, f (cubeWord a b σ) := by
  have hl : ∀ ν ∈ cube a b, cubeWord a b (fun j => if ν j = a j then 0 else 1) = ν := by
    intro ν hν
    funext j
    have hj := Fintype.mem_piFinset.mp hν j
    simp only [mem_insert, mem_singleton] at hj
    unfold cubeWord
    by_cases h : ν j = a j
    · simp [h]
    · simp only [h, if_false, one_ne_zero]
      exact (hj.resolve_left h).symm
  refine Finset.sum_nbij' (fun ν j => if ν j = a j then 0 else 1) (cubeWord a b) (by simp)
    (fun σ _ => cubeWord_mem a b σ) hl ?_ fun ν hν => by rw [hl ν hν]
  intro σ _
  funext j
  unfold cubeWord
  by_cases h : σ j = 0
  · simp [h]
  · simp only [h, if_false, (hab j).symm]
    omega

/-- The words of a cube tensor the local algorithms: `P_{ν_σ}[x, y] = Σ_k c(σ, k) Ā(k, x) B̄(k, y)`
with Kronecker products `c`, `Ā`, `B̄`. -/
theorem cube_word {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {i : L} (hi : i * i = -1) {n : ℕ}
    (a b : Fin n → Fin 4) (hab : ∀ j, a j ≠ b j) :
    ∃ A B C : Fin n → Fin 2 → Fin 2 → L, ∀ σ x y, pauliWord L (cubeWord a b σ) x y =
      ∑ k : Fin n → Fin 2, (∏ j, C j (σ j) (k j)) * (∏ j, A j (k j) (x j)) *
        (∏ j, B j (k j) (y j)) := by
  have hloc := fun j => local_pair h2 hi (a j) (b j) (hab j)
  simp only [PairAlg] at hloc
  choose A B c hc using hloc
  refine ⟨A, B, fun j s κ => c j (if s = 0 then a j else b j) κ, ?_⟩
  intro σ x y
  have hmem : ∀ j, cubeWord a b σ j ∈ ({a j, b j} : Finset (Fin 4)) := by
    intro j
    unfold cubeWord
    split_ifs <;> simp
  rw [pauliWord, Finset.prod_congr rfl fun j _ => hc j _ (hmem j) (x j) (y j),
    Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rfl

/-! ## The noncommutative forms through `α` and `β` -/

section Forms

variable {L : Type*} [Field L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜]

/-- A bilinear rank decomposition `P[x, y] = Σ_k c_k a_k(x) b_k(y)` carries over to any bilinear
map. -/
theorem bilin_expand {ι κ : Type*} [Fintype ι] [Fintype κ] {P : ι → ι → L} {c : κ → L}
    {a' b' : κ → ι → L} (hP : ∀ x y, P x y = ∑ k, c k * a' k x * b' k y)
    (Φ : 𝒜 →ₗ[L] 𝒜 →ₗ[L] 𝒜) (X Y : ι → 𝒜) :
    ∑ x, ∑ y, P x y • Φ (X x) (Y y) = ∑ k, c k • Φ (∑ x, a' k x • X x) (∑ y, b' k y • Y y) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ring

variable {n : ℕ} {a b : Fin n → Fin 4} {A B C : Fin n → Fin 2 → Fin 2 → L}
  (hw : ∀ σ x y, pauliWord L (cubeWord a b σ) x y =
      ∑ k : Fin n → Fin 2, (∏ j, C j (σ j) (k j)) * (∏ j, A j (k j) (x j)) *
        (∏ j, B j (k j) (y j)))
  (X Y : (Fin n → Fin 2) → 𝒜)

include hw

theorem form_cubeWord (Φ : 𝒜 →ₗ[L] 𝒜 →ₗ[L] 𝒜) (σ : Fin n → Fin 2) :
    ∑ x, ∑ y, pauliWord L (cubeWord a b σ) x y • Φ (X x) (Y y) =
      ∑ k, (∏ j, C j (σ j) (k j)) • Φ (kronTransform A X k) (kronTransform B Y k) :=
  bilin_expand (hw σ) Φ X Y

theorem fxy_cubeWord (σ : Fin n → Fin 2) :
    fxy (L := L) X Y (cubeWord a b σ) =
      kronTransform C (fun k => kronTransform A X k * kronTransform B Y k) σ := by
  have := form_cubeWord hw X Y (LinearMap.mul L 𝒜) σ
  simp only [LinearMap.mul_apply'] at this
  exact this

theorem fyx_cubeWord (σ : Fin n → Fin 2) :
    fyx (L := L) X Y (cubeWord a b σ) =
      kronTransform C (fun k => kronTransform B Y k * kronTransform A X k) σ := by
  have := form_cubeWord hw X Y (LinearMap.mul L 𝒜).flip σ
  simp only [LinearMap.flip_apply, LinearMap.mul_apply'] at this
  exact this

theorem fstar_cubeWord (σ : Fin n → Fin 2) (z : 𝒜) :
    fstar (L := L) X Y (cubeWord a b σ) z =
      ∑ k, (∏ j, C j (σ j) (k j)) • (kronTransform A X k * z * kronTransform B Y k) := by
  have := form_cubeWord hw X Y ((LinearMap.mul L 𝒜).comp (LinearMap.mulRight L z)) σ
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mul_apply'] at this
  exact this

/-- **The circuit's formula.** With `α = Ā X`, `β = B̄ Y`, `F_σ = f^xy_{ν_σ}`, `G_σ = f^yx_{ν_σ}`
and `λ = cᵀ (w G)`, `Σ_{ν ∈ Q} w_ν f_ν^[2] = ½ (Σ_σ w_σ F_σ F_σ + Σ_k α_k λ_k β_k)`. -/
theorem sum_f2_eq (hab : ∀ j, a j ≠ b j) (w : (Fin n → Fin 4) → L)
    {α β F G lam : (Fin n → Fin 2) → 𝒜}
    (hα : α = kronTransform A X) (hβ : β = kronTransform B Y)
    (hF : F = kronTransform C fun k => α k * β k) (hG : G = kronTransform C fun k => β k * α k)
    (hlam : lam = kronTransform (fun j s t => C j t s) fun σ => w (cubeWord a b σ) • G σ) :
    ∑ ν ∈ cube a b, w ν • f2 (L := L) X Y ν =
      (2 : L)⁻¹ • (∑ σ, w (cubeWord a b σ) • (F σ * F σ) + ∑ k, α k * lam k * β k) := by
  subst hα hβ hF hG hlam
  rw [sum_cube hab]
  simp only [f2, fxy_cubeWord hw, fyx_cubeWord hw, fstar_cubeWord hw]
  have key : ∀ (α β G : (Fin n → Fin 2) → 𝒜), ∑ σ, w (cubeWord a b σ) •
      ∑ k, (∏ j, C j (σ j) (k j)) • (α k * G σ * β k) =
      ∑ k, α k * kronTransform (fun j s t => C j t s)
        (fun σ => w (cubeWord a b σ) • G σ) k * β k := by
    intro α β G
    simp only [kronTransform, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => ?_)
    rw [mul_comm]
  rw [← key, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_comm, smul_add]

end Forms

/-! ## The circuit -/

section Circuit

variable {L : Type*} [Field L] {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {inp : Set 𝒜}

/-- A family indexed by bit strings, each value reachable with `t` gates. -/
theorem reach_range_bits {n : ℕ} {B : Set 𝒜} {f : (Fin n → Fin 2) → 𝒜} {t : ℕ}
    (h : ∀ k, Reach inp B {f k} t) : Reach inp B (Set.range f) (2 ^ n * t) := by
  simpa using reach_range h

/-- Closes `B' ⊆ B ∪ S₁ ∪ ⋯ ∪ Sₘ` when every part of `B'` is one of the `Sᵢ`. -/
local macro "subset_union" : tactic =>
  `(tactic| (intro z hz; simp only [Set.mem_union] at hz ⊢; tauto))

/-- **One cube's weighted squares, exact count.** For a cube `Q = cube a b`, the weighted sum
`Σ_{ν ∈ Q} w_ν f_ν^[2]` of the noncommutative squares of its `2^n` forms is computed from the
variables and the constants of `L` with at most `(25 n + 13) 2^n + 5` gates. -/
theorem cube_circuit_count {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {i : L} (hi : i * i = -1)
    {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {inp : Set 𝒜}
    (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {n : ℕ} {X Y : (Fin n → Fin 2) → 𝒜}
    (hX : ∀ x, X x ∈ inp) (hY : ∀ y, Y y ∈ inp)
    (a b : Fin n → Fin 4) (hab : ∀ j, a j ≠ b j) (w : (Fin n → Fin 4) → L) :
    Reach inp ∅ {∑ ν ∈ cube a b, w ν • f2 (L := L) X Y ν} ((25 * n + 13) * 2 ^ n + 5) := by
  obtain ⟨A, B, C, hw⟩ := cube_word h2 hi a b hab
  obtain ⟨α, hα⟩ : ∃ f, f = kronTransform A X := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ f, f = kronTransform B Y := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ f, f = kronTransform C fun k => α k * β k := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ f, f = kronTransform C fun k => β k * α k := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ f, f = kronTransform (fun j s t => C j t s)
      fun σ => w (cubeWord a b σ) • G σ := ⟨_, rfl⟩
  rw [sum_f2_eq hw X Y hab w hα hβ hF hG hlam]
  have h0 : (0 : 𝒜) ∈ inp := by simpa using hc 0
  -- the inputs
  have r1 : Reach inp ∅ (Set.range X) (2 ^ n * 1) := reach_range_bits fun x => Reach.input (hX x)
  have r2 : Reach inp ∅ (Set.range Y) (2 ^ n * 1) := reach_range_bits fun y => Reach.input (hY y)
  -- `α = Ā X`, `β = B̄ Y`
  have r3 : Reach inp (Set.range X) (Set.range α) (5 * n * 2 ^ n) := by
    rw [hα]; exact kron_reach hc A X fun x => ⟨x, rfl⟩
  have r4 : Reach inp (Set.range Y) (Set.range β) (5 * n * 2 ^ n) := by
    rw [hβ]; exact kron_reach hc B Y fun y => ⟨y, rfl⟩
  -- the products `α_k β_k` and `β_k α_k`
  have r5 : Reach inp (Set.range α ∪ Set.range β) (Set.range fun k => α k * β k) (2 ^ n * 1) :=
    reach_range_bits fun k => Reach.mul (Or.inl ⟨k, rfl⟩) (Or.inr ⟨k, rfl⟩)
  have r6 : Reach inp (Set.range α ∪ Set.range β) (Set.range fun k => β k * α k) (2 ^ n * 1) :=
    reach_range_bits fun k => Reach.mul (Or.inr ⟨k, rfl⟩) (Or.inl ⟨k, rfl⟩)
  -- the forms `F_σ = f^xy_{ν_σ}` and `G_σ = f^yx_{ν_σ}`
  have r7 : Reach inp (Set.range fun k => α k * β k) (Set.range F) (5 * n * 2 ^ n) := by
    rw [hF]; exact kron_reach hc C _ fun k => ⟨k, rfl⟩
  have r8 : Reach inp (Set.range fun k => β k * α k) (Set.range G) (5 * n * 2 ^ n) := by
    rw [hG]; exact kron_reach hc C _ fun k => ⟨k, rfl⟩
  -- `λ = cᵀ (w G)`
  have r9 : Reach inp (Set.range G) (Set.range fun σ => w (cubeWord a b σ) • G σ) (2 ^ n * 2) :=
    reach_range_bits fun σ => reach_smul hc (Set.mem_range_self σ) _
  have r10 : Reach inp (Set.range fun σ => w (cubeWord a b σ) • G σ) (Set.range lam)
      (5 * n * 2 ^ n) := by
    rw [hlam]; exact kron_reach hc _ _ fun σ => ⟨σ, rfl⟩
  -- `Σ_σ w_σ F_σ F_σ`
  have r11 : Reach inp (Set.range F) (Set.range fun σ => F σ * F σ) (2 ^ n * 1) :=
    reach_range_bits fun σ => Reach.mul (Set.mem_range_self σ) (Set.mem_range_self σ)
  have r12 : Reach inp (Set.range fun σ => F σ * F σ) {∑ σ, w (cubeWord a b σ) • (F σ * F σ)}
      (3 * 2 ^ n + 1) := by
    simpa using reach_smulSum hc (univ : Finset (Fin n → Fin 2))
      (B := Set.range fun σ => F σ * F σ) (c := fun σ => w (cubeWord a b σ))
      (p := fun σ => F σ * F σ) fun σ _ => Set.mem_range_self σ
  -- `Σ_k α_k λ_k β_k`
  have r13 : Reach inp (Set.range α ∪ Set.range lam) (Set.range fun k => α k * lam k) (2 ^ n * 1) :=
    reach_range_bits fun k => Reach.mul (Or.inl ⟨k, rfl⟩) (Or.inr ⟨k, rfl⟩)
  have r14 : Reach inp ((Set.range fun k => α k * lam k) ∪ Set.range β)
      (Set.range fun k => α k * lam k * β k) (2 ^ n * 1) :=
    reach_range_bits fun k => Reach.mul (Or.inl ⟨k, rfl⟩) (Or.inr ⟨k, rfl⟩)
  have r15 : Reach inp (Set.range fun k => α k * lam k * β k) {∑ k, α k * lam k * β k}
      (2 ^ n + 1) := by
    simpa using Reach.sum h0 (univ : Finset (Fin n → Fin 2))
      (B := Set.range fun k => α k * lam k * β k) (p := fun k => α k * lam k * β k)
      fun k _ => Set.mem_range_self k
  -- the total
  have r16 : Reach inp ({∑ σ, w (cubeWord a b σ) • (F σ * F σ)} ∪ {∑ k, α k * lam k * β k})
      {∑ σ, w (cubeWord a b σ) • (F σ * F σ) + ∑ k, α k * lam k * β k} 1 :=
    Reach.add (Or.inl rfl) (Or.inr rfl)
  have r17 : Reach inp {∑ σ, w (cubeWord a b σ) • (F σ * F σ) + ∑ k, α k * lam k * β k}
      {(2 : L)⁻¹ • (∑ σ, w (cubeWord a b σ) • (F σ * F σ) + ∑ k, α k * lam k * β k)} 2 :=
    reach_smul hc (Set.mem_singleton _) _
  have r := (((((((((((((((r1.then r2 (by subset_union)).then r3 (by subset_union)).then r4
    (by subset_union)).then r5 (by subset_union)).then r6 (by subset_union)).then r7
    (by subset_union)).then r8 (by subset_union)).then r9 (by subset_union)).then r10
    (by subset_union)).then r11 (by subset_union)).then r12 (by subset_union)).then r13
    (by subset_union)).then r14 (by subset_union)).then r15 (by subset_union)).then r16
    (by subset_union)).then r17 (by subset_union)
  refine r.mono le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (le_of_eq ?_)
  ring

/-- **One cube's weighted squares.** For a cube `Q = cube a b`, the weighted sum
`Σ_{ν ∈ Q} w_ν f_ν^[2]` of the noncommutative squares of its `2^n` forms is computed from the
variables and the constants of `L` with `O(n 2^n)` gates: at most `100 (n + 1) 2^n` (the exact count
is `(25 n + 13) 2^n + 5`, `cube_circuit_count`). -/
theorem cube_circuit {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {i : L} (hi : i * i = -1)
    {𝒜 : Type*} [Ring 𝒜] [Algebra L 𝒜] {inp : Set 𝒜}
    (hc : ∀ c : L, algebraMap L 𝒜 c ∈ inp) {n : ℕ} {X Y : (Fin n → Fin 2) → 𝒜}
    (hX : ∀ x, X x ∈ inp) (hY : ∀ y, Y y ∈ inp)
    (a b : Fin n → Fin 4) (hab : ∀ j, a j ≠ b j) (w : (Fin n → Fin 4) → L) :
    Reach inp ∅ {∑ ν ∈ cube a b, w ν • f2 (L := L) X Y ν} (100 * (n + 1) * 2 ^ n) := by
  refine (cube_circuit_count h2 hi hc hX hY a b hab w).mono le_rfl le_rfl ?_
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith [Nat.zero_le (n * 2 ^ n)]

end Circuit

end PauliCubes
