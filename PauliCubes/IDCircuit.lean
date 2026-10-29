/-
**Hrubeš's Lemma 22 for the Pauli-cube identities**, and the resulting circuit bound for `ID_N`.

For each `n`, the weighted Pauli identity of `mainTarget` and the cube algorithms give a noncommutative
circuit for `ID_{2^n}`. Over a field `L ⊇ K` containing `√-1`, realized inside 2×2 matrices over the free
algebra (`Descent`), each cube contributes `Σ_{ν ∈ Q} w_ν f_ν^[2]` with `O(n 2^n)` gates (`cube_circuit`); every
word of nonzero weight is charged to one cube; the total is `Σ_ν w_ν f_ν^[2] = Σ X_x Y_y X_x Y_y`
(`sos_f2`); and reading off the top-left entry gives a circuit over `K`. Relabeling the words as
`Fin (2^n)` and setting surplus variables to zero then covers every `N`.
-/
import PauliCubes.Main
import PauliCubes.Descent
import PauliCubes.CubeCircuit
import PauliCubes.NCIdentity

open Finset Filter

namespace PauliCubes

universe u

/-! ## Relabeling and padding -/

variable {K : Type u} [Field K]

variable (K) in
/-- `ID` with the variables indexed by the words of length `n`. -/
noncomputable def IDw (n : ℕ) : FreeAlgebra K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2)) :=
  ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, FreeAlgebra.ι K (Sum.inl x) * FreeAlgebra.ι K (Sum.inr y) *
    FreeAlgebra.ι K (Sum.inl x) * FreeAlgebra.ι K (Sum.inr y)

theorem ncSizeLE_ID_pow {n s : ℕ} (h : NCSizeLE (IDw K n) s) : NCSizeLE (ID K (2 ^ n)) s := by
  let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by simp)
  let φ : FreeAlgebra K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2)) →ₐ[K] FreeAlgebra K (Fin (2 ^ n) ⊕ Fin (2 ^ n)) :=
    FreeAlgebra.lift K fun v => FreeAlgebra.ι K (Sum.map e e v)
  have hφ := h.map φ fun v => Or.inl ⟨Sum.map e e v, by simp [φ]⟩
  convert hφ using 1
  simp only [IDw, ID, map_sum, map_mul, φ, FreeAlgebra.lift_ι_apply, Sum.map_inl, Sum.map_inr]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp e]

/-- Setting the surplus variables to zero: `ID_M` restricts to `ID_N` for `N ≤ M`. -/
theorem ncSizeLE_ID_le {N M s : ℕ} (hNM : N ≤ M) (h : NCSizeLE (ID K M) s) : NCSizeLE (ID K N) s := by
  let pad : (Fin N → Fin N ⊕ Fin N) → Fin M → FreeAlgebra K (Fin N ⊕ Fin N) := fun t i =>
    if hi : (i : ℕ) < N then FreeAlgebra.ι K (t ⟨i, hi⟩) else 0
  let φ : FreeAlgebra K (Fin M ⊕ Fin M) →ₐ[K] FreeAlgebra K (Fin N ⊕ Fin N) :=
    FreeAlgebra.lift K (Sum.elim (pad Sum.inl) (pad Sum.inr))
  have hpad : ∀ t i, pad t i ∈ ncInputs K (Fin N ⊕ Fin N) := by
    intro t i
    simp only [pad]
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨0, map_zero _⟩
  have hφ := h.map φ fun v => by
    rcases v with i | i
    · simpa [φ] using hpad Sum.inl i
    · simpa [φ] using hpad Sum.inr i
  convert hφ using 1
  have hcast : ∀ (t : Fin N → Fin N ⊕ Fin N) (i : Fin N), pad t (Fin.castLE hNM i) = FreeAlgebra.ι K (t i) := by
    intro t i
    simp [pad, Fin.castLE]
  have hzero : ∀ (t : Fin N → Fin N ⊕ Fin N) (i : Fin M), i ∉ univ.map (Fin.castLEEmb hNM) → pad t i = 0 := by
    intro t i hi
    have : ¬ (i : ℕ) < N := fun hlt => hi (Finset.mem_map.mpr ⟨⟨i, hlt⟩, mem_univ _, Fin.ext rfl⟩)
    simp [pad, this]
  have hsum : ∀ g : Fin M → FreeAlgebra K (Fin N ⊕ Fin N),
      (∀ i ∉ univ.map (Fin.castLEEmb hNM), g i = 0) → ∑ i, g i = ∑ i : Fin N, g (Fin.castLE hNM i) := by
    intro g hg
    rw [← Finset.sum_subset (subset_univ _) fun i _ hi => hg i hi, Finset.sum_map]
    rfl
  simp only [ID, map_sum, map_mul, φ, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hsum _ fun i hi => by simp [hzero Sum.inl i hi]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum _ fun j hj => by simp [hzero Sum.inr j hj], hcast]
  exact Finset.sum_congr rfl fun j _ => by rw [hcast]

/-! ## One identity, one circuit -/

/-- Charging each word of nonzero weight to one cube that covers it. -/
theorem sum_cubes_eq {α M : Type*} [DecidableEq α] [Fintype α] [AddCommMonoid M]
    (C : Finset (Finset α)) (g : α → M) (hg : ∀ ν, g ν ≠ 0 → ∃ Q ∈ C, ν ∈ Q)
    (ch : α → Finset α) (hch : ∀ ν, (∃ Q ∈ C, ν ∈ Q) → ch ν ∈ C ∧ ν ∈ ch ν) :
    ∑ Q ∈ C, ∑ ν ∈ Q, (if ch ν = Q then g ν else 0) = ∑ ν, g ν := by
  have h1 : ∀ Q ∈ C, ∑ ν ∈ Q, (if ch ν = Q then g ν else 0) =
      ∑ ν, if ν ∈ Q then (if ch ν = Q then g ν else 0) else 0 := fun Q _ => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hc : ∃ Q ∈ C, ν ∈ Q
  · obtain ⟨hC, hν⟩ := hch ν hc
    have : ∀ Q ∈ C, (if ν ∈ Q then (if ch ν = Q then g ν else 0) else 0) =
        if ch ν = Q then g ν else 0 := by
      intro Q _
      by_cases hQ : ch ν = Q
      · subst hQ; simp [hν]
      · simp [hQ]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hC]
  · have hz : g ν = 0 := by
      by_contra hne
      exact hc (hg ν hne)
    rw [hz]
    exact Finset.sum_eq_zero fun Q _ => by simp

/-- **Lemma 22 for one length.** A weighted Pauli identity with `R` cubes gives a noncommutative circuit
for `ID` on `2 · 2^n` variables with `12 (R (100 (n+1) 2^n + 1) + 1)` gates. -/
theorem ncSizeLE_IDw (h2 : (2 : K) ≠ 0) {n R : ℕ} (hsos : PauliCubeSOS K n R) :
    NCSizeLE (IDw K n) (12 * (R * (100 * (n + 1) * 2 ^ n + 1) + 1)) := by
  classical
  obtain ⟨w, hw, C, hCR, hcube, hcov⟩ := hsos
  refine sqrt_neg_one_ext (K := K) fun L _ _ i hi ρ => ?_
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr h2
  let V := (Fin n → Fin 2) ⊕ (Fin n → Fin 2)
  let Xc : (Fin n → Fin 2) → CL (V := V) ρ := fun x => scalarCL ρ (FreeAlgebra.ι K (Sum.inl x))
  let Yc : (Fin n → Fin 2) → CL (V := V) ρ := fun y => scalarCL ρ (FreeAlgebra.ι K (Sum.inr y))
  let ch : (Fin n → Fin 4) → Finset (Fin n → Fin 4) := fun ν =>
    if h : ∃ Q ∈ C, ν ∈ Q then Classical.choose h else ∅
  have hch : ∀ ν, (∃ Q ∈ C, ν ∈ Q) → ch ν ∈ C ∧ ν ∈ ch ν := by
    intro ν h
    simp only [ch, dif_pos h]
    exact Classical.choose_spec h
  let wQ : Finset (Fin n → Fin 4) → (Fin n → Fin 4) → L := fun Q ν =>
    if ch ν = Q then algebraMap K L (w ν) else 0
  let S : Finset (Fin n → Fin 4) → CL (V := V) ρ := fun Q => ∑ ν ∈ Q, wQ Q ν • f2 (L := L) Xc Yc ν
  have hQ : ∀ Q ∈ C, Reach (cInputs ρ) ∅ {S Q} (100 * (n + 1) * 2 ^ n) := by
    intro Q hQC
    obtain ⟨a, b, hab, rfl⟩ := hcube Q hQC
    exact cube_circuit (𝒜 := CL (V := V) ρ) (inp := cInputs ρ) h2L hi (fun c => Or.inl ⟨c, rfl⟩) (fun x => Or.inr ⟨Sum.inl x, rfl⟩)
      (fun y => Or.inr ⟨Sum.inr y, rfl⟩) a b hab (wQ (cube a b))
  have hall := Reach.biUnion C hQ
  have hsum := Reach.sum (inp := cInputs ρ) (B := ∅ ∪ ⋃ Q ∈ C, {S Q}) (Or.inl ⟨0, map_zero _⟩) C
    (p := S) fun Q hQ => Or.inr (Set.mem_biUnion hQ (Set.mem_singleton _))
  have htot := hall.seq hsum
  have hid : ∑ Q ∈ C, S Q = scalarCL ρ (IDw K n) := by
    have hcs := sum_cubes_eq C (fun ν => algebraMap K L (w ν) • f2 (L := L) Xc Yc ν)
      (fun ν hν => by
        have hw0 : w ν ≠ 0 := fun h0 => hν (by simp [h0])
        obtain ⟨Q, hQ, hνQ⟩ := Finset.mem_biUnion.mp (hcov (by simpa using hw0))
        exact ⟨Q, hQ, hνQ⟩) ch hch
    simp only [S, wQ, ite_smul, zero_smul]
    rw [hcs, sos_f2 h2 w hw Xc Yc]
    simp only [IDw, Xc, Yc, ← scalarCLHom_apply, ← map_mul, ← map_sum]
  rw [hid] at htot
  refine (ncSizeLE_of_reach_CL ρ (z := scalarCL ρ (IDw K n)) (by simp [scalarCL]) htot).mono ?_
  simp only [Finset.sum_const, smul_eq_mul]
  have := Nat.mul_le_mul_right (100 * (n + 1) * 2 ^ n + 1) hCR
  nlinarith

/-! ## The exponent -/

theorem two_pow_clog_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.clog 2 N ≤ 2 * N := by
  rcases Nat.eq_or_lt_of_le hN with rfl | hN
  · simp
  · have hpos := Nat.clog_pos one_lt_two hN
    have hlt := Nat.pow_pred_clog_lt_self one_lt_two hN
    rw [Nat.pred_eq_sub_one] at hlt
    calc 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * N := by omega

theorem cost_le {n R : ℕ} {A B : ℝ} (hR : (R : ℝ) ≤ A) (hA : 1 ≤ A) (hB : (n : ℝ) + 1 ≤ B) :
    ((12 * (R * (100 * (n + 1) * 2 ^ n + 1) + 1) : ℕ) : ℝ) ≤ 1224 * (2 ^ n * A * B) := by
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hT : (1 : ℝ) ≤ ((n : ℝ) + 1) * 2 ^ n := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  push_cast
  have h1 : (R : ℝ) * (100 * ((n : ℝ) + 1) * 2 ^ n + 1) ≤ A * (101 * (((n : ℝ) + 1) * 2 ^ n)) := by
    have : (100 * ((n : ℝ) + 1) * 2 ^ n + 1) ≤ 101 * (((n : ℝ) + 1) * 2 ^ n) := by nlinarith
    calc (R : ℝ) * (100 * ((n : ℝ) + 1) * 2 ^ n + 1) ≤ A * (100 * ((n : ℝ) + 1) * 2 ^ n + 1) :=
          mul_le_mul_of_nonneg_right hR (by positivity)
      _ ≤ A * (101 * (((n : ℝ) + 1) * 2 ^ n)) := mul_le_mul_of_nonneg_left this (by linarith)
  have h3 : ((n : ℝ) + 1) * 2 ^ n ≤ B * 2 ^ n := mul_le_mul_of_nonneg_right hB (by positivity)
  have h4 : (1 : ℝ) ≤ A * (((n : ℝ) + 1) * 2 ^ n) := by nlinarith
  nlinarith

theorem eventually_succ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
  set r : ℝ := (2 : ℝ) ^ ε with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hε
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 1 hr1).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [ht, eventually_ge_atTop 1] with n hn hn1
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hrn, pow_one] at hn
  have : (2 : ℝ) ^ ((n : ℝ) * ε) = r ^ n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  rw [this]
  linarith

/-- **Noncommutative circuits for `ID_N`** (Hrubeš's Lemma 22 with the Pauli-cube identities). Over
every field with `2 ≠ 0`, for every `ε > 0` there is `C` such that `ID_N` has a noncommutative circuit
with at most `C N^(1.727899 + ε)` gates for every `N ≥ 1`. -/
theorem id_circuit (h2 : (2 : K) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → NCSizeLE (ID K N) ⌊C * (N : ℝ) ^ (1.727899 + ε)⌋₊ := by
  set c : ℝ := 1.727899 + ε with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((mainTarget h2 (ε / 2) (half_pos hε)).and (eventually_succ_le (half_pos hε)))
  refine ⟨1224 * (2 : ℝ) ^ c * ((2 : ℝ) ^ n₀) ^ c, fun N hN => ?_⟩
  set n := max (Nat.clog 2 N) n₀ with hn
  obtain ⟨hsos, hsucc⟩ := hn₀ n (le_max_right _ _)
  set A : ℝ := (2 : ℝ) ^ ((n : ℝ) * (0.727899 + ε / 2)) with hA
  have hA1 : 1 ≤ A := Real.one_le_rpow (by norm_num) (by positivity)
  have hR : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le (by linarith)
  have hcirc := ncSizeLE_ID_le (Nat.le_pow_clog one_lt_two N |>.trans
    (Nat.pow_le_pow_right two_pos (le_max_left _ _))) (ncSizeLE_ID_pow (ncSizeLE_IDw h2 hsos))
  refine hcirc.mono (Nat.le_floor ?_)
  refine (cost_le hR hA1 hsucc).trans ?_
  -- `2^n A B = (2^n)^c`, and `2^n ≤ 2 N 2^n₀`
  have hexp : (2 : ℝ) ^ n * A * (2 : ℝ) ^ ((n : ℝ) * (ε / 2)) = ((2 : ℝ) ^ n) ^ c := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_mul (by norm_num), hc]
    congr 1
    ring
  have hpow : ((2 : ℝ) ^ n) ≤ 2 * N * (2 : ℝ) ^ n₀ := by
    have h1 : 2 ^ n ≤ 2 ^ Nat.clog 2 N * 2 ^ n₀ := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right two_pos (by omega)
    have h2' : 2 ^ Nat.clog 2 N * 2 ^ n₀ ≤ 2 * N * 2 ^ n₀ :=
      Nat.mul_le_mul_right _ (two_pow_clog_le hN)
    exact_mod_cast h1.trans h2'
  rw [hexp]
  calc 1224 * ((2 : ℝ) ^ n) ^ c ≤ 1224 * (2 * N * (2 : ℝ) ^ n₀) ^ c := by
        gcongr
    _ = 1224 * (2 : ℝ) ^ c * ((2 : ℝ) ^ n₀) ^ c * (N : ℝ) ^ c := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
        ring

end PauliCubes
