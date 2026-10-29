/-
Composites of Majorana swaps, and moving any block of `2m` Majoranas onto the first `m` qubits.
-/
import IDMM.MajConj

noncomputable section
namespace IDMM
open Finset Matrix

variable {n : ℕ} {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K]

/-- The gate `1 + K` for the swap of `k` and `l`. -/
def gateM (K : Type*) [Field K] [SqrtNegOne K] (k l : MIdx n) : Matrix (Bits n) (Bits n) K := 1 + gK K (mpair k l)
/-- Its inverse `(1 − K)/2`. -/
def gateI (K : Type*) [Field K] [SqrtNegOne K] (k l : MIdx n) : Matrix (Bits n) (Bits n) K := (2 : K)⁻¹ • (1 - gK K (mpair k l))

theorem gateM_gateI (k l : MIdx n) : gateM K k l * gateI K k l = 1 := gate_inv (K := K) _ (gK_sq _)

theorem gateI_gateM (k l : MIdx n) : gateI K k l * gateM K k l = 1 := by
  have hK := gK_sq (K := K) (mpair k l)
  rw [gateI, gateM, smul_mul_assoc]
  have : (1 - gK K (mpair k l)) * (1 + gK K (mpair k l)) = (2 : K) • (1 : Matrix (Bits n) (Bits n) K) := by
    rw [two_smul]
    calc (1 - gK K (mpair k l)) * (1 + gK K (mpair k l)) = 1 - gK K (mpair k l) * gK K (mpair k l) := by
          noncomm_ring
      _ = 1 + 1 := by rw [hK]; abel
  rw [this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Apply a list of swaps to a Majorana-coordinate vector, first swap first. -/
def mswapList : List (MIdx n × MIdx n) → MV n → MV n
  | [], A => A
  | p :: L, A => mswapList L (mswap p.1 p.2 A)

/-- The gate product, first swap innermost. -/
def compM (K : Type*) [Field K] [SqrtNegOne K] : List (MIdx n × MIdx n) → Matrix (Bits n) (Bits n) K
  | [] => 1
  | p :: L => compM K L * gateM K p.1 p.2

/-- The inverse product. -/
def compI (K : Type*) [Field K] [SqrtNegOne K] : List (MIdx n × MIdx n) → Matrix (Bits n) (Bits n) K
  | [] => 1
  | p :: L => gateI K p.1 p.2 * compI K L

theorem compM_compI : ∀ L : List (MIdx n × MIdx n), compM K L * compI K L = 1
  | [] => by simp [compM, compI]
  | p :: L => by
    rw [compM, compI, mul_assoc, ← mul_assoc (gateM K _ _), gateM_gateI, one_mul, compM_compI L]

theorem compI_compM : ∀ L : List (MIdx n × MIdx n), compI K L * compM K L = 1
  | [] => by simp [compM, compI]
  | p :: L => by
    rw [compM, compI, mul_assoc, ← mul_assoc (compI K L), compI_compM L, one_mul, gateI_gateM]

/-- **Conjugation by a composite of swaps.** -/
theorem comp_conj : ∀ (L : List (MIdx n × MIdx n)), (∀ p ∈ L, p.1 ≠ p.2) → ∀ A : MV n,
    ∃ lam : K, lam ≠ 0 ∧ compM K L * pmatM K A * compI K L = lam • pmatM K (mswapList L A)
  | [], _, A => ⟨1, one_ne_zero, by simp [compM, compI, mswapList]⟩
  | p :: L, hL, A => by
    obtain ⟨l1, hl1, h1⟩ := gate_conj (K := K) p.1 p.2 (hL p (List.mem_cons_self ..)) A
    obtain ⟨l2, hl2, h2⟩ := comp_conj L (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (mswap p.1 p.2 A)
    refine ⟨l2 * l1, mul_ne_zero hl2 hl1, ?_⟩
    rw [compM, compI, mswapList]
    calc compM K L * gateM K p.1 p.2 * pmatM K A * (gateI K p.1 p.2 * compI K L)
        = compM K L * (gateM K p.1 p.2 * pmatM K A * gateI K p.1 p.2) * compI K L := by noncomm_ring
      _ = compM K L * (l1 • pmatM K (mswap p.1 p.2 A)) * compI K L := by
          rw [gateM, gateI, h1]
      _ = l1 • (compM K L * pmatM K (mswap p.1 p.2 A) * compI K L) := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = (l2 * l1) • pmatM K (mswapList L (mswap p.1 p.2 A)) := by
          rw [h2, smul_smul, mul_comm]

/-! ## Moving a block -/

/-- The support of a Majorana-coordinate vector lies in `U`. -/
def SuppIn (A : MV n) (U : Finset (MIdx n)) : Prop := ∀ k, coord A k = 1 → k ∈ U

theorem coord_mswap (k l j : MIdx n) (A : MV n) :
    coord (mswap k l A) j = coord A (Equiv.swap k l j) := by
  rw [mswap, coord_ofCoord]

theorem suppIn_mswap {A : MV n} {U : Finset (MIdx n)} (h : SuppIn A U) (k l : MIdx n) :
    SuppIn (mswap k l A) (U.image (Equiv.swap k l)) := by
  intro j hj
  rw [coord_mswap] at hj
  exact mem_image.mpr ⟨Equiv.swap k l j, h _ hj, Equiv.swap_apply_self k l j⟩

/-- **Any block can be moved into a target of the same size.** -/
theorem exists_move : ∀ (d : ℕ) (U T : Finset (MIdx n)), U.card = T.card → (U \ T).card = d →
    ∃ L : List (MIdx n × MIdx n), (∀ p ∈ L, p.1 ≠ p.2) ∧ L.length ≤ d ∧
      ∀ A : MV n, SuppIn A U → SuppIn (mswapList L A) T := by
  classical
  intro d
  induction d with
  | zero =>
    intro U T _ hd
    refine ⟨[], by simp, by simp, fun A hA k hk => ?_⟩
    have hsub : U ⊆ T := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hd; exact hd
    exact hsub (hA k hk)
  | succ d ih =>
    intro U T hcard hd
    obtain ⟨k, hk⟩ : (U \ T).Nonempty := by rw [← card_pos, hd]; omega
    have hTU : (T \ U).card = (U \ T).card := by
      have h1 := card_sdiff_add_card_inter U T
      have h2 := card_sdiff_add_card_inter T U
      rw [inter_comm] at h2
      omega
    obtain ⟨l, hl⟩ : (T \ U).Nonempty := by rw [← card_pos, hTU, hd]; omega
    rw [mem_sdiff] at hk hl
    have hkl : k ≠ l := fun h => hk.2 (h ▸ hl.1)
    set U' := U.image (Equiv.swap k l)
    have hcard' : U'.card = T.card := by
      rw [card_image_of_injective _ (Equiv.injective _), hcard]
    have hd' : (U' \ T).card = d := by
      have : U' \ T = (U \ T).erase k := by
        ext j
        simp only [U', mem_sdiff, mem_image, mem_erase]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hjT⟩
          by_cases hik : i = k
          · subst hik; rw [Equiv.swap_apply_left] at hjT; exact absurd hl.1 hjT
          · by_cases hil : i = l
            · subst hil; exact absurd hi hl.2
            · rw [Equiv.swap_apply_of_ne_of_ne hik hil] at hjT ⊢
              exact ⟨hik, hi, hjT⟩
        · rintro ⟨hjk, hjU, hjT⟩
          have hjl : j ≠ l := fun h => hl.2 (h ▸ hjU)
          refine ⟨⟨j, hjU, Equiv.swap_apply_of_ne_of_ne hjk hjl⟩, hjT⟩
      rw [this, card_erase_of_mem (mem_sdiff.mpr hk), hd]; rfl
    obtain ⟨L', hL', hlen', hmove'⟩ := ih U' T hcard' hd'
    refine ⟨(k, l) :: L', ?_, by simp; omega, fun A hA => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hkl
      · exact hL' p hp
    · exact hmove' _ (suppIn_mswap hA k l)

/-! ## The canonical block: the first `m` qubits -/

/-- The index of the qubit of a Majorana. -/
def qidx : MIdx n → Fin n
  | .inl i => i
  | .inr i => i

/-- The Majoranas of the first `m` qubits. -/
def canon (n m : ℕ) : Finset (MIdx n) := univ.filter fun k => (qidx k).val < m

theorem card_canon {n m : ℕ} (hm : m ≤ n) : (canon n m).card = 2 * m := by
  classical
  have hc : (univ.filter fun i : Fin n => i.val < m).card = m := by
    rw [Fin.card_filter_val_lt]; omega
  rw [canon, card_filter, Fintype.sum_sum_type]
  have h1 : (∑ i : Fin n, if (qidx (Sum.inl i : MIdx n)).val < m then 1 else 0) = m := by
    rw [← card_filter]; exact hc
  have h2 : (∑ i : Fin n, if (qidx (Sum.inr i : MIdx n)).val < m then 1 else 0) = m := by
    rw [← card_filter]; exact hc
  rw [h1, h2]; ring

/-- A vector supported on the first `m` qubits' Majoranas has a Pauli matrix supported on those qubits. -/
theorem jw_supp_canon {m : ℕ} {A : MV n} (h : SuppIn A (canon n m)) (j : Fin n) (hj : m ≤ j.val) :
    jwX A.1 A.2 j = 0 ∧ jwZ A.1 A.2 j = 0 := by
  have hs : ∀ i : Fin n, m ≤ i.val → A.1 i = 0 := by
    intro i hi
    rcases zmod2_cases (A.1 i) with h0 | h1
    · exact h0
    · have h2 := (mem_filter.mp (h (.inl i) h1)).2
      exact absurd h2 (by show ¬ i.val < m; omega)
  have ha : ∀ i : Fin n, m ≤ i.val → A.2 i = 0 := by
    intro i hi
    rcases zmod2_cases (A.2 i) with h0 | h1
    · exact h0
    · have h2 := (mem_filter.mp (h (.inr i) h1)).2
      exact absurd h2 (by show ¬ i.val < m; omega)
  refine ⟨by simp [jwX, hs j hj, ha j hj], ?_⟩
  simp only [jwZ, suffix]
  rw [ha j hj, zero_add]
  refine sum_eq_zero fun k hk => ?_
  rw [mem_filter] at hk
  have : m ≤ k.val := le_trans hj (le_of_lt hk.2)
  simp [hs k this, ha k this]

end IDMM
