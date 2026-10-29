import Mathlib

/-!
# Block cover: few blocks cover a corner class

`class_cover`: every pair `(S, T)` of subsets of `Fin n` with `|S| = a₀`, `|T| = b₀` lies in some
block `(U, V)` of a chosen family with `|U| = us`, `|V| = ua`, and the family has at most
`1 + 2n · C(n,a₀) C(n,b₀) / (C(us,a₀) C(ua,b₀))` blocks.

Proof outline.
* `greedy_cover`: if every element of `W` lies in at least `D > 0` blocks of `𝓑`, then some
  `C ⊆ 𝓑` covers `W` with `|C| ≤ 1 + (|𝓑| / D) log |W|`. Strong induction on `W`: double counting
  gives a block covering at least a `D / |𝓑|` fraction of `W`; remove it and use
  `log x ≤ x - 1` on the surviving fraction.
* `card_superset_ge`: at least `C(n - |S|, u - |S|)` sets `U ⊆ Fin n` with `|U| = u` contain `S`
  (inject `V ↦ V ∪ S` from `u - |S|`-subsets of `Sᶜ`).
* `Nat.choose_mul` turns `|𝓑| / D` into the stated ratio, and `|W| ≤ 4^n` with `log 2 ≤ 1` bounds
  `log |W| ≤ 2n`.
-/

namespace IDMM
open Finset

section Greedy

variable {α β : Type*} [DecidableEq β]

/-- Greedy set cover: if every element of `W` lies in at least `D > 0` blocks of `𝓑`, then
`1 + (|𝓑| / D) · log |W|` blocks of `𝓑` suffice to cover `W`. -/
theorem greedy_cover (mem : β → α → Prop) [∀ b x, Decidable (mem b x)]
    (𝓑 : Finset β) (D : ℕ) (hD : 0 < D) (W : Finset α)
    (hW : ∀ x ∈ W, D ≤ (𝓑.filter (fun b => mem b x)).card) :
    ∃ C ⊆ 𝓑, (∀ x ∈ W, ∃ b ∈ C, mem b x) ∧
      (C.card : ℝ) ≤ 1 + ((𝓑.card : ℝ) / D) * Real.log W.card := by
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, empty_subset _, by simp, by simp⟩
  -- Double counting: `∑_b |W ∩ b| = ∑_x #{b ∋ x} ≥ D |W|`.
  have hsum : ∑ b ∈ 𝓑, (W.filter (fun x => mem b x)).card
      = ∑ x ∈ W, (𝓑.filter (fun b => mem b x)).card := by
    simp only [card_filter]
    exact Finset.sum_comm
  have hlow : W.card * D ≤ ∑ b ∈ 𝓑, (W.filter (fun x => mem b x)).card := by
    rw [hsum]
    calc W.card * D = ∑ _x ∈ W, D := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hW
  have h𝓑ne : 𝓑.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨b, hb⟩ := card_pos.mp (lt_of_lt_of_le hD (hW x hx))
    exact ⟨b, (mem_filter.mp hb).1⟩
  -- Some block covers at least a `D / |𝓑|` fraction of `W`.
  obtain ⟨b, hb𝓑, hb⟩ :
      ∃ b ∈ 𝓑, W.card * D ≤ 𝓑.card * (W.filter (fun x => mem b x)).card := by
    apply exists_le_of_sum_le h𝓑ne
    rw [sum_const, smul_eq_mul, ← mul_sum]
    exact Nat.mul_le_mul_left _ hlow
  have hsplit : (W.filter (fun x => mem b x)).card + (W.filter (fun x => ¬ mem b x)).card
      = W.card := card_filter_add_card_filter_not _
  rcases (W.filter (fun x => ¬ mem b x)).eq_empty_or_nonempty with hW'e | hW'ne
  · -- One block covers everything.
    refine ⟨{b}, by simpa using hb𝓑, ?_, ?_⟩
    · intro x hx
      refine ⟨b, mem_singleton_self b, ?_⟩
      by_contra h
      have : x ∈ W.filter (fun x => ¬ mem b x) := mem_filter.mpr ⟨hx, h⟩
      rw [hW'e] at this
      simp at this
    · have hW1 : (1 : ℝ) ≤ W.card := by exact_mod_cast card_pos.mpr hne
      have : 0 ≤ ((𝓑.card : ℝ) / D) * Real.log W.card :=
        mul_nonneg (by positivity) (Real.log_nonneg hW1)
      simp only [card_singleton, Nat.cast_one]
      linarith
  · have hcpos : 0 < (W.filter (fun x => mem b x)).card := by
      have h0 : 0 < 𝓑.card * (W.filter (fun x => mem b x)).card :=
        lt_of_lt_of_le (Nat.mul_pos (card_pos.mpr hne) hD) hb
      exact Nat.pos_of_ne_zero fun h => by simp [h] at h0
    have hss : W.filter (fun x => ¬ mem b x) ⊂ W := by
      rw [filter_ssubset]
      obtain ⟨x, hx⟩ := card_pos.mp hcpos
      exact ⟨x, (mem_filter.mp hx).1, not_not.mpr (mem_filter.mp hx).2⟩
    obtain ⟨C', hC'sub, hC'cov, hC'card⟩ :=
      ih _ hss (fun x hx => hW x (mem_filter.mp hx).1)
    refine ⟨insert b C', insert_subset hb𝓑 hC'sub, ?_, ?_⟩
    · intro x hx
      by_cases h : mem b x
      · exact ⟨b, mem_insert_self _ _, h⟩
      · obtain ⟨c, hc, hcx⟩ := hC'cov x (mem_filter.mpr ⟨hx, h⟩)
        exact ⟨c, mem_insert_of_mem hc, hcx⟩
    · have hins : ((insert b C').card : ℝ) ≤ C'.card + 1 := by
        exact_mod_cast card_insert_le b C'
      have hsplitR : ((W.filter (fun x => mem b x)).card : ℝ)
          + ((W.filter (fun x => ¬ mem b x)).card : ℝ) = W.card := by exact_mod_cast hsplit
      have hbR : (W.card : ℝ) * D ≤ (𝓑.card : ℝ) * (W.filter (fun x => mem b x)).card := by
        exact_mod_cast hb
      set w : ℝ := (W.card : ℝ) with hw
      set w' : ℝ := ((W.filter (fun x => ¬ mem b x)).card : ℝ) with hw'
      set c : ℝ := ((W.filter (fun x => mem b x)).card : ℝ) with hc
      set B : ℝ := (𝓑.card : ℝ) with hB
      set d : ℝ := (D : ℝ) with hd
      have hwpos : 0 < w := by rw [hw]; exact_mod_cast card_pos.mpr hne
      have hw'pos : 0 < w' := by rw [hw']; exact_mod_cast card_pos.mpr hW'ne
      have hBpos : 0 < B := by rw [hB]; exact_mod_cast card_pos.mpr h𝓑ne
      have hdpos : 0 < d := by rw [hd]; exact_mod_cast hD
      -- `log w' - log w ≤ w'/w - 1 = -c/w`.
      have h1 : c / w ≤ Real.log w - Real.log w' := by
        have hl := Real.log_le_sub_one_of_pos (div_pos hw'pos hwpos)
        rw [Real.log_div hw'pos.ne' hwpos.ne'] at hl
        have he : w' / w - 1 = -(c / w) := by
          field_simp
          linarith
        linarith
      have h2 : 1 ≤ (B / d) * (c / w) := by
        rw [div_mul_div_comm, le_div_iff₀ (mul_pos hdpos hwpos)]
        linarith
      have h3 : (B / d) * (c / w) ≤ (B / d) * (Real.log w - Real.log w') :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hBpos.le hdpos.le)
      rw [mul_sub] at h3
      linarith

end Greedy

/-- At least `C(n - |S|, u - |S|)` sets `U ⊆ Fin n` with `|U| = u` contain `S`. -/
theorem card_superset_ge (n u : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ u) :
    (n - S.card).choose (u - S.card) ≤
      ((powersetCard u (univ : Finset (Fin n))).filter (fun U => S ⊆ U)).card := by
  have h1 : (powersetCard (u - S.card) Sᶜ).card = (n - S.card).choose (u - S.card) := by
    rw [card_powersetCard, card_compl, Fintype.card_fin]
  rw [← h1]
  apply card_le_card_of_injOn (fun V => V ∪ S)
  · intro V hV
    rw [mem_coe, mem_powersetCard] at hV
    have hdisj : Disjoint V S := by
      rw [← subset_compl_iff_disjoint_right]
      exact hV.1
    rw [mem_coe, mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint hdisj, hV.2]
    omega
  · intro V₁ hV₁ V₂ hV₂ heq
    rw [mem_coe, mem_powersetCard] at hV₁ hV₂
    have hd₁ : Disjoint V₁ S := by
      rw [← subset_compl_iff_disjoint_right]
      exact hV₁.1
    have hd₂ : Disjoint V₂ S := by
      rw [← subset_compl_iff_disjoint_right]
      exact hV₂.1
    have heq' : V₁ ∪ S = V₂ ∪ S := heq
    rw [← union_sdiff_cancel_right hd₁, ← union_sdiff_cancel_right hd₂, heq']

/-- Every pair `(S, T)` with `|S| = a₀`, `|T| = b₀` lies in some chosen block `(U, V)` with
`|U| = us`, `|V| = ua`, and few blocks are needed. -/
theorem class_cover (n a₀ b₀ us ua : ℕ) (ha : a₀ ≤ us) (hus : us ≤ n) (hb : b₀ ≤ ua)
    (hua : ua ≤ n) :
    ∃ C : Finset (Finset (Fin n) × Finset (Fin n)),
      (∀ p ∈ C, p.1.card = us ∧ p.2.card = ua) ∧
      (∀ S T : Finset (Fin n), S.card = a₀ → T.card = b₀ → ∃ p ∈ C, S ⊆ p.1 ∧ T ⊆ p.2) ∧
      (C.card : ℝ) ≤ 1 + 2 * n * (((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) /
        ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ)) := by
  classical
  set W : Finset (Finset (Fin n) × Finset (Fin n)) :=
    (powersetCard a₀ (univ : Finset (Fin n))) ×ˢ (powersetCard b₀ (univ : Finset (Fin n)))
    with hWdef
  set 𝓑 : Finset (Finset (Fin n) × Finset (Fin n)) :=
    (powersetCard us (univ : Finset (Fin n))) ×ˢ (powersetCard ua (univ : Finset (Fin n)))
    with h𝓑def
  set D : ℕ := (n - a₀).choose (us - a₀) * (n - b₀).choose (ua - b₀) with hDdef
  have hD : 0 < D := Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hcov : ∀ x ∈ W, D ≤ (𝓑.filter (fun p => x.1 ⊆ p.1 ∧ x.2 ⊆ p.2)).card := by
    rintro ⟨S, T⟩ hx
    simp only [hWdef, mem_product, mem_powersetCard] at hx
    rw [h𝓑def, filter_product (fun U => S ⊆ U) (fun V => T ⊆ V), card_product]
    have h1 := card_superset_ge n us S (by omega)
    have h2 := card_superset_ge n ua T (by omega)
    rw [hx.1.2] at h1
    rw [hx.2.2] at h2
    exact Nat.mul_le_mul h1 h2
  obtain ⟨C, hCsub, hCcov, hCcard⟩ :=
    greedy_cover (fun p x => x.1 ⊆ p.1 ∧ x.2 ⊆ p.2) 𝓑 D hD W hcov
  refine ⟨C, ?_, ?_, ?_⟩
  · intro p hp
    have := hCsub hp
    simp only [h𝓑def, mem_product, mem_powersetCard] at this
    exact ⟨this.1.2, this.2.2⟩
  · intro S T hS hT
    have hx : (S, T) ∈ W := by
      simp only [hWdef, mem_product, mem_powersetCard]
      exact ⟨⟨subset_univ _, hS⟩, ⟨subset_univ _, hT⟩⟩
    exact hCcov _ hx
  · have hM : 0 < us.choose a₀ * ua.choose b₀ :=
      Nat.mul_pos (Nat.choose_pos ha) (Nat.choose_pos hb)
    -- `|𝓑| / D` is exactly the stated ratio.
    have hratio : (𝓑.card : ℝ) / D = ((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) /
        ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ) := by
      have hBc : 𝓑.card = n.choose us * n.choose ua := by
        simp [h𝓑def, card_product, card_powersetCard]
      have key : 𝓑.card * (us.choose a₀ * ua.choose b₀) = (n.choose a₀ * n.choose b₀) * D := by
        rw [hBc, hDdef]
        have e1 := Nat.choose_mul (n := n) (k := us) (s := a₀) ha
        have e2 := Nat.choose_mul (n := n) (k := ua) (s := b₀) hb
        calc n.choose us * n.choose ua * (us.choose a₀ * ua.choose b₀)
            = (n.choose us * us.choose a₀) * (n.choose ua * ua.choose b₀) := by ring
          _ = _ := by rw [e1, e2]; ring
      rw [div_eq_div_iff (by exact_mod_cast hD.ne') (by exact_mod_cast hM.ne')]
      exact_mod_cast key
    -- `log |W| ≤ 2n`.
    have hlogW : Real.log W.card ≤ 2 * n := by
      have hWc : W.card = n.choose a₀ * n.choose b₀ := by
        simp [hWdef, card_product, card_powersetCard]
      have hWpos : 0 < W.card := by
        rw [hWc]; exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
      have hle : W.card ≤ 2 ^ n * 2 ^ n := by
        rw [hWc]; exact Nat.mul_le_mul (Nat.choose_le_two_pow n a₀) (Nat.choose_le_two_pow n b₀)
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hn : (n : ℝ) * Real.log 2 ≤ n := by
        have := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) n)
        linarith
      calc Real.log W.card ≤ Real.log ((2 ^ n * 2 ^ n : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast hWpos) (by exact_mod_cast hle)
        _ = n * Real.log 2 + n * Real.log 2 := by
            push_cast
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        _ ≤ 2 * n := by linarith
    have hK : 0 ≤ ((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) /
        ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ) := by positivity
    rw [hratio] at hCcard
    calc (C.card : ℝ)
        ≤ 1 + ((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) / ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ) *
            Real.log W.card := hCcard
      _ ≤ 1 + ((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) / ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ) *
            (2 * n) := by gcongr
      _ = 1 + 2 * n * (((n.choose a₀ * n.choose b₀ : ℕ) : ℝ) /
            ((us.choose a₀ * ua.choose b₀ : ℕ) : ℝ)) := by ring

end IDMM
