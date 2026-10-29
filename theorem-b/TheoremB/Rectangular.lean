/-
Theorem B for two alphabets: the crossing [x = v][y = u] with x, v among the partitions of h and
y, u among the partitions of E.

Lemma 9 of Appendix B holds on V_E for every E, and Anthropic's formalization proves its integer
form for monomials of any weight (`GeneralPieces.Series.sum_Qk_of`, `Qk_eq_Qk'_of`). So the pieces
of Appendix B, with labels of weight h and vectors of weight E, write the crossing on
p(h) × p(E) letters as a sum of row-wise and column-wise terms whose middle weights are at most
E + h. With the partition bounds p(E) ≤ e^{c√E} and p(E) ≥ H·e^{c√E}/E^B (c = π√(2/3)) of the
same formalization, this gives composition formulas of type [N₁, N₂, M] over ℂ with
log M ≤ √(log²N₁ + log²N₂) + o(log N₁ + log N₂).

The rectangular bound c(λ₁, λ₂) ≤ 2√(λ₁² + λ₂²) was first stated, without a machine check, by
Vaibhav Tulsyan in github.com/xennygrimmato/eth-hamiltonicity, research/pieces.md §2.3 (27 Oct 2026).

* `TheoremB.Rect.sum_piece`, `piece_row`, `piece_col`: the pieces add up to the crossing and factor
  through the monomials of weight E + s − h + i (row-wise) and E + h − s − i (column-wise).
* `TheoremB.Rect.pler_le`: if N₁ ≤ p(h) and N₂ ≤ p(E), the crossing on N₁ × N₂ letters is a sum of
  at most (2(E+h)+1)(2h+1)·C(E+h) terms over ℚ, where C(m) = p(0) + ⋯ + p(m).
* `TheoremB.Rect.prodLER_of_PLER`, `sosLER_of_prodLER`: each term is one product of two bilinear
  forms, and over ℂ each product is two squares.
* `TheoremB.Rect.pler_exp_le`, `TheoremB.Rect.hurwitzR_exp_le`: for every ε > 0 there is a C with
  M ≤ exp(√(log²N₁ + log²N₂) + ε·(log N₁ + log N₂) + C) for all N₁, N₂ ≥ 1.
-/
import TheoremB.Defs
import TheoremB.CharP
import ClauseBound.Part.Upper
import ClauseBound.Part.Lower
import ClauseBound.Part.Bits

open Finset ClauseBound.Boson

namespace TheoremB.Rect

/-! ### The pieces for two alphabets -/

/-- What membership in P h gives. -/
theorem facts {γ : Type} {h : ℕ} {μ : γ → Multiset ℕ} (hμ : ∀ x, μ x ∈ P h) (x : γ) :
    (μ x).sum = h ∧ 0 ∉ μ x ∧ Pos (μ x).toList ∧ (μ x).toList.sum = h := by
  obtain ⟨hs, h0⟩ := mem_P.1 (hμ x)
  refine ⟨hs, h0, fun n hn => Nat.one_le_iff_ne_zero.2 fun e => h0 ?_, ?_⟩
  · rw [← e]
    exact Multiset.mem_toList.1 hn
  · rw [← Multiset.sum_coe, Multiset.coe_toList, hs]

theorem zz_pos {ν : Multiset ℕ} (h0 : 0 ∉ ν) : 0 < zz ν := by
  unfold zz
  refine Finset.prod_pos fun k hk => ?_
  have hk0 : k ≠ 0 := fun e => h0 (e ▸ Multiset.mem_toFinset.1 hk)
  exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hk0) _) (Nat.factorial_pos _)

section Pieces

variable {α β : Type} {h E : ℕ} {μ : α → Multiset ℕ} {ν : β → Multiset ℕ}

/-- The piece number s: (1/z_{μ(v)})·Q_s(a^{μ(x)}, t^{μ(v)}) at the entry (ν(u), ν(y)). -/
noncomputable def piece (μ : α → Multiset ℕ) (ν : β → Multiset ℕ) (s : ℤ) (x v : α) (y u : β) : ℚ :=
  ((zz (μ v) : ℕ) : ℚ)⁻¹ * ((Qk (aFam (μ x).toList) (μ v).toList s (ν u) (ν y) : ℤ) : ℚ)

/-- **The pieces add up to the crossing** [x = v][y = u], for labels of weight h and vectors of
weight E. -/
theorem sum_piece [DecidableEq α] [DecidableEq β] (hμ : ∀ x, μ x ∈ P h) (hν : ∀ y, ν y ∈ P E) (hiμ : Function.Injective μ)
    (hiν : Function.Injective ν) (x v : α) (y u : β) :
    ∑ s ∈ Icc (-((E : ℤ) + h)) ((E : ℤ) + h), piece μ ν s x v y u =
      if x = v ∧ y = u then 1 else 0 := by
  obtain ⟨hsy, h0y, -, -⟩ := facts hν y
  obtain ⟨-, h0u, -, -⟩ := facts hν u
  obtain ⟨-, h0v, hpv, hlv⟩ := facts hμ v
  obtain ⟨-, -, hpx, hlx⟩ := facts hμ x
  have hA : (aFam (μ x).toList).Ok (μ v).toList.sum := by rw [hlv, ← hlx]; exact aFam_ok hpx
  have hsum := GeneralPieces.Series.sum_Qk_of AppHalfPieces.stExpansion hA hpv h0u h0y
  rw [hsy, hlv] at hsum
  unfold piece
  rw [← Finset.mul_sum, ← Int.cast_sum, hsum, CharP.pairF_aFam hpx hpv (by rw [hlx, hlv]),
    Multiset.coe_toList, Multiset.coe_toList]
  have hz : ((zz (μ v) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (zz_pos h0v).ne'
  simp only [hiμ.eq_iff, hiν.eq_iff]
  by_cases hxv : x = v <;> by_cases hyu : y = u
  · subst hxv hyu
    simp [hz]
  · have : ¬ u = y := fun e => hyu e.symm
    simp [hxv, hyu, this]
  · subst hyu
    simp [hxv]
  · have : ¬ u = y := fun e => hyu e.symm
    simp [hxv, hyu, this]

/-- **The row-wise factorization**: through the monomials τ of weight E + s − h + i. -/
theorem piece_row (hμ : ∀ x, μ x ∈ P h) (hν : ∀ y, ν y ∈ P E) (s : ℤ) (x v : α) (y u : β) :
    piece μ ν s x v y u = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (E + (s - h + i)),
      (Half.fL (aFam (μ x).toList) h i (fun L => op L (s - h + i) τ (ν y)) : ℚ) *
        (((zz (μ v) : ℕ) : ℚ)⁻¹ * (op (μ v).toList (h - s - i) (ν u) τ : ℚ)) := by
  obtain ⟨hsy, h0y, -, -⟩ := facts hν y
  obtain ⟨-, h0u, -, -⟩ := facts hν u
  obtain ⟨-, -, hpv, hlv⟩ := facts hμ v
  obtain ⟨-, -, hpx, hlx⟩ := facts hμ x
  have hA : (aFam (μ x).toList).Ok (μ v).toList.sum := by rw [hlv, ← hlx]; exact aFam_ok hpx
  unfold piece
  rw [GeneralPieces.Series.Qk_eq_Qk'_of AppHalfPieces.stExpansion hA hpv s h0u h0y, CharP.Qk'_eq,
    hsy, hlv, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  push_cast
  ring

/-- **The column-wise factorization**: through the monomials τ of weight E + h − s − i. -/
theorem piece_col (hμ : ∀ x, μ x ∈ P h) (hν : ∀ y, ν y ∈ P E) (s : ℤ) (x v : α) (y u : β) :
    piece μ ν s x v y u = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (E + (h - s - i)),
      (Half.fL (aFam (μ x).toList) h i (fun L => op L (s - h + i) (ν u) τ) : ℚ) *
        (((zz (μ v) : ℕ) : ℚ)⁻¹ * (op (μ v).toList (h - s - i) τ (ν y) : ℚ)) := by
  obtain ⟨hsy, -, -, -⟩ := facts hν y
  obtain ⟨-, -, -, hlv⟩ := facts hμ v
  unfold piece
  rw [Half.Qk_eq, hsy, hlv, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  push_cast
  ring

end Pieces

/-! ### The number of terms -/

/-- C(m) = p(0) + ⋯ + p(m). -/
def Csum (m : ℕ) : ℕ := ∑ e ∈ range (m + 1), Partitions.p e

theorem card_Pz_le {m : ℤ} {W : ℕ} (hm : m ≤ W) : (Pz m).card ≤ Csum W := by
  rw [Half.card_Pz]
  unfold ClauseBound.Part.pz Csum
  split_ifs with h0
  · have hmem : m.toNat ∈ range (W + 1) := by simp only [mem_range]; omega
    exact Finset.single_le_sum (f := Partitions.p) (fun _ _ => Nat.zero_le _) hmem
  · exact Nat.zero_le _

/-- From a sum over a finite set of terms of the two shapes to a crossing decomposition. -/
theorem pler_of_sum {K : Type} [CommRing K] {α β ι : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset ι) (g g' : ι → α → β → K) (col : ι → Bool)
    (hT : ∀ (x v : α) (y u : β), (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ j ∈ T, if col j then g j x u * g' j v y else g j x y * g' j v u) : PLER K α β T.card := by
  refine ⟨fun k => g (T.equivFin.symm k), fun k => g' (T.equivFin.symm k),
    fun k => col (T.equivFin.symm k), fun x v y u => ?_⟩
  rw [hT x v y u, ← Finset.sum_coe_sort T]
  exact Fintype.sum_equiv T.equivFin _ _ fun j => by simp

/-- **P(N₁, N₂) over ℚ.** If N₁ ≤ p(h) and N₂ ≤ p(E), the crossing on N₁ × N₂ letters is a sum of
at most (2(E+h)+1)(2h+1)·C(E+h) terms of the two shapes: row-wise for s ≤ 0 and column-wise for
s > 0. -/
theorem pler_le {N₁ N₂ h E : ℕ} (h1 : N₁ ≤ Partitions.p h) (h2 : N₂ ≤ Partitions.p E) :
    ∃ M, PLER ℚ (Fin N₁) (Fin N₂) M ∧ M ≤ (2 * (E + h) + 1) * ((2 * h + 1) * Csum (E + h)) := by
  have h1' : N₁ ≤ (P h).card := by rw [card_P]; exact h1
  have h2' : N₂ ≤ (P E).card := by rw [card_P]; exact h2
  let μ : Fin N₁ → Multiset ℕ := fun x => ((P h).equivFin.symm (Fin.castLE h1' x)).1
  let ν : Fin N₂ → Multiset ℕ := fun y => ((P E).equivFin.symm (Fin.castLE h2' y)).1
  have hμ : ∀ x, μ x ∈ P h := fun x => ((P h).equivFin.symm (Fin.castLE h1' x)).2
  have hν : ∀ y, ν y ∈ P E := fun y => ((P E).equivFin.symm (Fin.castLE h2' y)).2
  have hiμ : Function.Injective μ := fun a b e =>
    Fin.castLE_injective h1' ((P h).equivFin.symm.injective (Subtype.ext e))
  have hiν : Function.Injective ν := fun a b e =>
    Fin.castLE_injective h2' ((P E).equivFin.symm.injective (Subtype.ext e))
  let T : Finset (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) := (Icc (-((E : ℤ) + h)) ((E : ℤ) + h)).sigma fun s =>
    (range (2 * h + 1)).sigma fun i =>
      if s ≤ 0 then Pz (E + (s - h + i)) else Pz (E + (h - s - i))
  let g : (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) → Fin N₁ → Fin N₂ → ℚ := fun j a b =>
    if j.1 ≤ 0 then (Half.fL (aFam (μ a).toList) h j.2.1 (fun L => op L (j.1 - h + j.2.1) j.2.2 (ν b)) : ℚ)
    else (Half.fL (aFam (μ a).toList) h j.2.1 (fun L => op L (j.1 - h + j.2.1) (ν b) j.2.2) : ℚ)
  let g' : (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) → Fin N₁ → Fin N₂ → ℚ := fun j a b =>
    ((zz (μ a) : ℕ) : ℚ)⁻¹ * (if j.1 ≤ 0 then (op (μ a).toList (h - j.1 - j.2.1) (ν b) j.2.2 : ℚ)
      else (op (μ a).toList (h - j.1 - j.2.1) j.2.2 (ν b) : ℚ))
  refine ⟨T.card, pler_of_sum T g g' (fun j => decide (¬ j.1 ≤ 0)) fun x v y u => ?_, ?_⟩
  · rw [← sum_piece hμ hν hiμ hiν x v y u, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_sigma]
    by_cases hs : s ≤ 0
    · rw [piece_row hμ hν s]
      simp [g, g', hs]
    · rw [piece_col hμ hν s]
      simp [g, g', hs]
  · rw [Finset.card_sigma]
    have hb : ∀ s ∈ Icc (-((E : ℤ) + h)) ((E : ℤ) + h), ((range (2 * h + 1)).sigma fun i =>
        if s ≤ 0 then Pz (E + (s - h + i)) else Pz (E + (h - s - i))).card ≤
          (2 * h + 1) * Csum (E + h) := by
      intro s hs
      rw [Finset.card_sigma]
      have : ∀ i ∈ range (2 * h + 1),
          (if s ≤ 0 then Pz (E + (s - h + i)) else Pz (E + (h - s - i))).card ≤ Csum (E + h) := by
        intro i hi
        rw [mem_range] at hi
        split_ifs with h0
        · exact card_Pz_le (by push_cast; omega)
        · exact card_Pz_le (by push_cast; omega)
      calc _ ≤ ∑ _i ∈ range (2 * h + 1), Csum (E + h) := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, card_range, smul_eq_mul]
    calc _ ≤ ∑ _s ∈ Icc (-((E : ℤ) + h)) ((E : ℤ) + h), (2 * h + 1) * Csum (E + h) :=
          Finset.sum_le_sum hb
      _ = _ := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega

/-! ### Products of bilinear forms, and squares over ℂ -/

theorem bilR_comb {K : Type} [CommRing K] {N₁ N₂ : ℕ} (a b : K) (f f' : Fin N₁ → Fin N₂ → K)
    (X : Fin N₁ → K) (Y : Fin N₂ → K) :
    bilR (fun i j => a * f i j + b * f' i j) X Y = a * bilR f X Y + b * bilR f' X Y := by
  simp only [bilR, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Σ_{x,v,y,u} A(x,y)·B(v,u) = (Σ A)(Σ B). -/
theorem sum4_row {K : Type} [CommRing K] {N₁ N₂ : ℕ} (A B : Fin N₁ → Fin N₂ → K) :
    ∑ x, ∑ v, ∑ y, ∑ u, A x y * B v u = (∑ x, ∑ y, A x y) * ∑ v, ∑ u, B v u := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul_sum]

/-- Σ_{x,v,y,u} A(x,u)·B(v,y) = (Σ A)(Σ B). -/
theorem sum4_col {K : Type} [CommRing K] {N₁ N₂ : ℕ} (A B : Fin N₁ → Fin N₂ → K) :
    ∑ x, ∑ v, ∑ y, ∑ u, A x u * B v y = (∑ x, ∑ u, A x u) * ∑ v, ∑ y, B v y := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_comm]

/-- Σ_{x,v,y,u} (Σ_t T_t)·m = Σ_t Σ_{x,v,y,u} T_t·m. -/
theorem sum4_sum {K : Type} [CommRing K] {N₁ N₂ M : ℕ}
    (T : Fin M → Fin N₁ → Fin N₁ → Fin N₂ → Fin N₂ → K) (m : Fin N₁ → Fin N₁ → Fin N₂ → Fin N₂ → K) :
    ∑ x, ∑ v, ∑ y, ∑ u, (∑ t, T t x v y u) * m x v y u =
      ∑ t, ∑ x, ∑ v, ∑ y, ∑ u, T t x v y u * m x v y u := by
  simp only [Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_comm

/-- Each term of a crossing decomposition becomes one product of two bilinear forms in
(Σ X_i²)(Σ Y_j²) = Σ_{x,v,y,u} [x=v][y=u]·X_x·Y_y·X_v·Y_u. Over ℂ. -/
theorem prodLER_of_PLER {N₁ N₂ M : ℕ} (h : PLER ℚ (Fin N₁) (Fin N₂) M) : ProdLER ℂ N₁ N₂ M := by
  obtain ⟨g, g', col, hg⟩ := h
  refine ⟨fun t i j => (g t i j : ℂ), fun t i j => (g' t i j : ℂ), fun X Y => ?_⟩
  have hc : ∀ (x v : Fin N₁) (y u : Fin N₂), (if x = v ∧ y = u then (1 : ℂ) else 0) =
      ∑ t, (((if col t then g t x u * g' t v y else g t x y * g' t v u : ℚ)) : ℂ) := by
    intro x v y u
    rw [← Rat.cast_sum, ← hg x v y u]
    split_ifs <;> simp
  have h1 : ∑ x, ∑ v, ∑ y, ∑ u,
      (if x = v ∧ y = u then (1 : ℂ) else 0) * (X x * Y y * X v * Y u) =
      (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x (fun v _ hv => ?_) (by simp)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single y (fun u _ hu => by simp [Ne.symm hu]) (by simp)]
      simp only [and_self, if_true, one_mul]
      ring
    · exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun u _ => by simp [Ne.symm hv]
  rw [← h1]
  simp_rw [hc]
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hct : col t = true
  · simp only [hct, ↓reduceIte, Rat.cast_mul]
    calc ∑ x, ∑ v, ∑ y, ∑ u, (g t x u : ℂ) * (g' t v y : ℂ) * (X x * Y y * X v * Y u)
        = ∑ x, ∑ v, ∑ y, ∑ u, ((g t x u : ℂ) * X x * Y u) * ((g' t v y : ℂ) * X v * Y y) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ =>
            Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => by ring
      _ = (∑ x, ∑ u, (g t x u : ℂ) * X x * Y u) * ∑ v, ∑ y, (g' t v y : ℂ) * X v * Y y :=
          sum4_col (fun x u => (g t x u : ℂ) * X x * Y u) (fun v y => (g' t v y : ℂ) * X v * Y y)
      _ = _ := rfl
  · simp only [hct, Bool.false_eq_true, ↓reduceIte, Rat.cast_mul]
    calc ∑ x, ∑ v, ∑ y, ∑ u, (g t x y : ℂ) * (g' t v u : ℂ) * (X x * Y y * X v * Y u)
        = ∑ x, ∑ v, ∑ y, ∑ u, ((g t x y : ℂ) * X x * Y y) * ((g' t v u : ℂ) * X v * Y u) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ =>
            Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => by ring
      _ = (∑ x, ∑ y, (g t x y : ℂ) * X x * Y y) * ∑ v, ∑ u, (g' t v u : ℂ) * X v * Y u :=
          sum4_row (fun x y => (g t x y : ℂ) * X x * Y y) (fun v u => (g' t v u : ℂ) * X v * Y u)
      _ = _ := rfl

/-- Over ℂ each product is two squares: z·z' = ((z + z')/2)² + (i(z − z')/2)². -/
theorem sosLER_of_prodLER {N₁ N₂ M : ℕ} (h : ProdLER ℂ N₁ N₂ M) : SOSLER ℂ N₁ N₂ (M + M) := by
  obtain ⟨f, f', hf⟩ := h
  refine ⟨Fin.append (fun t i j => (1 / 2 : ℂ) * f t i j + (1 / 2 : ℂ) * f' t i j)
    (fun t i j => (Complex.I / 2) * f t i j + (-Complex.I / 2) * f' t i j), fun X Y => ?_⟩
  rw [Fin.sum_univ_add, hf X Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.append_left, Fin.append_right, bilR_comb]
  linear_combination (-(bilR (f t) X Y - bilR (f' t) X Y) ^ 2 / 4) * Complex.I_sq

/-! ### Sizes: from the number of letters to the weight -/

theorem cHR_pos : 0 < Partitions.cHR := ClauseBound.Part.Upper.cHR_pos

/-- C(m) ≤ (m + 1)·e^{c√m}, from p(e) ≤ e^{c√e}. -/
theorem Csum_le (m : ℕ) : (Csum m : ℝ) ≤ (m + 1) * Real.exp (Partitions.cHR * Real.sqrt m) := by
  unfold Csum
  push_cast
  calc ∑ e ∈ range (m + 1), (Partitions.p e : ℝ)
      ≤ ∑ _e ∈ range (m + 1), Real.exp (Partitions.cHR * Real.sqrt m) := by
        refine Finset.sum_le_sum fun e he => (ClauseBound.Part.p_le_exp e).trans ?_
        rw [mem_range] at he
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) cHR_pos.le)
        exact_mod_cast (by omega : e ≤ m)
    _ = (m + 1) * Real.exp (Partitions.cHR * Real.sqrt m) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

theorem exists_p_ge (N : ℕ) : ∃ h, N ≤ Partitions.p h :=
  ⟨2 * N, by have := ClauseBound.Part.Bits.succ_le_two_mul_p (2 * N); omega⟩

/-- The least h with N ≤ p(h). -/
noncomputable def hOf (N : ℕ) : ℕ := Nat.find (exists_p_ge N)

theorem le_p_hOf (N : ℕ) : N ≤ Partitions.p (hOf N) := Nat.find_spec (exists_p_ge N)

theorem p_lt_of_lt_hOf {N k : ℕ} (hk : k < hOf N) : Partitions.p k < N :=
  not_le.1 (Nat.find_min (exists_p_ge N) hk)

/-- **The weight against the number of letters.** With the lower bound
H·e^{c√E}/E^B ≤ p(E), the least h with N ≤ p(h) has c√h ≤ log N + B·log(h + 1) + c + |log H|. -/
theorem key {H : ℝ} {B : ℕ} (hH : 0 < H)
    (hp : ∀ E : ℕ, 1 ≤ E → H * Real.exp (Partitions.cHR * Real.sqrt E) / (E : ℝ) ^ B ≤ Partitions.p E)
    {N : ℕ} (hN : 1 ≤ N) :
    Partitions.cHR * Real.sqrt (hOf N) ≤
      Real.log N + B * Real.log ((hOf N : ℝ) + 1) + (Partitions.cHR + |Real.log H|) := by
  have hc := cHR_pos
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have habs : 0 ≤ |Real.log H| := abs_nonneg _
  have hlogh : 0 ≤ Real.log ((hOf N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg (hOf N) : (0 : ℝ) ≤ hOf N)])
  have hBl := mul_nonneg hB hlogh
  rcases Nat.lt_or_ge (hOf N) 2 with h2 | h2
  · have hs : Real.sqrt (hOf N) ≤ 1 := Real.sqrt_le_one.2 (by exact_mod_cast (by omega : hOf N ≤ 1))
    have := mul_le_mul_of_nonneg_left hs hc.le
    linarith
  · set k := hOf N - 1 with hk
    have hk1 : 1 ≤ k := by omega
    have hlt : Partitions.p k < N := p_lt_of_lt_hOf (by omega)
    have hkpos : (0 : ℝ) < (k : ℝ) ^ B := by
      have : (0 : ℝ) < k := by exact_mod_cast hk1
      positivity
    have h3 : H * Real.exp (Partitions.cHR * Real.sqrt k) < N * (k : ℝ) ^ B := by
      have := lt_of_le_of_lt (hp k hk1) (by exact_mod_cast hlt : (Partitions.p k : ℝ) < N)
      rwa [div_lt_iff₀ hkpos] at this
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h4 := Real.log_lt_log (by positivity) h3
    rw [Real.log_mul hH.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hNpos.ne' hkpos.ne', Real.log_pow] at h4
    have hkr : (k : ℝ) + 1 = hOf N := by
      have : k + 1 = hOf N := by omega
      exact_mod_cast this
    have h5 : Real.log k ≤ Real.log ((hOf N : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hk1) (by rw [← hkr]; linarith)
    have h6 : Real.sqrt (hOf N) ≤ Real.sqrt k + 1 := by
      rw [Real.sqrt_le_left (by positivity), ← hkr]
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k), Real.sqrt_nonneg (k : ℝ)]
    have h7 := mul_le_mul_of_nonneg_left h6 hc.le
    have h8 := mul_le_mul_of_nonneg_left h5 hB
    have h9 := neg_le_abs (Real.log H)
    nlinarith

/-- log y ≤ y/k + log k − 1 for y, k > 0 (the tangent line of log at k). -/
theorem log_le_tangent {y k : ℝ} (hy : 0 < y) (hk : 0 < k) :
    Real.log y ≤ y / k + Real.log k - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hy hk)
  rw [Real.log_div hy.ne' hk.ne'] at this
  linarith

/-- **log(h + 1) = o(log N).** If c√h ≤ log N + B·log(h + 1) + K, then for every δ > 0,
log(h + 1) ≤ δ·log N + C. -/
theorem log_succ_le {B K δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) : ∃ C : ℝ, ∀ (N h : ℕ), 1 ≤ N →
    Partitions.cHR * Real.sqrt h ≤ Real.log N + B * Real.log ((h : ℝ) + 1) + K →
      Real.log ((h : ℝ) + 1) ≤ δ * Real.log N + C := by
  set c := Partitions.cHR with hcdef
  have hc : 0 < c := cHR_pos
  set k₁ : ℝ := (4 * B + c) / c with hk₁def
  have hk₁ : 0 < k₁ := by positivity
  have hck₁ : c * k₁ = 4 * B + c := by rw [hk₁def]; field_simp
  set D : ℝ := c / 2 + 2 * B * (Real.log k₁ - 1) + K with hDdef
  set a : ℝ := 2 / c with hadef
  have ha : 0 < a := by positivity
  set k₂ : ℝ := 2 * a / δ with hk₂def
  have hk₂ : 0 < k₂ := by positivity
  have hak : a / k₂ = δ / 2 := by rw [hk₂def]; field_simp
  refine ⟨2 * ((a * D + 1) / k₂ + Real.log k₂ - 1), fun N h hN hkey => ?_⟩
  have hs0 := Real.sqrt_nonneg (h : ℝ)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hy0 : 0 < Real.sqrt h + 1 := by linarith
  -- log(h + 1) ≤ 2·log(√h + 1).
  have hl1 : Real.log ((h : ℝ) + 1) ≤ 2 * Real.log (Real.sqrt h + 1) := by
    have hp2 := Real.log_pow (Real.sqrt h + 1) 2
    push_cast at hp2
    rw [← hp2]
    exact Real.log_le_log (by positivity)
      (by nlinarith [Real.sq_sqrt (Nat.cast_nonneg h : (0 : ℝ) ≤ h)])
  -- B·log(h + 1) ≤ (c/2)(√h + 1) + 2B(log k₁ − 1).
  have hl2 : B * Real.log ((h : ℝ) + 1) ≤ c / 2 * (Real.sqrt h + 1) + 2 * B * (Real.log k₁ - 1) := by
    have t := log_le_tangent hy0 hk₁
    have hfrac : 2 * B * ((Real.sqrt h + 1) / k₁) ≤ c / 2 * (Real.sqrt h + 1) := by
      rw [show 2 * B * ((Real.sqrt h + 1) / k₁) = (Real.sqrt h + 1) * (2 * B / k₁) by ring]
      rw [show c / 2 * (Real.sqrt h + 1) = (Real.sqrt h + 1) * (c / 2) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hy0.le
      rw [div_le_iff₀ hk₁]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hl1 hB, mul_le_mul_of_nonneg_left t (by linarith : (0 : ℝ) ≤ 2 * B)]
  -- √h ≤ a·log N + a·D.
  have hsq : Real.sqrt h ≤ a * Real.log N + a * D := by
    have : c / 2 * Real.sqrt h ≤ Real.log N + D := by rw [hDdef]; linarith
    have e : a * (c / 2) = 1 := by rw [hadef]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left this ha.le]
  -- log(√h + 1) ≤ (δ/2)·log N + (aD + 1)/k₂ + log k₂ − 1.
  have hy1 : 0 < a * Real.log N + a * D + 1 := by linarith
  have hl3 : Real.log (Real.sqrt h + 1) ≤ Real.log (a * Real.log N + a * D + 1) :=
    Real.log_le_log hy0 (by linarith)
  have t2 := log_le_tangent hy1 hk₂
  have e2 : (a * Real.log N + a * D + 1) / k₂ = a / k₂ * Real.log N + (a * D + 1) / k₂ := by ring
  rw [e2, hak] at t2
  linarith

/-- Minkowski for two coordinates, with x ≤ a + e and y ≤ b + f. -/
theorem sqrt_sq_add_le {a b e f x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ a + e) (hy : y ≤ b + f) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) + e + f := by
  set S := Real.sqrt (a ^ 2 + b ^ 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSa : a ≤ S := le_trans (le_abs_self a) (Real.abs_le_sqrt (by nlinarith [sq_nonneg b]))
  have hSb : b ≤ S := le_trans (le_abs_self b) (Real.abs_le_sqrt (by nlinarith [sq_nonneg a]))
  have hS2 : S ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  rw [Real.sqrt_le_left (by positivity)]
  have hx2 : x ^ 2 ≤ (a + e) ^ 2 := by nlinarith
  have hy2 : y ^ 2 ≤ (b + f) ^ 2 := by nlinarith
  nlinarith [mul_nonneg he hf, mul_le_mul_of_nonneg_left hSa he, mul_le_mul_of_nonneg_left hSb hf]

/-- c·√(E + h) = √((c√h)² + (c√E)²). -/
theorem cHR_sqrt_add (h E : ℕ) :
    Partitions.cHR * Real.sqrt ((E : ℝ) + h) =
      Real.sqrt ((Partitions.cHR * Real.sqrt h) ^ 2 + (Partitions.cHR * Real.sqrt E) ^ 2) := by
  have hc := cHR_pos
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg h), Real.sq_sqrt (Nat.cast_nonneg E),
    ← mul_add, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le, add_comm ((E : ℝ)) h]

/-- **P(N₁, N₂) ≤ e^{√(log²N₁ + log²N₂) + o(log N₁ + log N₂)} over ℚ**: for every ε > 0 there is a C
such that, for all N₁, N₂ ≥ 1, the crossing on N₁ × N₂ letters is a sum of at most
exp(√(log²N₁ + log²N₂) + ε·(log N₁ + log N₂) + C) row-wise and column-wise terms. -/
theorem pler_exp_le {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, ∀ N₁ N₂ : ℕ, 1 ≤ N₁ → 1 ≤ N₂ →
    ∃ M : ℕ, PLER ℚ (Fin N₁) (Fin N₂) M ∧
      (M : ℝ) ≤ Real.exp (Real.sqrt (Real.log N₁ ^ 2 + Real.log N₂ ^ 2) +
        ε * (Real.log N₁ + Real.log N₂) + C) := by
  obtain ⟨H, B, hH, hp⟩ := ClauseBound.Part.exists_le_p
  set c := Partitions.cHR with hcdef
  have hc : 0 < c := cHR_pos
  set K : ℝ := c + |Real.log H|
  have hK : 0 ≤ K := by positivity
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set δ : ℝ := ε / (B + 3) with hδdef
  have hδ : 0 < δ := by positivity
  have hBδ : (B + 3) * δ = ε := by rw [hδdef]; field_simp
  obtain ⟨C₁, hC₁⟩ := log_succ_le (K := K) hB hδ
  refine ⟨2 * ((B + 3) * C₁) + 2 * K + Real.log 8, fun N₁ N₂ hN₁ hN₂ => ?_⟩
  set h := hOf N₁ with hhdef
  set E := hOf N₂ with hEdef
  obtain ⟨M, hP, hM⟩ := pler_le (le_p_hOf N₁) (le_p_hOf N₂)
  refine ⟨M, hP, ?_⟩
  have k1 := key hH hp hN₁
  have k2 := key hH hp hN₂
  have l1 := hC₁ N₁ h hN₁ k1
  have l2 := hC₁ N₂ E hN₂ k2
  have hl1 : 0 ≤ Real.log N₁ := Real.log_nonneg (by exact_mod_cast hN₁)
  have hl2 : 0 ≤ Real.log N₂ := Real.log_nonneg (by exact_mod_cast hN₂)
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have lh0 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by linarith)
  have lE0 : 0 ≤ Real.log ((E : ℝ) + 1) := Real.log_nonneg (by linarith)
  -- M ≤ 8·((h+1)(E+1))³·e^{c√(E+h)}.
  set Q : ℝ := ((h : ℝ) + 1) * ((E : ℝ) + 1) with hQdef
  have hQ1 : 1 ≤ Q := by nlinarith
  have hQ0 : 0 < Q := by linarith
  have hCs := Csum_le (E + h)
  push_cast at hCs
  have hMr : (M : ℝ) ≤ (2 * ((E : ℝ) + h) + 1) * ((2 * (h : ℝ) + 1) * Csum (E + h)) := by
    exact_mod_cast hM
  have hexp := Real.exp_pos (c * Real.sqrt ((E : ℝ) + h))
  have hf1 : 2 * ((E : ℝ) + h) + 1 ≤ 2 * Q := by nlinarith
  have hf2 : 2 * (h : ℝ) + 1 ≤ 2 * Q := by nlinarith
  have hf3 : (E : ℝ) + h + 1 ≤ 2 * Q := by nlinarith
  have hM2 : (M : ℝ) ≤ 8 * Q ^ 3 * Real.exp (c * Real.sqrt ((E : ℝ) + h)) := by
    have hCs' : (Csum (E + h) : ℝ) ≤ 2 * Q * Real.exp (c * Real.sqrt ((E : ℝ) + h)) :=
      hCs.trans (mul_le_mul_of_nonneg_right hf3 hexp.le)
    have hCnn : (0 : ℝ) ≤ Csum (E + h) := Nat.cast_nonneg _
    calc (M : ℝ) ≤ (2 * ((E : ℝ) + h) + 1) * ((2 * (h : ℝ) + 1) * Csum (E + h)) := hMr
      _ ≤ (2 * Q) * ((2 * Q) * (2 * Q * Real.exp (c * Real.sqrt ((E : ℝ) + h)))) := by
          gcongr
      _ = 8 * Q ^ 3 * Real.exp (c * Real.sqrt ((E : ℝ) + h)) := by ring
  -- 8·Q³·e^{c√(E+h)} = e^{log 8 + 3 log Q + c√(E+h)}.
  have hexpQ : 8 * Q ^ 3 * Real.exp (c * Real.sqrt ((E : ℝ) + h)) =
      Real.exp (Real.log 8 + 3 * Real.log Q + c * Real.sqrt ((E : ℝ) + h)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
      show 3 * Real.log Q = Real.log (Q ^ 3) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  rw [hexpQ] at hM2
  refine hM2.trans (Real.exp_le_exp.2 ?_)
  -- The exponent.
  have hlogQ : Real.log Q = Real.log ((h : ℝ) + 1) + Real.log ((E : ℝ) + 1) :=
    Real.log_mul (by positivity) (by positivity)
  have hmink : c * Real.sqrt ((E : ℝ) + h) ≤ Real.sqrt (Real.log N₁ ^ 2 + Real.log N₂ ^ 2) +
      (B * Real.log ((h : ℝ) + 1) + K) + (B * Real.log ((E : ℝ) + 1) + K) := by
    rw [cHR_sqrt_add h E]
    exact sqrt_sq_add_le hl1 hl2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by linarith) (by linarith)
  have hm1 := mul_le_mul_of_nonneg_left l1 (by linarith : (0 : ℝ) ≤ B + 3)
  have hm2 := mul_le_mul_of_nonneg_left l2 (by linarith : (0 : ℝ) ≤ B + 3)
  have hε' : (B + 3) * (δ * Real.log N₁) + (B + 3) * (δ * Real.log N₂) =
      ε * (Real.log N₁ + Real.log N₂) := by rw [← hBδ]; ring
  linarith

/-- **Hurwitz's problem for two lengths over ℂ**: for every ε > 0 there is a C such that, for all
N₁, N₂ ≥ 1, (X₁² + ⋯ + X_{N₁}²)(Y₁² + ⋯ + Y_{N₂}²) is a sum of at most
exp(√(log²N₁ + log²N₂) + ε·(log N₁ + log N₂) + C) squares of complex bilinear forms. -/
theorem hurwitzR_exp_le {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, ∀ N₁ N₂ : ℕ, 1 ≤ N₁ → 1 ≤ N₂ →
    ∃ M : ℕ, SOSLER ℂ N₁ N₂ M ∧
      (M : ℝ) ≤ Real.exp (Real.sqrt (Real.log N₁ ^ 2 + Real.log N₂ ^ 2) +
        ε * (Real.log N₁ + Real.log N₂) + C) := by
  obtain ⟨C, hC⟩ := pler_exp_le hε
  refine ⟨C + Real.log 2, fun N₁ N₂ hN₁ hN₂ => ?_⟩
  obtain ⟨M, hP, hM⟩ := hC N₁ N₂ hN₁ hN₂
  refine ⟨M + M, sosLER_of_prodLER (prodLER_of_PLER hP), ?_⟩
  rw [show Real.sqrt (Real.log N₁ ^ 2 + Real.log N₂ ^ 2) + ε * (Real.log N₁ + Real.log N₂) +
      (C + Real.log 2) = (Real.sqrt (Real.log N₁ ^ 2 + Real.log N₂ ^ 2) +
      ε * (Real.log N₁ + Real.log N₂) + C) + Real.log 2 by ring, Real.exp_add,
    Real.exp_log (by norm_num)]
  push_cast
  linarith

/-- The diagonal N₁ = N₂ = N: exponent √2, as for the square crossing. -/
theorem hurwitzR_diag {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∃ M : ℕ, SOSLER ℂ N N M ∧ (M : ℝ) ≤ Real.exp ((Real.sqrt 2 + 2 * ε) * Real.log N + C) := by
  obtain ⟨C, hC⟩ := hurwitzR_exp_le hε
  refine ⟨C, fun N hN => ?_⟩
  obtain ⟨M, hS, hM⟩ := hC N N hN hN
  refine ⟨M, hS, hM.trans (le_of_eq ?_)⟩
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [show Real.log N ^ 2 + Real.log N ^ 2 = 2 * Real.log N ^ 2 by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq hl]
  ring_nf

end TheoremB.Rect
