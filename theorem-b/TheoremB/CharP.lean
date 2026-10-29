/-
Theorem B in positive characteristic: the algebra.

Anthropic's formalization proves the identities behind Appendix B for integer matrices, with b = t^ν
not yet divided by anything (`GeneralPieces.Series.sum_Qk_of`, `Qk_eq_Qk'_of`). Here they are read in
a field of characteristic p. The monomials with a part divisible by p, or with a part repeated p or
more times, span an ideal that every operator a[r] maps into itself (`op_dvd`), so both factorizations
of a piece may drop them; and z_ν = ∏ k^{m_k}·m_k! is invertible for the monomials that remain, so
b = t^ν/z_ν replaces the h!-scaled normalization, which vanishes modulo p once h ≥ p.
-/
import TheoremB.Defs
import GeneralPieces.Main
import GeneralPieces.Half.List
import GeneralPieces.Series.LemmaQ
import ClauseBound.Boson.Half

open Finset ClauseBound.Boson

namespace TheoremB.CharP

/-! ### Monomials that survive modulo p -/

/-- No part is divisible by p and no part occurs p or more times. -/
def Adm (p : ℕ) (σ : Multiset ℕ) : Prop := ∀ k ∈ σ, ¬ p ∣ k ∧ σ.count k < p

instance (p : ℕ) (σ : Multiset ℕ) : Decidable (Adm p σ) := by unfold Adm; infer_instance

theorem Adm.erase {p : ℕ} {σ : Multiset ℕ} (h : Adm p σ) (l : ℕ) : Adm p (σ.erase l) := fun k hk =>
  ⟨(h k (Multiset.mem_of_mem_erase hk)).1,
    lt_of_le_of_lt (Multiset.count_le_of_le k (Multiset.erase_le l σ)) (h k (Multiset.mem_of_mem_erase hk)).2⟩

/-- Removing one part k from a monomial that does not survive: either the factor k·m_k(σ) of ∇_k is
divisible by p, or what is left still does not survive. -/
theorem not_adm_erase {p : ℕ} (hp : 0 < p) {σ : Multiset ℕ} (h : ¬ Adm p σ) (k : ℕ) :
    (p : ℤ) ∣ (k : ℤ) * (σ.count k : ℤ) ∨ ¬ Adm p (σ.erase k) := by
  simp only [Adm, not_forall, not_and_or, not_not, not_lt] at h
  obtain ⟨j, hj, hj'⟩ := h
  by_cases hjk : j = k
  · subst hjk
    rcases hj' with hd | hc
    · exact Or.inl (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hd) _)
    · rcases Nat.eq_or_lt_of_le hc with he | hlt
      · left
        rw [← he]
        exact Dvd.intro_left _ rfl
      · right
        intro ha
        have hc' : (σ.erase j).count j = σ.count j - 1 := Multiset.count_erase_self j σ
        have hmem : j ∈ σ.erase j := Multiset.count_pos.1 (by omega)
        have := (ha j hmem).2
        omega
  · right
    intro ha
    have hmem : j ∈ σ.erase k := (Multiset.mem_erase_of_ne hjk).2 hj
    have hc : (σ.erase k).count j = σ.count j := Multiset.count_erase_of_ne hjk σ
    rcases hj' with hd | hc'
    · exact (ha j hmem).1 hd
    · have := (ha j hmem).2
      omega

/-- **Stability.** Every entry of a[r] from a monomial that does not survive to one that does is
divisible by p: modulo p, a[r] maps the ideal (t_{pk}, t_k^p) into itself. -/
theorem op_dvd {p : ℕ} (hp : 0 < p) : ∀ (a : List ℕ) (r : ℤ) (π σ : Multiset ℕ), Adm p π → ¬ Adm p σ →
    (p : ℤ) ∣ op a r π σ
  | [], r, π, σ, hπ, hσ => by
    have hne : π ≠ σ := fun e => hσ (e ▸ hπ)
    by_cases hr : r = 0 <;> simp [op, one, hr, hne]
  | n :: a, r, π, σ, hπ, hσ => by
    show (p : ℤ) ∣ nop n (op a) r π σ
    unfold nop
    refine dvd_add (Finset.dvd_sum fun l _ => ?_) (Finset.dvd_sum fun k _ => ?_)
    · refine Dvd.dvd.mul_left ?_ _
      unfold cre
      split_ifs
      · exact op_dvd hp a _ _ _ (hπ.erase l) hσ
      · exact dvd_zero _
    · refine Dvd.dvd.mul_left ?_ _
      unfold ann
      rcases not_adm_erase hp hσ k with hk | hk
      · exact Dvd.dvd.mul_right hk _
      · exact Dvd.dvd.mul_left (op_dvd hp a _ _ _ hπ hk) _

theorem fL_dvd {p : ℕ} (A : FA) (h i : ℕ) {g : List ℕ → ℤ} (hg : ∀ L, (p : ℤ) ∣ g L) :
    (p : ℤ) ∣ Half.fL A h i g := by
  unfold Half.fL
  refine Dvd.dvd.mul_left (List.dvd_sum fun z hz => ?_) _
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hz
  exact Dvd.dvd.mul_left (hg c.2) _

/-- z_ν is not divisible by p for a monomial that survives. -/
theorem zz_ne_zero (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] {ν : Multiset ℕ}
    (hν : Adm p ν) : ((zz ν : ℕ) : K) ≠ 0 := by
  have pp : Prime p := Nat.Prime.prime Fact.out
  rw [Ne, CharP.cast_eq_zero_iff K p]
  unfold zz
  intro hd
  obtain ⟨k, hk, hdk⟩ := (Prime.dvd_finsetProd_iff pp _).1 hd
  rw [Multiset.mem_toFinset] at hk
  rcases pp.dvd_or_dvd hdk with h1 | h2
  · exact (hν k hk).1 (pp.dvd_of_dvd_pow h1)
  · exact absurd ((Nat.Prime.dvd_factorial Fact.out).1 h2) (not_le.2 (hν k hk).2)

/-- A sum of integers cast into a field of characteristic p may drop the monomials that do not
survive, when their terms are divisible by p. -/
theorem cast_sum_filter {p : ℕ} (K : Type) [Field K] [CharP K p] (S : Finset (Multiset ℕ))
    (f : Multiset ℕ → ℤ) (hf : ∀ τ ∈ S, ¬ Adm p τ → (p : ℤ) ∣ f τ) :
    ((∑ τ ∈ S, f τ : ℤ) : K) = ∑ τ ∈ S.filter (Adm p), (f τ : K) := by
  rw [Int.cast_sum, ← Finset.sum_filter_add_sum_filter_not S (Adm p)]
  rw [Finset.sum_eq_zero (s := S.filter (fun τ => ¬ Adm p τ)) (fun τ hτ => ?_), add_zero]
  rw [Finset.mem_filter] at hτ
  exact (CharP.intCast_eq_zero_iff K p _).2 (hf τ hτ.1 hτ.2)

/-! ### The pairing a^μ[−h]·t^ν = z_ν·[μ = ν] over ℤ -/

open GeneralPieces in
/-- From Anthropic's `lemmaDual` (a^μ[−h]·b^ν = h!·[μ = ν] with b^ν = (h!/z_ν)·t^ν, over ℚ): the
integer a^μ[−h]·t^ν is z_ν·[μ = ν]. -/
theorem pairF_aFam {L ν : List ℕ} (hL : Pos L) (hν : Pos ν) (hs : L.sum = ν.sum) :
    Series.pairF (aFam L) ν = if (L : Multiset ℕ) = ν then (zz (ν : Multiset ℕ) : ℤ) else 0 := by
  have hwL : AppHalfPieces.wt (ptn L) = ν.sum := by rw [Half.wt_ptn hL, hs]
  have hwν : AppHalfPieces.wt (ptn ν) = ν.sum := Half.wt_ptn hν
  have key := AppHalfPieces.lemmaDual ν.sum (ptn L) (ptn ν) hwL hwν
  rw [AppHalfPieces.bFam, hwν, AppHalfPieces.opFacts.smul_right, Half.aFam_eq hL] at key
  have hc := congrArg (AppHalfPieces.coef 0) key
  have hA : ∀ c ∈ aFam L, Pos c.2 := fun c hc => (aFam_ok hL c hc).1
  have e1 : AppHalfPieces.coef 0 (AppHalfPieces.op (Half.polyOf (aFam L)) (-(ν.sum : ℤ))
      (AppHalfPieces.tpow (ptn ν))) = (Series.pairF (aFam L) ν : ℚ) := by
    rw [Half.polyOf, Half.coef_op_polyK _ hA, Series.pairF, Half.toN_ptn hν]
    have h0 : toN (0 : AppHalfPieces.Ptn) = 0 := by simp [toN]
    rw [h0, Int.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    simp
  have e2 : ∀ (q : ℚ) (f : AppHalfPieces.V), AppHalfPieces.coef 0 (q • f) = q * AppHalfPieces.coef 0 f :=
    fun q f => MvPolynomial.coeff_smul _ _ _
  have e3 : ∀ q : ℚ, AppHalfPieces.coef 0 (MvPolynomial.C q : AppHalfPieces.V) = q := fun q => by
    simp [AppHalfPieces.coef]
  rw [e2, e1, e3] at hc
  have hz : AppHalfPieces.zz (ptn ν) = zz (ν : Multiset ℕ) := by rw [Half.zz_eq, Half.toN_ptn hν]
  rw [hz] at hc
  have hiff : ptn L = ptn ν ↔ (L : Multiset ℕ) = ν := by
    constructor
    · intro e
      rw [← Half.toN_ptn hL, ← Half.toN_ptn hν, e]
    · intro e
      have : ∀ M : List ℕ, ptn M = Multiset.map Nat.toPNat' (M : Multiset ℕ) := fun M => by
        rw [ptn, toPNats, Multiset.map_coe]
      rw [this, this, e]
  simp only [hiff] at hc
  have hdvd : zz (ν : Multiset ℕ) ∣ ν.sum.factorial :=
    zz_dvd_factorial ⟨(ν : Multiset ℕ), fun hi => hν _ (Multiset.mem_coe.1 hi), by rw [Multiset.sum_coe]⟩
  have hzpos : (0 : ℚ) < zz (ν : Multiset ℕ) := by
    have : 0 < zz (ν : Multiset ℕ) := Nat.pos_of_ne_zero fun h0 => by
      rw [h0] at hdvd
      exact (Nat.factorial_pos _).ne' (Nat.eq_zero_of_zero_dvd hdvd)
    exact_mod_cast this
  have hfpos : (0 : ℚ) < ν.sum.factorial := by exact_mod_cast Nat.factorial_pos _
  have hq : ((Series.pairF (aFam L) ν : ℤ) : ℚ) =
      ((if (L : Multiset ℕ) = ν then (zz (ν : Multiset ℕ) : ℤ) else 0 : ℤ) : ℚ) := by
    split_ifs with he
    · rw [if_pos he] at hc
      push_cast
      field_simp at hc
      linarith
    · rw [if_neg he] at hc
      push_cast
      rcases mul_eq_zero.1 hc with h1 | h1
      · exact absurd h1 (div_pos hfpos hzpos).ne'
      · exact h1
  exact_mod_cast hq

/-! ### The row form of Q_s, as a double sum -/

theorem list_sum_mul_sum' {β ι : Type} (A : List β) (S : Finset ι) (k : β → ℤ) (G : ι → ℤ)
    (F : β → ι → ℤ) :
    (A.map fun c => k c * ∑ τ ∈ S, G τ * F c τ).sum = ∑ τ ∈ S, G τ * (A.map fun c => k c * F c τ).sum := by
  induction A with
  | nil => simp
  | cons c A ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => by ring

/-- Display (54) for the matrices: Q'_s written as a sum over i ≤ 2h and the monomials τ of one
weight, of a function of (π, τ) times a function of (τ, σ). -/
theorem Qk'_eq (A : FA) (b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) :
    Qk' A b s π σ = ∑ i ∈ range (2 * b.sum + 1), ∑ τ ∈ Pz (σ.sum + (s - b.sum + i)),
      op b (b.sum - s - i) π τ * Half.fL A b.sum i (fun L => op L (s - b.sum + i) τ σ) := by
  unfold Qk' Half.fL mul2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_sum_mul_sum' A _ (fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ))
      (fun τ => op b (b.sum - s - i) π τ) (fun c τ => op c.2 (s - b.sum + i) τ σ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => by ring

/-! ### The pieces in characteristic p -/

/-- The monomials of weight m that survive modulo p. -/
def APz (p : ℕ) (m : ℤ) : Finset (Multiset ℕ) := (Pz m).filter (Adm p)

/-- d_p(E): the partitions of E with no part divisible by p and no part p or more times. -/
def d (p E : ℕ) : ℕ := ((P E).filter (Adm p)).card

/-- C_p(E) = d_p(0) + ⋯ + d_p(E). -/
def C (p E : ℕ) : ℕ := ∑ e ∈ range (E + 1), d p e

theorem card_APz_le (p : ℕ) {m : ℤ} {E : ℕ} (hm : m ≤ E) : (APz p m).card ≤ C p E := by
  unfold APz Pz
  split_ifs with h0
  · have hmem : m.toNat ∈ range (E + 1) := by simp only [mem_range]; omega
    exact Finset.single_le_sum (f := d p) (fun _ _ => Nat.zero_le _) hmem
  · simp

/-- From a sum over a finite set of terms of the two shapes to a crossing decomposition. -/
theorem plef_of_sum {K : Type} [CommRing K] {α ι : Type} [DecidableEq α] (T : Finset ι)
    (g g' : ι → α → α → K) (col : ι → Bool)
    (hT : ∀ x y u v, (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ j ∈ T, if col j then g j x u * g' j y v else g j x y * g' j u v) : PLEF K α T.card := by
  refine ⟨fun k => g (T.equivFin.symm k), fun k => g' (T.equivFin.symm k),
    fun k => col (T.equivFin.symm k), fun x y u v => ?_⟩
  rw [hT x y u v, ← Finset.sum_coe_sort T]
  exact Fintype.sum_equiv T.equivFin _ _ fun j => by simp

section Pieces

variable {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [CharP K p]
variable {α : Type} [DecidableEq α] {h : ℕ} {μ : α → Multiset ℕ}

/-- The piece number s: (1/z_{μ(v)})·Q_s(a^{μ(x)}, t^{μ(v)}) at the entry (μ(u), μ(y)), in K. -/
noncomputable def piece (μ : α → Multiset ℕ) (s : ℤ) (x y u v : α) : K :=
  ((zz (μ v) : ℕ) : K)⁻¹ * ((Qk (aFam (μ x).toList) (μ v).toList s (μ u) (μ y) : ℤ) : K)

omit [Fact p.Prime] [DecidableEq α] in
theorem facts (hμ : ∀ x, μ x ∈ (P h).filter (Adm p)) (x : α) :
    (μ x).sum = h ∧ 0 ∉ μ x ∧ Adm p (μ x) ∧ Pos (μ x).toList ∧ (μ x).toList.sum = h := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (hμ x)
  obtain ⟨hs, h0⟩ := mem_P.1 h1
  refine ⟨hs, h0, h2, fun n hn => Nat.one_le_iff_ne_zero.2 fun e => h0 ?_, ?_⟩
  · rw [← e]
    exact Multiset.mem_toList.1 hn
  · rw [← Multiset.sum_coe, Multiset.coe_toList, hs]

/-- **The pieces add up to the crossing**, in every field of characteristic p. -/
theorem sum_piece (hμ : ∀ x, μ x ∈ (P h).filter (Adm p)) (hinj : Function.Injective μ)
    (x y u v : α) :
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), piece K μ s x y u v = if x = v ∧ y = u then 1 else 0 := by
  obtain ⟨hsy, h0y, -, -, -⟩ := facts hμ y
  obtain ⟨-, h0u, -, -, -⟩ := facts hμ u
  obtain ⟨-, -, hav, hpv, hlv⟩ := facts hμ v
  obtain ⟨-, -, -, hpx, hlx⟩ := facts hμ x
  have hA : (aFam (μ x).toList).Ok (μ v).toList.sum := by rw [hlv, ← hlx]; exact aFam_ok hpx
  have hsum := GeneralPieces.Series.sum_Qk_of AppHalfPieces.stExpansion hA hpv h0u h0y
  rw [hsy, hlv] at hsum
  have hI : Icc (-((h : ℤ) + h)) ((h : ℤ) + h) = Icc (-(2 * h : ℤ)) (2 * h) := by congr 1 <;> ring
  rw [hI] at hsum
  unfold piece
  rw [← Finset.mul_sum, ← Int.cast_sum, hsum, pairF_aFam hpx hpv (by rw [hlx, hlv]),
    Multiset.coe_toList, Multiset.coe_toList]
  have hz := zz_ne_zero p K hav
  simp only [hinj.eq_iff]
  by_cases hxv : x = v <;> by_cases hyu : y = u
  · subst hxv hyu
    simp [hz]
  · have : ¬ u = y := fun e => hyu e.symm
    simp [hxv, hyu, this]
  · subst hyu
    simp [hxv]
  · have : ¬ u = y := fun e => hyu e.symm
    simp [hxv, hyu, this]

omit [DecidableEq α] in
/-- **Display (54) in characteristic p**: the row-wise factorization, through the monomials of
weight s + i that survive. -/
theorem piece_row (hμ : ∀ x, μ x ∈ (P h).filter (Adm p)) (s : ℤ) (x y u v : α) :
    piece K μ s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ APz p (s + i),
      (Half.fL (aFam (μ x).toList) h i (fun L => op L (s - h + i) τ (μ y)) : K) *
        (((zz (μ v) : ℕ) : K)⁻¹ * (op (μ v).toList (h - s - i) (μ u) τ : K)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hsy, h0y, -, -, -⟩ := facts hμ y
  obtain ⟨-, h0u, hau, -, -⟩ := facts hμ u
  obtain ⟨-, -, -, hpv, hlv⟩ := facts hμ v
  obtain ⟨-, -, -, hpx, hlx⟩ := facts hμ x
  have hA : (aFam (μ x).toList).Ok (μ v).toList.sum := by rw [hlv, ← hlx]; exact aFam_ok hpx
  unfold piece
  rw [GeneralPieces.Series.Qk_eq_Qk'_of AppHalfPieces.stExpansion hA hpv s h0u h0y, Qk'_eq, hsy, hlv,
    Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : ((h : ℤ) + (s - h + i)) = s + i := by ring
  rw [hw, cast_sum_filter K _ _ (fun τ _ hτ => Dvd.dvd.mul_right (op_dvd hp _ _ _ _ hau hτ) _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  push_cast
  ring

omit [DecidableEq α] in
/-- **Display (55) in characteristic p**: the column-wise factorization, through the monomials of
weight 2h − s − i that survive. -/
theorem piece_col (hμ : ∀ x, μ x ∈ (P h).filter (Adm p)) (s : ℤ) (x y u v : α) :
    piece K μ s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ APz p (2 * h - s - i),
      (Half.fL (aFam (μ x).toList) h i (fun L => op L (s - h + i) (μ u) τ) : K) *
        (((zz (μ v) : ℕ) : K)⁻¹ * (op (μ v).toList (h - s - i) τ (μ y) : K)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hsy, -, -, -, -⟩ := facts hμ y
  obtain ⟨-, -, hau, -, -⟩ := facts hμ u
  obtain ⟨-, -, -, -, hlv⟩ := facts hμ v
  unfold piece
  rw [Half.Qk_eq, hsy, hlv, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : ((h : ℤ) + (h - s - i)) = 2 * h - s - i := by ring
  rw [hw, cast_sum_filter K _ _ (fun τ _ hτ =>
      Dvd.dvd.mul_right (fL_dvd _ _ _ fun L => op_dvd hp _ _ _ _ hau hτ) _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  push_cast
  ring

end Pieces

/-- **P_F(N) in characteristic p, for one alphabet.** If N partitions of h survive modulo p, the
crossing on N letters is a sum of at most (4h+1)(2h+1)·C_p(2h) terms of the two shapes, over every
field of characteristic p: row-wise for s ≤ 0 and column-wise for s > 0. -/
theorem plef_le {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [CharP K p] {N h : ℕ} (hN : N ≤ d p h) :
    ∃ M, PLEF K (Fin N) M ∧ M ≤ (4 * h + 1) * ((2 * h + 1) * C p (2 * h)) := by
  set S := (P h).filter (Adm p) with hS
  let μ : Fin N → Multiset ℕ := fun x => (S.equivFin.symm (Fin.castLE hN x)).1
  have hμ : ∀ x, μ x ∈ (P h).filter (Adm p) := fun x => (S.equivFin.symm (Fin.castLE hN x)).2
  have hinj : Function.Injective μ := fun a b e =>
    Fin.castLE_injective hN (S.equivFin.symm.injective (Subtype.ext e))
  let T : Finset (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) := (Icc (-(2 * h : ℤ)) (2 * h)).sigma fun s =>
    (range (2 * h + 1)).sigma fun i => if s ≤ 0 then APz p (s + i) else APz p (2 * h - s - i)
  let g : (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) → Fin N → Fin N → K := fun j a b =>
    if j.1 ≤ 0 then (Half.fL (aFam (μ a).toList) h j.2.1 (fun L => op L (j.1 - h + j.2.1) j.2.2 (μ b)) : K)
    else (Half.fL (aFam (μ a).toList) h j.2.1 (fun L => op L (j.1 - h + j.2.1) (μ b) j.2.2) : K)
  let g' : (Σ _ : ℤ, Σ _ : ℕ, Multiset ℕ) → Fin N → Fin N → K := fun j a b =>
    ((zz (μ b) : ℕ) : K)⁻¹ * (if j.1 ≤ 0 then (op (μ b).toList (h - j.1 - j.2.1) (μ a) j.2.2 : K)
      else (op (μ b).toList (h - j.1 - j.2.1) j.2.2 (μ a) : K))
  refine ⟨T.card, plef_of_sum T g g' (fun j => decide (¬ j.1 ≤ 0)) fun x y u v => ?_, ?_⟩
  · rw [← sum_piece K hμ hinj x y u v, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_sigma]
    by_cases hs : s ≤ 0
    · rw [piece_row K hμ s]
      simp [g, g', hs]
    · rw [piece_col K hμ s]
      simp [g, g', hs]
  · rw [Finset.card_sigma]
    have hb : ∀ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ((range (2 * h + 1)).sigma fun i =>
        if s ≤ 0 then APz p (s + i) else APz p (2 * h - s - i)).card ≤ (2 * h + 1) * C p (2 * h) := by
      intro s hs
      rw [Finset.card_sigma]
      have : ∀ i ∈ range (2 * h + 1), (if s ≤ 0 then APz p (s + i) else APz p (2 * h - s - i)).card
          ≤ C p (2 * h) := by
        intro i hi
        rw [mem_range] at hi
        split_ifs with h0
        · exact card_APz_le p (by push_cast; omega)
        · exact card_APz_le p (by push_cast; omega)
      calc _ ≤ ∑ _i ∈ range (2 * h + 1), C p (2 * h) := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, card_range, smul_eq_mul]
    calc _ ≤ ∑ _s ∈ Icc (-(2 * h : ℤ)) (2 * h), (2 * h + 1) * C p (2 * h) := Finset.sum_le_sum hb
      _ = _ := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega

end TheoremB.CharP
