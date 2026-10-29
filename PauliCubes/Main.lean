/-
The main theorem: `MainTarget K` holds over every field with `2 ≠ 0`.

Call a word cheap when its normalized type has cube-cover cost at most `t₀ = 1.727899`. For each `n ≥ 1`
the crossing decomposes using cheap words only (`decomp_or_dual`); otherwise a dual certificate gives an
invariant polynomial whose support points are all expensive (`cert_invariant`, Jensen), while its
expansion in normal monomials (`ginv_span`) exposes a vertex of cost at most `t₀`
(`exists_support_le_vertices`, `normal_vertex_cost`). The decomposition gives a Pauli SOS identity
supported on cheap words (`sos_of_cross`), and the cheap words are covered type by type
(`cover_type`), at most `(n + 1)⁴ ⌈(2n + 2) 2^(n (0.727899 + ε/2))⌉` cubes in all.
-/
import PauliCubes.Cert
import PauliCubes.Generation
import PauliCubes.Bound
import PauliCubes.Cover
import PauliCubes.NoCancel

open Finset MvPolynomial Filter

namespace PauliCubes

/-- The threshold `t₀ = 1.727899`. -/
noncomputable def t0 : ℝ := 1727899 / 1000000

/-- A word is cheap when its normalized type has cube-cover cost at most `t₀`. -/
def Cheap {n : ℕ} (ν : Fin n → Fin 4) : Prop := cubeCost (normPt (wordType ν) n) ≤ t0

noncomputable instance {n : ℕ} : DecidablePred (@Cheap n) := fun _ => Real.decidableLE _ _

/-! ## Types and the cost function -/

theorem sum_wordType {n : ℕ} (ν : Fin n → Fin 4) : ∑ a, wordType ν a = n := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin 4))) (f := ν) fun _ _ => mem_univ _
  simpa [wordType] using this.symm

theorem normPt_perm_mem {n : ℕ} (hn : 0 < n) (ν : Fin n → Fin 4) (σ : Equiv.Perm (Fin 4)) :
    normPt (wordType ν) n ∘ σ ∈ stdSimplex ℝ (Fin 4) := by
  refine ⟨fun a => normPt_nonneg _ _ _, ?_⟩
  show ∑ a, normPt (wordType ν) n (σ a) = 1
  rw [Equiv.sum_comp σ (normPt (wordType ν) n)]
  simp only [normPt]
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_wordType]
  exact div_self (by exact_mod_cast hn.ne')

theorem card_G : Fintype.card (Equiv.Perm (Fin 4) × Bool) = 48 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_bool]
  rfl

/-- **Jensen.** A sum of 48 letter-permuted types of expensive words is expensive. -/
theorem expensive_sum {n : ℕ} (hn : 0 < n)
    (f : Equiv.Perm (Fin 4) × Bool → Equiv.Perm (Fin 4) × (Fin n → Fin 4))
    (hf : ∀ j, ¬ Cheap (f j).2) :
    t0 < cubeCost (normPt ⇑(∑ j, Finsupp.mapDomain (f j).1 (wexp (f j).2)) (48 * n)) := by
  set p : Equiv.Perm (Fin 4) × Bool → Fin 4 → ℝ :=
    fun j => normPt (wordType (f j).2) n ∘ (f j).1.symm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpt : normPt ⇑(∑ j, Finsupp.mapDomain (f j).1 (wexp (f j).2)) (48 * n) =
      ∑ j, (1 / 48 : ℝ) • p j := by
    funext a
    simp only [normPt, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.mapDomain_equiv_apply,
      wexp_apply, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul, p,
      Function.comp_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ := cubeCost_concave.le_map_sum (t := univ) (w := fun _ => (1 / 48 : ℝ)) (p := p)
    (fun _ _ => by norm_num)
    (by rw [Finset.sum_const, Finset.card_univ, card_G, nsmul_eq_mul]; norm_num)
    (fun j _ => normPt_perm_mem hn _ _)
  rw [hpt]
  refine lt_of_lt_of_le ?_ hJ
  have hlt : ∀ j ∈ (univ : Finset (Equiv.Perm (Fin 4) × Bool)), (1 / 48 : ℝ) • t0 <
      (1 / 48 : ℝ) • cubeCost (p j) := by
    intro j _
    rw [smul_eq_mul, smul_eq_mul]
    have : cubeCost (p j) = cubeCost (normPt (wordType (f j).2) n) := cubeCost_comp_perm _ _
    rw [this]
    have := hf j
    rw [Cheap, not_le] at this
    linarith
  calc t0 = ∑ _j : Equiv.Perm (Fin 4) × Bool, (1 / 48 : ℝ) • t0 := by
        rw [Finset.sum_const, Finset.card_univ, card_G, nsmul_eq_mul, smul_eq_mul]
        ring
    _ < ∑ j, (1 / 48 : ℝ) • cubeCost (p j) := Finset.sum_lt_sum_of_nonempty univ_nonempty hlt

theorem exists_mu_lt {x : Fin 4 → ℝ} {s : ℝ} (h : cubeCost x < s) :
    ∃ μ ∈ PairDist, 1 + ∑ a, x a * Real.logb 2 (1 / marg μ a) < s := by
  have h' : (⨅ μ : PairDist, ∑ a, x a * Real.logb 2 (1 / marg μ.1 a)) < s - 1 := by
    unfold cubeCost at h
    linarith
  have : Nonempty PairDist := ⟨⟨unifPair, unifPair_mem⟩⟩
  obtain ⟨μ, hμ⟩ := exists_lt_of_ciInf_lt h'
  exact ⟨μ.1, μ.2, by linarith⟩

theorem sum_normPt_mul (v : Fin 4 → ℕ) (d : ℕ) (ℓ : Fin 4 → ℝ) :
    ∑ a, normPt v d a * ℓ a = (∑ a, ℓ a * (v a : ℝ)) / d := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [normPt]
  ring

/-- A cheap vertex that no linear functional can separate from the support contradicts an
all-expensive support. -/
theorem vertex_contra {K : Type*} [Field K] {F : MvPolynomial (Fin 4) K} {d : ℕ} (hd : 0 < d)
    (V : Fin 4 → ℕ) (hV : cubeCost (normPt V d) ≤ t0)
    (hexp : ∀ e ∈ F.support, t0 < cubeCost (normPt ⇑e d))
    (hNC : ∀ ℓ : Fin 4 → ℝ, ∃ e ∈ F.support, lin ℓ e ≤ ∑ a, ℓ a * (V a : ℝ)) : False := by
  obtain ⟨e₀, he₀, -⟩ := hNC 0
  obtain ⟨e₁, he₁, hmin⟩ :=
    F.support.exists_min_image (fun e => cubeCost (normPt ⇑e d)) ⟨e₀, he₀⟩
  obtain ⟨μ, hμ, hlt⟩ := exists_mu_lt (lt_of_le_of_lt hV (hexp e₁ he₁))
  obtain ⟨e, he, hle⟩ := hNC fun a => Real.logb 2 (1 / marg μ a)
  have h1 := cubeCost_le hμ (x := normPt ⇑e d) (normPt_nonneg _ _)
  have h2 : ∑ a, normPt ⇑e d a * Real.logb 2 (1 / marg μ a) ≤
      ∑ a, normPt V d a * Real.logb 2 (1 / marg μ a) := by
    rw [sum_normPt_mul, sum_normPt_mul]
    exact div_le_div_of_nonneg_right hle (by positivity)
  have h3 := hmin e he
  linarith

/-- **No certificate.** For `n ≥ 1`, every functional vanishing on cheap row words and orthogonal
to cheap column words annihilates the crossing. -/
theorem no_cert {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 0 < n)
    (y : (Fin n → Fin 4) → K) (hy0 : ∀ β, Cheap β → y β = 0)
    (hy1 : ∀ ν, Cheap ν → ∑ β, y β * colVec K ν β = 0) : ∑ β, y β * crossVec K β = 0 := by
  by_contra hy2
  obtain ⟨F, hFG, hFh, hF0, hFs⟩ := cert_invariant h2 Cheap y hy0 hy1 hy2
  have hd : 0 < 48 * n := by omega
  have hexp : ∀ e ∈ F.support, t0 < cubeCost (normPt ⇑e (48 * n)) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hFs e he
    exact expensive_sum hn f hf
  have hspan := ginv_span h2 hFG hFh
  rw [Finsupp.mem_span_image_iff_linearCombination] at hspan
  obtain ⟨l, hl, hlF⟩ := hspan
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hlF
  have hS : l.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at hlF
    exact hF0 hlF.symm
  obtain ⟨m₀, hm₀⟩ := hS
  have hdeg : m₀.deg = 48 * n := hl hm₀
  have hNC := fun ℓ => exists_support_le_vertices (K := K) l.support (fun m => l m)
    (fun m hm => Finsupp.mem_support_iff.mp hm) hm₀ ℓ
  rw [hlF] at hNC
  have hv := normal_vertex_cost m₀ (by omega)
  rw [hdeg, min_le_iff] at hv
  rcases hv with hA | hB
  · exact vertex_contra hd m₀.A hA hexp fun ℓ => by
      obtain ⟨e, he, h, -⟩ := hNC ℓ
      exact ⟨e, he, h⟩
  · exact vertex_contra hd m₀.B hB hexp fun ℓ => by
      obtain ⟨e, he, -, h⟩ := hNC ℓ
      exact ⟨e, he, h⟩

/-! ## Covering the cheap words -/

theorem cubeCovered_mono {n : ℕ} {S T : Finset (Fin n → Fin 4)} {R R' : ℕ} (h : CubeCovered T R)
    (hST : S ⊆ T) (hR : R ≤ R') : CubeCovered S R' := by
  obtain ⟨C, hC, hcube, hcov⟩ := h
  exact ⟨C, hC.trans hR, hcube, hST.trans hcov⟩

theorem cubeCovered_biUnion {n : ℕ} {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (S : ι → Finset (Fin n → Fin 4)) {R : ℕ} (h : ∀ τ ∈ T, CubeCovered (S τ) R) :
    CubeCovered (T.biUnion S) (T.card * R) := by
  classical
  have h' : ∀ τ, ∃ C : Finset (Finset (Fin n → Fin 4)),
      τ ∈ T → C.card ≤ R ∧ (∀ Q ∈ C, IsCube Q) ∧ S τ ⊆ C.biUnion id := by
    intro τ
    by_cases hτ : τ ∈ T
    · obtain ⟨C, hC⟩ := h τ hτ
      exact ⟨C, fun _ => hC⟩
    · exact ⟨∅, fun h => absurd h hτ⟩
  choose C hC using h'
  refine ⟨T.biUnion C, ?_, ?_, ?_⟩
  · calc (T.biUnion C).card ≤ ∑ τ ∈ T, (C τ).card := Finset.card_biUnion_le
      _ ≤ ∑ _τ ∈ T, R := Finset.sum_le_sum fun τ hτ => (hC τ hτ).1
      _ = T.card * R := by rw [Finset.sum_const, smul_eq_mul]
  · intro Q hQ
    obtain ⟨τ, hτ, hQ⟩ := Finset.mem_biUnion.mp hQ
    exact (hC τ hτ).2.1 Q hQ
  · intro ν hν
    obtain ⟨τ, hτ, hν⟩ := Finset.mem_biUnion.mp hν
    obtain ⟨Q, hQ, hνQ⟩ := Finset.mem_biUnion.mp ((hC τ hτ).2.2 hν)
    exact Finset.mem_biUnion.mpr ⟨Q, Finset.mem_biUnion.mpr ⟨τ, hτ, hQ⟩, hνQ⟩

/-- The cheap words are covered type by type: at most `(n + 1)⁴` types, each by `cover_type`. -/
theorem cheap_covered {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    CubeCovered (univ.filter fun ν : Fin n → Fin 4 => Cheap ν)
      ((n + 1) ^ 4 * ⌈(2 * (n : ℝ) + 2) * (2 : ℝ) ^ ((n : ℝ) * (t0 - 1 + δ))⌉₊) := by
  classical
  set T := (univ.filter fun ν : Fin n → Fin 4 => Cheap ν).image wordType with hTdef
  have hT : T.card ≤ (n + 1) ^ 4 := by
    have hsub : T ⊆ Fintype.piFinset fun _ : Fin 4 => range (n + 1) := by
      intro τ hτ
      obtain ⟨ν, -, rfl⟩ := Finset.mem_image.mp hτ
      rw [Fintype.mem_piFinset]
      intro a
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)).trans
        (sum_wordType ν).le
    calc T.card ≤ _ := Finset.card_le_card hsub
      _ = (n + 1) ^ 4 := by simp [Fintype.card_piFinset]
  have hcov := cubeCovered_biUnion T
    (fun τ => univ.filter fun ν : Fin n → Fin 4 => wordType ν = τ)
    (R := ⌈(2 * (n : ℝ) + 2) * (2 : ℝ) ^ ((n : ℝ) * (t0 - 1 + δ))⌉₊) fun τ hτ => by
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hτ
      exact cover_type (wordType ν) hn (Finset.mem_filter.mp hν).2 hδ
  refine cubeCovered_mono hcov ?_ (Nat.mul_le_mul_right _ hT)
  intro ν hν
  exact Finset.mem_biUnion.mpr ⟨wordType ν, Finset.mem_image_of_mem _ hν, by simp⟩

/-! ## The count is eventually below `2^(n (0.727899 + ε))` -/

theorem poly_le {x : ℝ} (hx : 1 ≤ x) : (x + 1) ^ 4 * (2 * x + 3) ≤ 81 * x ^ 5 := by
  have h1 : (x + 1) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have h2 : 0 ≤ 2 * x + 3 := by linarith
  calc (x + 1) ^ 4 * (2 * x + 3) ≤ (2 * x) ^ 4 * (5 * x) :=
        mul_le_mul h1 (by linarith) h2 (by positivity)
    _ = 80 * x ^ 5 := by ring
    _ ≤ 81 * x ^ 5 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < x) 5]

theorem eventually_count_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n + 1) ^ 4 * ⌈(2 * (n : ℝ) + 2) * (2 : ℝ) ^ ((n : ℝ) * (t0 - 1 + ε / 2))⌉₊ ≤
        ⌊(2 : ℝ) ^ ((n : ℝ) * (0.727899 + ε))⌋₊ := by
  set r : ℝ := (2 : ℝ) ^ (ε / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 5 hr1).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 81))
  filter_upwards [ht, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hc : t0 - 1 = 0.727899 := by norm_num [t0]
  rw [hc]
  set A : ℝ := (2 : ℝ) ^ ((n : ℝ) * (0.727899 + ε / 2)) with hA
  have hA1 : 1 ≤ A := Real.one_le_rpow (by norm_num) (by positivity)
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  have hsplit : (2 : ℝ) ^ ((n : ℝ) * (0.727899 + ε)) = A * r ^ n := by
    rw [hA, hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hpoly : 81 * (n : ℝ) ^ 5 < r ^ n := by
    rw [div_lt_iff₀ hrn] at hn
    linarith
  rw [hsplit]
  apply Nat.le_floor
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2 * (n : ℝ) + 2) * A by positivity)
  push_cast
  calc ((n : ℝ) + 1) ^ 4 * (⌈(2 * (n : ℝ) + 2) * A⌉₊ : ℝ)
      ≤ ((n : ℝ) + 1) ^ 4 * ((2 * (n : ℝ) + 2) * A + 1) :=
        mul_le_mul_of_nonneg_left hceil.le (by positivity)
    _ ≤ ((n : ℝ) + 1) ^ 4 * ((2 * (n : ℝ) + 3) * A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = ((n : ℝ) + 1) ^ 4 * (2 * (n : ℝ) + 3) * A := by ring
    _ ≤ 81 * (n : ℝ) ^ 5 * A := mul_le_mul_of_nonneg_right (poly_le hn1') (by positivity)
    _ ≤ A * r ^ n := by nlinarith

/-! ## The main theorem -/

/-- **Main theorem.** Over every field with `2 ≠ 0`: for every `ε > 0` and all large `n`, the Pauli
identity `|x|²|y|² = Σ_ν w_ν (xᵀ P_ν y)²` holds with the words of nonzero weight covered by at most
`2^(n (0.727899 + ε))` cubes. -/
theorem mainTarget {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) : MainTarget K := by
  intro ε hε
  filter_upwards [eventually_count_le hε, eventually_gt_atTop 0] with n hcount hn
  classical
  rcases decomp_or_dual h2 (fun ν : Fin n → Fin 4 => Cheap ν) with
    ⟨r, d, hr, hd, h⟩ | ⟨y, hy0, hy1, hy2⟩
  · refine ⟨fun ν => tsgn K ν * (r ν + d ν), fun X Y => sos_of_cross X Y r d h, ?_⟩
    refine cubeCovered_mono (cheap_covered hn (half_pos hε)) (fun ν hν => ?_) hcount
    rw [Finset.mem_filter] at hν ⊢
    refine ⟨mem_univ _, ?_⟩
    by_contra hc
    exact hν.2 (show tsgn K ν * (r ν + d ν) = 0 by rw [hr ν hc, hd ν hc, add_zero, mul_zero])
  · exact absurd (no_cert h2 hn y hy0 hy1) hy2

end PauliCubes
