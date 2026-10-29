/-
Theorem B in positive characteristic: the growth of d_p and C_p.

d_p(E) counts the partitions of E with no part divisible by p and no part repeated p or more times.
They are counted by their multiplicities: a choice of a multiplicity below p for each part p·q + r + 1
(q < Q, r < p − 1). Their generating function is a finite product, and its logarithm is a sum of
values of the decreasing function g(y) = log Σ_{m<p} e^{−ym}, compared with an integral of g. The
constant A = (1 − 1/p)·∫₀^∞ g is never computed: it cancels between the alphabet and the pieces.
-/
import TheoremB.CharP
import Mathlib.Analysis.SumIntegralComparisons
import TheoremB.Corollaries

open Finset ClauseBound.Boson

namespace TheoremB.CharP

/-! ### Counting the surviving partitions by their multiplicities -/

section Count

variable (p Q : ℕ)

/-- The parts p·q + r + 1 for q < Q and r < p − 1: the positive integers below p·Q that p does not
divide, each once. -/
def part (j : Fin Q × Fin (p - 1)) : ℕ := p * j.1 + j.2 + 1

/-- A multiplicity below p for each part. -/
def W : Finset (Fin Q × Fin (p - 1) → ℕ) := Fintype.piFinset fun _ => range p

/-- The weight Σ part·multiplicity. -/
def w (f : Fin Q × Fin (p - 1) → ℕ) : ℕ := ∑ j, part p Q j * f j

/-- The monomial with these multiplicities. -/
def mono (f : Fin Q × Fin (p - 1) → ℕ) : Multiset ℕ := ∑ j, Multiset.replicate (f j) (part p Q j)

variable {p Q}

theorem part_eq (j : Fin Q × Fin (p - 1)) : part p Q j = p * j.1 + ((j.2 : ℕ) + 1) := by
  unfold part; ring

theorem part_pos (j : Fin Q × Fin (p - 1)) : 1 ≤ part p Q j := Nat.le_add_left 1 _

theorem part_mod (hp : 0 < p) (j : Fin Q × Fin (p - 1)) : part p Q j % p = (j.2 : ℕ) + 1 := by
  have hr : (j.2 : ℕ) + 1 < p := by have := j.2.2; omega
  rw [part_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem part_not_dvd (hp : 0 < p) (j : Fin Q × Fin (p - 1)) : ¬ p ∣ part p Q j := by
  rw [Nat.dvd_iff_mod_eq_zero, part_mod hp]
  omega

theorem part_injective (hp : 0 < p) : Function.Injective (part p Q) := by
  intro j j' e
  have hr : (j.2 : ℕ) + 1 < p := by have := j.2.2; omega
  have hr' : (j'.2 : ℕ) + 1 < p := by have := j'.2.2; omega
  have hm : (j.2 : ℕ) + 1 = (j'.2 : ℕ) + 1 := by rw [← part_mod hp j, ← part_mod hp j', e]
  have hq := congrArg (· / p) e
  simp only [part_eq, Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr', add_zero] at hq
  exact Prod.ext (Fin.ext hq) (Fin.ext (by omega))

/-- Every positive integer below p·Q that p does not divide is a part. -/
theorem exists_part (hp : 0 < p) {a : ℕ} (hpa : ¬ p ∣ a) (haQ : a < p * Q) :
    ∃ j, part p Q j = a := by
  have hmod : 1 ≤ a % p := Nat.one_le_iff_ne_zero.2 fun h => hpa (Nat.dvd_of_mod_eq_zero h)
  have hlt : a % p < p := Nat.mod_lt a hp
  have hq : a / p < Q := (Nat.div_lt_iff_lt_mul hp).2 (by rw [mul_comm]; exact haQ)
  refine ⟨(⟨a / p, hq⟩, ⟨a % p - 1, by omega⟩), ?_⟩
  rw [part_eq]
  simp only
  have := Nat.div_add_mod a p
  omega

theorem count_mono (f : Fin Q × Fin (p - 1) → ℕ) (a : ℕ) :
    (mono p Q f).count a = ∑ j, if part p Q j = a then f j else 0 := by
  unfold mono
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]

theorem count_mono_part (hp : 0 < p) (f : Fin Q × Fin (p - 1) → ℕ) (j : Fin Q × Fin (p - 1)) :
    (mono p Q f).count (part p Q j) = f j := by
  rw [count_mono, Finset.sum_eq_single j]
  · simp
  · intro j' _ hne
    rw [if_neg fun e => hne (part_injective hp e)]
  · simp

theorem sum_mono (f : Fin Q × Fin (p - 1) → ℕ) : (mono p Q f).sum = w p Q f := by
  unfold mono w
  rw [Multiset.sum_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]

theorem mem_mono {f : Fin Q × Fin (p - 1) → ℕ} {a : ℕ} (h : a ∈ mono p Q f) :
    ∃ j, part p Q j = a ∧ f j ≠ 0 := by
  obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 h
  obtain ⟨hn, rfl⟩ := Multiset.mem_replicate.1 hj
  exact ⟨j, rfl, hn⟩

/-- A surviving partition of E < p·Q is the monomial of its own multiplicities. -/
theorem mono_count (hp : 0 < p) {E : ℕ} (hEQ : E < p * Q) {μ : Multiset ℕ}
    (hμ : μ ∈ (P E).filter (Adm p)) : mono p Q (fun j => μ.count (part p Q j)) = μ := by
  obtain ⟨hP, hA⟩ := Finset.mem_filter.1 hμ
  obtain ⟨hs, -⟩ := mem_P.1 hP
  refine Multiset.ext.2 fun a => ?_
  rw [count_mono]
  by_cases ha : a ∈ μ
  · have haE : a ≤ E := hs ▸ Multiset.le_sum_of_mem ha
    obtain ⟨j₀, rfl⟩ := exists_part (Q := Q) hp (hA _ ha).1 (by omega)
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j' _ hne
      rw [if_neg fun e => hne (part_injective hp e)]
    · simp
  · rw [Multiset.count_eq_zero.2 ha]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with e
    · rw [e]
      exact Multiset.count_eq_zero.2 ha
    · rfl

/-- **d_p(E) counts the multiplicity choices of weight E**, for E < p·Q. -/
theorem d_eq (hp : 0 < p) {E : ℕ} (hEQ : E < p * Q) :
    d p E = ((W p Q).filter fun f => w p Q f = E).card := by
  symm
  refine Finset.card_nbij' (mono p Q) (fun μ j => μ.count (part p Q j)) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Set.mem_ofPred_eq] at hf ⊢
    obtain ⟨hW, hw⟩ := hf
    refine ⟨mem_P.2 ⟨by rw [sum_mono, hw], fun h0 => ?_⟩, fun a ha => ?_⟩
    · obtain ⟨j, hj, -⟩ := mem_mono h0
      have := part_pos j
      omega
    · obtain ⟨j, rfl, -⟩ := mem_mono ha
      refine ⟨part_not_dvd hp j, ?_⟩
      rw [count_mono_part hp]
      exact mem_range.1 (Fintype.mem_piFinset.1 hW j)
  · intro μ hμ
    have hμ' : μ ∈ (P E).filter (Adm p) := hμ
    obtain ⟨hP, hA⟩ := Finset.mem_filter.1 hμ'
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨Fintype.mem_piFinset.2 fun j => mem_range.2 ?_, ?_⟩
    · by_cases hj : part p Q j ∈ μ
      · exact (hA _ hj).2
      · rw [Multiset.count_eq_zero.2 hj]
        exact hp
    · rw [← sum_mono, mono_count hp hEQ hμ', (mem_P.1 hP).1]
  · intro f _
    funext j
    exact count_mono_part hp f j
  · intro μ hμ
    exact mono_count hp hEQ hμ

/-- **C_p(H) counts the multiplicity choices of weight at most H**, for H < p·Q. -/
theorem C_eq (hp : 0 < p) {H : ℕ} (hHQ : H < p * Q) :
    C p H = ((W p Q).filter fun f => w p Q f ≤ H).card := by
  rw [card_eq_sum_card_fiberwise (f := w p Q) (t := range (H + 1)) fun f hf => by
    simp only [coe_filter, Set.mem_ofPred_eq] at hf
    simp only [coe_range, Set.mem_Iio]
    omega]
  unfold C
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [mem_range] at hE
  rw [d_eq hp (by omega : E < p * Q), Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun f _ => ?_
  constructor
  · intro e
    exact ⟨by omega, e⟩
  · exact fun h => h.2

end Count

/-! ### The generating function -/

section GF

variable (p Q : ℕ)

/-- G(y) = Σ_{m<p} e^{−ym}. -/
noncomputable def G (y : ℝ) : ℝ := ∑ m ∈ range p, Real.exp (-(y * m))

/-- g(y) = log G(y). -/
noncomputable def g (y : ℝ) : ℝ := Real.log (G p y)

/-- F(x) = Σ_f e^{−x·w(f)}. -/
noncomputable def F (x : ℝ) : ℝ := ∑ f ∈ W p Q, Real.exp (-(x * w p Q f))

variable {p Q}

theorem one_le_G (hp : 0 < p) (y : ℝ) : 1 ≤ G p y := by
  unfold G
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, mul_zero, neg_zero, Real.exp_zero]
  have : 0 ≤ ∑ m ∈ range k, Real.exp (-(y * ((m + 1 : ℕ) : ℝ))) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  linarith

theorem G_pos (hp : 0 < p) (y : ℝ) : 0 < G p y := lt_of_lt_of_le one_pos (one_le_G hp y)

theorem g_nonneg (hp : 0 < p) (y : ℝ) : 0 ≤ g p y := Real.log_nonneg (one_le_G hp y)

/-- The product formula: F(x) = ∏_j G(part_j·x). -/
theorem F_eq_prod (x : ℝ) : F p Q x = ∏ j, G p (part p Q j * x) := by
  unfold F G W
  rw [prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold w
  rw [← Real.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem log_F (hp : 0 < p) (x : ℝ) : Real.log (F p Q x) = ∑ j, g p (part p Q j * x) := by
  rw [F_eq_prod, Real.log_prod fun j _ => (G_pos hp _).ne']
  rfl

theorem F_pos (hp : 0 < p) (x : ℝ) : 0 < F p Q x := by
  rw [F_eq_prod]
  exact Finset.prod_pos fun j _ => G_pos hp _

/-- **Chernoff, upper side**: C_p(H)·e^{−xH} ≤ F(x). -/
theorem C_mul_exp_le (hp : 0 < p) {H : ℕ} (hHQ : H < p * Q) {x : ℝ} (hx : 0 ≤ x) :
    (C p H : ℝ) * Real.exp (-(x * H)) ≤ F p Q x := by
  rw [C_eq hp hHQ, ← nsmul_eq_mul, ← Finset.sum_const]
  calc ∑ _f ∈ (W p Q).filter (fun f => w p Q f ≤ H), Real.exp (-(x * H))
      ≤ ∑ f ∈ (W p Q).filter (fun f => w p Q f ≤ H), Real.exp (-(x * w p Q f)) := by
        refine Finset.sum_le_sum fun f hf => Real.exp_le_exp.2 ?_
        have : (w p Q f : ℝ) ≤ H := by exact_mod_cast (Finset.mem_filter.1 hf).2
        nlinarith
    _ ≤ F p Q x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => (Real.exp_pos _).le

/-- **Chernoff, both tails**: for z ≤ x ≤ y and L ≤ H, the mass of F(x) outside weights [L, H] is
controlled by F(y) and F(z), so the rest is at most C_p(H)·e^{−xL}. -/
theorem F_le_tails (hp : 0 < p) {H L : ℕ} (hHQ : H < p * Q) {x y z : ℝ} (hz : 0 ≤ z) (hzx : z ≤ x)
    (hxy : x ≤ y) :
    F p Q x ≤ Real.exp ((y - x) * L) * F p Q y + C p H * Real.exp (-(x * L))
      + Real.exp (-((x - z) * H)) * F p Q z := by
  have hx : 0 ≤ x := le_trans hz hzx
  unfold F
  rw [← Finset.sum_filter_add_sum_filter_not (W p Q) (fun f => w p Q f < L)]
  rw [← Finset.sum_filter_add_sum_filter_not ((W p Q).filter fun f => ¬ w p Q f < L)
    (fun f => w p Q f ≤ H)]
  have h1 : ∑ f ∈ (W p Q).filter (fun f => w p Q f < L), Real.exp (-(x * w p Q f))
      ≤ Real.exp ((y - x) * L) * ∑ f ∈ W p Q, Real.exp (-(y * w p Q f)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun f hf => ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun _ _ _ => by positivity)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : (w p Q f : ℝ) ≤ L := by exact_mod_cast (Finset.mem_filter.1 hf).2.le
    nlinarith
  have h2 : ∑ f ∈ ((W p Q).filter fun f => ¬ w p Q f < L).filter (fun f => w p Q f ≤ H),
      Real.exp (-(x * w p Q f)) ≤ C p H * Real.exp (-(x * L)) := by
    calc _ ≤ ∑ _f ∈ ((W p Q).filter fun f => ¬ w p Q f < L).filter (fun f => w p Q f ≤ H),
          Real.exp (-(x * L)) := by
          refine Finset.sum_le_sum fun f hf => Real.exp_le_exp.2 ?_
          rw [Finset.mem_filter, Finset.mem_filter] at hf
          have : (L : ℝ) ≤ w p Q f := by exact_mod_cast not_lt.1 hf.1.2
          nlinarith
      _ = (((W p Q).filter fun f => ¬ w p Q f < L).filter (fun f => w p Q f ≤ H)).card *
          Real.exp (-(x * L)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C p H * Real.exp (-(x * L)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          rw [C_eq hp hHQ, Finset.filter_filter]
          exact_mod_cast Finset.card_le_card fun f hf => by
            simp only [Finset.mem_filter] at hf ⊢
            exact ⟨hf.1, hf.2.2⟩
  have h3 : ∑ f ∈ ((W p Q).filter fun f => ¬ w p Q f < L).filter (fun f => ¬ w p Q f ≤ H),
      Real.exp (-(x * w p Q f)) ≤ Real.exp (-((x - z) * H)) * ∑ f ∈ W p Q, Real.exp (-(z * w p Q f)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun f hf => ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (fun f hf => (Finset.mem_filter.1 (Finset.mem_filter.1 hf).1).1) fun _ _ _ => by positivity)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [Finset.mem_filter] at hf
    have : (H : ℝ) ≤ w p Q f := by exact_mod_cast (not_le.1 hf.2).le
    nlinarith
  linarith

end GF

/-! ### g and its integral -/

section Integral

variable {p : ℕ}

theorem G_antitone (p : ℕ) : Antitone (G p) := by
  intro a b hab
  unfold G
  refine Finset.sum_le_sum fun m _ => Real.exp_le_exp.2 ?_
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem g_antitone (hp : 0 < p) : Antitone (g p) := fun _ b hab =>
  Real.log_le_log (G_pos hp b) (G_antitone p hab)

theorem g_le_log (hp : 0 < p) {y : ℝ} (hy : 0 ≤ y) : g p y ≤ Real.log p := by
  have h := g_antitone hp hy
  have h0 : G p 0 = p := by simp [G]
  unfold g at h ⊢
  rwa [h0] at h

theorem g_le_exp (hp : 0 < p) {y : ℝ} (hy : 0 ≤ y) : g p y ≤ ((p : ℝ) - 1) * Real.exp (-y) := by
  have h1 := Real.log_le_sub_one_of_pos (G_pos hp y)
  refine le_trans h1 ?_
  unfold G
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, add_sub_cancel_right]
  have hle : ∀ m ∈ range k, Real.exp (-(y * ((m + 1 : ℕ) : ℝ))) ≤ Real.exp (-y) := fun m _ =>
    Real.exp_le_exp.2 (by push_cast; nlinarith)
  refine le_trans (Finset.sum_le_sum hle) ?_
  simp

theorem g_intervalIntegrable (hp : 0 < p) (a b : ℝ) :
    IntervalIntegrable (g p) MeasureTheory.volume a b :=
  ((g_antitone hp).antitoneOn _).intervalIntegrable

theorem integral_exp_neg' (a b : ℝ) : ∫ t in a..b, Real.exp (-t) = Real.exp (-a) - Real.exp (-b) := by
  rw [intervalIntegral.integral_comp_neg (fun t => Real.exp t), integral_exp]

theorem integral_g_le (hp : 0 < p) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, g p t ≤ ((p : ℝ) - 1) * Real.exp (-a) := by
  have hc : Continuous fun t : ℝ => ((p : ℝ) - 1) * Real.exp (-t) :=
    continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  have h1 : ∫ t in a..b, g p t ≤ ∫ t in a..b, ((p : ℝ) - 1) * Real.exp (-t) :=
    intervalIntegral.integral_mono_on hab (g_intervalIntegrable hp a b) (hc.intervalIntegrable a b)
      fun t ht => g_le_exp hp (le_trans ha ht.1)
  rw [intervalIntegral.integral_const_mul, integral_exp_neg'] at h1
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  nlinarith [Real.exp_pos (-b)]

/-- J(Y) = ∫₀^Y g. -/
noncomputable def J (p : ℕ) (Y : ℝ) : ℝ := ∫ t in (0 : ℝ)..Y, g p t

theorem J_sub (hp : 0 < p) (a b : ℝ) : J p b - J p a = ∫ t in a..b, g p t :=
  intervalIntegral.integral_interval_sub_left (g_intervalIntegrable hp 0 b) (g_intervalIntegrable hp 0 a)

theorem J_nonneg (hp : 0 < p) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ J p Y :=
  intervalIntegral.integral_nonneg hY fun t _ => g_nonneg hp t

theorem J_mono (hp : 0 < p) {a b : ℝ} (hab : a ≤ b) : J p a ≤ J p b := by
  have := J_sub hp a b
  have h0 : 0 ≤ ∫ t in a..b, g p t := intervalIntegral.integral_nonneg hab fun t _ => g_nonneg hp t
  linarith

theorem J_le_mul (hp : 0 < p) {Y : ℝ} (hY : 0 ≤ Y) : J p Y ≤ Y * Real.log p := by
  have h := intervalIntegral.integral_mono_on hY (g_intervalIntegrable hp 0 Y)
    (continuous_const.intervalIntegrable 0 Y) fun t ht => g_le_log hp ht.1
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  exact h

theorem J_bdd (hp : 0 < p) {Y : ℝ} (hY : 0 ≤ Y) : J p Y ≤ (p : ℝ) - 1 := by
  have := integral_g_le hp le_rfl hY
  rwa [neg_zero, Real.exp_zero, mul_one] at this

/-- I = ∫₀^∞ g, as the supremum of ∫₀^n g. -/
noncomputable def I (p : ℕ) : ℝ := ⨆ n : ℕ, J p n

theorem bdd_J (hp : 0 < p) : BddAbove (Set.range fun n : ℕ => J p n) :=
  ⟨(p : ℝ) - 1, by rintro _ ⟨n, rfl⟩; exact J_bdd hp (Nat.cast_nonneg n)⟩

theorem J_le_I (hp : 0 < p) {Y : ℝ} : J p Y ≤ I p :=
  le_trans (J_mono hp (Nat.le_ceil Y)) (le_ciSup (bdd_J hp) ⌈Y⌉₊)

theorem I_le (hp : 0 < p) {Y : ℝ} (hY : 0 ≤ Y) : I p ≤ J p Y + ((p : ℝ) - 1) * Real.exp (-Y) := by
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  refine ciSup_le fun n => ?_
  by_cases hn : (n : ℝ) ≤ Y
  · have := J_mono hp hn
    nlinarith [Real.exp_pos (-Y)]
  · have h1 := J_sub hp Y n
    have h2 := integral_g_le hp hY (le_of_lt (not_le.1 hn))
    linarith

theorem I_nonneg (hp : 0 < p) : 0 ≤ I p := le_trans (J_nonneg hp (Y := 0) le_rfl) (J_le_I hp)

theorem I_pos (hp : 2 ≤ p) : 0 < I p := by
  have hp0 : 0 < p := by omega
  have hG : 1 < G p 1 := by
    unfold G
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero]
    have : 0 ≤ ∑ m ∈ range k, Real.exp (-(1 * ((m + 1 + 1 : ℕ) : ℝ))) :=
      Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    have := Real.exp_pos (-(1 * ((0 + 1 : ℕ) : ℝ)))
    linarith
  have hg : 0 < g p 1 := Real.log_pos hG
  have hJ : g p 1 ≤ J p 1 := by
    have h := intervalIntegral.integral_mono_on zero_le_one (continuous_const.intervalIntegrable 0 1)
      (g_intervalIntegrable hp0 0 1) fun t ht => g_antitone hp0 ht.2
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at h
  exact lt_of_lt_of_le hg (le_trans hJ (J_le_I hp0))

/-- The Riemann sum of one residue class, from above: Σ_{q<Q} g((pq + a)x) ≤ log p + I/(px). -/
theorem sum_g_le (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) {x : ℝ} (hx : 0 < x) (Q : ℕ) :
    ∑ q ∈ range Q, g p ((p * q + a) * x) ≤ Real.log p + I p / (p * x) := by
  have hpx : 0 < (p : ℝ) * x := mul_pos (by exact_mod_cast hp) hx
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hI : 0 ≤ I p / (p * x) := div_nonneg (I_nonneg hp) hpx.le
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => g p ((p : ℝ) * x * t + a * x) := ⟨_, rfl⟩
  have hfa : Antitone f := fun s t hst => by
    simp only [hf]
    exact g_antitone hp (by nlinarith)
  have hterm : ∀ q : ℕ, g p ((p * q + a) * x) = f q := fun q => by simp only [hf]; ring_nf
  rcases Q with _ | k
  · simp only [range_zero, sum_empty]
    linarith
  rw [Finset.sum_range_succ']
  simp only [hterm]
  have h0 : f ((0 : ℕ) : ℝ) ≤ Real.log p := by
    simp only [hf, Nat.cast_zero, mul_zero, zero_add]
    exact g_le_log hp (by positivity)
  have h1 := AntitoneOn.sum_le_integral (f := f) (x₀ := 0) (a := k) (hfa.antitoneOn _)
  simp only [zero_add] at h1
  have h2 : ∫ t in (0 : ℝ)..k, f t = (p * x)⁻¹ * (J p (p * x * k + a * x) - J p (a * x)) := by
    simp only [hf]
    rw [intervalIntegral.integral_comp_mul_add (fun t => g p t) hpx.ne', smul_eq_mul, mul_zero, zero_add,
      J_sub hp]
  have h3 : J p (p * x * k + a * x) - J p (a * x) ≤ I p := by
    have := J_le_I hp (Y := p * x * k + a * x)
    have := J_nonneg hp (by positivity : (0 : ℝ) ≤ a * x)
    linarith
  have h4 : (p * x)⁻¹ * (J p (p * x * k + a * x) - J p (a * x)) ≤ I p / (p * x) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hpx.le)
  have h5 : ∑ i ∈ range k, f ((i + 1 : ℕ) : ℝ) ≤ I p / (p * x) := by
    rw [← h2] at h4
    exact le_trans h1 h4
  calc _ ≤ I p / (p * x) + Real.log p := add_le_add h5 h0
    _ = _ := add_comm _ _

/-- The Riemann sum of one residue class, from below. -/
theorem le_sum_g (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ p) {x : ℝ} (hx : 0 < x) (Q : ℕ) :
    I p / (p * x) - Real.log p - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x)
      ≤ ∑ q ∈ range Q, g p ((p * q + a) * x) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpx : 0 < (p : ℝ) * x := mul_pos hp' hx
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => g p ((p : ℝ) * x * t + a * x) := ⟨_, rfl⟩
  have hfa : Antitone f := fun s t hst => by
    simp only [hf]
    exact g_antitone hp (by nlinarith)
  have hterm : ∀ q : ℕ, g p ((p * q + a) * x) = f q := fun q => by simp only [hf]; ring_nf
  simp only [hterm]
  have h1 := AntitoneOn.integral_le_sum (f := f) (x₀ := 0) (a := Q) (hfa.antitoneOn _)
  simp only [zero_add] at h1
  have h2 : ∫ t in (0 : ℝ)..Q, f t = (p * x)⁻¹ * (J p (p * x * Q + a * x) - J p (a * x)) := by
    simp only [hf]
    rw [intervalIntegral.integral_comp_mul_add (fun t => g p t) hpx.ne', smul_eq_mul, mul_zero, zero_add,
      J_sub hp]
  have hE : 0 ≤ p * x * Q + a * x := by positivity
  have h3 := I_le hp hE
  have h4 := J_le_mul hp (by positivity : (0 : ℝ) ≤ a * x)
  have h5 : Real.exp (-(p * x * Q + a * x)) ≤ Real.exp (-(p * x * Q)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h6 : I p - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) - a * x * Real.log p
      ≤ J p (p * x * Q + a * x) - J p (a * x) := by nlinarith
  have h7 : a * x * Real.log p / (p * x) ≤ Real.log p := by
    rw [div_le_iff₀ hpx]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hap) hx.le) hlog]
  have h8 : (I p - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) - a * x * Real.log p) / (p * x)
      ≤ ∫ t in (0 : ℝ)..Q, f t := by
    rw [h2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hpx.le)
  have h9 : (I p - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) - a * x * Real.log p) / (p * x)
      = I p / (p * x) - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x) - a * x * Real.log p / (p * x) := by
    ring
  linarith

/-- log F(x) as a double sum over the residues and the quotients. -/
theorem log_F_eq (hp : 0 < p) (Q : ℕ) (x : ℝ) :
    Real.log (F p Q x) = ∑ r : Fin (p - 1), ∑ q ∈ range Q, g p ((p * q + ((r : ℝ) + 1)) * x) := by
  rw [log_F hp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun q => g p ((p * q + ((r : ℝ) + 1)) * x)) Q]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [part_eq]

/-- **The two-sided bound** A/x − c − c'·e^{−pxQ}/x ≤ log F(x) ≤ A/x + c with A = (p−1)·I/p. -/
theorem log_F_le (hp : 0 < p) (Q : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.log (F p Q x) ≤ ((p : ℝ) - 1) * Real.log p + ((p : ℝ) - 1) * I p / p / x := by
  rw [log_F_eq hp]
  have hpx : (p : ℝ) * x ≠ 0 := (mul_pos (by exact_mod_cast hp) hx).ne'
  calc ∑ r : Fin (p - 1), ∑ q ∈ range Q, g p ((p * q + ((r : ℝ) + 1)) * x)
      ≤ ∑ _r : Fin (p - 1), (Real.log p + I p / (p * x)) :=
        Finset.sum_le_sum fun r _ => sum_g_le hp (by positivity) hx Q
    _ = _ := by
      rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
      field_simp
      ring

theorem le_log_F (hp : 0 < p) (Q : ℕ) {x : ℝ} (hx : 0 < x) :
    ((p : ℝ) - 1) * I p / p / x - ((p : ℝ) - 1) * Real.log p
      - ((p : ℝ) - 1) * ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x) ≤ Real.log (F p Q x) := by
  rw [log_F_eq hp]
  have hpx : (p : ℝ) * x ≠ 0 := (mul_pos (by exact_mod_cast hp) hx).ne'
  calc _ = ∑ _r : Fin (p - 1), (I p / (p * x) - Real.log p - ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x)) := by
        rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
        field_simp
        ring
    _ ≤ _ := Finset.sum_le_sum fun r _ => le_sum_g hp (by positivity) (by
        have := r.2
        have h1 : ((r : ℕ) : ℝ) + 1 ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h1
        push_cast at h1
        linarith) hx Q

end Integral

/-! ### The saddle point -/

section Saddle

variable {p : ℕ}

/-- A = (1 − 1/p)·∫₀^∞ g, the growth constant; it is never computed. -/
noncomputable def A (p : ℕ) : ℝ := ((p : ℝ) - 1) * I p / p

/-- B = (p − 1)·log p. -/
noncomputable def B (p : ℕ) : ℝ := ((p : ℝ) - 1) * Real.log p

theorem A_pos (hp : 2 ≤ p) : 0 < A p := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp
  exact div_pos (mul_pos (by linarith) (I_pos hp)) (by linarith)

theorem B_nonneg (hp : 0 < p) : 0 ≤ B p := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact mul_nonneg (by linarith) (Real.log_nonneg h1)

theorem F_le_exp (hp : 0 < p) (Q : ℕ) {x : ℝ} (hx : 0 < x) : F p Q x ≤ Real.exp (B p + A p / x) := by
  rw [← Real.exp_log (F_pos hp x)]
  refine Real.exp_le_exp.2 (le_trans (log_F_le hp Q hx) (le_of_eq ?_))
  unfold A B
  ring

theorem exp_neg_le_inv {u : ℝ} (hu : 0 < u) : Real.exp (-u) ≤ 1 / u := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hu (by linarith [Real.add_one_le_exp u])

theorem exp_le_F (hp : 0 < p) {Q H : ℕ} (hHQ : H < p * Q) (hH : 1 ≤ H) {x : ℝ} (hx : 0 < x) :
    Real.exp (A p / x - B p - ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * (x * x * H))) ≤ F p Q x := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hQ : (H : ℝ) ≤ p * Q := by exact_mod_cast hHQ.le
  have hxH : 0 < x * H := by positivity
  have he : Real.exp (-(p * x * Q)) ≤ 1 / (x * H) :=
    le_trans (Real.exp_le_exp.2 (by nlinarith)) (exp_neg_le_inv hxH)
  have hc : 0 ≤ ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * x) := div_nonneg (mul_nonneg hp1 hp1) (by positivity)
  have e1 : ((p : ℝ) - 1) * ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x)
      = (((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * x)) * Real.exp (-(p * x * Q)) := by ring
  have e2 : ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * (x * x * H))
      = (((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * x)) * (1 / (x * H)) := by
    field_simp
  have h2 : ((p : ℝ) - 1) * ((p : ℝ) - 1) * Real.exp (-(p * x * Q)) / (p * x)
      ≤ ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * (x * x * H)) := by
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left he hc
  rw [← Real.exp_log (F_pos hp x)]
  refine Real.exp_le_exp.2 ?_
  have h3 := le_log_F hp Q hx
  have e3 : A p / x = ((p : ℝ) - 1) * I p / p / x := rfl
  unfold B
  rw [e3]
  linarith

/-- **Upper growth**: C_p(H) ≤ e^{2√(AH) + B}. -/
theorem C_le (hp : 2 ≤ p) {H : ℕ} (hH : 1 ≤ H) :
    (C p H : ℝ) ≤ Real.exp (2 * Real.sqrt (A p * H) + B p) := by
  have hp0 : 0 < p := by omega
  have hA := A_pos hp
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (A p * H) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 (mul_pos hA hH')
  have hss : s * s = A p * H := hs_def ▸ Real.mul_self_sqrt (mul_pos hA hH').le
  rw [← hs_def]
  have hx : 0 < s / H := div_pos hs hH'
  have hxH : s / H * H = s := by field_simp
  have hAx : A p / (s / H) = s := by
    field_simp
    linarith
  have hHQ : H < p * (H / p + 1) := Nat.lt_mul_div_succ H hp0
  have h1 := C_mul_exp_le hp0 hHQ hx.le
  have h2 := F_le_exp hp0 (H / p + 1) hx
  have h3 : (C p H : ℝ) = (C p H : ℝ) * Real.exp (-(s / H * H)) * Real.exp (s / H * H) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [h3]
  calc (C p H : ℝ) * Real.exp (-(s / H * H)) * Real.exp (s / H * H)
      ≤ Real.exp (B p + A p / (s / H)) * Real.exp (s / H * H) :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) (Real.exp_pos _).le
    _ = Real.exp (2 * s + B p) := by
        rw [← Real.exp_add, hAx, hxH]
        ring_nf

/-- **Lower growth**: for 0 < γ ≤ 1/8 and all large H, C_p(H) ≥ e^{2√(AH)(1 − 2γ − 2γ²) − B'}. -/
theorem le_C (hp : 2 ≤ p) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 8) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → Real.exp (2 * Real.sqrt (A p * H) * (1 - 2 * γ - 2 * γ ^ 2)
      - (2 * Real.sqrt (A p) + B p + ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * A p) + Real.log 2))
        ≤ C p H := by
  have hp0 : 0 < p := by omega
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    linarith
  have hA := A_pos hp
  have hB := B_nonneg hp0
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * A p) := ⟨_, rfl⟩
  rw [← hB2]
  have hB2n : 0 ≤ B2 := hB2 ▸ div_nonneg (mul_nonneg hp1 hp1) (by positivity)
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = γ ^ 2 * (1 + 10 * γ + 8 * γ ^ 2) / ((1 + γ) * (1 + 2 * γ)) := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = γ ^ 2 / (1 + γ) := ⟨_, rfl⟩
  have hm1p : 0 < m1 := hm1 ▸ by positivity
  have hm2p : 0 < m2 := hm2 ▸ by positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = (2 * B p + B2 + Real.log 4) / min m1 m2 := ⟨_, rfl⟩
  have hmin : 0 < min m1 m2 := lt_min hm1p hm2p
  have hS₀n : 0 ≤ S₀ := hS₀ ▸ div_nonneg (by linarith) hmin.le
  refine ⟨max 1 ⌈S₀ ^ 2 / A p⌉₊, fun H hH => ?_⟩
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) hH
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hHp : (0 : ℝ) < H := by linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (A p * H) := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 (mul_pos hA hHp)
  have hss : s * s = A p * H := hs_def ▸ Real.mul_self_sqrt (mul_pos hA hHp).le
  have hsS : S₀ ≤ s := by
    rw [hs_def, Real.le_sqrt hS₀n (mul_pos hA hHp).le]
    have h1 : S₀ ^ 2 / A p ≤ H :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hH)
    rw [div_le_iff₀ hA] at h1
    linarith
  have hkey : 2 * B p + B2 + Real.log 4 ≤ s * min m1 m2 := by
    have : S₀ * min m1 m2 = 2 * B p + B2 + Real.log 4 := by rw [hS₀]; field_simp
    have := mul_le_mul_of_nonneg_right hsS hmin.le
    linarith
  have hk1 : 2 * B p + B2 + Real.log 4 ≤ s * m1 :=
    le_trans hkey (mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le)
  have hk2 : 2 * B p + B2 + Real.log 4 ≤ s * m2 :=
    le_trans hkey (mul_le_mul_of_nonneg_left (min_le_right _ _) hs.le)
  -- the three points t, x = (1+γ)t, y = (1+2γ)t, with t = √(A/H)
  have ht : 0 < s / H := div_pos hs hHp
  have htH : s / H * H = s := by field_simp
  have hAt : A p / (s / H) = s := by
    field_simp
    linarith
  have httH : s / H * (s / H) * H = A p := by
    field_simp
    linarith
  have ht_le : s / H ≤ Real.sqrt (A p) := by
    rw [Real.le_sqrt ht.le hA.le]
    have : s / H * (s / H) * 1 ≤ s / H * (s / H) * H :=
      mul_le_mul_of_nonneg_left hH' (by positivity)
    calc (s / H) ^ 2 = s / H * (s / H) * 1 := by ring
      _ ≤ s / H * (s / H) * H := this
      _ = A p := httH
  have hx : 0 < (1 + γ) * (s / H) := by positivity
  have hy : 0 < (1 + 2 * γ) * (s / H) := by positivity
  have hAx : A p / ((1 + γ) * (s / H)) = s / (1 + γ) := by
    rw [mul_comm, ← div_div, hAt]
  have hAy : A p / ((1 + 2 * γ) * (s / H)) = s / (1 + 2 * γ) := by
    rw [mul_comm, ← div_div, hAt]
  have hγ4 : 0 ≤ 1 - 4 * γ := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = ⌊(1 - 4 * γ) * H⌋₊ := ⟨_, rfl⟩
  have hL1 : (L : ℝ) ≤ (1 - 4 * γ) * H := hL ▸ Nat.floor_le (by positivity)
  have hL2 : (1 - 4 * γ) * H < L + 1 := hL ▸ Nat.lt_floor_add_one _
  have hHQ : H < p * (H / p + 1) := Nat.lt_mul_div_succ H hp0
  have tails := F_le_tails (L := L) hp0 hHQ (x := (1 + γ) * (s / H)) (y := (1 + 2 * γ) * (s / H))
    ht.le (le_mul_of_one_le_left ht.le (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) ht.le)
  have hFy := F_le_exp hp0 (H / p + 1) hy
  have hFz := F_le_exp hp0 (H / p + 1) ht
  have hFx := exp_le_F hp0 hHQ hH1 hx
  rw [hAy] at hFy
  rw [hAt] at hFz
  rw [hAx] at hFx
  have hxxH : ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * ((1 + γ) * (s / H) * ((1 + γ) * (s / H)) * H)) ≤ B2 := by
    have hX : (1 + γ) * (s / H) * ((1 + γ) * (s / H)) * H = (1 + γ) ^ 2 * A p := by
      rw [← httH]
      ring
    rw [hB2, hX]
    refine div_le_div_of_nonneg_left (mul_nonneg hp1 hp1) (mul_pos hp' hA) ?_
    have : A p ≤ (1 + γ) ^ 2 * A p := le_mul_of_one_le_left hA.le (one_le_pow₀ (by linarith))
    exact mul_le_mul_of_nonneg_left this hp'.le
  obtain ⟨E, hE_def⟩ : ∃ E, E = Real.exp (s / (1 + γ) - B p - B2) := ⟨_, rfl⟩
  have hE : E ≤ F p (H / p + 1) ((1 + γ) * (s / H)) :=
    hE_def ▸ le_trans (Real.exp_le_exp.2 (by linarith)) hFx
  have hE4 : Real.exp (s / (1 + γ) - B p - B2 - Real.log 4) = E / 4 := by
    rw [hE_def, Real.exp_sub _ (Real.log 4), Real.exp_log (by norm_num)]
  have h1 : Real.exp (((1 + 2 * γ) * (s / H) - (1 + γ) * (s / H)) * L) *
      F p (H / p + 1) ((1 + 2 * γ) * (s / H)) ≤ E / 4 := by
    have hyx : ((1 + 2 * γ) * (s / H) - (1 + γ) * (s / H)) * L ≤ γ * (1 - 4 * γ) * s := by
      have : ((1 + 2 * γ) * (s / H) - (1 + γ) * (s / H)) * L = γ * (s / H) * L := by ring
      rw [this]
      have h2 : γ * (s / H) * L ≤ γ * (s / H) * ((1 - 4 * γ) * H) :=
        mul_le_mul_of_nonneg_left hL1 (by positivity)
      have h3 : γ * (s / H) * ((1 - 4 * γ) * H) = γ * (1 - 4 * γ) * s := by
        field_simp
      linarith
    have hm : s / (1 + γ) - s / (1 + 2 * γ) - γ * (1 - 4 * γ) * s = s * m1 := by
      rw [hm1]
      field_simp
      ring
    calc _ ≤ Real.exp (γ * (1 - 4 * γ) * s) * Real.exp (B p + s / (1 + 2 * γ)) :=
          mul_le_mul (Real.exp_le_exp.2 hyx) hFy (F_pos hp0 _).le (Real.exp_pos _).le
      _ = Real.exp (γ * (1 - 4 * γ) * s + (B p + s / (1 + 2 * γ))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (s / (1 + γ) - B p - B2 - Real.log 4) := Real.exp_le_exp.2 (by linarith)
      _ = E / 4 := hE4
  have h3 : Real.exp (-(((1 + γ) * (s / H) - s / H) * H)) * F p (H / p + 1) (s / H) ≤ E / 4 := by
    have hxz : ((1 + γ) * (s / H) - s / H) * H = γ * s := by
      field_simp
      ring
    have hm : s / (1 + γ) - s + γ * s = s * m2 := by
      rw [hm2]
      field_simp
      ring
    rw [hxz]
    calc _ ≤ Real.exp (-(γ * s)) * Real.exp (B p + s) :=
          mul_le_mul_of_nonneg_left hFz (Real.exp_pos _).le
      _ = Real.exp (-(γ * s) + (B p + s)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (s / (1 + γ) - B p - B2 - Real.log 4) := Real.exp_le_exp.2 (by linarith)
      _ = E / 4 := hE4
  have hC : E / 2 ≤ C p H * Real.exp (-((1 + γ) * (s / H) * L)) := by linarith
  have hC2 : Real.exp (s / (1 + γ) - B p - B2 - Real.log 2 + (1 + γ) * (s / H) * L) ≤ C p H := by
    have e1 : Real.exp (s / (1 + γ) - B p - B2 - Real.log 2 + (1 + γ) * (s / H) * L)
        = E / 2 * Real.exp ((1 + γ) * (s / H) * L) := by
      rw [Real.exp_add, Real.exp_sub _ (Real.log 2), Real.exp_log (by norm_num), hE_def]
    rw [e1]
    calc E / 2 * Real.exp ((1 + γ) * (s / H) * L)
        ≤ C p H * Real.exp (-((1 + γ) * (s / H) * L)) * Real.exp ((1 + γ) * (s / H) * L) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ = C p H := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  refine le_trans (Real.exp_le_exp.2 ?_) hC2
  have hxL : (1 + γ) * (1 - 4 * γ) * s - 2 * Real.sqrt (A p) ≤ (1 + γ) * (s / H) * L := by
    have h4 : (1 + γ) * (s / H) * ((1 - 4 * γ) * H - 1) ≤ (1 + γ) * (s / H) * L :=
      mul_le_mul_of_nonneg_left (by linarith) hx.le
    have h5 : (1 + γ) * (s / H) * ((1 - 4 * γ) * H - 1) = (1 + γ) * (1 - 4 * γ) * s - (1 + γ) * (s / H) := by
      field_simp
    have h6 : (1 + γ) * (s / H) ≤ 2 * Real.sqrt (A p) :=
      calc (1 + γ) * (s / H) ≤ 2 * (s / H) := mul_le_mul_of_nonneg_right (by linarith) ht.le
        _ ≤ 2 * Real.sqrt (A p) := by linarith
    linarith
  have hinv : s * (1 - γ) ≤ s / (1 + γ) := by
    rw [le_div_iff₀ (by linarith)]
    have e : s * (1 - γ) * (1 + γ) = s - s * γ ^ 2 := by ring
    have := mul_nonneg hs.le (sq_nonneg γ)
    linarith
  have e : 2 * s * (1 - 2 * γ - 2 * γ ^ 2) = s * (1 - γ) + (1 + γ) * (1 - 4 * γ) * s := by ring
  linarith

end Saddle

/-! ### P_F(N) ≤ N^{√2 + o(1)} in characteristic p -/

section Main

variable {p : ℕ}

theorem log_le_sqrt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.log n ≤ δ * Real.sqrt n := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hδ
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually h)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_trans (le_max_left _ _) hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1),
    abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at h1
  exact h1

theorem sqrt_succ_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by
  calc Real.sqrt (x + 1) ≤ Real.sqrt ((Real.sqrt x + 1) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x])
    _ = Real.sqrt x + 1 := Real.sqrt_sq (by positivity)

theorem C_le_of_d_le {K H : ℕ} (hK : ∀ e ≤ H, d p e ≤ K) : C p H ≤ (H + 1) * K := by
  unfold C
  calc ∑ e ∈ range (H + 1), d p e ≤ ∑ _e ∈ range (H + 1), K :=
        Finset.sum_le_sum fun e he => hK e (by rw [mem_range] at he; omega)
    _ = (H + 1) * K := by rw [Finset.sum_const, card_range, smul_eq_mul]

/-- d_p is unbounded. -/
theorem d_unbounded (hp : 2 ≤ p) (N : ℕ) : ∃ h, N ≤ d p h := by
  by_contra hcon
  push Not at hcon
  have hA := A_pos hp
  obtain ⟨H₀, hH₀⟩ := le_C hp (γ := 1 / 8) (by norm_num) le_rfl
  obtain ⟨B', hB'⟩ : ∃ B', B' = 2 * Real.sqrt (A p) + B p +
      ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * A p) + Real.log 2 := ⟨_, rfl⟩
  rw [← hB'] at hH₀
  obtain ⟨r, hr_def⟩ : ∃ r, r = Real.sqrt (A p) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.2 hA
  obtain ⟨n₀, hn₀⟩ := log_le_sqrt (δ := r / 4) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T, T = (B' + r / 4 + Real.log N) / r := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = max H₀ n₀ + ⌈T ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  have h1 := hH₀ H (by omega)
  have hN1 : 1 ≤ N := by have := hcon 0; omega
  have h2 : (C p H : ℝ) ≤ (H + 1) * N := by
    have := C_le_of_d_le (H := H) (K := N) fun e _ => (hcon e).le
    exact_mod_cast this
  have hHp : (0 : ℝ) < H + 1 := by positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have h3 : 2 * Real.sqrt (A p * H) * (1 - 2 * (1 / 8) - 2 * (1 / 8) ^ 2) - B'
      ≤ Real.log (H + 1) + Real.log N := by
    rw [← Real.log_mul hHp.ne' hNp.ne']
    have := Real.log_le_log (Real.exp_pos _) (le_trans h1 h2)
    rwa [Real.log_exp] at this
  have h4 : Real.sqrt (A p * H) = r * Real.sqrt H := by rw [hr_def, Real.sqrt_mul hA.le]
  have h5 : Real.log ((H : ℝ) + 1) ≤ r / 4 * (Real.sqrt H + 1) := by
    have := hn₀ (H + 1) (by omega)
    push_cast at this
    exact le_trans this (mul_le_mul_of_nonneg_left (sqrt_succ_le (Nat.cast_nonneg H)) (by positivity))
  have hTs : T ≤ Real.sqrt H := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have : (⌈T ^ 2⌉₊ : ℝ) ≤ H := by exact_mod_cast (show ⌈T ^ 2⌉₊ ≤ H by omega)
    exact le_trans (Nat.le_ceil _) this
  have hrT : r * T = B' + r / 4 + Real.log N := by rw [hT]; field_simp
  have h6 : r * T ≤ r * Real.sqrt H := mul_le_mul_of_nonneg_left hTs hr.le
  have h7 : 0 < r * Real.sqrt H := mul_pos hr (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < H by omega)))
  rw [h4] at h3
  linarith

/-- **P_F(N) ≤ N^{√2+ε} in characteristic p.** For every prime p and every ε > 0 there is N₀ such
that for every field K of characteristic p and every N ≥ N₀, the crossing [x = v][y = u] on N letters
is a sum of at most N^{√2+ε} terms g(x,y)·g'(u,v) or g(x,u)·g'(y,v) with values in K. -/
theorem plef_rpow (p : ℕ) [hpf : Fact p.Prime] {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (K : Type) [Field K] [CharP K p] (N : ℕ), N₀ ≤ N →
      ∃ M : ℕ, PLEF K (Fin N) M ∧ (M : ℝ) ≤ (N : ℝ) ^ (Real.sqrt 2 + ε) := by
  have hp : 2 ≤ p := hpf.out.two_le
  have hp0 : 0 < p := by omega
  have hA := A_pos hp
  have hB := B_nonneg hp0
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt 2 := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := hq ▸ Real.sqrt_nonneg 2
  obtain ⟨r, hr_def⟩ : ∃ r, r = Real.sqrt (A p) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.2 hA
  have hqe : 0 < q + ε := by linarith
  obtain ⟨γ, hγ_def⟩ : ∃ γ, γ = min (1 / 8 : ℝ) (ε / (6 * (q + ε))) := ⟨_, rfl⟩
  have hγ : 0 < γ := hγ_def ▸ lt_min (by norm_num) (by positivity)
  have hγ1 : γ ≤ 1 / 8 := hγ_def ▸ min_le_left _ _
  have hγ2 : γ ≤ ε / (6 * (q + ε)) := hγ_def ▸ min_le_right _ _
  obtain ⟨κ, hκ_def⟩ : ∃ κ, κ = 1 - 2 * γ - 2 * γ ^ 2 := ⟨_, rfl⟩
  have hκ : q + ε / 2 ≤ (q + ε) * κ := by
    have h1 : (q + ε) * γ ≤ ε / 6 := by
      have := mul_le_mul_of_nonneg_left hγ2 hqe.le
      rwa [show (q + ε) * (ε / (6 * (q + ε))) = ε / 6 by field_simp] at this
    have h2 : γ ^ 2 ≤ γ / 8 := by nlinarith
    have h3 : (q + ε) * γ ^ 2 ≤ (q + ε) * (γ / 8) := mul_le_mul_of_nonneg_left h2 hqe.le
    rw [hκ_def]
    nlinarith
  obtain ⟨H₀, hH₀⟩ := le_C hp hγ hγ1
  obtain ⟨B', hB'⟩ : ∃ B', B' = 2 * Real.sqrt (A p) + B p +
      ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * A p) + Real.log 2 := ⟨_, rfl⟩
  rw [← hB', ← hκ_def] at hH₀
  have hB'0 : 0 ≤ B' := by
    have h1 : 0 ≤ ((p : ℝ) - 1) * ((p : ℝ) - 1) / (p * A p) :=
      div_nonneg (mul_self_nonneg _) (mul_pos (by positivity) hA).le
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h3 := Real.sqrt_nonneg (A p)
    linarith
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = ε * r / (2 * (2 + q + ε)) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ by positivity
  have hδD : (2 + q + ε) * δ = ε * r / 2 := by rw [hδ_def]; field_simp
  obtain ⟨n₀, hn₀⟩ := log_le_sqrt hδ
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = Real.log 15 + 2 * (q * r) + B p + (q + ε) * B' + (2 + q + ε) * δ :=
    ⟨_, rfl⟩
  obtain ⟨h₁, hdef₁⟩ : ∃ h₁ : ℕ, h₁ = max (max 3 (H₀ + 1)) (max n₀ (⌈(2 * K₀ / (ε * r)) ^ 2⌉₊ + 1)) :=
    ⟨_, rfl⟩
  refine ⟨C p h₁ + 1, fun K _ _ N hN => ?_⟩
  classical
  have hex := d_unbounded hp N
  obtain ⟨h, hh⟩ : ∃ h, h = Nat.find hex := ⟨_, rfl⟩
  have hNh : N ≤ d p h := hh ▸ Nat.find_spec hex
  have hlt : ∀ e < h, d p e < N := fun e he => not_le.1 (Nat.find_min hex (hh ▸ he))
  have hh₁ : h₁ < h := by
    by_contra hle
    push Not at hle
    have : d p h ≤ C p h₁ :=
      Finset.single_le_sum (f := d p) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
    omega
  obtain ⟨M, hM, hMle⟩ := plef_le K hNh
  refine ⟨M, hM, ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have h3 : 3 ≤ h := by omega
  have hhR : (3 : ℝ) ≤ h := by exact_mod_cast h3
  -- C(h − 1) < h·N, since d_p(e) < N below h
  have hCh : (C p (h - 1) : ℝ) < h * N := by
    have h1 : C p (h - 1) ≤ (h - 1 + 1) * (N - 1) :=
      C_le_of_d_le fun e he => by have := hlt e (by omega); omega
    have h2 : (h - 1 + 1) * (N - 1) < h * N := by
      rw [Nat.sub_add_cancel (by omega)]
      exact Nat.mul_lt_mul_of_le_of_lt le_rfl (by omega) (by omega)
    exact_mod_cast lt_of_le_of_lt h1 h2
  obtain ⟨u, hu⟩ : ∃ u, u = Real.sqrt ((h - 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = Real.sqrt (h : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := hu ▸ Real.sqrt_nonneg _
  -- log N from below, by the lower growth at H = h − 1
  have hlow := hH₀ (h - 1) (by omega)
  have hsq1 : Real.sqrt (A p * ((h - 1 : ℕ) : ℝ)) = r * u := by rw [hr_def, hu, Real.sqrt_mul hA.le]
  rw [hsq1] at hlow
  have hlogN : 2 * (r * u) * κ - B' - Real.log h ≤ Real.log N := by
    have h1 : Real.exp (2 * (r * u) * κ - B') < h * N := lt_of_le_of_lt hlow hCh
    have h2 := Real.log_lt_log (Real.exp_pos _) h1
    rw [Real.log_exp, Real.log_mul (by positivity) hNp.ne'] at h2
    linarith
  -- M from above, by the upper growth at H = 2h
  have hup := C_le hp (H := 2 * h) (by omega)
  have hsq2 : Real.sqrt (A p * ((2 * h : ℕ) : ℝ)) = q * r * v := by
    push_cast
    rw [Real.sqrt_mul hA.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hq, hr_def, hv]
    ring
  rw [hsq2] at hup
  have hMR : (M : ℝ) ≤ 15 * (h : ℝ) ^ 2 * Real.exp (2 * (q * r * v) + B p) := by
    have h1 : (M : ℝ) ≤ (4 * h + 1) * ((2 * h + 1) * C p (2 * h)) := by exact_mod_cast hMle
    have h7 : 0 ≤ (7 * (h : ℝ) + 1) * ((h : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : ((4 * h + 1) * (2 * h + 1) : ℝ) ≤ 15 * (h : ℝ) ^ 2 := by linarith
    have hC0 : (0 : ℝ) ≤ C p (2 * h) := Nat.cast_nonneg _
    calc (M : ℝ) ≤ (4 * h + 1) * ((2 * h + 1) * C p (2 * h)) := h1
      _ = ((4 * h + 1) * (2 * h + 1)) * C p (2 * h) := by ring
      _ ≤ 15 * (h : ℝ) ^ 2 * Real.exp (2 * (q * r * v) + B p) :=
          mul_le_mul h2 hup hC0 (by positivity)
  have hvu : v ≤ u + 1 := by
    have e : (h : ℝ) = ((h - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ h)]
      ring
    rw [hv, hu, e]
    exact sqrt_succ_le (Nat.cast_nonneg _)
  have hlogh : Real.log h ≤ δ * (u + 1) := by
    have := hn₀ h (by omega)
    rw [← hv] at this
    exact le_trans this (mul_le_mul_of_nonneg_left hvu hδ.le)
  have hthr : K₀ ≤ ε * r / 2 * u := by
    have h1 : 2 * K₀ / (ε * r) ≤ u := by
      rw [hu]
      refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
      have : ((⌈(2 * K₀ / (ε * r)) ^ 2⌉₊ : ℕ) : ℝ) ≤ ((h - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show ⌈(2 * K₀ / (ε * r)) ^ 2⌉₊ ≤ h - 1 by omega)
      exact le_trans (Nat.le_ceil _) this
    have h2 : 0 < ε * r := by positivity
    rw [div_le_iff₀ h2] at h1
    linarith
  have hfinal : Real.log 15 + 2 * Real.log h + 2 * (q * r * v) + B p ≤ Real.log N * (q + ε) := by
    have e1 := mul_le_mul_of_nonneg_left hlogN hqe.le
    have e2 : (q + ε / 2) * (2 * (r * u)) ≤ ((q + ε) * κ) * (2 * (r * u)) :=
      mul_le_mul_of_nonneg_right hκ (by positivity)
    have e3 : q * r * v ≤ q * r * (u + 1) := mul_le_mul_of_nonneg_left hvu (by positivity)
    have e4 : (2 + q + ε) * Real.log h ≤ (2 + q + ε) * (δ * (u + 1)) :=
      mul_le_mul_of_nonneg_left hlogh (by positivity)
    have e5 : (2 + q + ε) * (δ * (u + 1)) = ε * r / 2 * u + (2 + q + ε) * δ := by
      rw [← hδD]
      ring
    rw [hK₀] at hthr
    linarith
  rw [Real.rpow_def_of_pos hNp]
  calc (M : ℝ) ≤ 15 * (h : ℝ) ^ 2 * Real.exp (2 * (q * r * v) + B p) := hMR
    _ = Real.exp (Real.log 15 + 2 * Real.log h + 2 * (q * r * v) + B p) := by
        rw [show Real.log 15 + 2 * Real.log h + 2 * (q * r * v) + B p
            = Real.log (15 * (h : ℝ) ^ 2) + (2 * (q * r * v) + B p) by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
              push_cast
              ring,
          Real.exp_add (Real.log (15 * (h : ℝ) ^ 2)), Real.exp_log (by positivity)]
    _ ≤ Real.exp (Real.log N * (q + ε)) := Real.exp_le_exp.2 hfinal

end Main

/-! ### Hurwitz's problem in odd characteristic -/

section Hurwitz

/-- Each term of a crossing decomposition with values in K becomes one product of two bilinear forms
in (Σ X_i²)(Σ Y_j²), as in `TheoremB.prodLE_of_PLE`. -/
theorem prodLE_of_PLEF {K : Type} [CommRing K] {N M : ℕ} (h : PLEF K (Fin N) M) : ProdLE K N M := by
  obtain ⟨g, g', col, hg⟩ := h
  refine ⟨fun t i j => g t i j, fun t i j => g' t j i, fun X Y => ?_⟩
  have h1 : ∑ x, ∑ y, ∑ u, ∑ v, (if x = v ∧ y = u then (1 : K) else 0) * (X x * Y y * X v * Y u) =
      (∑ i, X i ^ 2) * (∑ j, Y j ^ 2) := by
    simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [← h1]
  simp_rw [hg]
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hct : col t = true
  · simp only [hct, ↓reduceIte]
    calc ∑ x, ∑ y, ∑ u, ∑ v, g t x u * g' t y v * (X x * Y y * X v * Y u)
        = ∑ x, ∑ u, ∑ y, ∑ v, (g t x u * X x * Y u) * (g' t y v * X v * Y y) :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun v _ => by ring
      _ = (∑ x, ∑ u, g t x u * X x * Y u) * ∑ y, ∑ v, g' t y v * X v * Y y := sum4_mul _ _
      _ = _ := by
          simp only [bil]
          congr 1
          exact Finset.sum_comm
  · simp only [hct, Bool.false_eq_true, ↓reduceIte]
    calc ∑ x, ∑ y, ∑ u, ∑ v, g t x y * g' t u v * (X x * Y y * X v * Y u)
        = ∑ x, ∑ y, ∑ u, ∑ v, (g t x y * X x * Y y) * (g' t u v * X v * Y u) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      _ = (∑ x, ∑ y, g t x y * X x * Y y) * ∑ u, ∑ v, g' t u v * X v * Y u := sum4_mul _ _
      _ = _ := by
          simp only [bil]
          congr 1
          exact Finset.sum_comm

/-- If 2 is invertible and −1 = a² + b², each product of two forms is three squares:
f·f' = (c(f + f'))² + (ac(f − f'))² + (bc(f − f'))² with c = 1/2. -/
theorem sosLE_of_prodLE_three {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    (hab : a ^ 2 + b ^ 2 = -1) {N M : ℕ} (h : ProdLE K N M) : SOSLE K N (M + M + M) := by
  obtain ⟨f, f', hf⟩ := h
  obtain ⟨c, hc⟩ : ∃ c : K, 2 * c = 1 := ⟨(2 : K)⁻¹, mul_inv_cancel₀ h2⟩
  refine ⟨Fin.append (Fin.append (fun t i j => c * f t i j + c * f' t i j)
    (fun t i j => (a * c) * f t i j + (-(a * c)) * f' t i j))
    (fun t i j => (b * c) * f t i j + (-(b * c)) * f' t i j), fun X Y => ?_⟩
  rw [Fin.sum_univ_add, Fin.sum_univ_add, hf X Y, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.append_left, Fin.append_right, bil_comb]
  linear_combination (-(c ^ 2 * (bil (f t) X Y - bil (f' t) X Y) ^ 2)) * hab
    + (-(bil (f t) X Y * bil (f' t) X Y * (2 * c + 1))) * hc

/-- **Hurwitz's problem in odd characteristic is at most n^{√2 + o(1)}.** For every odd prime p and
every ε > 0 there is N₀ such that over every field K of characteristic p and for every N ≥ N₀,
(X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of at most N^{√2+ε} squares of bilinear forms over K.
Hrubeš (CCC 2024) has O(N^{1.62}) over every field of positive characteristic. -/
theorem hurwitz_le_rpow (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (K : Type) [Field K] [CharP K p] (N : ℕ), N₀ ≤ N →
      ∃ M : ℕ, SOSLE K N M ∧ (M : ℝ) ≤ (N : ℝ) ^ (Real.sqrt 2 + ε) := by
  obtain ⟨N₁, hN₁⟩ := plef_rpow p (half_pos hε)
  obtain ⟨a₀, b₀, hab₀⟩ := ZMod.sq_add_sq p (-1)
  refine ⟨max N₁ ⌈(3 : ℝ) ^ (2 / ε)⌉₊, fun K _ _ N hN => ?_⟩
  obtain ⟨M, hP, hM⟩ := hN₁ K N (le_of_max_le_left hN)
  have h2 : (2 : K) ≠ 0 := by
    have : ((2 : ℕ) : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K p]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).1 hd)
    exact_mod_cast this
  have hab : (ZMod.castHom (dvd_refl p) K a₀) ^ 2 + (ZMod.castHom (dvd_refl p) K b₀) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, ← map_add, hab₀, map_neg, map_one]
  refine ⟨M + M + M, sosLE_of_prodLE_three h2 hab (prodLE_of_PLEF hP), ?_⟩
  have hN3 : (3 : ℝ) ^ (2 / ε) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN3
  have h3 : (3 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by norm_num), show 2 / ε * (ε / 2) = (1 : ℝ) by field_simp,
            Real.rpow_one]
      _ ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hN3 (by positivity)
  calc ((M + M + M : ℕ) : ℝ) = 3 * M := by push_cast; ring
    _ ≤ 3 * (N : ℝ) ^ (Real.sqrt 2 + ε / 2) := by linarith
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (Real.sqrt 2 + ε / 2) := by gcongr
    _ = (N : ℝ) ^ (Real.sqrt 2 + ε) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring

end Hurwitz

end TheoremB.CharP
