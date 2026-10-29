import Mathlib
import IDMM.Statements

/-!
# Covering estimate (§4): the block layout bound

`layout_bound_mu`: for every `1/2 < μ < 1`, every `δ > 0` and all large `n`, every corner class
`(a, b)` admits a block layout `(u_s, u_a)` with `u_s + u_a = 2 * mOfMu μ n` and
`C(n,a) C(n,b) ≤ 2^(n (gHalfMu μ + δ)) · C(u_s, a₀) C(u_a, b₀)`.
`layout_bound` is the case `μ = muQ = 200/293` (`mOf`, `gHalf`).

Proof outline (`a₀ = min a (n-a)`, `b₀ = min b (n-b)`, `M = 2 * mOfMu μ n`, `L = M - n`).
* Take `u` maximizing `T u = C(u, a₀) C(M - u, b₀)` over `0 ≤ u ≤ M`. The upper Vandermonde
  identity `∑_u T u = C(M+1, a₀+b₀+1)` gives `C(M, a₀+b₀) ≤ (M+1) T u`.
* If `L ≤ u ≤ n`, use `(u, M - u)`: Vandermonde `C(n,a₀)C(n,b₀) ≤ C(2n, k)`, monotonicity of
  `C(2n,k)/C(M,k)` up to `k = n/2`, and the entropy bounds
  `C(N,K) K^K (N-K)^(N-K) ≤ N^N ≤ (N+1) C(N,K) K^K (N-K)^(N-K)` reduce everything to
  `φ(2n) - φ(2n-h) - φ(M) + φ(M-h)` with `φ x = x log x`, which convexity of `φ` bounds by its
  value at `h = n/2`, `M = 2μn`, namely `n · gHalfMu μ · log 2`.
* If `u < L` (resp. `u > n`), maximality forces `a₀ (n+1) ≤ b₀ L` (resp. the mirror), and the
  capped layout `(L, n)` (resp. `(n, L)`) works: the same convexity argument reduces it to
  midpoint concavity of the entropy (the two layouts coincide on the boundary).
* The polynomial factor `(M+1)^2` is absorbed into `2^(nδ)` for `n ≥ n₀`.
-/

namespace IDMM

noncomputable def muQ : ℝ := 200 / 293

/-- Block size: number of qubits in a matrix block. -/
noncomputable def mOf (n : ℕ) : ℕ := ⌈muQ * n⌉₊

/-- The analytic covering exponent g(1/2) = 2H(1/4) − 2μ·H(1/(4μ)) at μ = 200/293
(so 1/(4μ) = 293/800). -/
noncomputable def gHalf : ℝ := 2 * binaryEntropy (1 / 4) - 2 * muQ * binaryEntropy (293 / 800)

/-- Block size for a general block fraction `μ`. -/
noncomputable def mOfMu (μ : ℝ) (n : ℕ) : ℕ := ⌈μ * n⌉₊

/-- The covering exponent g(1/2) = 2H(1/4) − 2μ·H(1/(4μ)) for a general `μ`. -/
noncomputable def gHalfMu (μ : ℝ) : ℝ :=
  2 * binaryEntropy (1 / 4) - 2 * μ * binaryEntropy (1 / (4 * μ))

namespace Layout

open Finset

/-! ### Binomial coefficient facts -/

theorem choose_mul_choose_le (n a b : ℕ) : n.choose a * n.choose b ≤ (2 * n).choose (a + b) := by
  rw [two_mul, Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => n.choose ij.1 * n.choose ij.2)
    (fun _ _ => Nat.zero_le _) (show ((a, b) : ℕ × ℕ) ∈ antidiagonal (a + b) by simp)

/-- Upper Vandermonde identity. -/
theorem sum_antidiagonal_choose (a : ℕ) : ∀ M b : ℕ,
    ∑ p ∈ antidiagonal M, p.1.choose a * p.2.choose b = (M + 1).choose (a + b + 1) := by
  intro M
  induction M with
  | zero =>
    intro b
    rcases a with _ | a <;> rcases b with _ | b <;> simp <;>
      exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ M ih =>
    intro b
    rw [Finset.Nat.sum_antidiagonal_succ']
    rcases b with _ | b
    · simp only [Nat.choose_zero_right, mul_one] at ih ⊢
      have := ih 0
      simp only [Nat.choose_zero_right, mul_one, add_zero] at this
      rw [this, Nat.choose_succ_succ (M + 1) a]
    · rw [Nat.choose_zero_succ, mul_zero, zero_add]
      have hpt : ∀ p ∈ antidiagonal M, p.1.choose a * (p.2 + 1).choose (b + 1)
          = p.1.choose a * p.2.choose b + p.1.choose a * p.2.choose (b + 1) := by
        intro p _; rw [Nat.choose_succ_succ, mul_add]
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ih b, ih (b + 1),
        show a + (b + 1) + 1 = (a + b + 1) + 1 by ring, Nat.choose_succ_succ (M + 1) (a + b + 1)]

theorem choose_ratio_mono {N M k : ℕ} (hMN : M ≤ N) :
    ∀ h, k ≤ h → h ≤ M → N.choose k * M.choose h ≤ N.choose h * M.choose k := by
  intro h hkh
  induction h, hkh using Nat.le_induction with
  | base => intro _; rw [mul_comm]
  | succ h hkh ih =>
    intro hhM
    have ih' := ih (by omega)
    apply Nat.le_of_mul_le_mul_right (c := h + 1) _ (Nat.succ_pos h)
    calc N.choose k * M.choose (h + 1) * (h + 1)
        = N.choose k * M.choose h * (M - h) := by
          rw [mul_assoc, Nat.choose_succ_right_eq]; ring
      _ ≤ N.choose h * M.choose k * (M - h) := Nat.mul_le_mul_right _ ih'
      _ ≤ N.choose h * M.choose k * (N - h) := Nat.mul_le_mul_left _ (by omega)
      _ = N.choose (h + 1) * M.choose k * (h + 1) := by
          rw [mul_right_comm (N.choose (h + 1)), Nat.choose_succ_right_eq]; ring

theorem choose_entropy_upper (N K : ℕ) : N.choose K * (K ^ K * (N - K) ^ (N - K)) ≤ N ^ N := by
  rcases le_or_gt K N with hK | hK
  · have hsum := add_pow K (N - K) N
    rw [Nat.add_sub_cancel' hK] at hsum
    rw [hsum]
    have := Finset.single_le_sum (f := fun m => K ^ m * (N - K) ^ (N - m) * N.choose m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · simp [Nat.choose_eq_zero_of_lt hK]

/-- The binomial term `t j = K^j (N-K)^(N-j) C(N,j)` is maximized at `j = K`. -/
theorem binom_term_le {N K : ℕ} (hK : K ≤ N) (j : ℕ) (hj : j ≤ N) :
    K ^ j * (N - K) ^ (N - j) * N.choose j ≤ K ^ K * (N - K) ^ (N - K) * N.choose K := by
  set t : ℕ → ℕ := fun j => K ^ j * (N - K) ^ (N - j) * N.choose j with ht
  -- ratio identity: t (j+1) * ((j+1) * (N-K)) = t j * ((N-j) * K)
  have hrat : ∀ j, j < N → t (j + 1) * ((j + 1) * (N - K)) = t j * ((N - j) * K) := by
    intro j hjN
    simp only [ht]
    have e1 : N - j = (N - (j + 1)) + 1 := by omega
    rw [e1, pow_succ, pow_succ]
    have := Nat.choose_succ_right_eq N j
    rw [← e1] at *
    calc K ^ j * K * (N - K) ^ (N - (j + 1)) * N.choose (j + 1) * ((j + 1) * (N - K))
        = K ^ j * K * (N - K) ^ (N - (j + 1)) * (N - K) * (N.choose (j + 1) * (j + 1)) := by ring
      _ = K ^ j * K * (N - K) ^ (N - (j + 1)) * (N - K) * (N.choose j * (N - j)) := by rw [this]
      _ = _ := by ring
  show t j ≤ t K
  rcases le_or_gt K j with hKj | hjK
  · -- decreasing on [K, N]
    induction j, hKj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hKj ih =>
      have hjN : j < N := by omega
      have hpos : 0 < (j + 1) * (N - K) := Nat.mul_pos (Nat.succ_pos j) (by omega)
      have hstep : t (j + 1) ≤ t j := by
        apply Nat.le_of_mul_le_mul_right (c := (j + 1) * (N - K)) _ hpos
        rw [hrat j hjN]
        exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul (show N - j ≤ N - K by omega)
          (show K ≤ j + 1 by omega)).trans (le_of_eq (mul_comm _ _)))
      exact hstep.trans (ih (by omega))
  · -- increasing on [0, K]
    rcases eq_or_lt_of_le hK with hKN | hKN
    · -- K = N: every term with j < N vanishes
      have : t j = 0 := by
        simp only [ht]
        rw [hKN, Nat.sub_self, zero_pow (by omega)]
        simp
      rw [this]; exact Nat.zero_le _
    · have key : ∀ d, d ≤ K → t (K - d) ≤ t K := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d ih =>
          intro hd
          have hjN : K - (d + 1) < N := by omega
          have e : K - (d + 1) + 1 = K - d := by omega
          have hpos : 0 < (K - (d + 1) + 1) * (N - K) := Nat.mul_pos (Nat.succ_pos _) (by omega)
          have hstep : t (K - (d + 1)) ≤ t (K - d) := by
            apply Nat.le_of_mul_le_mul_right (c := (K - (d + 1) + 1) * (N - K)) _ hpos
            have h1 := hrat (K - (d + 1)) hjN
            rw [e] at h1
            rw [e, h1]
            exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul (show K - d ≤ K by omega)
              (show N - K ≤ N - (K - (d + 1)) by omega)).trans (le_of_eq (mul_comm _ _)))
          exact hstep.trans (ih (by omega))
      have := key (K - j) (by omega)
      rwa [Nat.sub_sub_self (by omega)] at this

theorem choose_entropy_lower {N K : ℕ} (hK : K ≤ N) :
    N ^ N ≤ (N + 1) * (N.choose K * (K ^ K * (N - K) ^ (N - K))) := by
  have hsum := add_pow K (N - K) N
  rw [Nat.add_sub_cancel' hK] at hsum
  rw [hsum]
  have := Finset.sum_le_card_nsmul (range (N + 1))
    (fun m => K ^ m * (N - K) ^ (N - m) * N.choose m) (K ^ K * (N - K) ^ (N - K) * N.choose K)
    (fun j hj => binom_term_le hK j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  simp only [card_range, smul_eq_mul] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- One step of the hypergeometric ratio: if moving one slot from the second block to the first
does not increase `C(u,a) C(v,b)`, then `a (v+1) ≤ b (u+1)`. -/
theorem step_ratio {a b u v : ℕ} (hpos : 0 < u.choose a * (v + 1).choose b)
    (hle : (u + 1).choose a * v.choose b ≤ u.choose a * (v + 1).choose b) :
    a * (v + 1) ≤ b * (u + 1) := by
  have hau : a ≤ u := by
    by_contra h
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hpos
    simp at hpos
  have hbv : b ≤ v + 1 := by
    by_contra h
    rw [Nat.choose_eq_zero_of_lt (k := b) (by omega)] at hpos
    simp at hpos
  have e1 := Nat.choose_mul_succ_eq u a
  have e2 := Nat.choose_mul_succ_eq v b
  -- T0 (u+1) (v+1-b) = T1 (u+1-a) (v+1)
  have hid : u.choose a * (v + 1).choose b * ((u + 1) * (v + 1 - b))
      = (u + 1).choose a * v.choose b * ((u + 1 - a) * (v + 1)) := by
    calc u.choose a * (v + 1).choose b * ((u + 1) * (v + 1 - b))
        = (u.choose a * (u + 1)) * ((v + 1).choose b * (v + 1 - b)) := by ring
      _ = ((u + 1).choose a * (u + 1 - a)) * (v.choose b * (v + 1)) := by rw [e1, e2]
      _ = _ := by ring
  have key : (u + 1) * (v + 1 - b) ≤ (u + 1 - a) * (v + 1) := by
    apply Nat.le_of_mul_le_mul_left _ hpos
    rw [hid]
    exact Nat.mul_le_mul_right _ hle
  zify [hau, hbv, (by omega : a ≤ u + 1)] at key ⊢
  nlinarith

/-! ### Convexity of `φ x = x log x` -/

/-- `φ x = x log x`. -/
noncomputable def phi (x : ℝ) : ℝ := x * Real.log x

/-- Binary entropy in nats. -/
noncomputable def Hn (t : ℝ) : ℝ := -(t * Real.log t + (1 - t) * Real.log (1 - t))

/-- Increasing differences of the convex function `φ` on `[0, ∞)`. -/
theorem phi_add_le {x y x' y' : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hxx' : x ≤ x')
    (hd : x' - x = y' - y) : phi x' + phi y ≤ phi x + phi y' := by
  have hy'eq : y' = y + (x' - x) := by linarith
  subst hy'eq
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · ring_nf; exact le_rfl
  rcases eq_or_lt_of_le hxx' with rfl | hxx''
  · ring_nf; exact le_rfl
  have hspos : 0 < y + (x' - x) - x := by linarith
  set t := (x' - x) / (y + (x' - x) - x) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hspos.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hspos]; linarith
  have hmx : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hx
  have hmy : y + (x' - x) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have h1 := Real.convexOn_mul_log.2 hmx hmy (sub_nonneg.mpr ht1) ht0 (by ring)
  have h2 := Real.convexOn_mul_log.2 hmx hmy ht0 (sub_nonneg.mpr ht1) (by ring)
  have e1 : (1 - t) • x + t • (y + (x' - x)) = x' := by
    simp only [smul_eq_mul, ht]; field_simp; ring
  have e2 : t • x + (1 - t) • (y + (x' - x)) = y := by
    simp only [smul_eq_mul, ht]; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  unfold phi
  linarith

theorem Hn_mid {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : Hn s + Hn (1 / 2 - s) ≤ 2 * Hn (1 / 4) := by
  have m1 : s ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr h0
  have m2 : (1 / 2 - s) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have m3 : (1 - s) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have m4 : (1 - (1 / 2 - s)) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hs : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have c1 := Real.convexOn_mul_log.2 m1 m2 hh hh hs
  have c2 := Real.convexOn_mul_log.2 m3 m4 hh hh hs
  simp only [smul_eq_mul] at c1 c2
  rw [show (1 / 2 : ℝ) * s + 1 / 2 * (1 / 2 - s) = 1 / 4 by ring] at c1
  rw [show (1 / 2 : ℝ) * (1 - s) + 1 / 2 * (1 - (1 / 2 - s)) = 3 / 4 by ring] at c2
  unfold Hn
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
  linarith

/-- `φ N - φ (N - h) = N · H(h/N) + φ h`. -/
theorem phi_sub_eq (N h : ℝ) (hN : N ≠ 0) : phi N - phi (N - h) = N * Hn (h / N) + phi h := by
  have key : ∀ z : ℝ, N * (z / N * Real.log (z / N)) = z * Real.log z - z * Real.log N := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    rw [Real.log_div hz hN]; field_simp
  have e : 1 - h / N = (N - h) / N := by field_simp
  unfold Hn phi
  rw [e]
  linear_combination key h + key (N - h)

theorem gHalfMu_mul_log (μ : ℝ) :
    gHalfMu μ * Real.log 2 = 2 * Hn (1 / 4) - 2 * μ * Hn (1 / (4 * μ)) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold gHalfMu binaryEntropy Hn
  field_simp

/-- `n · g(1/2) · log 2` as a difference of `φ`-increments. -/
theorem gHalfMu_phi {μ : ℝ} (hμ : μ ≠ 0) (n : ℝ) (hn : n ≠ 0) :
    n * gHalfMu μ * Real.log 2 = (phi (2 * n) - phi (2 * n - n / 2))
      - (phi (2 * μ * n) - phi (2 * μ * n - n / 2)) := by
  rw [phi_sub_eq _ _ (mul_ne_zero two_ne_zero hn),
    phi_sub_eq _ _ (mul_ne_zero (mul_ne_zero two_ne_zero hμ) hn),
    show n / 2 / (2 * n) = 1 / 4 by field_simp; ring,
    show n / 2 / (2 * μ * n) = 1 / (4 * μ) by field_simp; ring,
    mul_assoc, gHalfMu_mul_log]
  ring

theorem two_mu_ge {μ : ℝ} (hμ : 1 / 2 < μ) : (1 : ℝ) ≤ 2 * μ := by linarith

theorem expoA {μ : ℝ} (hμ0 : 1 / 2 < μ) {n h M : ℝ} (hn : 0 < n) (hh : h ≤ n / 2)
    (hM1 : 2 * μ * n ≤ M) (hM2 : M ≤ 2 * n) :
    (phi (2 * n) - phi h - phi (2 * n - h)) - (phi M - phi h - phi (M - h))
      ≤ n * gHalfMu μ * Real.log 2 := by
  have hμ := two_mu_ge hμ0
  have hμn : n ≤ 2 * μ * n := by nlinarith
  have s1 := phi_add_le (x := M - n / 2) (y := M - h) (x' := 2 * n - n / 2) (y' := 2 * n - h)
    (by linarith) (by linarith) (by linarith) (by ring)
  have s2 := phi_add_le (x := 2 * μ * n - n / 2) (y := M - n / 2) (x' := 2 * μ * n) (y' := M)
    (by linarith) (by linarith) (by linarith) (by ring)
  rw [gHalfMu_phi (show (0 : ℝ) < μ by linarith).ne' n hn.ne']
  linarith

theorem expoB {μ : ℝ} (hμ0 : 1 / 2 < μ) {n L M a : ℝ} (hn : 0 < n) (hL : 0 < L) (hM : M = n + L)
    (hM1 : 2 * μ * n ≤ M) (hM2 : M ≤ 2 * n) (ha : a ≤ n * L / (2 * M)) :
    (phi n - phi a - phi (n - a)) - (phi L - phi a - phi (L - a))
      ≤ n * gHalfMu μ * Real.log 2 := by
  have hμ := two_mu_ge hμ0
  have hμne : μ ≠ 0 := (show (0 : ℝ) < μ by linarith).ne'
  have hμn : n ≤ 2 * μ * n := by nlinarith
  have hMpos : 0 < M := by linarith
  set x := n * L / (2 * M) with hx
  have hxL : x ≤ L := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  have hLn : L ≤ n := by linarith
  have s1 := phi_add_le (x := L - x) (y := L - a) (x' := n - x) (y' := n - a)
    (by linarith) (by linarith) (by linarith) (by ring)
  have q1 := phi_sub_eq n x hn.ne'
  have q2 := phi_sub_eq L x hL.ne'
  have ex1 : x / n = L / (2 * M) := by rw [hx]; field_simp
  have ex2 : x / L = n / (2 * M) := by rw [hx]; field_simp
  rw [ex1] at q1
  rw [ex2] at q2
  have hmid := Hn_mid (s := L / (2 * M)) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  rw [show 1 / 2 - L / (2 * M) = n / (2 * M) by field_simp; linarith] at hmid
  -- `M · H(n/(2M)) ≥ 2μn · H(1/(4μ))`
  have s2 := phi_add_le (x := 2 * μ * n - n / 2) (y := M - n / 2) (x' := 2 * μ * n) (y' := M)
    (by linarith) (by linarith) (by linarith) (by ring)
  have q3 := phi_sub_eq M (n / 2) hMpos.ne'
  rw [show n / 2 / M = n / (2 * M) by field_simp] at q3
  have hg := gHalfMu_phi hμne n hn.ne'
  have hnm := mul_le_mul_of_nonneg_left hmid hn.le
  have hsplit : n * Hn (L / (2 * M)) - L * Hn (n / (2 * M))
      = n * (Hn (L / (2 * M)) + Hn (n / (2 * M))) - M * Hn (n / (2 * M)) := by
    rw [hM]; ring
  have hq4 := phi_sub_eq (2 * μ * n) (n / 2) (mul_ne_zero (mul_ne_zero two_ne_zero hμne) hn.ne')
  rw [show n / 2 / (2 * μ * n) = 1 / (4 * μ) by field_simp; ring] at hq4
  have hgl := gHalfMu_mul_log μ
  nlinarith

/-! ### Binomial coefficients versus `exp ∘ φ` -/

theorem natpow_eq_exp (N : ℕ) : ((N : ℝ)) ^ N = Real.exp (phi N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [phi]
  · rw [phi, ← Real.log_pow, Real.exp_log (pow_pos (Nat.cast_pos.mpr hN) N)]

theorem choose_le_exp {N K : ℕ} (hK : K ≤ N) :
    (N.choose K : ℝ) ≤ Real.exp (phi N - phi K - phi ((N : ℝ) - K)) := by
  have h' : ((N.choose K : ℕ) : ℝ) * (((K : ℝ)) ^ K * (((N - K : ℕ) : ℝ)) ^ (N - K))
      ≤ ((N : ℝ)) ^ N := by exact_mod_cast choose_entropy_upper N K
  rw [natpow_eq_exp N, natpow_eq_exp K, natpow_eq_exp (N - K), Nat.cast_sub hK] at h'
  rw [Real.exp_sub, Real.exp_sub, div_div, le_div_iff₀ (by positivity)]
  exact h'

theorem exp_le_choose {N K : ℕ} (hK : K ≤ N) :
    Real.exp (phi N - phi K - phi ((N : ℝ) - K)) ≤ ((N : ℝ) + 1) * N.choose K := by
  have h' : ((N : ℝ)) ^ N ≤ ((N : ℝ) + 1) * (((N.choose K : ℕ) : ℝ) *
      (((K : ℝ)) ^ K * (((N - K : ℕ) : ℝ)) ^ (N - K))) := by
    exact_mod_cast choose_entropy_lower hK
  rw [natpow_eq_exp N, natpow_eq_exp K, natpow_eq_exp (N - K), Nat.cast_sub hK] at h'
  rw [Real.exp_sub, Real.exp_sub, div_div, div_le_iff₀ (by positivity)]
  calc _ ≤ _ := h'
    _ = _ := by ring

/-! ### The two layouts -/

theorem n_le_twoMu {μ : ℝ} (hμ : 1 / 2 < μ) (n : ℕ) : (n : ℝ) ≤ 2 * μ * n := by
  have := two_mu_ge hμ; have := Nat.cast_nonneg (α := ℝ) n; nlinarith

/-- Uncapped layout: the block holding the maximizing split `T`. -/
theorem caseA_bound {μ : ℝ} (hμ : 1 / 2 < μ) {n M a b T : ℕ} (hn : 1 ≤ n) (hM1 : 2 * μ * n ≤ M) (hM2 : M ≤ 2 * n)
    (hab : a + b ≤ n / 2) (hT : (M + 1).choose (a + b + 1) ≤ (M + 1) * T) :
    ((n.choose a * n.choose b : ℕ) : ℝ)
      ≤ ((M : ℝ) + 1) ^ 2 * Real.exp (n * gHalfMu μ * Real.log 2) * T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnM : n ≤ M := by exact_mod_cast (n_le_twoMu hμ n).trans hM1
  set h := n / 2 with hh
  have hhM : h ≤ M := (Nat.div_le_self n 2).trans hnM
  have h1 : n.choose a * n.choose b ≤ (2 * n).choose (a + b) := choose_mul_choose_le n a b
  have h2 := choose_ratio_mono (N := 2 * n) (M := M) (k := a + b) hM2 h hab hhM
  have h3 : M.choose (a + b) ≤ (M + 1) * T := by
    refine le_trans ?_ hT
    rw [Nat.choose_succ_succ]
    exact Nat.le_add_right _ _
  have hN : n.choose a * n.choose b * M.choose h ≤ (2 * n).choose h * ((M + 1) * T) :=
    calc n.choose a * n.choose b * M.choose h ≤ (2 * n).choose (a + b) * M.choose h :=
          Nat.mul_le_mul_right _ h1
      _ ≤ (2 * n).choose h * M.choose (a + b) := h2
      _ ≤ (2 * n).choose h * ((M + 1) * T) := Nat.mul_le_mul_left _ h3
  have hR : ((n.choose a * n.choose b : ℕ) : ℝ) * (M.choose h : ℝ)
      ≤ ((2 * n).choose h : ℝ) * (((M : ℝ) + 1) * T) := by exact_mod_cast hN
  have hZ := choose_le_exp (N := 2 * n) (K := h) (by omega)
  have hY := exp_le_choose (N := M) (K := h) hhM
  push_cast at hZ
  set E2 := phi (2 * (n : ℝ)) - phi h - phi (2 * (n : ℝ) - h)
  set EM := phi (M : ℝ) - phi h - phi ((M : ℝ) - h)
  have hE : E2 - EM ≤ n * gHalfMu μ * Real.log 2 :=
    expoA hμ hnR (Nat.cast_div_le.trans (by norm_num)) hM1 (by exact_mod_cast hM2)
  set X : ℝ := ((n.choose a * n.choose b : ℕ) : ℝ)
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have key : X * Real.exp EM ≤ ((M : ℝ) + 1) ^ 2 * Real.exp E2 * T :=
    calc X * Real.exp EM ≤ X * (((M : ℝ) + 1) * M.choose h) := mul_le_mul_of_nonneg_left hY hX0
      _ = ((M : ℝ) + 1) * (X * M.choose h) := by ring
      _ ≤ ((M : ℝ) + 1) * (((2 * n).choose h : ℝ) * (((M : ℝ) + 1) * T)) :=
          mul_le_mul_of_nonneg_left hR hM0
      _ = ((M : ℝ) + 1) ^ 2 * ((2 * n).choose h : ℝ) * T := by ring
      _ ≤ ((M : ℝ) + 1) ^ 2 * Real.exp E2 * T := by gcongr
  have hX : X ≤ ((M : ℝ) + 1) ^ 2 * Real.exp (E2 - EM) * T := by
    rw [Real.exp_sub, show ((M : ℝ) + 1) ^ 2 * (Real.exp E2 / Real.exp EM) * T
      = ((M : ℝ) + 1) ^ 2 * Real.exp E2 * T / Real.exp EM by ring, le_div_iff₀ (Real.exp_pos EM)]
    exact key
  calc X ≤ ((M : ℝ) + 1) ^ 2 * Real.exp (E2 - EM) * T := hX
    _ ≤ ((M : ℝ) + 1) ^ 2 * Real.exp (n * gHalfMu μ * Real.log 2) * T := by gcongr

/-- Capped layout `(L, n)`: the first block is as small as allowed. -/
theorem caseB_bound {μ : ℝ} (hμ : 1 / 2 < μ) {n L a b : ℕ} (hn : 1 ≤ n) (hM1 : 2 * μ * n ≤ ((n + L : ℕ) : ℝ))
    (hM2 : n + L ≤ 2 * n) (hL : 1 ≤ L) (hab : a + b ≤ n / 2) (hstep : a * (n + 1) ≤ b * L) :
    a ≤ L ∧ (n.choose a : ℝ) ≤ ((L : ℝ) + 1) * Real.exp (n * gHalfMu μ * Real.log 2) * L.choose a := by
  have hb : b ≤ n := by omega
  have haL : a ≤ L := by
    have h1 : a * (n + 1) < L * (n + 1) := by
      calc a * (n + 1) ≤ b * L := hstep
        _ ≤ n * L := Nat.mul_le_mul_right _ hb
        _ < (n + 1) * L := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self n) (by omega)
        _ = L * (n + 1) := mul_comm _ _
    exact (Nat.lt_of_mul_lt_mul_right h1).le
  refine ⟨haL, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  push_cast at hM1
  have hab' : ((a : ℝ) + b) ≤ n / 2 := by
    have : ((a + b : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hab
    push_cast at this
    exact this.trans Nat.cast_div_le
  have hst : (a : ℝ) * (n + 1) ≤ b * L := by exact_mod_cast hstep
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hx : (a : ℝ) ≤ n * L / (2 * (n + L)) := by
    rw [le_div_iff₀ (by positivity)]
    have : (b : ℝ) * L ≤ (n / 2 - a) * L := mul_le_mul_of_nonneg_right (by linarith) hLR.le
    nlinarith
  have hE := expoB hμ (M := (n : ℝ) + L) hnR hLR rfl hM1 (by exact_mod_cast hM2) hx
  have hZ := choose_le_exp (N := n) (K := a) (by omega)
  have hY := exp_le_choose (N := L) (K := a) haL
  set En := phi (n : ℝ) - phi a - phi ((n : ℝ) - a)
  set EL := phi (L : ℝ) - phi a - phi ((L : ℝ) - a)
  calc (n.choose a : ℝ) ≤ Real.exp En := hZ
    _ = Real.exp (En - EL) * Real.exp EL := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * gHalfMu μ * Real.log 2) * (((L : ℝ) + 1) * L.choose a) := by gcongr
    _ = _ := by ring

theorem mOfMu_le {μ : ℝ} (hμ1 : μ ≤ 1) (n : ℕ) : mOfMu μ n ≤ n := by
  unfold mOfMu
  rw [Nat.ceil_le]
  have : μ ≤ 1 := hμ1
  have := Nat.cast_nonneg (α := ℝ) n
  nlinarith

theorem choose_min {n a : ℕ} (ha : a ≤ n) : n.choose (min a (n - a)) = n.choose a := by
  rcases le_total a (n - a) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.choose_symm ha]

/-- For `a + b ≤ n/2` there is a layout of the `2 * mOfMu μ n` slots with the stated loss. -/
theorem core {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ ≤ 1) {n a b : ℕ} (hn : 1 ≤ n) (hab : a + b ≤ n / 2) :
    ∃ us ua : ℕ, us + ua = 2 * mOfMu μ n ∧ us ≤ n ∧ ua ≤ n ∧ a ≤ us ∧ b ≤ ua ∧
      ((n.choose a * n.choose b : ℕ) : ℝ) ≤
        (((2 * mOfMu μ n : ℕ) : ℝ) + 1) ^ 2 * Real.exp (n * gHalfMu μ * Real.log 2) *
          ((us.choose a * ua.choose b : ℕ) : ℝ) := by
  set M := 2 * mOfMu μ n with hMdef
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : 2 * μ * n ≤ (M : ℝ) := by
    rw [hMdef]; push_cast
    have := Nat.le_ceil (μ * n)
    unfold mOfMu; linarith
  have hmOf : mOfMu μ n ≤ n := mOfMu_le hμ1 n
  have hM2 : M ≤ 2 * n := by omega
  have hnM : n < M := by
    have : (n : ℝ) < 2 * μ * n := by nlinarith
    exact_mod_cast this.trans_le hM1
  set L := M - n with hLdef
  have hLM : M = n + L := by omega
  have hL1 : 1 ≤ L := by omega
  set f : ℕ × ℕ → ℕ := fun p => p.1.choose a * p.2.choose b with hf
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (antidiagonal M) f ⟨(0, M), by simp⟩
  have hp' : p.1 + p.2 = M := mem_antidiagonal.mp hp
  have hsum : (M + 1).choose (a + b + 1) ≤ (M + 1) * f p := by
    rw [← sum_antidiagonal_choose a M b]
    have := Finset.sum_le_card_nsmul (antidiagonal M) f (f p) hmax
    simpa [Finset.Nat.card_antidiagonal, hf] using this
  have hfpos : 0 < f p := by
    have : 0 < (M + 1).choose (a + b + 1) := Nat.choose_pos (by omega)
    have := this.trans_le hsum
    exact Nat.pos_of_mul_pos_left this
  have hap : a ≤ p.1 := by
    by_contra h
    have : f p = 0 := by simp [hf, Nat.choose_eq_zero_of_lt (not_le.mp h)]
    omega
  have hbp : b ≤ p.2 := by
    by_contra h
    have : f p = 0 := by simp [hf, Nat.choose_eq_zero_of_lt (not_le.mp h)]
    omega
  have hM1' : 2 * μ * n ≤ ((n + L : ℕ) : ℝ) := by rw [← hLM]; exact hM1
  have hpoly : ((L : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ 2 := by
    have : (L : ℝ) ≤ M := by exact_mod_cast (show L ≤ M by omega)
    nlinarith
  have hE0 : 0 ≤ Real.exp (n * gHalfMu μ * Real.log 2) := (Real.exp_pos _).le
  by_cases hlo : p.1 < L
  · -- capped on the second block: layout `(L, n)`
    obtain ⟨v, hv⟩ : ∃ v, p.2 = v + 1 := ⟨p.2 - 1, by omega⟩
    have hq : (p.1 + 1, v) ∈ antidiagonal M := mem_antidiagonal.mpr (by simp; omega)
    have hle := hmax _ hq
    simp only [hf, hv] at hle hfpos
    have hr := step_ratio hfpos hle
    have hstep : a * (n + 1) ≤ b * L :=
      calc a * (n + 1) ≤ a * (v + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ b * (p.1 + 1) := hr
        _ ≤ b * L := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨haL, hB⟩ := caseB_bound hμ hn hM1' (by omega) hL1 hab hstep
    refine ⟨L, n, by omega, by omega, le_rfl, haL, by omega, ?_⟩
    push_cast
    have h0 : (0 : ℝ) ≤ n.choose b := Nat.cast_nonneg _
    calc (n.choose a : ℝ) * n.choose b
        ≤ (((L : ℝ) + 1) * Real.exp (n * gHalfMu μ * Real.log 2) * L.choose a) * n.choose b :=
          mul_le_mul_of_nonneg_right hB h0
      _ ≤ (((M : ℝ) + 1) ^ 2 * Real.exp (n * gHalfMu μ * Real.log 2) * L.choose a) * n.choose b := by
          gcongr
      _ = _ := by ring
  by_cases hhi : n < p.1
  · -- capped on the first block: layout `(n, L)`
    obtain ⟨u, hu⟩ : ∃ u, p.1 = u + 1 := ⟨p.1 - 1, by omega⟩
    have hq : (u, p.2 + 1) ∈ antidiagonal M := mem_antidiagonal.mpr (by simp; omega)
    have hle := hmax _ hq
    simp only [hf, hu] at hle hfpos
    have hr := step_ratio (a := b) (b := a) (u := p.2) (v := u)
      (by rw [mul_comm]; exact hfpos) (by rw [mul_comm, mul_comm (p.2.choose b)]; exact hle)
    have hstep : b * (n + 1) ≤ a * L :=
      calc b * (n + 1) ≤ b * (u + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ a * (p.2 + 1) := hr
        _ ≤ a * L := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨hbL, hB⟩ := caseB_bound hμ hn hM1' (by omega) hL1 (by omega) hstep
    refine ⟨n, L, by omega, le_rfl, by omega, by omega, hbL, ?_⟩
    push_cast
    have h0 : (0 : ℝ) ≤ n.choose a := Nat.cast_nonneg _
    calc (n.choose a : ℝ) * n.choose b
        ≤ n.choose a * (((L : ℝ) + 1) * Real.exp (n * gHalfMu μ * Real.log 2) * L.choose b) :=
          mul_le_mul_of_nonneg_left hB h0
      _ ≤ n.choose a * (((M : ℝ) + 1) ^ 2 * Real.exp (n * gHalfMu μ * Real.log 2) * L.choose b) := by
          gcongr
      _ = _ := by ring
  · -- uncapped
    refine ⟨p.1, p.2, hp', by omega, by omega, hap, hbp, ?_⟩
    have := caseA_bound hμ hn hM1 (by exact_mod_cast hM2) hab hsum
    simpa [hf] using this

end Layout

open Layout in
theorem layout_bound_mu {μ : ℝ} (hμ0 : 1 / 2 < μ) (hμ1 : μ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a b : ℕ, a ≤ n → b ≤ n →
    min a (n - a) + min b (n - b) ≤ n / 2 →
    ∃ us ua : ℕ, us + ua = 2 * mOfMu μ n ∧ us ≤ n ∧ ua ≤ n ∧
      min a (n - a) ≤ us ∧ min b (n - b) ≤ ua ∧
      ((n.choose a * n.choose b : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ)) *
          ((us.choose (min a (n - a)) * ua.choose (min b (n - b)) : ℕ) : ℝ) := by
  set c := δ * Real.log 2 with hc
  have hcpos : 0 < c := mul_pos hδ (Real.log_pos one_lt_two)
  refine ⟨⌈54 / c ^ 3⌉₊ + 1, ?_⟩
  intro n hn a b ha hb hab
  have hn1 : 1 ≤ n := by omega
  have hnc : 54 / c ^ 3 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (54 / c ^ 3)
    have h2 : ((⌈54 / c ^ 3⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈54 / c ^ 3⌉₊ ≤ n)
    linarith
  obtain ⟨us, ua, h1, h2, h3, h4, h5, hB⟩ := core hμ0 hμ1.le hn1 hab
  refine ⟨us, ua, h1, h2, h3, h4, h5, ?_⟩
  rw [choose_min ha, choose_min hb] at hB
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpoly : (((2 * mOfMu μ n : ℕ) : ℝ) + 1) ^ 2 ≤ Real.exp (n * c) := by
    have hM : ((2 * mOfMu μ n : ℕ) : ℝ) ≤ 2 * n := by
      exact_mod_cast (by have := mOfMu_le hμ1.le n; omega : 2 * mOfMu μ n ≤ 2 * n)
    have hexp := Real.pow_div_factorial_le_exp (x := n * c) (by positivity) 3
    norm_num [Nat.factorial] at hexp
    have hc3 : 54 ≤ n * c ^ 3 := by rwa [div_le_iff₀ (by positivity)] at hnc
    have hM0 : (0 : ℝ) ≤ ((2 * mOfMu μ n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcube : (n * c) ^ 3 = (n : ℝ) ^ 2 * (n * c ^ 3) := by ring
    calc (((2 * mOfMu μ n : ℕ) : ℝ) + 1) ^ 2 ≤ (2 * n + 1) ^ 2 := by gcongr
      _ ≤ 9 * (n : ℝ) ^ 2 := by nlinarith
      _ ≤ (n * c) ^ 3 / 6 := by
          rw [hcube]; nlinarith [mul_le_mul_of_nonneg_left hc3 (sq_nonneg (n : ℝ))]
      _ ≤ Real.exp (n * c) := hexp
  have hrpow : (2 : ℝ) ^ ((n : ℝ) * (gHalfMu μ + δ))
      = Real.exp (n * gHalfMu μ * Real.log 2) * Real.exp (n * c) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, hc]; ring_nf
  rw [hrpow]
  set E := Real.exp (n * gHalfMu μ * Real.log 2)
  set T : ℝ := ((us.choose (min a (n - a)) * ua.choose (min b (n - b)) : ℕ) : ℝ)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hT : 0 ≤ T := Nat.cast_nonneg _
  calc ((n.choose a * n.choose b : ℕ) : ℝ) ≤ (((2 * mOfMu μ n : ℕ) : ℝ) + 1) ^ 2 * E * T := hB
    _ ≤ Real.exp (n * c) * E * T := by gcongr
    _ = E * Real.exp (n * c) * T := by ring

theorem layout_bound {δ : ℝ} (hδ : 0 < δ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a b : ℕ, a ≤ n → b ≤ n →
    min a (n - a) + min b (n - b) ≤ n / 2 →
    ∃ us ua : ℕ, us + ua = 2 * mOf n ∧ us ≤ n ∧ ua ≤ n ∧
      min a (n - a) ≤ us ∧ min b (n - b) ≤ ua ∧
      ((n.choose a * n.choose b : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * (gHalf + δ)) *
          ((us.choose (min a (n - a)) * ua.choose (min b (n - b)) : ℕ) : ℝ) := by
  have hg : gHalf = gHalfMu muQ := by
    unfold gHalf gHalfMu muQ
    norm_num
  have hm : ∀ n, mOf n = mOfMu muQ n := fun _ => rfl
  simp only [hg, hm]
  exact layout_bound_mu (by unfold muQ; norm_num) (by unfold muQ; norm_num) hδ

end IDMM
