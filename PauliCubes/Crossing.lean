/-
The crossing `[x = v][y = u]` on `2^n` letters, decomposed into Pauli words in two cuts, and the
contraction that turns such a decomposition into a weighted sum of squares of Pauli forms.

Row cut: `row β = P_β(x, y) P_β(u, v)`. Column cut: `col ν = P_ν(x, u) P_ν(y, v)`.
One qubit: `[x = v][y = u] = ½ Σ_a s_a P_a(x, y) P_a(u, v)` with `s = (1, 1, 1, -1)`, and
`P_a(x, u) P_a(y, v) = Σ_b M(a, b) P_b(x, y) P_b(u, v)` with `M = h / 2`, `h` the table of commutation signs.
-/
import PauliCubes.Defs

open Finset

namespace PauliCubes

variable {K : Type*} [Field K]

/-- `s_a`: +1 for the symmetric letters I, X, Z and -1 for J. It is also the transpose sign. -/
def sgn1 (K : Type*) [Field K] : Fin 4 → K := ![1, 1, 1, -1]

/-- Commutation signs of the letters I, X, Z, J. -/
def hsign (K : Type*) [Field K] : Fin 4 → Fin 4 → K :=
  ![![1, 1, 1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

/-- The change of cut, `M = h / 2`. -/
noncomputable def cutM (K : Type*) [Field K] (a b : Fin 4) : K := 2⁻¹ * hsign K a b

theorem cross1_row (h2 : (2 : K) ≠ 0) (x y u v : Fin 2) :
    (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ a, (2⁻¹ * sgn1 K a) * (pauli1 K a x y * pauli1 K a u v) := by
  have hh : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
    simp [Fin.sum_univ_four, pauli1, sgn1] <;> first | ring1 | linear_combination hh | linear_combination -hh

theorem col1_row (h2 : (2 : K) ≠ 0) (a : Fin 4) (x y u v : Fin 2) :
    pauli1 K a x u * pauli1 K a y v = ∑ b, cutM K a b * (pauli1 K b x y * pauli1 K b u v) := by
  have hh : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  fin_cases a <;> fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
    simp [Fin.sum_univ_four, pauli1, cutM, hsign] <;>
    first | ring1 | linear_combination hh | linear_combination -hh

theorem pauli1_transpose (a : Fin 4) (s t : Fin 2) : pauli1 K a t s = sgn1 K a * pauli1 K a s t := by
  fin_cases a <;> fin_cases s <;> fin_cases t <;> simp [pauli1, sgn1]

variable {n : ℕ}

/-- The row-cut tensor of a word. -/
def rowT (K : Type*) [Field K] (β : Fin n → Fin 4) (x y u v : Fin n → Fin 2) : K :=
  pauliWord K β x y * pauliWord K β u v

/-- The column-cut tensor of a word. -/
def colT (K : Type*) [Field K] (ν : Fin n → Fin 4) (x y u v : Fin n → Fin 2) : K :=
  pauliWord K ν x u * pauliWord K ν y v

theorem rowT_eq (β : Fin n → Fin 4) (x y u v : Fin n → Fin 2) :
    rowT K β x y u v = ∏ i, (pauli1 K (β i) (x i) (y i) * pauli1 K (β i) (u i) (v i)) := by
  simp [rowT, pauliWord, Finset.prod_mul_distrib]

/-- The crossing in the row cut: `[x = v][y = u] = Σ_β (Π_i s_{β_i} / 2) row β`. -/
theorem cross_eq_row (h2 : (2 : K) ≠ 0) (x y u v : Fin n → Fin 2) :
    (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ β : Fin n → Fin 4, (∏ i, (2⁻¹ * sgn1 K (β i))) * rowT K β x y u v := by
  classical
  have hind : (if x = v ∧ y = u then 1 else 0 : K) = ∏ i, (if x i = v i ∧ y i = u i then 1 else 0 : K) := by
    by_cases h : x = v ∧ y = u
    · rw [if_pos h]; symm; exact Finset.prod_eq_one fun i _ => by simp [h.1, h.2]
    · rw [if_neg h]; symm
      have : ∃ i, ¬ (x i = v i ∧ y i = u i) := by
        by_contra hc; push Not at hc
        exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
      obtain ⟨i, hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [hind, Finset.prod_congr rfl fun i _ => cross1_row h2 (x i) (y i) (u i) (v i),
    Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [rowT_eq, ← Finset.prod_mul_distrib]

/-- A column-cut tensor in the row cut: `col ν = Σ_β (Π_i M(ν_i, β_i)) row β`. -/
theorem col_eq_row (h2 : (2 : K) ≠ 0) (ν : Fin n → Fin 4) (x y u v : Fin n → Fin 2) :
    colT K ν x y u v = ∑ β : Fin n → Fin 4, (∏ i, cutM K (ν i) (β i)) * rowT K β x y u v := by
  have : colT K ν x y u v = ∏ i, (pauli1 K (ν i) (x i) (u i) * pauli1 K (ν i) (y i) (v i)) := by
    simp [colT, pauliWord, Finset.prod_mul_distrib]
  rw [this, Finset.prod_congr rfl fun i _ => col1_row h2 (ν i) (x i) (y i) (u i) (v i),
    Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [rowT_eq, ← Finset.prod_mul_distrib]

/-- The transpose sign of a word. -/
def tsgn (K : Type*) [Field K] (ν : Fin n → Fin 4) : K := ∏ i, sgn1 K (ν i)

theorem tsgn_sq (ν : Fin n → Fin 4) : tsgn K ν ^ 2 = 1 := by
  rw [tsgn, ← Finset.prod_pow]
  have h1 : ∀ a : Fin 4, sgn1 K a ^ 2 = 1 := by intro a; fin_cases a <;> simp [sgn1]
  exact Finset.prod_eq_one fun i _ => h1 (ν i)

theorem pauliWord_transpose (ν : Fin n → Fin 4) (x y : Fin n → Fin 2) :
    pauliWord K ν y x = tsgn K ν * pauliWord K ν x y := by
  simp only [pauliWord, tsgn, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => pauli1_transpose (ν i) (x i) (y i)

/-! ## Contraction -/

section contraction
variable (X Y : (Fin n → Fin 2) → K)

/-- Contract a four-index tensor against `X_x Y_y Y_u X_v`. -/
def contract (T : (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → K) : K :=
  ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2) × (Fin n → Fin 2) × (Fin n → Fin 2),
    T p.1 p.2.1 p.2.2.1 p.2.2.2 * (X p.1 * Y p.2.1 * Y p.2.2.1 * X p.2.2.2)

theorem contract_sum {ι : Type*} [Fintype ι] (c : ι → K)
    (T : ι → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → K) :
    contract X Y (fun x y u v => ∑ i, c i * T i x y u v) = ∑ i, c i * contract X Y (T i) := by
  simp only [contract, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

theorem contract_add (T T' : (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → K) :
    contract X Y (fun x y u v => T x y u v + T' x y u v) = contract X Y T + contract X Y T' := by
  simp only [contract, add_mul, Finset.sum_add_distrib]

theorem contract_nested (T : (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → (Fin n → Fin 2) → K) :
    contract X Y T = ∑ x, ∑ y, ∑ u, ∑ v, T x y u v * (X x * Y y * Y u * X v) := by
  simp only [contract, Fintype.sum_prod_type]

theorem contract_cross :
    contract X Y (fun x y u v => (if x = v ∧ y = u then 1 else 0 : K)) =
      (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) := by
  classical
  rw [contract_nested, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [ite_and, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single y (fun u _ hu => by simp [Ne.symm hu]) (by simp)]
  rw [Finset.sum_eq_single x (fun v _ hv => by simp [Ne.symm hv]) (by simp)]
  simp only [if_true]
  ring

theorem contract_rowT (ν : Fin n → Fin 4) :
    contract X Y (rowT K ν) = tsgn K ν * pauliForm K ν X Y ^ 2 := by
  rw [contract_nested]
  have hsplit : ∀ x y : Fin n → Fin 2, ∑ u, ∑ v, rowT K ν x y u v * (X x * Y y * Y u * X v) =
      (pauliWord K ν x y * X x * Y y) * (tsgn K ν * pauliForm K ν X Y) := by
    intro x y
    have h1 : tsgn K ν * pauliForm K ν X Y = ∑ u, ∑ v, pauliWord K ν u v * Y u * X v := by
      rw [pauliForm, Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [pauliWord_transpose ν v u]; linear_combination (pauliWord K ν v u * X u * Y v) * tsgn_sq (K := K) ν
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [rowT]; ring
  simp only [hsplit, ← Finset.sum_mul]
  rw [pauliForm]; ring

theorem contract_colT (ν : Fin n → Fin 4) :
    contract X Y (colT K ν) = tsgn K ν * pauliForm K ν X Y ^ 2 := by
  rw [contract_nested]
  have h1 : tsgn K ν * pauliForm K ν X Y = ∑ y, ∑ v, pauliWord K ν y v * Y y * X v := by
    rw [pauliForm, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [pauliWord_transpose ν v y]; linear_combination (pauliWord K ν v y * X y * Y v) * tsgn_sq (K := K) ν
  have : ∑ x, ∑ y, ∑ u, ∑ v, colT K ν x y u v * (X x * Y y * Y u * X v) =
      ∑ x, ∑ u, ∑ y, ∑ v, (pauliWord K ν x u * X x * Y u) * (pauliWord K ν y v * Y y * X v) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun v _ => ?_
    simp only [colT]; ring
  rw [this]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← h1]
  rw [pauliForm]; ring

/-- **Contraction.** A decomposition of the crossing into row-cut and column-cut Pauli words gives a
weighted sum-of-squares identity in Pauli forms, with weight `tsgn ν · (r ν + d ν)`. -/
theorem sos_of_cross (r d : (Fin n → Fin 4) → K)
    (h : ∀ x y u v, (if x = v ∧ y = u then 1 else 0 : K) =
      ∑ β, r β * rowT K β x y u v + ∑ ν, d ν * colT K ν x y u v) :
    (∑ x, X x ^ 2) * (∑ y, Y y ^ 2) = ∑ ν, (tsgn K ν * (r ν + d ν)) * pauliForm K ν X Y ^ 2 := by
  rw [← contract_cross X Y]
  have : (fun x y u v => (if x = v ∧ y = u then 1 else 0 : K)) =
      fun x y u v => (∑ β, r β * rowT K β x y u v) + ∑ ν, d ν * colT K ν x y u v := by
    funext x y u v; exact h x y u v
  rw [this, contract_add, contract_sum, contract_sum]
  simp only [contract_rowT, contract_colT, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

end contraction

end PauliCubes
