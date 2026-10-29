/-
**The block circuit for one length** (cycle 055 §§2–5), over any field `K` with `2 ≠ 0` and `√−1`.

Given a block matrix-multiplication oracle (`BlockMM`, `M` gates per product family or middle insertion) for
`2^m × 2^(n−m)` inputs and, for every corner class, a family of blocks of `2m` Majoranas covering the class,
`ID` on `2^n` words has a noncommutative circuit with `2·2^n + (#blocks)·(cost per block + 1) + 1` gates. Each block
costs its input transforms plus one `block_assembly_gen`.
-/
import IDMM.MajClassBlock
import IDMM.BlockAssembly
import PauliCubes.IDCircuit
import IDMM.MajSOS

noncomputable section
namespace IDMM
open Finset Matrix PauliCubes OAI.MatrixMultiplication.Arithmetic

variable {n m : ℕ} {K : Type*} [Field K] [NeZero (2 : K)] [SqrtNegOne K]

/-! ## One block -/

section blockReach
variable {𝒜 : Type*} [Ring 𝒜] [Algebra K 𝒜] {inp : Set 𝒜}

/-- Gates for one block, given `M` gates per oracle call. -/
def blockCost (n m M : ℕ) : ℕ := 7 * 2 ^ n * (4 * m + 1) + blockGenCost m M

/-- **One block.** The words of a block, with any coefficients, from the inputs. -/
theorem block_reach (hc : ∀ z : K, algebraMap K 𝒜 z ∈ inp) (hm : m ≤ n)
    (L : List (MIdx n × MIdx n)) (hL : ∀ q ∈ L, q.1 ≠ q.2) (hlen : L.length ≤ 2 * m) (σ : MV n)
    {M : ℕ} (hMM : BlockMM inp m (n - m) M)
    (Wd : Finset (Fin n → Fin 4)) (w : (Fin n → Fin 4) → K) (Aw : (Fin n → Fin 4) → MV n)
    (hA : ∀ ν ∈ Wd, majV ν = Aw ν + σ ∧ SuppIn (mswapList L (Aw ν)) (canon n m))
    {B : Set 𝒜} (X Y : Bits n → 𝒜) (hX : ∀ x, X x ∈ B) (hY : ∀ y, Y y ∈ B) :
    Reach inp B {∑ ν ∈ Wd, w ν • f2 (L := K) X Y ν} (blockCost n m M) := by
  classical
  let lamOf : MV n → K := fun A => Classical.choose (block_word_mat (K := K) L hL σ A)
  have hlamOf : ∀ A, pmatM K (A + σ) =
      lamOf A • (compI K L * pmatM K (mswapList L A) * (compM K L * pmatM K σ)) :=
    fun A => (Classical.choose_spec (block_word_mat (K := K) L hL σ A)).2
  have h1 : Reach inp B (Set.range (leftT (compI K L) X)) (7 * 2 ^ n * L.length) :=
    reach_leftT_compI hc L hX
  have h2 : Reach inp B (Set.range (rightT (pmatM K σ) Y)) (7 * 2 ^ n) := by
    rw [pmatM_factor]; exact reach_rightT_factor hc hY _ _ _ _
  have h3 : Reach inp (B ∪ Set.range (rightT (pmatM K σ) Y))
      (Set.range (rightT (compM K L) (rightT (pmatM K σ) Y))) (7 * 2 ^ n * L.length) :=
    reach_rightT_compM hc L (fun y => Set.mem_union_right _ (Set.mem_range_self y))
  have hXY := h1.union (h2.seq h3)
  have hXb : ∀ ps, Xblk K hm L X ps ∈ B ∪ (Set.range (leftT (compI K L) X) ∪
      Set.range (rightT (compM K L) (rightT (pmatM K σ) Y))) :=
    fun ps => Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_range_self _))
  have hYb : ∀ qs, Yblk K hm L σ Y qs ∈ B ∪ (Set.range (leftT (compI K L) X) ∪
      Set.range (rightT (compM K L) (rightT (pmatM K σ) Y))) := by
    intro qs
    have : Yblk K hm L σ Y qs = rightT (compM K L) (rightT (pmatM K σ) Y) (joinB hm qs.1 qs.2) := by
      simp only [Yblk, rightT_mul]
    rw [this]
    exact Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_range_self _))
  have hblk := block_assembly_gen (inp := inp) hc (Xblk K hm L X) (Yblk K hm L σ Y) hXb hYb hMM Wd w
    (fun ν => lamOf (Aw ν)) (fun ν => αblk hm L (Aw ν)) (fun ν => βblk hm L (Aw ν))
  have heq : ∑ ν ∈ Wd, w ν • f2 (L := K) X Y ν =
      ∑ ν ∈ Wd, w ν • ((2 : K)⁻¹ •
        (fxyT (Xblk K hm L X) (Yblk K hm L σ Y) (fun ν => lamOf (Aw ν)) (fun ν => αblk hm L (Aw ν))
            (fun ν => βblk hm L (Aw ν)) ν *
          fxyT (Xblk K hm L X) (Yblk K hm L σ Y) (fun ν => lamOf (Aw ν)) (fun ν => αblk hm L (Aw ν))
            (fun ν => βblk hm L (Aw ν)) ν +
        fstarT (Xblk K hm L X) (Yblk K hm L σ Y) (fun ν => lamOf (Aw ν)) (fun ν => αblk hm L (Aw ν))
            (fun ν => βblk hm L (Aw ν)) ν
          (fyxT (Xblk K hm L X) (Yblk K hm L σ Y) (fun ν => lamOf (Aw ν)) (fun ν => αblk hm L (Aw ν))
            (fun ν => βblk hm L (Aw ν)) ν))) := by
    refine sum_congr rfl fun ν hν => ?_
    obtain ⟨hV, hS⟩ := hA ν hν
    rw [f2_block (hlamOf (Aw ν)) hS ν hV X Y]
    rfl
  rw [heq]
  refine (hXY.seq hblk).mono le_rfl le_rfl ?_
  unfold blockCost
  have h4 : 7 * 2 ^ n * L.length ≤ 7 * 2 ^ n * (2 * m) := Nat.mul_le_mul_left _ hlen
  have h5 : 7 * 2 ^ n * (4 * m + 1) = 7 * 2 ^ n * (2 * m) + 7 * 2 ^ n * (2 * m) + 7 * 2 ^ n := by ring
  linarith

end blockReach

/-! ## All blocks -/

/-- The corner classes. -/
def cornerSet (n : ℕ) : Finset (ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1)).filter fun ab => min ab.1 (n - ab.1) + min ab.2 (n - ab.2) ≤ n / 2

theorem mem_cornerSet {ab : ℕ × ℕ} : ab ∈ cornerSet n ↔ ab.1 ≤ n ∧ ab.2 ≤ n ∧ InCorner n ab.1 ab.2 := by
  simp only [cornerSet, mem_filter, mem_product, mem_range, InCorner]
  omega

/-- **`ID` on `2^n` words from block covers.** -/
theorem idw_blocks (hm : m ≤ n) {M : ℕ}
    (hMM : BlockMM (ncInputs K ((Fin n → Fin 2) ⊕ (Fin n → Fin 2))) m (n - m) M)
    (Ccl : ℕ × ℕ → Finset (Finset (Fin n) × Finset (Fin n)))
    (hsize : ∀ ab ∈ cornerSet n, ∀ p ∈ Ccl ab, p.1.card + p.2.card = 2 * m)
    (hcov : ∀ ab ∈ cornerSet n, ∀ S T : Finset (Fin n), S.card = min ab.1 (n - ab.1) →
      T.card = min ab.2 (n - ab.2) → ∃ p ∈ Ccl ab, S ⊆ p.1 ∧ T ⊆ p.2) :
    NCSizeLE (IDw K n)
      (2 * 2 ^ n + ((∑ ab ∈ cornerSet n, (Ccl ab).card) * (blockCost n m M + 1) + 1)) := by
  classical
  obtain ⟨w, hw, hsupp⟩ := majorana_sos (K := K) n
  let V := (Fin n → Fin 2) ⊕ (Fin n → Fin 2)
  let inp : Set (FreeAlgebra K V) := ncInputs K V
  have hc : ∀ z : K, algebraMap K (FreeAlgebra K V) z ∈ inp := fun z => Or.inr ⟨z, rfl⟩
  have h0 : (0 : FreeAlgebra K V) ∈ inp := by simpa using hc 0
  let X : Bits n → FreeAlgebra K V := fun x => FreeAlgebra.ι K (Sum.inl x)
  let Y : Bits n → FreeAlgebra K V := fun y => FreeAlgebra.ι K (Sum.inr y)
  let B0 : Set (FreeAlgebra K V) := Set.range X ∪ Set.range Y
  -- the inputs
  have hin : Reach inp ∅ B0 (2 * 2 ^ n) := by
    have h := Reach.biUnion (inp := inp) (B := ∅) (univ : Finset V)
      (S := fun v => {FreeAlgebra.ι K v}) (t := fun _ => 1) (fun v _ => Reach.input (Or.inl ⟨v, rfl⟩))
    refine h.mono le_rfl ?_ ?_
    · rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
      · exact Set.mem_biUnion (mem_univ (Sum.inl x)) rfl
      · exact Set.mem_biUnion (mem_univ (Sum.inr y)) rfl
    · simp [V, Fintype.card_sum]; omega
  -- choosing a block for each word
  have hclass : ∀ ν, w ν ≠ 0 → classOf ν ∈ cornerSet n := fun ν hν =>
    mem_cornerSet.mpr ⟨weight_le _, weight_le _, hsupp ν hν⟩
  have hex : ∀ ν, w ν ≠ 0 → ∃ p ∈ Ccl (classOf ν), supp (relA ν).1 ⊆ p.1 ∧ supp (relA ν).2 ⊆ p.2 :=
    fun ν hν => hcov _ (hclass ν hν) _ _ (card_supp_relA ν).1 (card_supp_relA ν).2
  let pick : (Fin n → Fin 4) → Finset (Fin n) × Finset (Fin n) := fun ν =>
    if h : w ν ≠ 0 then Classical.choose (hex ν h) else (∅, ∅)
  have hpick : ∀ ν (h : w ν ≠ 0), pick ν ∈ Ccl (classOf ν) ∧
      supp (relA ν).1 ⊆ (pick ν).1 ∧ supp (relA ν).2 ⊆ (pick ν).2 := by
    intro ν h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec (hex ν h)
  let ch : (Fin n → Fin 4) → (ℕ × ℕ) × (Finset (Fin n) × Finset (Fin n)) := fun ν => (classOf ν, pick ν)
  let Blocks : Finset ((ℕ × ℕ) × (Finset (Fin n) × Finset (Fin n))) :=
    (cornerSet n).biUnion fun ab => (Ccl ab).image fun p => (ab, p)
  have hmemB : ∀ b ∈ Blocks, b.1 ∈ cornerSet n ∧ b.2 ∈ Ccl b.1 := by
    intro b hb
    obtain ⟨ab, hab, hb⟩ := mem_biUnion.mp hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact ⟨hab, hp⟩
  have hch : ∀ ν ∈ univ.filter (fun ν => w ν ≠ 0), ch ν ∈ Blocks := by
    intro ν hν
    have hν' := (mem_filter.mp hν).2
    exact mem_biUnion.mpr ⟨classOf ν, hclass ν hν', mem_image.mpr ⟨pick ν, (hpick ν hν').1, rfl⟩⟩
  -- the move of each block
  have hmove : ∀ b ∈ Blocks, ∃ L : List (MIdx n × MIdx n), (∀ q ∈ L, q.1 ≠ q.2) ∧ L.length ≤ 2 * m ∧
      ∀ A : MV n, SuppIn A (blockU b.2) → SuppIn (mswapList L A) (canon n m) := by
    intro b hb
    obtain ⟨hab, hp⟩ := hmemB b hb
    exact exists_moveL hm b.2 (by rw [card_blockU]; exact hsize _ hab _ hp)
  let Lb : (ℕ × ℕ) × (Finset (Fin n) × Finset (Fin n)) → List (MIdx n × MIdx n) := fun b =>
    if h : b ∈ Blocks then Classical.choose (hmove b h) else []
  have hLb : ∀ b ∈ Blocks, (∀ q ∈ Lb b, q.1 ≠ q.2) ∧ (Lb b).length ≤ 2 * m ∧
      ∀ A : MV n, SuppIn A (blockU b.2) → SuppIn (mswapList (Lb b) A) (canon n m) := by
    intro b hb
    simp only [Lb, dif_pos hb]
    exact Classical.choose_spec (hmove b hb)
  -- the words of each block
  let Wd : (ℕ × ℕ) × (Finset (Fin n) × Finset (Fin n)) → Finset (Fin n → Fin 4) := fun b =>
    (univ.filter fun ν => w ν ≠ 0).filter fun ν => ch ν = b
  let Sb : (ℕ × ℕ) × (Finset (Fin n) × Finset (Fin n)) → FreeAlgebra K V := fun b =>
    ∑ ν ∈ Wd b, w ν • f2 (L := K) X Y ν
  have hblk : ∀ b ∈ Blocks, Reach inp B0 {Sb b} (blockCost n m M) := by
    intro b hb
    obtain ⟨hL, hlen, hmv⟩ := hLb b hb
    refine block_reach hc hm (Lb b) hL hlen (shiftCl n b.1.1 b.1.2) hMM (Wd b) w relA ?_ X Y
      (fun x => Set.mem_union_left _ (Set.mem_range_self x))
      (fun y => Set.mem_union_right _ (Set.mem_range_self y))
    intro ν hν
    obtain ⟨hν1, hν2⟩ := mem_filter.mp hν
    have hw0 := (mem_filter.mp hν1).2
    have hcl : classOf ν = b.1 := congrArg Prod.fst hν2
    have hpk : pick ν = b.2 := congrArg Prod.snd hν2
    refine ⟨?_, hmv _ ?_⟩
    · rw [majV_eq_relA_add, hcl]
    · obtain ⟨_, hs1, hs2⟩ := hpick ν hw0
      rw [hpk] at hs1 hs2
      exact suppIn_blockU hs1 hs2
  have hall := Reach.biUnion Blocks hblk
  have hsum := Reach.sum (inp := inp) (B := B0 ∪ ⋃ b ∈ Blocks, {Sb b}) h0 Blocks (p := Sb)
    fun b hb => Or.inr (Set.mem_biUnion hb (Set.mem_singleton _))
  have htot := hin.seq ((hall.seq hsum).mono Set.subset_union_right le_rfl le_rfl)
  -- the total is `ID`
  have hid : ∑ b ∈ Blocks, Sb b = IDw K n := by
    have h1 : ∑ b ∈ Blocks, Sb b = ∑ ν ∈ univ.filter (fun ν => w ν ≠ 0), w ν • f2 (L := K) X Y ν :=
      sum_fiberwise_of_maps_to hch _
    have h2 : ∑ ν ∈ univ.filter (fun ν => w ν ≠ 0), w ν • f2 (L := K) X Y ν =
        ∑ ν, algebraMap K K (w ν) • f2 (L := K) X Y ν := by
      rw [sum_filter]
      refine sum_congr rfl fun ν _ => ?_
      by_cases h : w ν = 0
      · simp [h]
      · simp [h]
    rw [h1, h2, sos_f2 two_ne_zero w hw X Y]
    rfl
  rw [hid] at htot
  refine htot.ncSizeLE.mono ?_
  have hcard : Blocks.card ≤ ∑ ab ∈ cornerSet n, (Ccl ab).card :=
    card_biUnion_le.trans (sum_le_sum fun ab _ => card_image_le)
  simp only [sum_const, smul_eq_mul]
  nlinarith

end IDMM
