import PauliCubes.Circuit

namespace IDMM
open PauliCubes
variable {R : Type*} [Ring R] {inp B : Set R}

/-- Materialize an available value or a source in at most one counted node. -/
theorem reach_source {x : R} (hx : x ∈ inp ∪ B) : Reach inp B {x} 1 := by
  rcases hx with hx | hx
  · exact Reach.input hx
  · exact (Reach.refl (Set.singleton_subset_iff.mpr hx)).mono le_rfl le_rfl (by omega)

/-- Free-source gates can be simulated in the all-nodes-counted model. -/
theorem reach_source_gate {g : R} (hg : IsGate inp (inp ∪ B) g) : Reach inp B {g} 3 := by
  rcases hg with hg | ⟨p,hp,q,hq,rfl | rfl⟩
  · exact (Reach.input hg).mono le_rfl le_rfl (by omega)
  · have h := (reach_source hp).union (reach_source hq)
    exact h.seq (Reach.add (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
  · have h := (reach_source hp).union (reach_source hq)
    exact h.seq (Reach.mul (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))

theorem builds_charge_sources : ∀ {gs : List R} {B : Set R},
    Builds inp (inp ∪ B) gs → Reach inp B {x | x ∈ gs} (3 * gs.length)
  | [], _, _ => Reach.refl (by simp)
  | g :: gs, B, ⟨hg,hgs⟩ => by
    have hg' := reach_source_gate hg
    have hsub : insert g (inp ∪ B) ⊆ inp ∪ (B ∪ {g}) := by aesop
    have hgs' := builds_charge_sources (hgs.mono hsub)
    exact (hg'.trans hgs').mono le_rfl (by simp; aesop) (by simp; omega)

/-- Shared output charging adds at most one node per requested output, not per free register. -/
theorem reach_charge_sources {S : Set R} {s : ℕ} (h : Reach inp inp S s)
    {J : Type*} [Fintype J] (f : J → R) (hf : ∀ j, f j ∈ S) :
    Reach inp ∅ (Set.range f) (3*s + Fintype.card J) := by
  classical
  obtain ⟨gs,hgs,hlen,hS⟩ := h
  have hb : Builds inp (inp ∪ (∅ : Set R)) gs := by simpa using hgs
  have h₁ := builds_charge_sources hb
  have h₂ : Reach inp ((∅ : Set R) ∪ {x | x ∈ gs})
      (⋃ j ∈ (Finset.univ : Finset J), {f j}) (∑ _j : J, 1) := by
    apply Reach.biUnion
    intro j _
    apply reach_source
    rcases hS (hf j) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  refine (h₁.seq h₂).mono le_rfl ?_ ?_
  · rintro _ ⟨j,rfl⟩
    simp
  · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    omega
end IDMM
