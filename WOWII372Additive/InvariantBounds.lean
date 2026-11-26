module
public import WOWII372Additive.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-! Reductions on the exact invariants used by WOWII 372. -/
@[expose] public section
namespace WOWII.InvariantBounds
open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {T : SimpleGraph α}

/-- The path partition by singleton walks. -/
theorem pathCover_attained (T : SimpleGraph α) :
    ∃ P : Finset (Finset α), P.card = T.pathCoverNumber ∧ IsPathCover T P := by
  classical
  apply Nat.sInf_mem (s := {k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover T P})
  let P : Finset (Finset α) := Finset.univ.image fun v : α => {v}
  refine ⟨P.card, P, rfl, ?_⟩
  constructor
  · intro s hs t ht hst
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ht
    simpa using hst
  · constructor
    · intro v _
      exact Finset.mem_biUnion.mpr ⟨{v}, Finset.mem_image.mpr ⟨v,by simp,rfl⟩, by simp⟩
    · intro s hs
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hs
      exact ⟨v,v,.nil,SimpleGraph.Walk.IsPath.nil,by simp⟩

omit [DecidableEq α] in
theorem tdom_attained (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalNDominatingSet T.totalDominationNumber D := by
  classical
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hn
  apply Nat.sInf_mem (s := {k | ∃ D : Finset α, T.IsTotalNDominatingSet k D})
  refine ⟨Fintype.card α, Finset.univ, ⟨?_, Finset.card_univ⟩⟩
  intro v
  obtain ⟨u,hu⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
  exact ⟨u,by simp,hu⟩

omit [Fintype α] [DecidableEq α] in
theorem vertexCoverNum_le_card {S : Finset α} (h : T.IsVertexCover (S : Set α)) :
    T.vertexCoverNum.toNat ≤ S.card := by
  apply ENat.toNat_le_of_le_natCast
  simpa using h.vertexCoverNum_le

/-- A cover for every pair of witnesses suffices for the sharp additive theorem. -/
theorem additive_of_covers (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (makeCover : ∀ (P : Finset (Finset α)) (D : Finset α),
      IsPathCover T P → T.IsTotalDominating (D : Set α) →
      ∃ S : Finset α, T.IsVertexCover (S : Set α) ∧
        S.card + (if 1 < P.card then 1 else 0) ≤ D.card + (P.card - 1)) :
    T.vertexCoverNum.toNat + (if 1 < T.pathCoverNumber then 1 else 0) ≤
      T.totalDominationNumber + (T.pathCoverNumber - 1) := by
  obtain ⟨P,pc,hp⟩ := pathCover_attained T
  obtain ⟨D,hd⟩ := tdom_attained hT hn
  obtain ⟨S,hs,b⟩ := makeCover P D hp hd.1
  have hv := vertexCoverNum_le_card hs
  rw [pc, hd.2] at b
  omega

omit [DecidableEq α] in
theorem tdom_pos (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) : 0 < T.totalDominationNumber := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨D,hD⟩ := tdom_attained hT hn
  obtain ⟨w,hw,_⟩ := hD.1 (Classical.arbitrary α)
  rw [← hD.2]
  exact Finset.card_pos.mpr ⟨w,hw⟩

theorem regularized_of_additive (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (h : T.vertexCoverNum.toNat + (if 1 < T.pathCoverNumber then 1 else 0) ≤
      T.totalDominationNumber + (T.pathCoverNumber - 1)) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := by
  by_cases hp : T.pathCoverNumber ≤ 2
  · have hx : max 1 (T.pathCoverNumber - 1) = 1 := by omega
    rw [hx, Nat.mul_one]
    split at h <;> omega
  · have hx : max 1 (T.pathCoverNumber - 1) = (T.pathCoverNumber - 2) + 1 := by omega
    rw [hx, Nat.mul_add, Nat.mul_one]
    have lo := Nat.mul_le_mul_right (T.pathCoverNumber - 2) (tdom_pos hT hn)
    simp only [Nat.one_mul] at lo
    split at h <;> omega

end WOWII.InvariantBounds
