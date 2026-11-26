module
public import Mathlib.Basic.Real.Basic
public import WOWII372Additive.TreeModel
public import WOWII372Additive.LabeledTree
public import WOWII372Additive.InvariantBounds
public import WOWII372Additive.PathEdges

/-! The sharp tree bound and the three WOWII 372 statements on the upstream types. -/
@[expose] public section
open SimpleGraph

namespace WOWII.TreeCover.Shape
variable {α : Type*}

/-- Label the vertices of the rooted tree by their images in the input graph. -/
def label : (s : Shape) → (s.Vertex → α) → LabeledTree α
  | .vertex, f => .vertex (f ())
  | .join l r, f => .join (l.label (fun x => f (.inl x))) (r.label (fun y => f (.inr y)))

private theorem label_root (s : Shape) (f : s.Vertex → α) : (s.label f).root = f s.root := by
  induction s with
  | vertex => rfl
  | join l r il _ => exact il _

variable [DecidableEq α]

private theorem label_nodes (s : Shape) (f : s.Vertex → α) (a : α) :
    a ∈ (s.label f).nodes ↔ ∃ u, f u = a := by
  induction s with
  | vertex =>
    change a ∈ ({f ()} : Finset α) ↔ ∃ u : Unit, f u = a
    constructor
    · intro h; exact ⟨(), (Finset.mem_singleton.mp h).symm⟩
    · rintro ⟨⟨⟩,rfl⟩; exact Finset.mem_singleton_self _
  | join l r il ir =>
    simp only [label,LabeledTree.nodes,Finset.mem_union,il,ir]
    constructor
    · rintro (⟨v,h⟩ | ⟨v,h⟩)
      · exact ⟨.inl v,h⟩
      · exact ⟨.inr v,h⟩
    · rintro ⟨v,h⟩
      cases v with
      | inl v => exact Or.inl ⟨v,h⟩
      | inr v => exact Or.inr ⟨v,h⟩

private theorem label_unique (s : Shape) (f : s.Vertex → α) (hf : Function.Injective f) :
    (s.label f).uniqueLabels := by
  induction s with
  | vertex => trivial
  | join l r il ir =>
    refine ⟨il _ (hf.comp Sum.inl_injective),ir _ (hf.comp Sum.inr_injective),?_⟩
    apply Finset.disjoint_left.mpr
    intro a hl hr
    obtain ⟨u,hu⟩ := (label_nodes _ _ _).mp hl
    obtain ⟨v,hv⟩ := (label_nodes _ _ _).mp hr
    exact Sum.inl_ne_inr (hf (hu.trans hv.symm))

private theorem label_edges (s : Shape) (f : s.Vertex → α) (a b : α) :
    s(a,b) ∈ (s.label f).edges ↔ ∃ u v, f u = a ∧ f v = b ∧ s.graph.Adj u v := by
  induction s generalizing a b with
  | vertex => simp [label,LabeledTree.edges]
  | join l r il ir =>
    simp only [label,LabeledTree.edges,Finset.mem_insert,Finset.mem_union,label_root,Sym2.eq_iff]
    constructor
    · rintro ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | hl | hr)
      · exact ⟨.inl l.root,.inr r.root,rfl,rfl,⟨rfl,rfl⟩⟩
      · exact ⟨.inr r.root,.inl l.root,rfl,rfl,⟨rfl,rfl⟩⟩
      · obtain ⟨u,v,hu,hv,h⟩ := (il _ _ _).mp hl
        exact ⟨.inl u,.inl v,hu,hv,h⟩
      · obtain ⟨u,v,hu,hv,h⟩ := (ir _ _ _).mp hr
        exact ⟨.inr u,.inr v,hu,hv,h⟩
    · rintro ⟨u,v,rfl,rfl,adj⟩
      cases u with
      | inl u =>
        cases v with
        | inl v => exact Or.inr (Or.inl ((il _ _ _).mpr ⟨u,v,rfl,rfl,adj⟩))
        | inr v =>
          obtain ⟨rfl,rfl⟩ := graph_join_adj_inl_inr.mp adj
          exact Or.inl (Or.inl ⟨rfl,rfl⟩)
      | inr u =>
        cases v with
        | inl v =>
          obtain ⟨rfl,rfl⟩ := graph_join_adj_inr_inl.mp adj
          exact Or.inl (Or.inr ⟨rfl,rfl⟩)
        | inr v => exact Or.inr (Or.inr ((ir _ _ _).mpr ⟨u,v,rfl,rfl,adj⟩))

/-- A finite Mathlib tree has a labelling with its exact vertex and edge finsets. -/
theorem exists_labeling [Fintype α] {T : SimpleGraph α} [DecidableRel T.Adj] (hT : T.IsTree) :
    ∃ t : LabeledTree α, t.uniqueLabels ∧ t.nodes = Finset.univ ∧ t.edges = T.edgeFinset := by
  obtain ⟨s,⟨e⟩⟩ := exists_iso_of_isTree_unrooted hT
  refine ⟨s.label e, label_unique _ _ e.injective, ?_, ?_⟩
  · exact Finset.eq_univ_of_forall fun a => (label_nodes _ _ _).mpr (e.surjective a)
  · ext p
    induction p using Sym2.inductionOn with
    | _ a b =>
      rw [label_edges,T.mem_edgeFinset]
      constructor
      · rintro ⟨u,v,rfl,rfl,ha⟩
        exact e.map_rel_iff.mpr ha
      · intro ha
        exact ⟨e.symm a,e.symm b,e.apply_symm_apply a,e.apply_symm_apply b,
          e.symm.map_rel_iff.mpr ha⟩

end WOWII.TreeCover.Shape

namespace WOWII.Solution
open WOWII.TreeCover WOWII.InvariantBounds
variable {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)

/-- Construct a vertex cover from any path partition and any total dominating set. -/
theorem cover_of_pathCover (hT : T.IsTree) (P : Finset (Finset α)) (D : Finset α)
    (hp : T.IsPathCover P) (hd : T.IsTotalDominating (D : Set α)) :
    ∃ S : Finset α, T.IsVertexCover (S : Set α) ∧
      S.card + (if 1 < P.card then 1 else 0) ≤ D.card + (P.card - 1) := by
  classical
  obtain ⟨t,unique,vertices,edges⟩ := Shape.exists_labeling hT
  let H := T.pathCoverSubgraph P
  have hh (v : α) : H.degree v ≤ 2 := pathCoverSubgraph_degree_le_two hT hp v
  have count : (T.edgeFinset \ H.edgeFinset).card + 1 = P.card :=
    pathCoverSubgraph_card_sdiff_edgeFinset_add_one hT hp
  obtain ⟨S,hs,b⟩ := LabeledTree.cover_of_representation D H t unique vertices edges hd hh
  refine ⟨S,hs,?_⟩
  split at b <;> split <;> omega

/-- Sharp additive inequality, including the one-path case. -/
theorem additive (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat + (if 1 < T.pathCoverNumber then 1 else 0) ≤
      T.totalDominationNumber + (T.pathCoverNumber - 1) :=
  additive_of_covers hT hn (cover_of_pathCover T hT)

/-- On the positive-denominator domain, the vertex cover number is at most γₜ + p - 2. -/
theorem additive_of_two_le (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber + T.pathCoverNumber - 2 := by
  have bound := additive T hT hn
  rw [ite_eq_left (show 1 < T.pathCoverNumber from hp)] at bound
  omega

/-- The numerator is bounded by total domination times the regularizing factor. -/
theorem regularized (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) :=
  regularized_of_additive hT hn (additive T hT hn)

/-- The original two-path variant, including one-path covers. -/
theorem two_paths (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  have h := additive T hT hn
  split at h <;> omega

/-- The ratio in precisely the real-valued form stated by WOWII. -/
theorem conjecture372 (hT : T.IsTree) (hn : 2 < Fintype.card α) (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber := by
  have hp' : 1 ≤ T.pathCoverNumber - 1 := by omega
  have bound := regularized T hT (by omega)
  rw [max_eq_right hp'] at bound
  have pos : (0 : ℝ) < (T.pathCoverNumber : ℝ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < T.pathCoverNumber by omega)
  apply (div_le_iff₀ pos).mpr
  have cast : ((T.pathCoverNumber - 1 : ℕ) : ℝ) = (T.pathCoverNumber : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ T.pathCoverNumber),Nat.cast_one]
  rw [← cast]
  exact_mod_cast bound

end WOWII.Solution
