module
public import WOWII372Additive.TreeCover
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import WOWII372Additive.Defs

/-! Transport the checked tree bound to a finite labelled representation. -/
@[expose] public section
namespace WOWII.TreeCover
open SimpleGraph

inductive LabeledTree (α : Type*) where
  | vertex (v : α)
  | join (left right : LabeledTree α)

namespace LabeledTree
variable {α : Type*} [DecidableEq α]

def root : LabeledTree α → α
  | .vertex v => v
  | .join l _ => l.root

def nodes : LabeledTree α → Finset α
  | .vertex v => {v}
  | .join l r => l.nodes ∪ r.nodes

def edges : LabeledTree α → Finset (Sym2 α)
  | .vertex _ => ∅
  | .join l r => insert s(l.root, r.root) (l.edges ∪ r.edges)

def uniqueLabels : LabeledTree α → Prop
  | .vertex _ => True
  | .join l r => l.uniqueLabels ∧ r.uniqueLabels ∧ Disjoint l.nodes r.nodes

theorem root_mem (t : LabeledTree α) : t.root ∈ t.nodes := by
  induction t with
  | vertex v => simp [root, nodes]
  | join l r hl _ => exact Finset.mem_union_left _ hl

theorem ends {t : LabeledTree α} {a b : α} (h : s(a,b) ∈ t.edges) :
    a ∈ t.nodes ∧ b ∈ t.nodes := by
  induction t generalizing a b with
  | vertex => simp [edges] at h
  | join l r il ir =>
    simp only [edges, Finset.mem_insert, Finset.mem_union, Sym2.eq_iff] at h
    simp only [nodes, Finset.mem_union]
    rcases h with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | h | h
    · exact ⟨Or.inl l.root_mem, Or.inr r.root_mem⟩
    · exact ⟨Or.inr r.root_mem, Or.inl l.root_mem⟩
    · exact ⟨Or.inl (il h).1, Or.inl (il h).2⟩
    · exact ⟨Or.inr (ir h).1, Or.inr (ir h).2⟩

private theorem edge_disjoint {l r : LabeledTree α} (h : Disjoint l.nodes r.nodes) :
    Disjoint l.edges r.edges := by
  apply Finset.disjoint_left.mpr
  intro e
  induction e using Sym2.inductionOn with
  | _ a b => exact fun x y => Finset.disjoint_left.mp h (ends x).1 (ends y).1

private theorem cross_new {l r : LabeledTree α} (h : Disjoint l.nodes r.nodes) :
    s(l.root,r.root) ∉ l.edges ∪ r.edges := by
  intro e
  rcases Finset.mem_union.mp e with el | er
  · exact Finset.disjoint_left.mp h (ends el).2 r.root_mem
  · exact Finset.disjoint_left.mp h l.root_mem (ends er).1

variable (D : Finset α) (H : SimpleGraph α) [DecidableRel H.Adj]

def decorate : LabeledTree α → Tree
  | .vertex v => .vertex (decide (v ∈ D))
  | .join l r => .join (decide (¬ H.Adj l.root r.root)) (decorate l) (decorate r)

private theorem member_eq (t : LabeledTree α) :
    (t.decorate D H).member = decide (t.root ∈ D) := by
  induction t with
  | vertex => rfl
  | join l _ ih _ => exact ih

private theorem root_dom_iff (t : LabeledTree α) (hu : t.uniqueLabels) :
    (t.decorate D H).rootDominated = true ↔ ∃ w ∈ D, s(t.root,w) ∈ t.edges := by
  induction t with
  | vertex => simp [decorate, Tree.rootDominated, edges]
  | join l r il _ =>
    obtain ⟨lu,_,sep⟩ := hu
    have hx := Finset.disjoint_left.mp sep l.root_mem
    simp only [decorate,Tree.rootDominated,Bool.or_eq_true, il lu, member_eq,
      decide_eq_true_eq,root,edges,Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro (⟨w,hw,he⟩ | hw)
      · exact ⟨w,hw,Or.inr (Or.inl he)⟩
      · exact ⟨r.root,hw,Or.inl rfl⟩
    · rintro ⟨w,hw,eq | he | he⟩
      · have : w = r.root := Sym2.congr_right.mp eq
        exact Or.inr (this ▸ hw)
      · exact Or.inl ⟨w,hw,he⟩
      · exact False.elim (hx (ends he).1)

private theorem inner_dom (t : LabeledTree α) (hu : t.uniqueLabels)
    (h : ∀ v ∈ t.nodes, v ≠ t.root → ∃ w ∈ D, s(v,w) ∈ t.edges) :
    (t.decorate D H).innerDominated := by
  induction t with
  | vertex => trivial
  | join l r il ir =>
    obtain ⟨lu,ru,sep⟩ := hu
    have disj := Finset.disjoint_left.mp sep
    have localDom (v : α) (hv : v ∈ l.nodes) (ne : v ≠ l.root) :
        ∃ w ∈ D, s(v,w) ∈ l.edges := by
      obtain ⟨w,hw,he⟩ := h v (Finset.mem_union_left _ hv) ne
      rcases Finset.mem_insert.mp he with eq | other
      · rcases Sym2.eq_iff.mp eq with ⟨vv,_⟩ | ⟨vv,_⟩
        · exact False.elim (ne vv)
        · exact False.elim (disj hv (vv ▸ r.root_mem))
      · rcases Finset.mem_union.mp other with el | er
        · exact ⟨w,hw,el⟩
        · exact False.elim (disj hv (ends er).1)
    have rightDom (v : α) (hv : v ∈ r.nodes) :
        (∃ w ∈ D, s(v,w) ∈ r.edges) ∨ (v = r.root ∧ l.root ∈ D) := by
      have ne : v ≠ l.root := fun z => disj l.root_mem (z ▸ hv)
      obtain ⟨w,hw,he⟩ := h v (Finset.mem_union_right _ hv) ne
      rcases Finset.mem_insert.mp he with eq | other
      · rcases Sym2.eq_iff.mp eq with ⟨vv,_⟩ | ⟨vv,ww⟩
        · exact False.elim (ne vv)
        · exact Or.inr ⟨vv,ww ▸ hw⟩
      · rcases Finset.mem_union.mp other with el | er
        · exact False.elim (disj (ends el).1 hv)
        · exact Or.inl ⟨w,hw,er⟩
    refine ⟨il lu localDom, ir ru (fun v hv hne =>
      (rightDom v hv).resolve_right (fun b => hne b.1)), ?_⟩
    rw [Bool.or_eq_true,root_dom_iff D H r ru,member_eq,decide_eq_true_eq]
    exact (rightDom r.root r.root_mem).imp_right And.right

private theorem dom_count (t : LabeledTree α) (hu : t.uniqueLabels) :
    (t.decorate D H).domSize = (t.nodes ∩ D).card := by
  induction t with
  | vertex v =>
    by_cases hv : v ∈ D <;> simp [decorate, Tree.domSize, bit, nodes, hv]
  | join l r il ir =>
    obtain ⟨lu,ru,sep⟩ := hu
    rw [nodes,Finset.union_inter_distrib_right,
      Finset.card_union_of_disjoint (sep.mono (Finset.inter_subset_left) (Finset.inter_subset_left))]
    exact congrArg₂ (· + ·) (il lu) (ir ru)

private theorem cut_count (t : LabeledTree α) (hu : t.uniqueLabels) :
    (t.decorate D H).cuts = (t.edges.filter fun e => e ∉ H.edgeSet).card := by
  classical
  induction t with
  | vertex => simp [decorate,Tree.cuts,edges]
  | join l r il ir =>
    obtain ⟨lu,ru,sep⟩ := hu
    have nd := edge_disjoint sep
    have new := cross_new sep
    have dis := nd.mono
      (Finset.filter_subset (fun e => e ∉ H.edgeSet) l.edges)
      (Finset.filter_subset (fun e => e ∉ H.edgeSet) r.edges)
    have fresh : s(l.root,r.root) ∉
        (l.edges.filter fun e => e ∉ H.edgeSet) ∪ (r.edges.filter fun e => e ∉ H.edgeSet) := by
      intro hm
      apply new
      exact Finset.mem_union.mpr ((Finset.mem_union.mp hm).imp
        (fun x => (Finset.mem_filter.mp x).1) (fun x => (Finset.mem_filter.mp x).1))
    by_cases ha : H.Adj l.root r.root <;>
      simp [decorate,Tree.cuts, edges,Finset.filter_insert, Finset.filter_union,
        Finset.card_union_of_disjoint dis, il lu, ir ru, bit, ha, Finset.card_insert_of_notMem fresh]

/-- Neighbors counted at an open root form a subset of its H-neighbors in that piece. -/
private theorem kept_count (t : LabeledTree α) (hu : t.uniqueLabels) :
    (t.decorate D H).keptDegree ≤
      (t.nodes.filter fun v => H.Adj t.root v).card := by
  induction t with
  | vertex => exact Nat.zero_le _
  | join l r il _ =>
    obtain ⟨lu,_,sep⟩ := hu
    have ld := il lu
    have dis := sep.mono (Finset.filter_subset (H.Adj l.root) l.nodes)
      (Finset.filter_subset (H.Adj l.root) r.nodes)
    change (l.decorate D H).keptDegree + bit (!(decide (¬ H.Adj l.root r.root))) ≤
      ((l.nodes ∪ r.nodes).filter (H.Adj l.root)).card
    rw [Finset.filter_union, Finset.card_union_of_disjoint dis]
    by_cases ha : H.Adj l.root r.root
    · have pos := Finset.card_pos.mpr (show (r.nodes.filter (H.Adj l.root)).Nonempty from
        ⟨r.root, Finset.mem_filter.mpr ⟨r.root_mem,ha⟩⟩)
      simpa only [ha, decide_not, decide_true, Bool.not_true, Bool.not_false, bit] using Nat.add_le_add ld pos
    · simpa [ha,bit] using Nat.add_le_add ld (Nat.zero_le ((r.nodes.filter (H.Adj l.root)).card))

variable [Fintype α]

private theorem path_bits (t : LabeledTree α) (hu : t.uniqueLabels) (hH : ∀ v, H.degree v ≤ 2) :
    (t.decorate D H).pathsOK := by
  induction t with
  | vertex => trivial
  | join l r il ir =>
    obtain ⟨lu,ru,sep⟩ := hu
    refine ⟨il lu,ir ru,?_,?_⟩
    all_goals
      have sub (a b : LabeledTree α) (au : a.uniqueLabels) (ab : Disjoint a.nodes b.nodes) :
          (a.decorate D H).keptDegree + bit (decide (H.Adj a.root b.root)) ≤ 2 := by
        let S := a.nodes.filter (H.Adj a.root)
        have kd : (a.decorate D H).keptDegree ≤ S.card := kept_count D H a au
        have incl : S ⊆ H.neighborFinset a.root := by
          intro v hv
          exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hv).2
        have sz := hH a.root
        rw [←SimpleGraph.card_neighborFinset_eq_degree] at sz
        by_cases ha : H.Adj a.root b.root
        · have outside : b.root ∉ S := fun h =>
            Finset.disjoint_left.mp ab (Finset.mem_filter.mp h).1 b.root_mem
          have add := Finset.card_le_card (Finset.insert_subset ((H.mem_neighborFinset _ _).mpr ha) incl)
          rw [Finset.card_insert_of_notMem outside] at add
          simp [ha,bit]; omega
        · have le := Finset.card_le_card incl
          simp [ha,bit]; omega
    · simpa [decide_not] using sub l r lu sep
    · simpa [decide_not, H.adj_comm] using sub r l ru sep.symm

omit [Fintype α] in
private theorem read_cover (t : LabeledTree α) (hu : t.uniqueLabels)
    (s : Selection (t.decorate D H)) (hc : s.covers) :
    ∃ S : Finset α, S ⊆ t.nodes ∧ S.card = s.size ∧
      (s.root = true ↔ t.root ∈ S) ∧
      ∀ a b, s(a,b) ∈ t.edges → a ∈ S ∨ b ∈ S := by
  induction t with
  | vertex v =>
    cases s with
    | one take =>
      cases take
      · exact ⟨∅, Finset.empty_subset _,rfl, by simp [Selection.root], by simp [edges]⟩
      · exact ⟨{v},Finset.Subset.refl _, by simp [Selection.size,bit], by simp [Selection.root,root], by simp [edges]⟩
  | join l r il ir =>
    obtain ⟨lu,ru,sep⟩ := hu
    cases s with
    | pair x y =>
      obtain ⟨xc,yc,xy⟩ := hc
      obtain ⟨A,As,Az,Ar,Ac⟩ := il lu x xc
      obtain ⟨B,Bs,Bz,Br,Bc⟩ := ir ru y yc
      refine ⟨A ∪ B,Finset.union_subset_union As Bs,?_,?_,?_⟩
      · simp [Finset.card_union_of_disjoint (sep.mono As Bs), Az, Bz, Selection.size]
      · have no : l.root ∉ B := fun h => Finset.disjoint_left.mp sep l.root_mem (Bs h)
        simpa [Selection.root,root,no] using Ar
      · intro a b he
        have insA {v : α} (h : v ∈ A) : v ∈ A ∪ B := Finset.mem_union_left _ h
        have insB {v : α} (h : v ∈ B) : v ∈ A ∪ B := Finset.mem_union_right _ h
        rcases Finset.mem_insert.mp he with he | he
        · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact xy.imp (fun h => insA (Ar.mp h)) (fun h => insB (Br.mp h))
          · exact xy.symm.imp (fun h => insB (Br.mp h)) (fun h => insA (Ar.mp h))
        · rcases Finset.mem_union.mp he with he | he
          · exact (Ac _ _ he).imp insA insA
          · exact (Bc _ _ he).imp insB insB

/-- Transfer for any vertex-labelled rooted representation of the actual graph. -/
theorem cover_of_representation {G : SimpleGraph α} [DecidableRel G.Adj]
    (t : LabeledTree α) (hu : t.uniqueLabels) (hv : t.nodes = Finset.univ)
    (he : t.edges = G.edgeFinset) (hd : G.IsTotalDominating (D : Set α))
    (hH : ∀ v, H.degree v ≤ 2) :
    ∃ S : Finset α, G.IsVertexCover (S : Set α) ∧
      S.card + (if 0 < (G.edgeFinset \ H.edgeFinset).card then 1 else 0) ≤
        D.card + (G.edgeFinset \ H.edgeFinset).card := by
  classical
  have dom (v : α) : ∃ w ∈ D, s(v,w) ∈ t.edges := by
    obtain ⟨w,hw,adj⟩ := hd v
    exact ⟨w,hw, he ▸ G.mem_edgeFinset.mpr (show s(v,w) ∈ G.edgeSet from adj)⟩
  have idom := inner_dom D H t hu (fun v _ _ => dom v)
  have rdom := (root_dom_iff D H t hu).mpr (dom t.root)
  obtain ⟨s,sc,b⟩ := Tree.exists_vertex_cover _ (path_bits D H t hu hH) idom rdom
  obtain ⟨S,_,sz,_,cover⟩ := read_cover D H t hu s sc
  have cut := cut_count D H t hu
  have filt : (t.edges.filter fun e => e ∉ H.edgeSet) = G.edgeFinset \ H.edgeFinset := by
    ext e; simp [he]
  rw [filt] at cut
  rw [dom_count D H t hu, hv, Finset.univ_inter, cut] at b
  refine ⟨S,fun a b ab => cover _ _ (he ▸ G.mem_edgeFinset.mpr ab), ?_⟩
  simpa only [sz] using b

end LabeledTree
end WOWII.TreeCover
