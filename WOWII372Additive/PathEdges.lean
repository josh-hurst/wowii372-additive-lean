/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import WOWII372Additive.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-!
# Path-cover edge subgraph bridge for finite trees

Given a finite tree `T : SimpleGraph α` and a vertex-disjoint path cover `P`
(`T.IsPathCover P`), define `T.pathCoverSubgraph P` to be the subgraph of `T`
keeping precisely those edges of `T` whose two endpoints lie in a common part
`s ∈ P`.

Because `T` is a tree, an edge of `T` has both endpoints on a path `p` iff it is
an edge of `p`. Consequently:

* `SimpleGraph.pathCoverSubgraph_le`: `T.pathCoverSubgraph P ≤ T`;
* `SimpleGraph.pathCoverSubgraph_isAcyclic`: `(T.pathCoverSubgraph P).IsAcyclic`;
* `SimpleGraph.pathCoverSubgraph_degree_le_two`: every vertex has degree at most `2`
  in `T.pathCoverSubgraph P`;
* `SimpleGraph.pathCoverSubgraph_card_edgeFinset_add_card`:
  `(T.pathCoverSubgraph P).edgeFinset.card + P.card = Fintype.card α`;
* `SimpleGraph.pathCoverSubgraph_card_sdiff_edgeFinset_add_one`:
  `(T.edgeFinset \ (T.pathCoverSubgraph P).edgeFinset).card + 1 = P.card`;
* `SimpleGraph.exists_pathSubgraph_of_isPathCover`: existential bundle using
  classical decidability on the produced subgraph `H`.
-/

namespace SimpleGraph

section PathHelpers

variable {α : Type*} {G : SimpleGraph α}

/-- In a path, at most one edge is incident to the start vertex. -/
private lemma path_start_unique_edge {a b u₁ u₂ : α} {p : G.Walk a b}
    (hp : p.IsPath) (h₁ : s(a, u₁) ∈ p.edges) (h₂ : s(a, u₂) ∈ p.edges) :
    u₁ = u₂ := by
  cases p with
  | nil => simp at h₁
  | @cons _ c _ h q =>
      rw [Walk.cons_isPath_iff] at hp
      have key : ∀ u : α, s(a, u) ∈ (Walk.cons h q).edges → u = c := by
        intro u hu
        rw [Walk.edges_cons, List.mem_cons] at hu
        rcases hu with heq | hmem
        · rcases Sym2.eq_iff.mp heq with ⟨-, huc⟩ | ⟨hac, -⟩
          · exact huc
          · exact absurd hac h.ne
        · exact absurd (Walk.fst_mem_support_of_mem_edges q hmem) hp.2
      rw [key u₁ h₁, key u₂ h₂]

/-- In a path, at most two edges are incident to any fixed vertex `w`: among
any three vertices joined to `w` by edges of the path, two coincide. -/
private lemma path_incident_edges_le_two {a b w u₁ u₂ u₃ : α} {p : G.Walk a b}
    (hp : p.IsPath) (h₁ : s(w, u₁) ∈ p.edges) (h₂ : s(w, u₂) ∈ p.edges)
    (h₃ : s(w, u₃) ∈ p.edges) :
    u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
  induction p with
  | nil => simp at h₁
  | @cons x c y h q ih =>
      by_cases hwx : w = x
      · subst hwx
        exact Or.inl (path_start_unique_edge hp h₁ h₂)
      · rw [Walk.cons_isPath_iff] at hp
        have key : ∀ u : α, s(w, u) ∈ (Walk.cons h q).edges →
            (u = x ∧ w = c) ∨ s(w, u) ∈ q.edges := by
          intro u hu
          rw [Walk.edges_cons, List.mem_cons] at hu
          rcases hu with heq | hmem
          · rcases Sym2.eq_iff.mp heq with ⟨hwx', -⟩ | ⟨hwc, hux⟩
            · exact absurd hwx' hwx
            · exact Or.inl ⟨hux, hwc⟩
          · exact Or.inr hmem
        rcases key u₁ h₁ with ⟨hu₁, hwc⟩ | m₁
        · rcases key u₂ h₂ with ⟨hu₂, -⟩ | m₂
          · exact Or.inl (hu₁.trans hu₂.symm)
          · rcases key u₃ h₃ with ⟨hu₃, -⟩ | m₃
            · exact Or.inr (Or.inl (hu₁.trans hu₃.symm))
            · subst hwc
              exact Or.inr (Or.inr (path_start_unique_edge hp.1 m₂ m₃))
        · rcases key u₂ h₂ with ⟨hu₂, hwc⟩ | m₂
          · rcases key u₃ h₃ with ⟨hu₃, -⟩ | m₃
            · exact Or.inr (Or.inr (hu₂.trans hu₃.symm))
            · subst hwc
              exact Or.inr (Or.inl (path_start_unique_edge hp.1 m₁ m₃))
          · rcases key u₃ h₃ with ⟨-, hwc⟩ | m₃
            · subst hwc
              exact Or.inl (path_start_unique_edge hp.1 m₁ m₂)
            · exact ih hp.1 m₁ m₂ m₃

/-- A path visiting `a` and `b` contains a subpath between `a` and `b` (in one
of the two directions) whose edges lie in the original path. -/
private lemma exists_subpath_edges_subset [DecidableEq α]
    {x y a b : α} {p : G.Walk x y} (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support) :
    (∃ q : G.Walk a b, q.IsPath ∧ q.edges ⊆ p.edges) ∨
    (∃ q : G.Walk b a, q.IsPath ∧ q.edges ⊆ p.edges) := by
  by_cases hbt : b ∈ (p.takeUntil a ha).support
  · exact Or.inr ⟨(p.takeUntil a ha).dropUntil b hbt, (hp.takeUntil ha).dropUntil hbt,
      List.Subset.trans ((p.takeUntil a ha).edges_dropUntil_subset_edges hbt)
        (p.edges_takeUntil_subset_edges ha)⟩
  · have hbd : b ∈ (p.dropUntil a ha).support := by
      have h2 : b ∈ ((p.takeUntil a ha).append (p.dropUntil a ha)).support := by
        rw [p.take_spec ha]
        exact hb
      rcases (Walk.mem_support_append_iff _ _).mp h2 with hcase | hcase
      · exact absurd hcase hbt
      · exact hcase
    exact Or.inl ⟨(p.dropUntil a ha).takeUntil b hbd, (hp.dropUntil ha).takeUntil hbd,
      List.Subset.trans ((p.dropUntil a ha).edges_takeUntil_subset_edges hbd)
        (p.edges_dropUntil_subset_edges ha)⟩

/-- In a tree, the unique path between two adjacent vertices is the single edge. -/
private lemma tree_isPath_eq_cons_nil (hG : G.IsTree) {a b : α} (hab : G.Adj a b)
    {q : G.Walk a b} (hq : q.IsPath) :
    q = Walk.cons hab Walk.nil := by
  obtain ⟨_, -, huniq⟩ := hG.existsUnique_path a b
  exact (huniq q hq).trans
    (huniq (Walk.cons hab Walk.nil) (Walk.IsPath.nil.cons (by simp [hab.ne]))).symm

/-- In a tree, any tree edge connecting two vertices on a path `p` is an edge of `p`. -/
private lemma tree_edge_mem_path_edges [DecidableEq α] (hG : G.IsTree)
    {a b x y : α} (hab : G.Adj a b)
    {p : G.Walk x y} (hp : p.IsPath) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    s(a, b) ∈ p.edges := by
  rcases exists_subpath_edges_subset hp ha hb with ⟨q, hq, hqe⟩ | ⟨q, hq, hqe⟩
  · have heq := tree_isPath_eq_cons_nil hG hab hq
    apply hqe
    rw [heq]
    simp
  · have heq := tree_isPath_eq_cons_nil hG hab.symm hq
    have hmem : s(b, a) ∈ p.edges := by
      apply hqe
      rw [heq]
      simp
    rwa [Sym2.eq_swap] at hmem

end PathHelpers

section PathCoverSubgraph

variable {α : Type*}

/-- The subgraph of `T` consisting of all edges of `T` whose endpoints lie in a
common part of `P`. When `T` is a tree and `P` is a path cover of `T`, these are
precisely the edges of the paths witnessing `P`. -/
def pathCoverSubgraph (T : SimpleGraph α) (P : Finset (Finset α)) : SimpleGraph α where
  Adj a b := T.Adj a b ∧ ∃ s ∈ P, a ∈ s ∧ b ∈ s
  symm := ⟨fun _ _ ⟨hab, s, hs, ha, hb⟩ => ⟨hab.symm, s, hs, hb, ha⟩⟩
  loopless := ⟨fun _ ⟨haa, _⟩ => T.loopless.irrefl _ haa⟩

@[simp]
theorem pathCoverSubgraph_adj (T : SimpleGraph α) (P : Finset (Finset α)) (a b : α) :
    (pathCoverSubgraph T P).Adj a b ↔ T.Adj a b ∧ ∃ s ∈ P, a ∈ s ∧ b ∈ s :=
  Iff.rfl

instance pathCoverSubgraph.instDecidableRelAdj [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (P : Finset (Finset α)) :
    DecidableRel (pathCoverSubgraph T P).Adj :=
  fun a b => inferInstanceAs (Decidable (T.Adj a b ∧ ∃ s ∈ P, a ∈ s ∧ b ∈ s))

theorem pathCoverSubgraph_le (T : SimpleGraph α) (P : Finset (Finset α)) :
    pathCoverSubgraph T P ≤ T :=
  fun _ _ h => h.1

theorem pathCoverSubgraph_isAcyclic {T : SimpleGraph α} (hT : T.IsTree)
    (P : Finset (Finset α)) :
    (pathCoverSubgraph T P).IsAcyclic :=
  hT.isAcyclic.anti (pathCoverSubgraph_le T P)

/-- In a tree with a path cover `P`, every vertex has degree at most `2` in
`T.pathCoverSubgraph P`. -/
theorem pathCoverSubgraph_degree_le_two [Fintype α] [DecidableEq α]
    {T : SimpleGraph α} (hT : T.IsTree)
    {P : Finset (Finset α)} (hP : T.IsPathCover P)
    (v : α) [Fintype ((pathCoverSubgraph T P).neighborSet v)] :
    (pathCoverSubgraph T P).degree v ≤ 2 := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  have hv_union : v ∈ P.biUnion id := hcov (Finset.mem_univ v)
  obtain ⟨s, hsP, hvs⟩ := Finset.mem_biUnion.mp hv_union
  obtain ⟨x, y, p, hp, hsup⟩ := hpaths s hsP
  have hvp : v ∈ p.support := by
    change v ∈ s at hvs
    rw [hsup, List.mem_toFinset] at hvs
    exact hvs
  have hmem_edge : ∀ u ∈ (pathCoverSubgraph T P).neighborFinset v, s(v, u) ∈ p.edges := by
    intro u hu
    rw [mem_neighborFinset, pathCoverSubgraph_adj] at hu
    rcases hu with ⟨hvu, s', hs'P, hvs', hus'⟩
    have hs_eq : s' = s := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj s' hs'P s hsP hne) hvs' hvs
    subst hs_eq
    have hup : u ∈ p.support := by
      rw [hsup, List.mem_toFinset] at hus'
      exact hus'
    exact tree_edge_mem_path_edges hT hvu hp hvp hup
  rw [← card_neighborFinset_eq_degree]
  by_contra hgt
  have h2 : 2 < ((pathCoverSubgraph T P).neighborFinset v).card := Nat.lt_of_not_ge hgt
  obtain ⟨u₁, u₂, u₃, h1, h2', h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp h2
  rcases path_incident_edges_le_two hp (hmem_edge u₁ h1) (hmem_edge u₂ h2') (hmem_edge u₃ h3) with
    h | h | h
  · exact h12 h
  · exact h13 h
  · exact h23 h

/-- In a tree with a path cover `P`, the edges of `T` inside a part `s ∈ P`
are precisely the edges of any witnessing path `p` for `s`, so there are
`s.card - 1` of them (stated additively without subtraction). -/
private lemma card_partEdges_add_one [Fintype α] [DecidableEq α]
    {T : SimpleGraph α} [Fintype T.edgeSet] (hT : T.IsTree)
    {s : Finset α} {u v : α} {p : T.Walk u v}
    (hp : p.IsPath) (hsup : s = p.support.toFinset) :
    (T.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card + 1 = s.card := by
  have heq : T.edgeFinset.filter (fun e => e.toFinset ⊆ s) = p.edges.toFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, List.mem_toFinset]
      constructor
      · rintro ⟨hab, hsub⟩
        have ha : a ∈ p.support := by
          have : a ∈ s := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b))
          rwa [hsup, List.mem_toFinset] at this
        have hb : b ∈ p.support := by
          have : b ∈ s := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right a b))
          rwa [hsup, List.mem_toFinset] at this
        exact tree_edge_mem_path_edges hT hab hp ha hb
      · intro hmem
        refine ⟨p.edges_subset_edgeSet hmem, ?_⟩
        intro z hz
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rw [hsup, List.mem_toFinset]
        rcases hz with rfl | rfl
        · exact p.fst_mem_support_of_mem_edges hmem
        · exact p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ hmem)
  rw [heq, hsup, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    List.toFinset_card_of_nodup hp.support_nodup, Walk.length_edges, Walk.length_support]

/-- In a tree with a path cover `P`, the number of retained path edges plus
`P.card` equals the order of the tree. -/
theorem pathCoverSubgraph_card_edgeFinset_add_card [Fintype α] [DecidableEq α]
    {T : SimpleGraph α} (hT : T.IsTree)
    {P : Finset (Finset α)} (hP : T.IsPathCover P)
    [Fintype (pathCoverSubgraph T P).edgeSet] :
    (pathCoverSubgraph T P).edgeFinset.card + P.card = Fintype.card α := by
  classical
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  let partEdges : Finset α → Finset (Sym2 α) :=
    fun s => T.edgeFinset.filter (fun e => e.toFinset ⊆ s)
  have hH_eq : (pathCoverSubgraph T P).edgeFinset = P.biUnion partEdges := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, pathCoverSubgraph_adj, Finset.mem_biUnion,
        partEdges, Finset.mem_filter]
      constructor
      · rintro ⟨hab, s, hsP, ha, hb⟩
        refine ⟨s, hsP, hab, ?_⟩
        intro z hz
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;> assumption
      · rintro ⟨s, hsP, hab, hsub⟩
        exact ⟨hab, s, hsP,
          hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b)),
          hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right a b))⟩
  have hpart_disj : Set.PairwiseDisjoint (P : Set (Finset α)) partEdges := by
    intro s₁ hs₁ s₂ hs₂ hne
    change Disjoint (partEdges s₁) (partEdges s₂)
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    induction e using Sym2.ind with
    | _ a b =>
      have ha₁ : a ∈ s₁ :=
        (Finset.mem_filter.mp he₁).2 (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b))
      have ha₂ : a ∈ s₂ :=
        (Finset.mem_filter.mp he₂).2 (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b))
      exact Finset.disjoint_left.mp (hdisj s₁ hs₁ s₂ hs₂ hne) ha₁ ha₂
  have hP_disj : Set.PairwiseDisjoint (P : Set (Finset α)) id := by
    intro s₁ hs₁ s₂ hs₂ hne
    exact hdisj s₁ hs₁ s₂ hs₂ hne
  have hbiUnion_univ : P.biUnion id = Finset.univ :=
    Finset.Subset.antisymm (Finset.subset_univ _) hcov
  have hsum_parts : ∑ s ∈ P, ((partEdges s).card + 1) = ∑ s ∈ P, s.card := by
    refine Finset.sum_congr rfl fun s hsP => ?_
    obtain ⟨u, v, p, hp, hsup⟩ := hpaths s hsP
    exact card_partEdges_add_one hT hp hsup
  calc
    (pathCoverSubgraph T P).edgeFinset.card + P.card
        = (P.biUnion partEdges).card + P.card := by rw [hH_eq]
    _ = (∑ s ∈ P, (partEdges s).card) + ∑ _s ∈ P, 1 := by
          rw [Finset.card_biUnion hpart_disj, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ s ∈ P, ((partEdges s).card + 1) := by rw [Finset.sum_add_distrib]
    _ = ∑ s ∈ P, s.card := hsum_parts
    _ = (P.biUnion id).card := (Finset.card_biUnion hP_disj).symm
    _ = (Finset.univ : Finset α).card := by rw [hbiUnion_univ]
    _ = Fintype.card α := Finset.card_univ

/-- In a tree with a path cover `P`, the number of tree edges outside
`T.pathCoverSubgraph P` plus `1` equals `P.card`. -/
theorem pathCoverSubgraph_card_sdiff_edgeFinset_add_one [Fintype α] [DecidableEq α]
    {T : SimpleGraph α} (hT : T.IsTree)
    {P : Finset (Finset α)} (hP : T.IsPathCover P)
    [Fintype T.edgeSet] [Fintype (pathCoverSubgraph T P).edgeSet] :
    (T.edgeFinset \ (pathCoverSubgraph T P).edgeFinset).card + 1 = P.card := by
  have hsub : (pathCoverSubgraph T P).edgeFinset ⊆ T.edgeFinset :=
    edgeFinset_mono (pathCoverSubgraph_le T P)
  have hsdiff :
      (T.edgeFinset \ (pathCoverSubgraph T P).edgeFinset).card +
        (pathCoverSubgraph T P).edgeFinset.card = T.edgeFinset.card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left,
      Finset.sdiff_union_of_subset hsub]
  have htree : T.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
  have hpath : (pathCoverSubgraph T P).edgeFinset.card + P.card = Fintype.card α :=
    pathCoverSubgraph_card_edgeFinset_add_card hT hP
  omega

open Classical in
/-- Bundled existential bridge for finite trees: given `hT : T.IsTree` and
`hP : T.IsPathCover P`, there exists a subgraph `H ≤ T` with maximum degree at
most `2` such that `(T.edgeFinset \ H.edgeFinset).card + 1 = P.card`. -/
theorem exists_pathSubgraph_of_isPathCover [Fintype α] [DecidableEq α]
    {T : SimpleGraph α} [Fintype T.edgeSet]
    (hT : T.IsTree) {P : Finset (Finset α)} (hP : T.IsPathCover P) :
    ∃ H : SimpleGraph α,
      H ≤ T ∧
      (∀ v, H.degree v ≤ 2) ∧
      (T.edgeFinset \ H.edgeFinset).card + 1 = P.card :=
  ⟨pathCoverSubgraph T P,
    pathCoverSubgraph_le T P,
    fun v => by convert pathCoverSubgraph_degree_le_two hT hP v,
    by convert pathCoverSubgraph_card_sdiff_edgeFinset_add_one hT hP⟩

end PathCoverSubgraph

end SimpleGraph
