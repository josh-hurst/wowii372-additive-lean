module
public import WOWII372Additive.TreeCover
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Mathlib `SimpleGraph` Representation for `WOWII.TreeCover.Shape`

This module equips `WOWII.TreeCover.Shape` with a finite vertex type `Shape.Vertex`,
a distinguished root `Shape.root`, and a simple graph `Shape.graph : SimpleGraph s.Vertex`
formed by disjoint union plus a single edge between the two subtree roots at every `.join`.

Main results:
* `Shape.card_vertex`: `Fintype.card s.Vertex = s.order`.
* `Shape.graph_isTree`: every `s.graph` is a `SimpleGraph.IsTree`.
* `Shape.exists_iso_of_isTree`: every finite Mathlib tree `G` with a chosen root `x`
  is isomorphic to `s.graph` for some `s : Shape` via an isomorphism mapping `s.root` to `x`.
-/

@[expose] public section

namespace WOWII.TreeCover.Shape

open SimpleGraph

/-- Finite vertex type of a tree shape: a singleton at `.vertex` and a disjoint sum at `.join`. -/
abbrev Vertex : Shape → Type
  | .vertex => Unit
  | .join l r => l.Vertex ⊕ r.Vertex

/-- Distinguished root vertex of a tree shape. -/
def root : (s : Shape) → s.Vertex
  | .vertex => ()
  | .join l _ => .inl l.root

instance instDecidableEqVertex : (s : Shape) → DecidableEq s.Vertex
  | .vertex => inferInstanceAs (DecidableEq Unit)
  | .join l r =>
    letI := l.instDecidableEqVertex
    letI := r.instDecidableEqVertex
    inferInstanceAs (DecidableEq (l.Vertex ⊕ r.Vertex))

instance instFintypeVertex : (s : Shape) → Fintype s.Vertex
  | .vertex => inferInstanceAs (Fintype Unit)
  | .join l r =>
    letI := l.instFintypeVertex
    letI := r.instFintypeVertex
    inferInstanceAs (Fintype (l.Vertex ⊕ r.Vertex))

instance instInhabitedVertex (s : Shape) : Inhabited s.Vertex := ⟨s.root⟩

@[simp]
theorem card_vertex (s : Shape) : Fintype.card s.Vertex = s.order := by
  induction s with
  | vertex =>
    exact Fintype.card_unique
  | join l r ihl ihr =>
    change Fintype.card (l.Vertex ⊕ r.Vertex) = l.order + r.order
    rw [Fintype.card_sum, ihl, ihr]

/-- Underlying adjacency relation for `Shape.graph`. -/
def graphAdj : (s : Shape) → s.Vertex → s.Vertex → Prop
  | .vertex, _, _ => False
  | .join l _, .inl u, .inl v => l.graphAdj u v
  | .join _ r, .inr u, .inr v => r.graphAdj u v
  | .join l r, .inl u, .inr v => u = l.root ∧ v = r.root
  | .join l r, .inr u, .inl v => u = r.root ∧ v = l.root

theorem graphAdj_symm {s : Shape} {u v : s.Vertex} : s.graphAdj u v → s.graphAdj v u := by
  induction s with
  | vertex => exact id
  | join l r ihl ihr =>
    cases u <;> cases v
    · exact ihl
    · rintro ⟨hu, hv⟩; exact ⟨hv, hu⟩
    · rintro ⟨hu, hv⟩; exact ⟨hv, hu⟩
    · exact ihr

theorem graphAdj_irrefl (s : Shape) (u : s.Vertex) : ¬ s.graphAdj u u := by
  induction s with
  | vertex => exact id
  | join l r ihl ihr =>
    cases u with
    | inl u => exact ihl u
    | inr u => exact ihr u

/-- The simple graph realized by a tree shape: disjoint subtrees linked by one root-to-root edge. -/
def graph (s : Shape) : SimpleGraph s.Vertex where
  Adj := s.graphAdj
  symm := ⟨fun _ _ h => graphAdj_symm h⟩
  loopless := ⟨graphAdj_irrefl s⟩

instance instDecidableRelGraphAdj : (s : Shape) → DecidableRel s.graph.Adj
  | .vertex => fun _ _ => isFalse id
  | .join l r =>
    letI := l.instDecidableRelGraphAdj
    letI := r.instDecidableRelGraphAdj
    fun
    | .inl u, .inl v => inferInstanceAs (Decidable (l.graph.Adj u v))
    | .inr u, .inr v => inferInstanceAs (Decidable (r.graph.Adj u v))
    | .inl u, .inr v => inferInstanceAs (Decidable (u = l.root ∧ v = r.root))
    | .inr u, .inl v => inferInstanceAs (Decidable (u = r.root ∧ v = l.root))

@[simp]
theorem graph_vertex_adj (u v : Shape.vertex.Vertex) : ¬ Shape.vertex.graph.Adj u v := id

@[simp]
theorem graph_vertex_eq_bot : Shape.vertex.graph = ⊥ := by
  ext u v
  simp

@[simp]
theorem graph_join_adj_inl_inl {l r : Shape} {u v : l.Vertex} :
    (l.join r).graph.Adj (.inl u) (.inl v) ↔ l.graph.Adj u v := Iff.rfl

@[simp]
theorem graph_join_adj_inr_inr {l r : Shape} {u v : r.Vertex} :
    (l.join r).graph.Adj (.inr u) (.inr v) ↔ r.graph.Adj u v := Iff.rfl

@[simp]
theorem graph_join_adj_inl_inr {l r : Shape} {u : l.Vertex} {v : r.Vertex} :
    (l.join r).graph.Adj (.inl u) (.inr v) ↔ u = l.root ∧ v = r.root := Iff.rfl

@[simp]
theorem graph_join_adj_inr_inl {l r : Shape} {u : r.Vertex} {v : l.Vertex} :
    (l.join r).graph.Adj (.inr u) (.inl v) ↔ u = r.root ∧ v = l.root := Iff.rfl

theorem graph_join_adj_roots (l r : Shape) :
    (l.join r).graph.Adj (.inl l.root) (.inr r.root) := ⟨rfl, rfl⟩

/-- Left subtree embedding into a joined graph. -/
def inlEmbedding (l r : Shape) : l.graph ↪g (l.join r).graph where
  toFun := Sum.inl
  inj' _ _ h := Sum.inl.inj h
  map_rel_iff' := Iff.rfl

/-- Right subtree embedding into a joined graph. -/
def inrEmbedding (l r : Shape) : r.graph ↪g (l.join r).graph where
  toFun := Sum.inr
  inj' _ _ h := Sum.inr.inj h
  map_rel_iff' := Iff.rfl

theorem order_eq_card_of_iso {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : Shape} (e : s.graph ≃g G) : s.order = Fintype.card V := by
  rw [← card_vertex s, e.card_eq]

/-! ### Forward direction: every `Shape.graph` is a tree -/

theorem graph_connected (s : Shape) : s.graph.Connected := by
  induction s with
  | vertex => exact SimpleGraph.Connected.of_subsingleton
  | join l r ihl ihr =>
    refine ⟨fun a b => ?_⟩
    have hlink : (l.join r).graph.Reachable (.inl l.root) (.inr r.root) :=
      (graph_join_adj_roots l r).reachable
    cases a with
    | inl u =>
      cases b with
      | inl v => exact (ihl u v).map (inlEmbedding l r).toHom
      | inr v =>
        exact ((ihl u l.root).map (inlEmbedding l r).toHom).trans <|
          hlink.trans ((ihr r.root v).map (inrEmbedding l r).toHom)
    | inr u =>
      cases b with
      | inl v =>
        exact ((ihr u r.root).map (inrEmbedding l r).toHom).trans <|
          hlink.symm.trans ((ihl l.root v).map (inlEmbedding l r).toHom)
      | inr v => exact (ihr u v).map (inrEmbedding l r).toHom

private theorem isCycle_induce {V : Type*} {G : SimpleGraph V} {S : Set V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) (hS : ∀ w ∈ c.support, w ∈ S) :
    (c.induce S hS).IsCycle := by
  have hmap : (c.induce S hS).map (SimpleGraph.Embedding.induce S).toHom = c :=
    SimpleGraph.Walk.map_induce c hS
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · have hedges : (c.induce S hS).edges.map (Sym2.map Subtype.val) = c.edges := by
      have := congrArg SimpleGraph.Walk.edges hmap
      rw [SimpleGraph.Walk.edges_map] at this
      exact this
    exact List.Nodup.of_map _ (hedges.symm ▸ hc.edges_nodup)
  · intro hnil
    apply hc.ne_nil
    rw [← hmap, hnil]
    rfl
  · have hs : (c.induce S hS).support.map Subtype.val = c.support := by
      have := congrArg SimpleGraph.Walk.support hmap
      rw [SimpleGraph.Walk.support_map] at this
      exact this
    have hsupp : (c.induce S hS).support.tail.map Subtype.val = c.support.tail := by
      rw [← hs, List.map_tail]
    exact List.Nodup.of_map _ (hsupp.symm ▸ hc.support_nodup)

theorem graph_isAcyclic (s : Shape) : s.graph.IsAcyclic := by
  induction s with
  | vertex => exact SimpleGraph.IsAcyclic.of_subsingleton
  | join l r ihl ihr =>
    let G := (l.join r).graph
    let G₀ := G.deleteEdges {s(Sum.inl l.root, Sum.inr r.root)}
    have hG₀_inl_inl : ∀ (a b : l.Vertex), G₀.Adj (.inl a) (.inl b) ↔ l.graph.Adj a b := by
      intro a b
      rw [SimpleGraph.deleteEdges_adj]
      simp [G]
    have hG₀_inr_inr : ∀ (a b : r.Vertex), G₀.Adj (.inr a) (.inr b) ↔ r.graph.Adj a b := by
      intro a b
      rw [SimpleGraph.deleteEdges_adj]
      simp [G]
    have hG₀_inl_inr : ∀ (a : l.Vertex) (b : r.Vertex), ¬ G₀.Adj (.inl a) (.inr b) := by
      intro a b h
      rw [SimpleGraph.deleteEdges_adj] at h
      rcases h with ⟨⟨rfl, rfl⟩, hne⟩
      exact hne rfl
    have hG₀_inr_inl : ∀ (a : r.Vertex) (b : l.Vertex), ¬ G₀.Adj (.inr a) (.inl b) := by
      intro a b h
      exact hG₀_inl_inr b a h.symm
    have hsplit : G = G₀ ⊔ SimpleGraph.edge (Sum.inl l.root) (Sum.inr r.root) := by
      ext a b
      rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      cases a <;> cases b
      · simp [G, hG₀_inl_inl]
      · simp [G, hG₀_inl_inr]
      · simp [G, hG₀_inr_inl]
      · simp [G, hG₀_inr_inr]
    have hadj_side : ∀ {a b : (l.join r).Vertex}, G₀.Adj a b → (a.isLeft ↔ b.isLeft) := by
      intro a b hab
      cases a <;> cases b
      · simp
      · exact (hG₀_inl_inr _ _ hab).elim
      · exact (hG₀_inr_inl _ _ hab).elim
      · simp
    have hreach_side : ∀ {a b : (l.join r).Vertex}, G₀.Reachable a b → (a.isLeft ↔ b.isLeft) := by
      rintro a b ⟨p⟩
      induction p with
      | nil => rfl
      | cons h _ ih => exact (hadj_side h).trans ih
    have hnotreach : ¬ G₀.Reachable (.inl l.root) (.inr r.root) := by
      intro h
      have := hreach_side h
      simp at this
    have hG₀_acyc : G₀.IsAcyclic := by
      intro v c hc
      have hside : ∀ w ∈ c.support, w.isLeft ↔ v.isLeft := fun w hw =>
        (hreach_side (c.takeUntil w hw).reachable).symm
      cases v with
      | inl u =>
        let SL : Set (l.join r).Vertex := {x | x.isLeft = true}
        have hSL : ∀ w ∈ c.support, w ∈ SL := fun w hw => by
          simpa [SL] using (hside w hw).mpr rfl
        let isoL : G₀.induce SL ≃g l.graph :=
          { toFun := fun ⟨x, hx⟩ => match x, hx with | .inl a, _ => a
            invFun := fun a => ⟨.inl a, rfl⟩
            left_inv := by
              rintro ⟨a | a, ha⟩
              · rfl
              · simp [SL] at ha
            right_inv := fun _ => rfl
            map_rel_iff' := by
              rintro ⟨a | a, ha⟩ ⟨b | b, hb⟩
              · exact (hG₀_inl_inl a b).symm
              · simp [SL] at hb
              · simp [SL] at ha
              · simp [SL] at ha }
        exact (isoL.isAcyclic_iff.mpr ihl) (c.induce SL hSL) (isCycle_induce hc hSL)
      | inr u =>
        let SR : Set (l.join r).Vertex := {x | x.isLeft = false}
        have hSR : ∀ w ∈ c.support, w ∈ SR := fun w hw => by
          simpa [SR] using (hside w hw).not.mpr (by simp)
        let isoR : G₀.induce SR ≃g r.graph :=
          { toFun := fun ⟨x, hx⟩ => match x, hx with | .inr a, _ => a
            invFun := fun a => ⟨.inr a, rfl⟩
            left_inv := by
              rintro ⟨a | a, ha⟩
              · simp [SR] at ha
              · rfl
            right_inv := fun _ => rfl
            map_rel_iff' := by
              rintro ⟨a | a, ha⟩ ⟨b | b, hb⟩
              · simp [SR] at ha
              · simp [SR] at ha
              · simp [SR] at hb
              · exact (hG₀_inr_inr a b).symm }
        exact (isoR.isAcyclic_iff.mpr ihr) (c.induce SR hSR) (isCycle_induce hc hSR)
    change G.IsAcyclic
    rw [hsplit]
    exact hG₀_acyc.sup_edge_of_not_reachable hnotreach

theorem graph_isTree (s : Shape) : s.graph.IsTree :=
  ⟨graph_connected s, graph_isAcyclic s⟩

/-! ### Representation theorem: every finite rooted Mathlib tree arises from a `Shape` -/

private theorem exists_iso_of_isTree_aux :
    ∀ (n : ℕ) {V : Type u} [Fintype V] {G : SimpleGraph V},
      Fintype.card V = n → G.IsTree → ∀ x : V,
      ∃ (s : Shape) (e : s.graph ≃g G), e s.root = x := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro V _ G hcard hG x
    classical
    by_cases hsub : Subsingleton V
    · refine ⟨.vertex,
        { toFun := fun _ => x
          invFun := fun _ => ()
          left_inv := fun _ => rfl
          right_inv := fun v => Subsingleton.elim x v
          map_rel_iff' := by
            intro a b
            exact ⟨fun h => (G.loopless.irrefl x h).elim, False.elim⟩ },
        rfl⟩
    · have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨y, hxy⟩ := hG.connected.preconnected.exists_adj_of_nontrivial x
      let H : SimpleGraph V := G.deleteEdges {s(x, y)}
      let cx : H.ConnectedComponent := H.connectedComponentMk x
      let cy : H.ConnectedComponent := H.connectedComponentMk y
      have hbr : ¬ H.Reachable x y :=
        SimpleGraph.isBridge_iff.mp
          (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hxy)
      have hcx_ne_cy : cx ≠ cy := fun h =>
        hbr (SimpleGraph.ConnectedComponent.eq.mp h)
      have hy_not_cx : y ∉ cx.supp := fun hy => hcx_ne_cy hy.symm
      have hx_not_cy : x ∉ cy.supp := fun hx => hcx_ne_cy hx
      have hdisj : ∀ v : V, v ∈ cx.supp → v ∉ cy.supp := fun v h1 h2 =>
        hcx_ne_cy (h1.symm.trans h2)
      have hcover : ∀ v : V, v ∈ cx.supp ∨ v ∈ cy.supp := by
        intro v
        obtain ⟨p, hp⟩ := hG.connected.exists_isPath x v
        by_cases he : s(x, y) ∈ p.edges
        · right
          cases p with
          | nil => simp at he
          | @cons _ z _ hxz p' =>
            have hy_supp : y ∈ (SimpleGraph.Walk.cons hxz p').support :=
              (SimpleGraph.Walk.cons hxz p').snd_mem_support_of_mem_edges he
            have hzy : y = z := by
              simpa using hG.isAcyclic.eq_snd_of_adj_start hp hxy hy_supp
            subst hzy
            have hnotmem : s(x, y) ∉ p'.edges := by
              have hnd : (s(x, y) :: p'.edges).Nodup := by
                simpa using hp.edges_nodup
              exact (List.nodup_cons.mp hnd).1
            have hreach : H.Reachable y v :=
              SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p', hnotmem⟩
            exact SimpleGraph.ConnectedComponent.eq.mpr hreach.symm
        · left
          have hreach : H.Reachable x v :=
            SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, he⟩
          exact SimpleGraph.ConnectedComponent.eq.mpr hreach.symm
      have hadj_cx : ∀ {u v : V}, u ∈ cx.supp → v ∈ cx.supp → (G.Adj u v ↔ H.Adj u v) := by
        intro u v hu hv
        constructor
        · intro huv
          refine SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hy_not_cx hv
          · exact hy_not_cx hu
        · intro huv
          exact (SimpleGraph.deleteEdges_adj.mp huv).1
      have hadj_cy : ∀ {u v : V}, u ∈ cy.supp → v ∈ cy.supp → (G.Adj u v ↔ H.Adj u v) := by
        intro u v hu hv
        constructor
        · intro huv
          refine SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hx_not_cy hu
          · exact hx_not_cy hv
        · intro huv
          exact (SimpleGraph.deleteEdges_adj.mp huv).1
      have hadj_cx_cy : ∀ {u v : V}, u ∈ cx.supp → v ∈ cy.supp → (G.Adj u v ↔ u = x ∧ v = y) := by
        intro u v hu hv
        constructor
        · intro huv
          by_cases heq : s(u, v) = s(x, y)
          · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨rfl, rfl⟩
            · exact (hy_not_cx hu).elim
          · have huvH : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, heq⟩
            have hxu : H.Reachable x u := (SimpleGraph.ConnectedComponent.eq.mp hu).symm
            have hvy : H.Reachable v y := SimpleGraph.ConnectedComponent.eq.mp hv
            exact (hbr (hxu.trans (huvH.reachable.trans hvy))).elim
        · rintro ⟨rfl, rfl⟩
          exact hxy
      have hadj_cy_cx : ∀ {u v : V}, u ∈ cy.supp → v ∈ cx.supp → (G.Adj u v ↔ u = y ∧ v = x) := by
        intro u v hu hv
        rw [G.adj_comm, hadj_cx_cy hv hu, and_comm]
      have hH_acyc : H.IsAcyclic := hG.isAcyclic.anti (G.deleteEdges_le _)
      have hcx_tree : cx.toSimpleGraph.IsTree := hH_acyc.isTree_connectedComponent cx
      have hcy_tree : cy.toSimpleGraph.IsTree := hH_acyc.isTree_connectedComponent cy
      have hcard_cx : Fintype.card cx < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt hy_not_cx
      have hcard_cy : Fintype.card cy < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt hx_not_cy
      let rx : cx := ⟨x, rfl⟩
      let ry : cy := ⟨y, rfl⟩
      obtain ⟨sl, el, hel⟩ := ih (Fintype.card cx) hcard_cx rfl hcx_tree rx
      obtain ⟨sr, er, her⟩ := ih (Fintype.card cy) hcard_cy rfl hcy_tree ry
      refine ⟨sl.join sr,
        { toFun := fun
            | .inl a => (el a).val
            | .inr b => (er b).val
          invFun := fun v =>
            if hv : v ∈ cx then .inl (el.symm ⟨v, hv⟩)
            else .inr (er.symm ⟨v, (hcover v).resolve_left hv⟩)
          left_inv := by
            rintro (a | b)
            · dsimp only
              rw [dite_eq_left (el a).prop]
              exact congrArg Sum.inl (el.symm_apply_apply a)
            · dsimp only
              have hnot : (er b).val ∉ cx := fun h => hdisj _ h (er b).prop
              rw [dite_eq_right hnot]
              exact congrArg Sum.inr (er.symm_apply_apply b)
          right_inv := by
            intro v
            by_cases hv : v ∈ cx
            · simp [hv]
            · simp [hv]
          map_rel_iff' := by
            rintro (a | a) (b | b)
            · change G.Adj (el a).val (el b).val ↔ sl.graph.Adj a b
              rw [hadj_cx (el a).prop (el b).prop]
              exact el.map_rel_iff
            · change G.Adj (el a).val (er b).val ↔ a = sl.root ∧ b = sr.root
              rw [hadj_cx_cy (el a).prop (er b).prop]
              constructor
              · rintro ⟨ha, hb⟩
                have ha' : el a = el sl.root := by
                  rw [hel]; exact Subtype.ext ha
                have hb' : er b = er sr.root := by
                  rw [her]; exact Subtype.ext hb
                exact ⟨el.injective ha', er.injective hb'⟩
              · rintro ⟨rfl, rfl⟩
                exact ⟨congrArg Subtype.val hel, congrArg Subtype.val her⟩
            · change G.Adj (er a).val (el b).val ↔ a = sr.root ∧ b = sl.root
              rw [hadj_cy_cx (er a).prop (el b).prop]
              constructor
              · rintro ⟨ha, hb⟩
                have ha' : er a = er sr.root := by
                  rw [her]; exact Subtype.ext ha
                have hb' : el b = el sl.root := by
                  rw [hel]; exact Subtype.ext hb
                exact ⟨er.injective ha', el.injective hb'⟩
              · rintro ⟨rfl, rfl⟩
                exact ⟨congrArg Subtype.val her, congrArg Subtype.val hel⟩
            · change G.Adj (er a).val (er b).val ↔ sr.graph.Adj a b
              rw [hadj_cy (er a).prop (er b).prop]
              exact er.map_rel_iff },
        ?_⟩
      exact congrArg Subtype.val hel

/-- Every finite Mathlib tree `G` with chosen root `x` is represented by some `Shape`
via a graph isomorphism mapping `s.root` to `x`. -/
theorem exists_iso_of_isTree
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsTree) (x : V) :
    ∃ (s : Shape) (e : s.graph ≃g G), e s.root = x := by
  have := Fintype.ofFinite V
  exact exists_iso_of_isTree_aux (Fintype.card V) rfl hG x

/-- Unrooted corollary: every finite Mathlib tree is isomorphic to `s.graph` for some `Shape`. -/
theorem exists_iso_of_isTree_unrooted
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ (s : Shape), Nonempty (s.graph ≃g G) := by
  obtain ⟨x⟩ := hG.connected.nonempty
  obtain ⟨s, e, _⟩ := exists_iso_of_isTree hG x
  exact ⟨s, ⟨e⟩⟩

end WOWII.TreeCover.Shape
