module
import Std

/-!
A finite rooted tree is made by joining the roots of disjoint trees by one edge.
Every vertex carries its membership bit in D. Each edge carries a deletion bit.
The theorem constructs an actual vertex cover. Its order is at most |D| on
paths and at most |D| + (#deleted edges) - 1 as soon as an edge was deleted.
The proof is structural induction with a finite, kernel-checked table.
-/

@[expose] public section
namespace WOWII.TreeCover

def bit : Bool → Nat | false => 0 | true => 1

inductive Tree where
  | vertex (inD : Bool)
  | join (cut : Bool) (left right : Tree)

namespace Tree

def member : Tree → Bool
  | .vertex d => d
  | .join _ l _ => l.member

def rootDominated : Tree → Bool
  | .vertex _ => false
  | .join _ l r => l.rootDominated || r.member

/-- All vertices except possibly the root have a neighbor in D. -/
def innerDominated : Tree → Prop
  | .vertex _ => True
  | .join _ l r => l.innerDominated ∧ r.innerDominated ∧
      (r.rootDominated || l.member) = true

def keptDegree : Tree → Nat
  | .vertex _ => 0
  | .join cut l _ => l.keptDegree + bit (!cut)

/-- The edges kept for the path partition have degree at most two. -/
def pathsOK : Tree → Prop
  | .vertex _ => True
  | .join cut l r => l.pathsOK ∧ r.pathsOK ∧
      l.keptDegree + bit (!cut) ≤ 2 ∧ r.keptDegree + bit (!cut) ≤ 2

private theorem degree_le_two (t : Tree) (h : t.pathsOK) : t.keptDegree ≤ 2 := by
  cases t with
  | vertex => exact Nat.zero_le 2
  | join _ _ _ => exact h.2.2.1

def domSize : Tree → Nat
  | .vertex d => bit d
  | .join _ l r => l.domSize + r.domSize

def cuts : Tree → Nat
  | .vertex _ => 0
  | .join cut l r => l.cuts + r.cuts + bit cut

private def anyCut : Tree → Bool
  | .vertex _ => false
  | .join cut l r => l.anyCut || r.anyCut || cut

private theorem anyCut_iff (t : Tree) : t.anyCut = true ↔ 0 < t.cuts := by
  induction t with
  | vertex => simp [anyCut, cuts]
  | join cut l r il ir =>
    cases cut <;> simp [anyCut, cuts, bit, il, ir] <;> omega

end Tree

/-- A subset of the vertices, with a membership bit at each vertex. -/
inductive Selection : Tree → Type where
  | one {d : Bool} (take : Bool) : Selection (.vertex d)
  | pair {cut l r} (s : Selection l) (t : Selection r) : Selection (.join cut l r)

namespace Selection

def root : {t : Tree} → Selection t → Bool
  | _, .one a => a
  | _, .pair l _ => l.root

def size : {t : Tree} → Selection t → Nat
  | _, .one a => bit a
  | _, .pair l r => l.size + r.size

/-- At least one end of every edge is selected, including deleted path edges. -/
def covers : {t : Tree} → Selection t → Prop
  | _, .one _ => True
  | _, .pair l r => l.covers ∧ r.covers ∧ (l.root = true ∨ r.root = true)

end Selection
namespace Tree

/-- One extra vertex may be needed to require the root in the constructed cover. -/
private def extra : Tree → Bool
  | .vertex _ => true
  | .join _ l r => l.extra && !r.extra

private def cost : Tree → Nat
  | .vertex _ => 0
  | .join _ l r => l.cost + r.cost + bit (l.extra && r.extra)

private def takeLeft (force lExtra rExtra : Bool) := force || !lExtra || rExtra

private def choose : (t : Tree) → Bool → Selection t
  | .vertex _, force => .one force
  | .join _ l r, force =>
    let take := takeLeft force l.extra r.extra
    .pair (l.choose take) (r.choose (!take))

private theorem choose_spec (t : Tree) (force : Bool) :
    (t.choose force).covers ∧ (force = true → (t.choose force).root = true) := by
  induction t generalizing force with
  | vertex => exact ⟨True.intro, id⟩
  | join cut l r il ir =>
    let take := takeLeft force l.extra r.extra
    obtain ⟨lc, lr⟩ := il take
    obtain ⟨rc, rr⟩ := ir (!take)
    refine ⟨⟨lc, rc, ?_⟩, ?_⟩
    · cases h : take with
      | false => exact Or.inr (rr (by simp [h]))
      | true => exact Or.inl (lr h)
    · intro h
      exact lr (by simp [take, takeLeft, h])

private theorem choose_size (t : Tree) (force : Bool) :
    (t.choose force).size = t.cost + bit (force && t.extra) := by
  induction t generalizing force with
  | vertex d => simp [choose, Selection.size, extra, cost]
  | join cut l r il ir =>
    simp only [choose, Selection.size, il, ir, cost, extra]
    cases force <;> cases hl : l.extra <;> cases hr : r.extra <;>
      simp [takeLeft, bit] <;> omega

private structure State where
  member : Bool
  dominated : Bool
  degree : Nat
  cut : Bool
  extra : Bool

private def state (t : Tree) : State :=
  ⟨t.member, t.rootDominated, t.keptDegree, t.anyCut, t.extra⟩

private def joined (l r : State) (cut : Bool) : State :=
  ⟨l.member, l.dominated || r.member, l.degree + bit (!cut),
    l.cut || r.cut || cut, l.extra && !r.extra⟩

/-- Additive change in cover size minus dominating-set size minus cuts. -/
private def increment (l r : State) (cut : Bool) : Int :=
  (bit (l.extra && r.extra) : Int) - bit cut

private def weight (t : Tree) : Int := (t.cost : Int) - t.domSize - t.cuts

private theorem weight_join (cut : Bool) (l r : Tree) :
    (join cut l r).weight = l.weight + r.weight + increment l.state r.state cut := by
  simp [weight, cost, domSize, cuts, increment, state]
  omega

/-- These are upper bounds on the weight at an open root. An absent entry marks
an unreachable state. Rows within each member/dominated pair use degree, then
the cut bit, then the extra-cover-cost bit, in ascending order. -/
private def potential (s : State) : Option Int :=
  let row : List (Option Int) :=
    match s.member, s.dominated with
    | false, false => [none, some 0, some (-1), some (-1), some 0, some 0, some 0, some (-1), some 0, some 0, some 0, some (-1)]
    | false, true  => [none, none, some (-1), some (-1), some 0, some (-1), some (-1), some (-1), some 0, some (-1), some (-1), some (-1)]
    | true, false  => [none, some (-1), some (-1), some (-2), some 0, some (-1), some (-1), some (-1), some 0, some (-1), some 0, some (-1)]
    | true, true   => [none, none, some (-2), some (-2), some (-1), some (-1), some (-1), some (-2), some 0, some (-1), some (-1), some (-1)]
  (row[4 * s.degree + 2 * bit s.cut + bit s.extra]?).join

private def validTransition (l r : State) (cut : Bool) : Bool :=
  (r.dominated || l.member) &&
    decide (l.degree + bit (!cut) ≤ 2) && decide (r.degree + bit (!cut) ≤ 2)

private def tableCheck (l r : State) (cut : Bool) : Bool :=
  if validTransition l r cut then
    match potential l, potential r with
    | some a, some b =>
      match potential (joined l r cut) with
      | some c => decide (a + b + increment l r cut ≤ c)
      | none => false
    | _, _ => true
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_all :
    ∀ (i d : Bool) (k : Fin 3) (c e j f : Bool) (m : Fin 3) (b g cut : Bool),
    tableCheck ⟨i,d,k,c,e⟩ ⟨j,f,m,b,g⟩ cut = true := by decide +kernel

private theorem certified (t : Tree) (hp : t.pathsOK) (hd : t.innerDominated) :
    ∃ a, potential t.state = some a ∧ t.weight ≤ a := by
  induction t with
  | vertex d =>
    cases d
    · exact ⟨0, rfl, by decide⟩
    · exact ⟨-1, rfl, by decide⟩
  | join cut l r il ir =>
    obtain ⟨lp, rp, lk, rk⟩ := hp
    obtain ⟨ld, rd, dom⟩ := hd
    obtain ⟨a, ha, la⟩ := il lp ld
    obtain ⟨b, hb, rb⟩ := ir rp rd
    have ck : tableCheck l.state r.state cut = true :=
      check_all _ _ ⟨l.keptDegree, by have := degree_le_two l lp; omega⟩ _ _
        _ _ ⟨r.keptDegree, by have := degree_le_two r rp; omega⟩ _ _ _
    have hv : validTransition l.state r.state cut = true := by
      simp [validTransition, state, dom, lk, rk]
    unfold tableCheck at ck
    rw [ite_eq_left hv, ha, hb] at ck
    cases hc : potential (joined l.state r.state cut) with
    | none => simp [hc] at ck
    | some c =>
      have le : a + b + increment l.state r.state cut ≤ c := by simpa [hc] using ck
      refine ⟨c, hc, ?_⟩
      rw [weight_join]
      omega

private def closedBound (cut : Bool) : Int := if cut then -1 else 0

private theorem closed :
    ∀ (i : Bool) (k : Fin 3) (c e : Bool),
    (potential ⟨i,true,k,c,e⟩).all (fun a => decide (a ≤ closedBound c)) = true := by
  decide +kernel

/-- For every finite tree in the root-joining presentation, any total dominating
set and any choice of deleted edges leaving degrees at most two yield a vertex
cover S. With no deleted edge, |S| ≤ |D|. With p−1>0 deleted edges,
|S| ≤ |D| + p − 2. All cardinalities count actual selected vertices or edges. -/
theorem exists_vertex_cover (t : Tree) (hp : t.pathsOK)
    (hd : t.innerDominated) (hr : t.rootDominated = true) :
    ∃ s : Selection t, s.covers ∧
      s.size + (if 0 < t.cuts then 1 else 0) ≤ t.domSize + t.cuts := by
  obtain ⟨a, ha, hweight⟩ := certified t hp hd
  have all := closed t.member ⟨t.keptDegree, by have := degree_le_two t hp; omega⟩ t.anyCut t.extra
  unfold state at ha
  rw [hr] at ha
  simp [ha] at all
  refine ⟨t.choose false, (choose_spec t false).1, ?_⟩
  rw [choose_size]
  simp only [Bool.false_and, bit, Nat.add_zero]
  unfold weight at hweight
  cases hc : t.anyCut with
  | false =>
    have hz : ¬ 0 < t.cuts := fun h => by simpa [hc] using ((anyCut_iff t).mpr h)
    simp [hc, closedBound] at all
    simp [hz]
    omega
  | true =>
    have hz := (anyCut_iff t).mp hc
    simp [hc, closedBound] at all
    simp [hz]
    omega

end Tree

/-- Unmarked finite tree, used to minimize the three invariants independently. -/
inductive Shape where
  | vertex
  | join (left right : Shape)

namespace Shape

def VertexSet : Shape → Type
  | .vertex => Bool
  | .join l r => l.VertexSet × r.VertexSet

def CutSet : Shape → Type
  | .vertex => Unit
  | .join l r => Bool × l.CutSet × r.CutSet

def order : Shape → Nat
  | .vertex => 1
  | .join l r => l.order + r.order

def size : (s : Shape) → s.VertexSet → Nat
  | .vertex, v => bit v
  | .join l r, v => l.size v.1 + r.size v.2

def selectedRoot : (s : Shape) → s.VertexSet → Bool
  | .vertex, v => v
  | .join l _, v => l.selectedRoot v.1

def isCover : (s : Shape) → s.VertexSet → Prop
  | .vertex, _ => True
  | .join l r, v => l.isCover v.1 ∧ r.isCover v.2 ∧
      (l.selectedRoot v.1 = true ∨ r.selectedRoot v.2 = true)

def allVertices : (s : Shape) → s.VertexSet
  | .vertex => true
  | .join l r => (l.allVertices, r.allVertices)

def allCuts : (s : Shape) → s.CutSet
  | .vertex => ()
  | .join l r => (true, l.allCuts, r.allCuts)

def mark : (s : Shape) → s.VertexSet → s.CutSet → Tree
  | .vertex, v, _ => .vertex v
  | .join l r, v, e => .join e.1 (l.mark v.1 e.2.1) (r.mark v.2 e.2.2)

def isTotalDominating (s : Shape) (v : s.VertexSet) : Prop :=
  let t := s.mark v s.allCuts
  t.innerDominated ∧ t.rootDominated = true

def isPathPartition (s : Shape) (e : s.CutSet) : Prop :=
  (s.mark s.allVertices e).pathsOK

def pathCount (s : Shape) (e : s.CutSet) : Nat := (s.mark s.allVertices e).cuts + 1

private theorem marks_vertex (s : Shape) (v : s.VertexSet) (e e' : s.CutSet) :
    (s.mark v e).member = (s.mark v e').member ∧
    (s.mark v e).rootDominated = (s.mark v e').rootDominated ∧
    ((s.mark v e).innerDominated ↔ (s.mark v e').innerDominated) ∧
    (s.mark v e).domSize = s.size v := by
  induction s with
  | vertex => exact ⟨rfl,rfl,Iff.rfl,rfl⟩
  | join l r il ir =>
    obtain ⟨a,b,c,d⟩ := il v.1 e.2.1 e'.2.1
    obtain ⟨f,g,h,j⟩ := ir v.2 e.2.2 e'.2.2
    simp only [mark, Tree.member, Tree.rootDominated, Tree.innerDominated, Tree.domSize, size]
    simp [a,b,c,d,f,g,h,j]

private theorem marks_edge (s : Shape) (v v' : s.VertexSet) (e : s.CutSet) :
    (s.mark v e).keptDegree = (s.mark v' e).keptDegree ∧
    ((s.mark v e).pathsOK ↔ (s.mark v' e).pathsOK) ∧
    (s.mark v e).cuts = (s.mark v' e).cuts := by
  induction s with
  | vertex => exact ⟨rfl,Iff.rfl,rfl⟩
  | join l r il ir =>
    obtain ⟨a,b,c⟩ := il v.1 v'.1 e.2.1
    obtain ⟨d,f,g⟩ := ir v.2 v'.2 e.2.2
    simp [mark, Tree.keptDegree, Tree.pathsOK, Tree.cuts, a,b,c,d,f,g]

private theorem cover_transfer (s : Shape) (v : s.VertexSet) (e : s.CutSet)
    (w : Selection (s.mark v e)) :
    ∃ a : s.VertexSet, (s.isCover a ↔ w.covers) ∧
      s.selectedRoot a = w.root ∧ s.size a = w.size := by
  induction s with
  | vertex =>
    cases w with
    | one a => exact ⟨a,Iff.rfl,rfl,rfl⟩
  | join l r il ir =>
    cases w with
    | pair wl wr =>
      obtain ⟨x,xc,xr,xn⟩ := il _ _ wl
      obtain ⟨y,yc,yr,yn⟩ := ir _ _ wr
      exact ⟨(x,y), by simp only [isCover, Selection.covers, xc, yc, xr, yr],
        xr, by simp only [size, Selection.size, xn, yn]⟩

/-- A minimum cardinality is attained, allowing arbitrary predicates on Nat. -/
theorem min_exists {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases less : ∃ m, m < n ∧ P m
    · obtain ⟨m,lt,hm⟩ := less
      exact ih m lt hm
    · exact ⟨n, hn, fun m hm => Nat.le_of_not_gt (fun lt => less ⟨m,lt,hm⟩)⟩

noncomputable def minimum (P : Nat → Prop) : Nat := by
  classical
  exact if h : ∃ n, P n then (min_exists h).choose else 0

private theorem minimum_spec {P : Nat → Prop} (h : ∃ n, P n) :
    P (minimum P) ∧ ∀ m, P m → minimum P ≤ m := by
  simpa only [minimum, dite_eq_left h] using (min_exists h).choose_spec

noncomputable def vertexCoverNumber (s : Shape) : Nat :=
  minimum fun n => ∃ v, s.isCover v ∧ s.size v = n

noncomputable def totalDominationNumber (s : Shape) : Nat :=
  minimum fun n => ∃ v, s.isTotalDominating v ∧ s.size v = n

noncomputable def pathCoverNumber (s : Shape) : Nat :=
  minimum fun n => ∃ e, s.isPathPartition e ∧ s.pathCount e = n

private theorem full_root (s : Shape) : (s.mark s.allVertices s.allCuts).member = true := by
  induction s with
  | vertex => rfl
  | join l r il _ => exact il

private theorem full_dom (s : Shape) : (s.mark s.allVertices s.allCuts).innerDominated := by
  induction s with
  | vertex => trivial
  | join l r il ir => exact ⟨il,ir,by simp [allVertices, allCuts, full_root l]⟩

private theorem full_paths (s : Shape) :
    (s.mark s.allVertices s.allCuts).pathsOK ∧
      (s.mark s.allVertices s.allCuts).keptDegree = 0 := by
  induction s with
  | vertex => exact ⟨True.intro, rfl⟩
  | join l r il ir =>
    exact ⟨⟨il.1,ir.1,by simp [allVertices,allCuts,bit,il.2],by simp [allVertices,allCuts,bit,ir.2]⟩,
      by simpa [mark, allVertices, allCuts, Tree.keptDegree, bit] using il.2⟩

private theorem root_full_dom (s : Shape) (h : 2 ≤ s.order) : s.isTotalDominating s.allVertices := by
  refine ⟨full_dom s, ?_⟩
  cases s with
  | vertex => simp [order] at h
  | join l r => simp [mark, allVertices, allCuts, Tree.rootDominated, full_root r]

/-- With all three invariants minimized independently on an unlabelled tree:
at p = 1 the bound is tau ≤ gamma, and at p ≥ 2 it is tau ≤ gamma + p - 2. -/
theorem additive (s : Shape) (h : 2 ≤ s.order) :
    s.vertexCoverNumber + (if 1 < s.pathCoverNumber then 1 else 0) ≤
      s.totalDominationNumber + (s.pathCoverNumber - 1) := by
  obtain ⟨⟨v,hv,vn⟩,_⟩ := @minimum_spec
    (fun n => ∃ v, s.isTotalDominating v ∧ s.size v = n)
    ⟨_,s.allVertices,root_full_dom s h,rfl⟩
  obtain ⟨⟨e,he,en⟩,_⟩ := @minimum_spec
    (fun n => ∃ e, s.isPathPartition e ∧ s.pathCount e = n)
    ⟨_,s.allCuts,(full_paths s).1,rfl⟩
  change s.size v = s.totalDominationNumber at vn
  change (s.mark s.allVertices e).cuts + 1 = s.pathCoverNumber at en
  obtain ⟨_,root_eq,dom_iff,ds⟩ := marks_vertex s v e s.allCuts
  obtain ⟨_,path_iff,cs⟩ := marks_edge s v s.allVertices e
  obtain ⟨w,wc,wb⟩ := Tree.exists_vertex_cover (s.mark v e)
    (path_iff.mpr he) (dom_iff.mpr hv.1) (root_eq.trans hv.2)
  obtain ⟨a,ac,_,az⟩ := cover_transfer s v e w
  have vc : s.vertexCoverNumber ≤ s.size a :=
    (@minimum_spec (fun n => ∃ a, s.isCover a ∧ s.size a = n)
      ⟨_,a,ac.mpr wc,rfl⟩).2 _ ⟨a,ac.mpr wc,rfl⟩
  rw [ds,vn,cs] at wb
  split at wb <;> split <;> omega

theorem two_paths (s : Shape) (h : 2 ≤ s.order) (hp : s.pathCoverNumber ≤ 2) :
    s.vertexCoverNumber ≤ s.totalDominationNumber := by
  have hb := additive s h
  split at hb <;> omega

theorem regularized (s : Shape) (h : 2 ≤ s.order) :
    s.vertexCoverNumber ≤ s.totalDominationNumber * max 1 (s.pathCoverNumber - 1) := by
  have hb := additive s h
  by_cases p : s.pathCoverNumber ≤ 2
  · have hh := two_paths s h p
    have hx : max 1 (s.pathCoverNumber - 1) = 1 := by omega
    simpa [hx] using hh
  · have hg : 1 ≤ s.totalDominationNumber := by
      obtain ⟨⟨v,hv,vn⟩,_⟩ := @minimum_spec
        (fun n => ∃ v, s.isTotalDominating v ∧ s.size v = n)
        ⟨_,s.allVertices,root_full_dom s h,rfl⟩
      change s.size v = s.totalDominationNumber at vn
      have pos (t : Tree) : (t.member = true → 0 < t.domSize) ∧
          (t.rootDominated = true → 0 < t.domSize) := by
        induction t with
        | vertex d => cases d <;> simp [Tree.member, Tree.rootDominated, Tree.domSize, bit]
        | join cut l r il ir =>
          simp only [Tree.member, Tree.rootDominated, Tree.domSize, Bool.or_eq_true]
          constructor
          · intro hx; have := il.1 hx; omega
          · rintro (hx | hy)
            · have := il.2 hx; omega
            · have := ir.1 hy; omega
      have hh := (pos (s.mark v s.allCuts)).2 hv.2
      have ds := (marks_vertex s v s.allCuts s.allCuts).2.2.2
      omega
    have hx : max 1 (s.pathCoverNumber - 1) = (s.pathCoverNumber - 2) + 1 := by omega
    rw [hx, Nat.mul_add, Nat.mul_one]
    have lo := Nat.mul_le_mul_right (s.pathCoverNumber - 2) hg
    simp only [Nat.one_mul] at lo
    split at hb <;> omega

/-- The original ratio on its positive-denominator domain, after clearing
the denominator. The expression is entirely in natural numbers. -/
theorem positive_denominator (s : Shape) (h : 2 < s.order) (hp : 2 ≤ s.pathCoverNumber) :
    s.vertexCoverNumber ≤ s.totalDominationNumber * (s.pathCoverNumber - 1) := by
  have hh := regularized s (by omega)
  have hx : max 1 (s.pathCoverNumber - 1) = s.pathCoverNumber - 1 := by omega
  simpa only [hx] using hh


end Shape

end WOWII.TreeCover
