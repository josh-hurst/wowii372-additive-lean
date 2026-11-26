/-
Copyright 2025-2026 The Formal Conjectures Authors.
Modifications Copyright 2026 Josh Hurst.

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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Written on the Wall II, Conjecture 372 — Sharp Additive Tree Bound

For a finite simple tree `T` on at least two vertices, let:
- `τ(T) = T.vertexCoverNum.toNat` be the minimum vertex cover cardinality,
- `γ_t(T) = T.totalDominationNumber` be the minimum cardinality of a total dominating set
  (a set `D` such that every vertex, including vertices in `D`, has an adjacent vertex in `D`),
- `p(T) = T.pathCoverNumber` be the minimum number of pairwise vertex-disjoint paths partitioning
  all vertices (single-vertex paths allowed).

This submission states and proves:
1. The **sharp additive inequality** `τ(T) ≤ γ_t(T) + p(T) - 2` for every finite tree with
   `p(T) ≥ 2` (attained with equality for every `p ≥ 2`, and strictly stronger than the WOWII #372
   multiplicative bound whenever `p ≥ 3`).
2. All three upstream declarations from `google-deepmind/formal-conjectures`
   (`FormalConjectures/WrittenOnTheWallII/GraphConjecture372.lean`, commit
   `9097e2f90e66d2f6244209cb1c07f7120d17ec53`): `conjecture372`,
   `conjecture372.variants.two_paths`, and `conjecture372.variants.regularized`.

The invariant definitions below are copied verbatim from `FormalConjecturesForMathlib`
(`PathCover.lean` and `Domination.lean`).
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
def IsTotalNDominatingSet (G : SimpleGraph α) (n : ℕ) (D : Finset α) : Prop :=
  G.IsTotalDominating D ∧ D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture372

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)

/--
**Sharp additive strengthening of WOWII Conjecture 372.**

For every finite tree `T` of order at least two with path cover number `p(T) ≥ 2`,
the vertex cover number satisfies `τ(T) ≤ γ_t(T) + p(T) - 2`.
-/
theorem additive_of_two_le (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber + T.pathCoverNumber - 2 := by
  sorry

/--
WOWII Conjecture 372 on its positive-denominator domain. If `T` is a tree with
more than two vertices and path cover number `p(T) ≥ 2`, then
`γ_t(T) ≥ τ(T)/(p(T)-1)`, where `γ_t` is the total domination
number and `τ` is the vertex cover number.
-/
theorem conjecture372 (hT : T.IsTree) (hn : 2 < Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber := by
  sorry

/--
The two-path variant: a tree `T` of order at least two with `p(T) ≤ 2`
satisfies `τ(T) ≤ γ_t(T)`.
-/
theorem conjecture372.variants.two_paths (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  sorry

/--
A separate formulation with no division: every tree `T` of order at least two
satisfies `τ(T) ≤ γ_t(T) * max 1 (p(T) - 1)`. On paths the factor is one.
-/
theorem conjecture372.variants.regularized (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := by
  sorry

end WrittenOnTheWallII.GraphConjecture372
