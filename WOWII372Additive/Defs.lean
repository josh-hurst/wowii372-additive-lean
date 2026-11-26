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

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Path Cover and Total Domination Definitions

Verbatim graph invariant definitions from `google-deepmind/formal-conjectures`
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/PathCover.lean` and
`Domination.lean` at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`).
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
