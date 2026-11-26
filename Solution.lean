/-
Copyright 2026 Josh Hurst.

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

public import WOWII372Additive

@[expose] public section

/-!
# Proved Solution

Supplies complete Lean 4 proofs of the sharp additive bound `additive_of_two_le`
and all three WOWII Conjecture 372 statements declared in `Challenge.lean`,
using only the permitted standard axioms (`propext`, `Quot.sound`, `Classical.choice`).
-/

namespace WrittenOnTheWallII.GraphConjecture372

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)

theorem additive_of_two_le (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber + T.pathCoverNumber - 2 :=
  WOWII.Solution.additive_of_two_le T hT hn hp

theorem conjecture372 (hT : T.IsTree) (hn : 2 < Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber :=
  WOWII.Solution.conjecture372 T hT hn hp

theorem conjecture372.variants.two_paths (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber :=
  WOWII.Solution.two_paths T hT hn hp

theorem conjecture372.variants.regularized (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) :=
  WOWII.Solution.regularized T hT hn

end WrittenOnTheWallII.GraphConjecture372
