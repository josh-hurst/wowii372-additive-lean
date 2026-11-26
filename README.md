# Written on the Wall II, Conjecture 372 — Sharp Additive Tree Bound in Lean 4

An independent Lean 4 / Mathlib formalization proving the **sharp additive tree inequality**
$$\tau(T) \le \gamma_t(T) + p(T) - 2 \qquad (p(T) \ge 2)$$
and, as immediate corollaries, all three upstream statements of **Written on the Wall II Conjecture 372** (E. DeLaViña, Graffiti.pc, 18 February 2009) from [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) (`FormalConjectures/WrittenOnTheWallII/GraphConjecture372.lean`, commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`).

## Main Formalized Results

For any finite simple tree $T$ with vertex cover number $\tau(T) = \text{vertexCoverNum}(T)$, total domination number $\gamma_t(T) = \text{totalDominationNumber}(T)$, and path cover number $p(T) = \text{pathCoverNumber}(T)$ (minimum number of pairwise vertex-disjoint paths partitioning $V(T)$, singletons allowed):

| Declaration (`WrittenOnTheWallII.GraphConjecture372.*`) | Statement |
|---|---|
| `additive_of_two_le` | For $n \ge 2$ and $p(T) \ge 2$: $\tau(T) \le \gamma_t(T) + p(T) - 2$ |
| `conjecture372` | For $n > 2$ and $p(T) \ge 2$: $\tau(T) / (p(T) - 1) \le \gamma_t(T)$ |
| `conjecture372.variants.two_paths` | For $n \ge 2$ and $p(T) \le 2$: $\tau(T) \le \gamma_t(T)$ |
| `conjecture372.variants.regularized` | For $n \ge 2$: $\tau(T) \le \gamma_t(T) \cdot \max(1, p(T) - 1)$ |

For all $\gamma_t \ge 2$ and $p \ge 2$, the additive bound is strictly stronger than the multiplicative WOWII #372 bound whenever $p \ge 3$ (since $\gamma_t(p - 1) - (\gamma_t + p - 2) = (\gamma_t - 1)(p - 2)$). Equality $\tau(T) = \gamma_t(T) + p(T) - 2$ holds for every $p \ge 2$ (witnessed on paper by the 5-vertex spider $(2,1,1)$ for $p = 2$ and the $(6k - 2)$-vertex $T_{10}$-chain family for $p = k + 1 \ge 3$; equality constructions are not formalized in Lean).

## Lean Proof Architecture

Rather than splitting $p \ge 3$ and $p \le 2$ or formalizing quotient trees, the Lean proof establishes the stronger additive bound directly for **every** path partition $P$ and **every** total dominating set $D$:

1. **Finite-state rooted-tree induction ([`WOWII372Additive/TreeCover.lean`](WOWII372Additive/TreeCover.lean)):** Every finite tree with a total dominating subset $D$ and a set of deleted (non-path) edges is represented inductively as binary joins of rooted trees (`Tree.vertex`, `Tree.join`). A finite potential function over a 48-state root summary `(inD, rootDominated, keptDegree ∈ {0,1,2}, anyCut, coverFlag)` is verified across all valid join transitions directly by Lean's kernel, constructing an explicit vertex cover of size at most $|D|$ on paths and at most $|D| + (\text{cuts}) - 1$ whenever at least one edge is cut.
2. **Mathlib tree & path-cover bridges ([`TreeModel.lean`](WOWII372Additive/TreeModel.lean), [`PathEdges.lean`](WOWII372Additive/PathEdges.lean), [`LabeledTree.lean`](WOWII372Additive/LabeledTree.lean)):** Any Mathlib `SimpleGraph.IsTree` on a finite type is shown isomorphic to a rooted binary-join shape (`exists_iso_of_isTree_unrooted`), and any `SimpleGraph.IsPathCover P` yields a spanning subgraph $H \le T$ with $\Delta(H) \le 2$ and $|E(T) \setminus E(H)| + 1 = |P|$.
3. **Minimization & upstream corollaries ([`InvariantBounds.lean`](WOWII372Additive/InvariantBounds.lean), [`Main.lean`](WOWII372Additive/Main.lean), [`Solution.lean`](Solution.lean)):** Minimizing over `IsPathCover` and `IsTotalNDominatingSet` yields `additive_of_two_le`, which immediately implies `regularized`, `two_paths`, and the real-valued quotient `conjecture372` using only `[propext, Quot.sound, Classical.choice]`, with zero `sorry` and zero `native_decide`.

## Provenance & Prior Work

* **Conjecture origin:** E. DeLaViña, *Written on the Wall II: Conjectures of Graffiti.pc*, Conjecture 372 (18 February 2009; August 2009 note settles $p \ge 3$).
* **Prior written preprint:** Jonas J. Gebendorfer, *Total domination and vertex covers of trees covered by two paths: A resolution of Written on the Wall II Conjecture 372 on its defined domain* (`doi:10.13140/RG.2.2.25035.55849`, 28 October 2026). The full text was not read during this development; priority for the stronger additive bound $\tau(T) \le \gamma_t(T) + p(T) - 2$ relative to Gebendorfer's full manuscript and prior domination literature has not been established and is not claimed.
* **Independent earlier Lean formalization:** [`8xp4jtb47i5h/wowii372-lean`](https://github.com/8xp4jtb47i5h/wowii372-lean) (pushed 2026-11-25 17:45 UTC) formalizes the three original WOWII #372 statements via the 2009 $\frac{3}{2}$-bound ($p \ge 3$) and path-position parity ($p \le 2$). Our development was produced independently without consulting that repository and additionally proves `additive_of_two_le`.
* **AI-assisted workflow:** Developed by Josh Hurst using multi-agent orchestration (GPT-6.2 Astra and Gemini 4 Neon in T3 Code), with independent adversarial agent reviews and mechanical verification.

## Verification & Submission

* `Challenge.lean` contains only Mathlib imports, verbatim upstream invariant definitions, and the four compared theorem statements.
* `Solution.lean` proves all four declarations and is verified against `Challenge.lean` via `comparator.json` and `./scripts/verify-comparator.sh`.
* Submissions to the Palomar Registry go to <https://submit.palomar-registry.org/>.

## License

Apache-2.0 (see [`LICENSE`](LICENSE)). Upstream definitions and theorem statements from `google-deepmind/formal-conjectures` retain their Apache-2.0 notices.
