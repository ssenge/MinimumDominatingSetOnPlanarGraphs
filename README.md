# Minimum Dominating Set on Planar Graphs

New results on the distributed approximation of minimum dominating set on planar graphs in the
LOCAL model. In [1], deterministic constant-round algorithms with ratio 7 + ε on planar graphs and
(1 + ε)-approximations in a number of rounds that depends only on ε were given, together with a
list of open problems. This repository works on three of them: the round exponent of the
(7 + ε)-approximation (Open Problem 4), the dependence of the number of rounds on ε (Open Problem
3), and the best ratio of constant-round algorithms on planar graphs of girth at least g (Open
Problem 7). Each folder holds one topic with its proofs, Lean files and scripts.

## Results

| Open problem of [1] | Before | Now | Status | Details |
|---|---|---|---|---|
| OP4: exponent κ in the (c/ε)^κ rounds of the planar (7 + ε)-approximation | κ ≈ 25.81 [1] | κ < 5.89 | Proved. Core inequalities machine-checked in Lean 4 + Mathlib | [op4](op4/) |
| OP3: rounds of the (1 + ε)-approximations (fractional, and randomized with expected size) | upper bound (c/ε)^25.81 [1], dependence on ε open | at least 1/ε − 4 rounds on every minor-closed class that contains all paths; Θ(1/ε) on forests and on outerplanar graphs | Lower bound machine-checked in Lean. Forests and outerplanar graphs proved on paper, with the combinatorial steps checked in Lean | [op4](op4/) |
| OP7: best ratio of deterministic constant-round algorithms on planar graphs of girth ≥ g | (3g − 2)/(g − 2): 13/3 for g = 5, 4 for g = 6, 19/5 for g = 7; lower bound 3 | 3.51 for g = 5, 3.23 for g = 6, 3.16 for g = 7, 3.13 for g = 8, 3.09 for g = 10, 3.04 for every g ≥ 30, 3.03 for every g ≥ 1000; better than [1] for 5 ≤ g ≤ 101 | **Not peer-reviewed.** Certificate LP feasible in exact rational arithmetic; written soundness argument, charge-level instance checks and AI referee passes | [op7](op7/) |

**Round exponent (OP4).** A different choice of the stars in the clustering step of [1] (random
centres) lowers the exponent of 1/ε from 25.81 to below 5.89 on planar graphs. The ratio stays
7 + ε. At ε = 0.01 the term (1/ε)^κ drops from about 10^52 to about 10^12. The paper is
[`op4/paper/main.pdf`](op4/paper/main.pdf) (*Random Centres and the ε-Dependence of
Constant-Round Planar Domination*). It refers to the tag `arxiv-v1`, where the files of `op4/`
sit at the top level of the repository.

**Dependence on ε (OP3).** Paths show that the (1 + ε)-approximations of [1] need at least
1/ε − 4 rounds, even when the algorithm knows the graph. On forests and on outerplanar graphs,
O(1/ε) rounds suffice with unbounded degrees, so the answer there is Θ(1/ε).

**Large girth (OP7).** A rule based on identifiers (rule R13) replaces threshold rounding on the
vertices that the fractional solution leaves undominated. Its ratio is bounded by a discharging
argument whose constants come from a linear program. That LP is feasible below (3g − 2)/(g − 2)
for every g from 5 to 101 and below 13/4 for every g ≥ 6, checked in exact rational arithmetic.
For g ≥ 1000 it gives 3.03, against the lower bound 3. The argument that each LP row is a
valid local inequality is in [`op7/SOUNDNESS.md`](op7/SOUNDNESS.md), and a script recomputes all
charges on adversarial instances. No person has reviewed the argument, so the ratios are not
claimed as theorems.

## References

1. S. Amiri and S. Siebertz. Almost optimal constant-round approximation of dominating set in graph
   classes with excluded minors. arXiv:2610.09618, 2026.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop
and check proofs, to write the simulation scripts, the Lean formalization and the certificate LPs,
and to draft the text.
