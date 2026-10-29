# OP7: Minimum Dominating Set on Planar Graphs of Large Girth

This folder is about Open Problem 7 of [1]: for each g >= 5, find the best approximation
ratio of deterministic constant-round LOCAL algorithms for minimum dominating set on planar graphs
of girth at least g. The known range is [3, (3g-2)/(g-2)]. The lower bound 3 comes from paths, and
the upper bound (13/3 for g = 5, 4 for g = 6) from threshold rounding of a fractional solution [1].

The approach here keeps the fractional solution of [1] for the dense part and replaces threshold
rounding on the rest by a rule based on identifiers (rule R13 below). Its ratio is analysed with a
discharging argument whose constants come from a linear program.

## Status

Please read this before relying on anything here.
- **Nothing here is a theorem yet.** The ratios below are feasible solutions of a certificate LP.
  Feasibility is checked in exact rational arithmetic (`cert_exact.py`). The argument that each
  row family is a valid local inequality is written up in [`SOUNDNESS.md`](SOUNDNESS.md). Two AI
  referee passes found no problem in v7 (the first one found the five flaws of the version before
  it). The three changes of v8 are argued in section 10 of that note; one AI
  referee pass on them found no soundness problem. The four changes of v9 are argued in section
  13 of the same note; one AI referee pass on them found no soundness problem. No person has
  reviewed the argument.
- The type model of the LP has been checked on instances: on adversarial planar girth-5 graphs,
  every local type that occurs is in the LP, and the dual solution it defines satisfies the
  claimed bound.
- The charges themselves have been checked on instances (`charge_check.py`): with the exact
  solution, every vertex and every heavy U-hub ends with at least the certified margin when the
  actual transfers and Euler terms are applied. For g >= 7 this runs on random trees and on
  subdivided planar graphs. For v9 it passed at all nine table values from (5, 3.51) to
  (1000, 3.03).
- The notebook `OP7.md` records every step, including approaches that failed.

## Rule R13

Input: a fractional dominating set x (the (1+eps)-approximation of [1] runs in constant rounds on
planar graphs) and identifiers.
1. Let D1 = {v : x_v >= 1/3}, and let U be the set of vertices not dominated by D1.
2. A hub is a vertex with at least 4 neighbours in U (it may lie in U itself).
   Let U' = U minus N[hubs] and T = idrule(G[U']).
3. Let Z = U minus U' and Q = Z minus N(T). The load of a hub w is a_w = |N(w) ∩ Q|, and a hub
   is heavy if a_w >= 4.
4. The set Q_h consists of the vertices of Q with a heavy hub in their closed neighbourhood.
   Let Q_l = Q minus Q_h and T2 = idrule(G[Q_l]).
5. Every vertex of Q_h without a neighbour in T2 selects a heavy hub of maximum load in its closed
   neighbourhood (smallest identifier on ties).
6. Output D1, T, T2 and the selected hubs.

Here idrule(G[S]) takes the vertices of S that have fewer smaller than larger identifiers among
their S-neighbours, plus every vertex of S with no such neighbour. The rule needs a constant
number of rounds after x is known.

Let LP_U = min x(N[U]) subject to x(N[u]) >= 1 for u in U and 0 <= x <= 1/3. The restriction of x
to N[U] is feasible, so LP_U <= x(V minus D1). If |D minus D1| <= rho LP_U for every U, the ratio
is at most max(3, rho) (1 + eps).

## Results so far (numerical, unproven)

The current certificate LP is `discharge_r13v9.py`. It uses only girth >= 5, except for the Euler
constant C = g/(g-2), which is set by the environment variable `GIRTH`. A certificate for g is
also one for every larger girth, since such graphs have girth >= g.

| girth g | v9 feasible at rho (exact check) | v9 infeasible at rho (float) | v8 (exact check) | known upper bound (3g-2)/(g-2) |
|---|---|---|---|---|
| 5 | 3.51 | 3.50 | 3.52 | 13/3 |
| 6 | 3.23 | 3.22 | 3.24 | 4 |
| 7 | 3.16 | 3.15 | 3.17 | 19/5 |
| 8 | 3.13 | 3.12 | 3.15 | 11/3 |
| 10 | 3.09 | 3.08 | 3.14 | 7/2 |
| 12 | 3.08 | 3.07 | 3.14 | 17/5 |
| 16 | 3.06 | 3.05 | 3.14 | 23/7 |
| 30 | 3.04 | 3.03 | 3.14 | 22/7 |
| 100 | 3.04 (covered by g = 30) | 3.03 | | 149/49 (3.041) |
| 1000 | 3.03 | 3.02 | | 1499/499 (3.004) |

If the certificate is sound, R13 improves the upper bound of [1] for every g from 5 to 101 (the
value 3.04 for g >= 30 is below 3 + 4/(g-2) up to g = 101), and its ratio is below 13/4 for
every g >= 6. For g >= 1000 it is within 0.03 of the lower bound 3, but there [1] is better.

Version 9 changes four things in v8 ([`SOUNDNESS.md`](SOUNDNESS.md), section 13). For g >= 10
the binding rows of v8 were the idrule pattern on G[Q_l] with every vertex a light hub inside U,
which v8 gave no Euler term. In v9 such a hub keeps the part of its Euler budget it does not
return, and receives the returns of neighbouring light hubs inside U. To claim the latter, each
Q_l-slot records whether that neighbour is a light hub inside U, and the transfers are keyed so
that this flag always agrees with the neighbour. Two further Euler families, G[U'] and G[Q_l],
give the idrule parts a density term of their own. At g = 1000 the binding row is now an
isolated Q_l-vertex whose only neighbour in the families is a light hub outside U.

Version 8 changes three things in v7 (section 10). A heavy hub inside U is one entity, so its
vertex part no longer needs a margin of its own. A fourth Euler family on Q_h and the heavy hubs
outside U adds the density of that part. A light hub returns (2 - C)/3 instead of 1/9 to each of
its Q_l-neighbours, which its Euler budget still allows.
The exact check rebuilds every coefficient as a rational, rounds the solution, recomputes the
derived bounds exactly and checks all 267,770 rows with fractions.

The v7 values were first found with `discharge_r13z.py`. Writing out the charge argument showed
five places where a row claimed more than the charges give; v7 fixes them. One of the five makes
`discharge_r13z.py` invalid, not just unproved: on a tree with 10 vertices its solution leaves a
vertex with negative charge. An independent adversarial referee pass (an AI agent) found the same
five problems and nothing further.

When no vertex of U has 4 or more neighbours in U (no U-hubs), the LP `discharge_r13.py` is
feasible at rho = 13/4 for g = 5, with margin 0.0075. It is infeasible at 3.20.

With U-hubs, v7 failed 13/4 on clusters of heavy hubs inside U whose Q-neighbours are all heavy
hubs inside U: a vertex there keeps at most rho/5 after its overclaim share, but a hub selected by
one vertex needs 1. In v8 such a hub and its own vertex part pay together, and the new Euler family
counts the density of the cluster; this is what brings g >= 6 below 13/4. At g = 5 the LP stops
at 3.51 (v9). What is left there is the Euler constant 5/3 of pentagons: with 3/2 in place of
5/3 (unsound, as a probe) the same types give 3.24, the value for g = 6. R13 itself does well on such clusters: its ratio stays at most 1.93 on patches of the
{5,4} tiling with searched identifiers.

In simulations against LP_U, R13 never went above ratio 3.0 on the adversarial batteries (random
planar girth-5 graphs, subdivided triangulations, pentagon grids, hosts with clusters of U-hubs,
{5,4} patches).

## The certificate LP in short

The dual of LP_U is max sum y - (1/3) sum_v (Y(v) - 1)^+, with Y(v) = y(N[v] ∩ U). The certificate
sets y = (1 - eps_t)/3 for every vertex of local type t. Each vertex starts with charge rho y minus
its share of the overclaim, minus 1 if it is in D. Charge then moves along edges between types, and
from vertices of Q_h to the heavy hubs they select or neighbour. Euler terms nu (deg/2 - g/(g-2))
on six subgraphs (Z with all hubs, the same plus U', the heavy hubs inside U, Q_h with the heavy
hubs, G[U'] and G[Q_l]) add the density bound of planar graphs of girth >= g. Every row of the LP says that some local configuration ends with nonnegative charge. The LP
maximizes the smallest margin; a positive margin certifies the ratio rho. Observation 11 in
`OP7.md` lists the rules in detail.

## Reproducing

Python 3 with numpy, scipy (HiGHS) and networkx. Run the commands inside `op7/`. The LP of
`discharge_r13v9.py` has about 75,800 variables and 268,000 rows and takes 10 to 20 minutes and
1 GB.

```bash
GIRTH=10 python3 discharge_r13v9.py 3.09  # prints the max margin; positive means feasible
GIRTH=10 python3 cert_exact.py discharge_r13v9 3.09  # exact rational check of the solution
python3 discharge_r13.py 3.25             # inputs without U-hubs
GIRTH=5 python3 check_r13z.py 4.0 1 20 300  # instance check of the type model
GIRTH=10 MOD=discharge_r13v9 python3 charge_check.py 3.09 1 3 60  # charge-level check (after cert_exact.py)
GIRTH=1000 python3 lp_diag.py discharge_r13v9 3.02 40  # rows with the largest dual weights
python3 pent_growth.py 1 3000             # R13 against LP_U on {5,4} patches
```

## Files

- `OP7.md`: research notebook with all observations, numbers and the plan.
- `SOUNDNESS.md`: why a feasible solution of `discharge_r13v7.py`, `discharge_r13v8.py` or
  `discharge_r13v9.py` proves the bound, row family by row family.
- Certificate LPs: `discharge_r13v9.py` (current, with U-hubs), `discharge_r13v8.py` and
  `discharge_r13v7.py` (previous),
  `discharge_r13.py` (no U-hubs),
  earlier versions `discharge_r13u.py` to `discharge_r13z.py`, `discharge_r12*.py`,
  `discharge_r2.py`, `discharge_h*.py`, `discharge_a2.py` (subcubic idrule, 3.1305), and
  `lp_diag.py`, `cert_exact.py` (exact check).
- Rules and instances: `round_exp.py` (all rules, including `hubrule_r13`), `clean_battery.py`,
  `uhub_cluster.py`, `pent_growth.py`, `dense_hub_battery.py`, `busy_z.py`, `planar_search.py` and
  smaller scripts named in `OP7.md`.
- Checks: `charge_check.py`, `check_r13z.py`, `check_r13.py`, `verify_cert_a.py`,
  `hub_lemma_check.py`.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop
and check the arguments, to write the scripts and the certificate LPs, and to draft the text.

## References

1. S. Amiri and S. Siebertz. Almost optimal constant-round approximation of dominating set in graph
   classes with excluded minors. arXiv:2610.09618, 2026.

The notebook `OP7.md` lists further references.

## License

Copyright 2026 Sebastian Senge. The code and the documentation in this repository are licensed
under the Apache License 2.0; see [`LICENSE`](../LICENSE).
