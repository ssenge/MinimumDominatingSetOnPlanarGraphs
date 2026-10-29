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
  it). The three changes of the current version v8 are argued in section 10 of that note; one AI
  referee pass on them found no soundness problem. No person has reviewed the argument.
- The type model of the LP has been checked on instances: on adversarial planar girth-5 graphs,
  every local type that occurs is in the LP, and the dual solution it defines satisfies the
  claimed bound.
- The charges themselves have been checked on instances (`charge_check.py`): with the exact
  solution, every vertex and every heavy U-hub ends with at least the certified margin when the
  actual transfers and Euler terms are applied. For g >= 7 this runs on random trees and on
  subdivided planar graphs.
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

The current certificate LP is `discharge_r13v8.py`. It uses only girth >= 5, except for the Euler
constant C = g/(g-2), which is set by the environment variable `GIRTH`. A certificate for g is
also one for every larger girth, since such graphs have girth >= g.

| girth g | v8 feasible at rho (exact check) | v8 infeasible at rho (float) | v7 (exact check) | known upper bound (3g-2)/(g-2) |
|---|---|---|---|---|
| 5 | 3.52 | 3.51 | 3.87 | 13/3 |
| 6 | 3.24 | 3.23 | 3.46 | 4 |
| 7 | 3.17 | 3.16 | 3.38 | 19/5 |
| 8 | 3.15 | 3.14 | 3.35 | 11/3 |
| 10 | 3.14 | 3.13 | 3.31 | 7/2 |
| 16 | 3.14 | 3.13 | 3.28 | 23/7 |
| 30 | 3.14 | 3.13 | | 22/7 |

The value 3.13 is infeasible up to g = 1000 as well. The idrule part alone needs 3.1305 (hub-free
subcubic certificate `discharge_a2.py`), so for large g the LP is close to that floor.
If the certificate is sound, R13 improves the upper bound of [1] for every g from 5 to 30, and
its ratio is below 13/4 for every g >= 6.

Version 8 changes three things in v7 ([`SOUNDNESS.md`](SOUNDNESS.md), section 10). A heavy hub inside U
is one entity, so its vertex part no longer needs a margin of its own. A fourth Euler family on
Q_h and the heavy hubs outside U adds the density of that part. A light hub returns (2 - C)/3
instead of 1/9 to each of its Q_l-neighbours, which its Euler budget still allows.
The exact check rebuilds every coefficient as a rational, rounds the solution, recomputes the
derived bounds exactly and checks all 163,519 rows with fractions.

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
at 3.52. R13 itself does well on such clusters: its ratio stays at most 1.93 on patches of the
{5,4} tiling with searched identifiers.

In simulations against LP_U, R13 never went above ratio 3.0 on the adversarial batteries (random
planar girth-5 graphs, subdivided triangulations, pentagon grids, hosts with clusters of U-hubs,
{5,4} patches).

## The certificate LP in short

The dual of LP_U is max sum y - (1/3) sum_v (Y(v) - 1)^+, with Y(v) = y(N[v] ∩ U). The certificate
sets y = (1 - eps_t)/3 for every vertex of local type t. Each vertex starts with charge rho y minus
its share of the overclaim, minus 1 if it is in D. Charge then moves along edges between types, and
from vertices of Q_h to the heavy hubs they select or neighbour. Euler terms nu (deg/2 - g/(g-2))
on four subgraphs (Z with all hubs, the same plus U', the heavy hubs inside U, and Q_h with the
heavy hubs) add the density bound of planar graphs of girth >= g. Every row of the LP says that some local configuration ends with nonnegative charge. The LP
maximizes the smallest margin; a positive margin certifies the ratio rho. Observation 11 in
`OP7.md` lists the rules in detail.

## Reproducing

Python 3 with numpy, scipy (HiGHS) and networkx. Run the commands inside `op7/`. The LP of
`discharge_r13v8.py` has about 44,500 variables and 164,000 rows and takes about 3 minutes and
0.6 GB.

```bash
GIRTH=5 python3 discharge_r13v8.py 3.55   # prints the max margin; positive means feasible
GIRTH=5 python3 cert_exact.py discharge_r13v8 3.52  # exact rational check of the solution
python3 discharge_r13.py 3.25             # inputs without U-hubs
GIRTH=5 python3 check_r13z.py 4.0 1 20 300  # instance check of the type model
GIRTH=5 python3 charge_check.py 3.52 1 20 300  # charge-level check (after cert_exact.py)
GIRTH=5 python3 lp_diag.py discharge_r13v8 3.45 40  # rows with the largest dual weights
python3 pent_growth.py 1 3000             # R13 against LP_U on {5,4} patches
```

## Files

- `OP7.md`: research notebook with all observations, numbers and the plan.
- `SOUNDNESS.md`: why a feasible solution of `discharge_r13v7.py` or `discharge_r13v8.py` proves
  the bound, row family by row family.
- Certificate LPs: `discharge_r13v8.py` (current, with U-hubs), `discharge_r13v7.py` (previous),
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
