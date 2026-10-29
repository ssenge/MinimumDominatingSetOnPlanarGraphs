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
- **Nothing here is a theorem yet.** The ratios below are feasible solutions of a certificate LP,
  solved in floating point (HiGHS through SciPy). There is no exact rational check, no written
  argument that each LP row is a valid local inequality, and no human review.
- The type model of the LP has been checked on instances: on adversarial planar girth-5 graphs,
  every local type that occurs is in the LP, and the dual solution it defines satisfies the
  claimed bound. This tests coverage, not the derivation of each row.
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

The certificate LP `discharge_r13z.py` uses only girth >= 5, except for the Euler constant
g/(g-2), which is set by the environment variable `GIRTH`. A larger g only makes the LP easier, so
a value feasible for g is feasible for every larger girth.

| girth g | LP feasible at rho | LP infeasible at rho | known upper bound (3g-2)/(g-2) |
|---|---|---|---|
| 5 | 3.90 | 3.85 | 13/3 |
| 6 | 3.50 | 3.40 | 4 |
| 7 | 3.50 | 3.35 | 19/5 |
| 8 | 3.35 | 3.30 | 11/3 |
| 10 | 3.35 | 3.30 | 7/2 |
| 14 | 3.30 | 3.25 | 10/3 |

If the certificate is sound, R13 improves the upper bound of [1] for every g from 5 to 15.

When no vertex of U has 4 or more neighbours in U (no U-hubs), the LP `discharge_r13.py` is
feasible at rho = 13/4 for g = 5, with margin 0.0075. It is infeasible at 3.20.

With U-hubs, 13/4 fails on clusters of heavy hubs inside U whose Q-neighbours are all heavy hubs
inside U. After paying its share of the overclaim, a vertex there keeps at most rho/5, but a hub
selected by only one vertex needs 1, and the local types cannot rule out clusters in which every
hub is selected exactly once. R13 itself does well on such clusters: its ratio stays at most 1.93
on patches of the {5,4} tiling with searched identifiers. The limit is in the local proof method.

In simulations against LP_U, R13 never went above ratio 3.0 on the adversarial batteries (random
planar girth-5 graphs, subdivided triangulations, pentagon grids, hosts with clusters of U-hubs,
{5,4} patches).

## The certificate LP in short

The dual of LP_U is max sum y - (1/3) sum_v (Y(v) - 1)^+, with Y(v) = y(N[v] ∩ U). The certificate
sets y = (1 - eps_t)/3 for every vertex of local type t. Each vertex starts with charge rho y minus
its share of the overclaim, minus 1 if it is in D. Charge then moves along edges between types, and
from vertices of Q_h to the heavy hubs they select or neighbour. Euler terms nu (deg/2 - g/(g-2))
on three subgraphs (Z with all hubs, the same plus U', and the heavy hubs inside U) add the
density bound of planar graphs of girth >= g. A hub inside U is split into a vertex part and a hub
part. Every row of the LP says that some local configuration ends with nonnegative charge. The LP
maximizes the smallest margin; a positive margin certifies the ratio rho. Observation 11 in
`OP7.md` lists the rules in detail.

## Reproducing

Python 3 with numpy, scipy (HiGHS) and networkx. Run the commands inside `op7/`. The LP of `discharge_r13z.py` has about 44,000
variables and 148,000 rows and takes about 3 minutes and 0.5 GB.

```bash
GIRTH=5 python3 discharge_r13z.py 3.9     # prints the max margin; positive means feasible
python3 discharge_r13.py 3.25             # inputs without U-hubs
GIRTH=5 python3 check_r13z.py 4.0 1 20 300  # instance check of the type model
GIRTH=5 python3 lp_diag.py discharge_r13z 3.25 40  # rows with the largest dual weights
python3 pent_growth.py 1 3000             # R13 against LP_U on {5,4} patches
```

## Files

- `OP7.md`: research notebook with all observations, numbers and the plan.
- Certificate LPs: `discharge_r13z.py` (current, with U-hubs), `discharge_r13.py` (no U-hubs),
  earlier versions `discharge_r13u.py` to `discharge_r13y.py`, `discharge_r12*.py`,
  `discharge_r2.py`, `discharge_h*.py`, `discharge_a2.py` (subcubic idrule, 3.1305), and
  `lp_diag.py`.
- Rules and instances: `round_exp.py` (all rules, including `hubrule_r13`), `clean_battery.py`,
  `uhub_cluster.py`, `pent_growth.py`, `dense_hub_battery.py`, `busy_z.py`, `planar_search.py` and
  smaller scripts named in `OP7.md`.
- Checks: `check_r13z.py`, `check_r13.py`, `verify_cert_a.py`, `hub_lemma_check.py`.

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
