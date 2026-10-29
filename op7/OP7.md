# OP7: constant-round domination on planar graphs of girth at least g

Open Problem 7 of [1] (arXiv:2610.09618, posed 7 Oct 2026): for each g >= 5, determine the infimum
of the deterministic constant-round LOCAL approximation ratios for minimum dominating set on planar
graphs of girth at least g.

## Known (checked 2026-10-28)

- Upper bound (2a+1+eps) with a = g/(g-2), that is (3g-2)/(g-2): 13/3 for g = 5, 4 for g = 6
  ([1], Cor. 8.2). Proof: the fractional (1+eps) algorithm on planar graphs, then threshold rounding
  at 1/(2a+1) ([1], Lemma 3.1), with the density bound of Fact 2.1.
- Lower bound 3 for every g, from paths ([1], Thm. 8.7, Ramsey argument on a line).
- Earlier results, as cited in [1]: ratio 18 for girth 5 and ratio 6 for triangle-free graphs.
- In [4] (SSS 2024), asymptotic Theta bounds for high girth and bounded expansion were given in
  terms of k and f(k). There are no planar constants there, so OP7 is not covered.
- No 2026 paper on OP7 found.
- [3] (arXiv:2610.31203, 22 Oct 2026): deterministic constant-round (d+1+eps) for mad <= d and
  bounded depth-one shallow-minor density; tight for even integers d. For planar girth 5 (mad < 10/3)
  this is again 13/3. Its Question 5.3 asks, for every real d >= 2, whether some class with mad <= d
  and bounded nabla_1 has no constant-round algorithm below d + 1. It does not cite the odd-degree
  results below.
- Odd degree ([2], arXiv:1002.0125): optimum exactly
  (Delta+1)/2 on odd-Delta-regular graphs (2 on cubic graphs), Delta+1 for even maximum degree
  Delta and Delta for odd maximum degree Delta. So bounded-degree classes with odd Delta are not
  witnesses for Question 5.3.
- In [12, Sec. 4] it is remarked that for C4-free planar graphs there is no reason yet to think
  3 is out of reach.

## Observations so far

1. **Homogeneity barrier for lower bounds.** All known lower bounds (paths 3, r-th powers of paths
   2r+1, square grid 5, triangular lattice 7) use graphs on which every interior vertex has the
   same ordered view, so the algorithm takes all of them and the ratio is n/gamma. If all vertices
   of degree d have the same ordered view, each has the same number of smaller neighbours, and
   counting edges gives in-degree = out-degree = d/2, so d is even. Planar graphs of girth >= 5
   have average degree < 10/3, so the only such graphs have degree 2, which gives 3. A lower
   bound above 3 needs constructions with several types of vertices. (To prove: the counting needs
   the boundary to be negligible, which fails with unbounded-degree hubs; check that case.)
2. **Periodic constructions.** For a periodic graph G with finite quotient Q under a group with an
   invariant order (Z or Z^2 translations), the Ramsey argument gives the bound
   gamma(Q) / (gamma per period of G), where gamma(Q) is the smallest union of orbits that
   dominates. For the honeycomb this is 2, below 3.
3. **The rounding is not tight on the honeycomb.** The honeycomb (girth 6, gamma = n/4) gets ratio 4
   from threshold rounding with the uniform fractional optimum 1/4. The rule "join if at most one
   neighbour has a smaller identifier, then add the undominated vertices" gives at most 3n/4 from
   the first part on every 3-regular graph (average in-degree 3/2), and an adversarial search over
   orderings on small tori reached only ratio 2.875 (`honey_rule.py`). So the bound 4 for g = 6
   is very likely not the truth.

4. **Cubic graphs (known, and weaker than known).** The rule of 3 gives |D| <= 3n/4 on cubic
   graphs (in/out-degree balance, checked in `cubic_rule.py`). The literature is stronger: the
   optimum on cubic graphs is 2 ([2], see above). Not a result.
5. **Combined rule.** idrule(1/3): D1 = {x >= 1/3}; on U = V minus N[D1], join if fewer U-neighbours
   have a smaller identifier than a larger one; then every undominated vertex of U joins. Rounds: 3
   after x. The repair is parallel (U minus N[D1 or J]). Bug fixed on 2026-10-28: `round_exp.idrule`
   first did the repair sequentially in index order, which is not a local rule. The numbers below
   were rerun with the parallel repair (`adv_round_fixed.log`, `battery_fixed.log`); the maxima did
   not change. Tests (`round_exp.py`, `adv_round.py`, `adv_battery.py`):
   - against optimal x (vertex and averaged) with adversarial identifiers: max 2.89 on girth 5 and
     6 families, where threshold rounding reaches 4.0 (honeycomb, dodecahedron);
   - against every fractional dominating set (the adversary picks the set {x >= 1/3} and the
     identifiers, an LP gives the cheapest x): max exactly 3.000 on planar girth >= 5 graphs
     (pentagon flowers, subdivided triangulations, random), threshold rounding up to 4.0;
   - non-planar girth >= 5 graphs: 2.8 to 2.86 for cubic ones, but 3.08 for the 4-regular
     incidence graph of PG(2,3), 4.45 for PG(2,5) (6-regular) and 5.6 for Hoffman-Singleton
     (`adv_dense.py`). So girth alone is not enough; the proof must use the density bound.
6. **Hubs around monotone paths.** On a monotone path inside G[U], idrule takes all but O(1) of
   its vertices, so the U-part is safe only if x(N[U]) >= |U|/3 there. With the constraints of U
   alone this fails: a cycle with two mega hubs and nested degree-2 hubs (period 5) has
   min x(N[U]) = 0.3067 n, so a U-part ratio of 3.26. In the full graph the nested hubs need D1
   neighbours, one per pocket of a mega hub, and the ratio tends to exactly 3 from below. With one
   D1 vertex adjacent to all hubs, each path vertex has at most one hub (else a C4), and the LP is
   n/3 again (ratio 2.94 at n = 300). So a proof must use that W vertices are dominated by D1, not
   only the constraints of U. Exhaustive check of this family (`pocket_enum.py`, log in
   `pocket_enum.log`): periodic monotone cycles, a mega hub on each side, up to 3 nested hubs per
   pocket, one D1 vertex per pocket, period P = 3..10, limit as the number of periods grows. The
   maximum is exactly 3 (reached for P = 3, 5, 6, 8, 9), never above. Annealing over general
   structures around a monotone cycle (`struct_search.py`) stays below 2.73; this search is weak.
   Exact dual: the claim |D| <= 3 x(V) holds iff some y >= 0 on V with
   Y(v) <= 1 on D1 has 3 sum y - sum_{D1} Y - sum_{not D1} (Y - 1)^+ >= |J u R|, where
   Y(v) = y(N[v]).
   **Conjecture.** On planar graphs of girth >= 5, idrule(1/3) gives |D| <= 3 x(V) for every
   fractional dominating set x. With [1, Thm. 6.2(b)] this would give ratio 3 + eps in constant
   rounds, matching the lower bound 3, and settle OP7 for every g >= 5.
7. **Hub rule (2026-10-28).** hubrule: D1 = {x >= 1/3}, U = V minus N[D1], hubs
   H = {w outside U and D1 with >= 4 neighbours in U} join D, U' = U minus N(H), then idrule on
   G[U'] (`round_exp.hubrule`; `hubrule_all` also makes U-vertices with >= 4 U-neighbours hubs).
   Adversarial battery: both stay at exactly 3.000 on planar girth >= 5 graphs, like idrule.
   Two negative checks: the cap-free packing dual (`packing_test.py`) fails on pocket structures
   by up to 1 per period, so the cap x <= 1/3 is essential; and the class "branch vertices
   induce maximum degree <= 2" is trivial (no hubs can occur there, threshold rounding gives 3).

   **Hub Lemma (proved).** Let G be planar and C4-free, x a fractional dominating set, and suppose
   G[U] has maximum degree <= 2. Then D = D1 + H + U' satisfies |D| <= 3 x(V) - 0.2 |U_H|, where
   U_H = U n N(H). Proof. Every vertex of N[U] has x < 1/3. A vertex v outside D1 and H lies in at
   most 3 closed neighbourhoods of U-vertices (1 + d_U(v) <= 3 inside U, <= 3 U-neighbours in W).
   So 3 x(V) >= |D1| + 3 x(H) + sum_{u in U} x(N[u] - H). For u in U' the term is >= 1, for u in
   U_H it is >= 1 - x(N(u) n H), and the hub terms sum to sum_H t_w x_w (t_w = |N(w) n U|). Hence
   3 x(V) >= |D1| + |U| - sum_H (t_w - 3) x_w >= |D| + |U_H| - e(B)/3, with B the bipartite graph
   between H and U_H. B is planar and C4-free, so of girth >= 6 and e(B) <= 1.5(|H| + |U_H|);
   with e(B) >= 4|H| this gives e(B) <= 2.4 |U_H|. Checked numerically on 4310 pocket
   structures with hubs (`hub_lemma_check.py`, scratch script over `pocket_enum.build`).
   Only C4-freeness is used, not girth 5, and the hubs' own domination is not needed.

   **What is missing for the full theorem** (D = D1 + H + T, T = idrule on G[U']): the same sum
   gives |D| <= 3 x(V) - (|U_H| - e(B)/3) + E with E = sum_{v not in D1, H} (l_v - 3) x_v and
   l_v = |N[v] n (T u U_H)|. Only U-vertices with >= 3 U-neighbours can have l_v >= 4. Two pieces:
   (a) internal overload at U-vertices of U-degree 3 with N[v] inside T u U_H; unweighted this is
   the cubic count |T| <= 3n/4 (all of N[u] in U, x(N[U]) >= n/4), a weighted version is open;
   (b) U-vertices of U-degree >= 4 (stars in G[U] need the cap penalty, not a packing); making
   them hubs too needs a counting that survives clusters of adjacent hubs. A counting with the
   linear bound 1 - X_q fails there; the convex bound (1 - X_q)^+ is needed.

8. **U-only relaxation and the subcubic case (2026-10-28).** For the hub rule, the U-only LP
   (constraints of U and the cap only) suffices for all instances found so far: direct search over U
   (`uonly_direct.py`) gives at most 2.8, and comb pockets (`comb_enum.py`) give at most 2.63.
   Hub-free subcubic case (G[U] of maximum degree <= 3, every W vertex with <= 3 U-neighbours):
   - **Merge forests beat 3 off the plane.** Two monotone J-paths, P-vertices with two smaller J
     neighbours, and monotone streams from the P-vertices merging in a binary tree
     (`merge_example.py`). With W vertices shared by three stream vertices and one D1 vertex,
     idrule reaches 3.03 against the full LP (n = 64). The graph is not planar. Planar comb versions
     (`planar_merge.py`) stay at 2.4 to 2.9, because planarity limits how W vertices can be
     shared. So a proof of the ratio 3 must use planarity also in the subcubic part.
   - **Local certificate for 3.13.** Write y = (1 - eps)/3 on U. A discharging LP over vertex types
     (neighbour slots: direction, in J, degree) with transfers on arcs (`discharge_a2.py`) is
     feasible exactly for rho >= 3.1305. This proves |T| <= rho LP_U for idrule on every subcubic
     G[U], for any graph, planar or not. The certificate was rechecked vertex by vertex on 600
     random instances (`verify_cert_a.py`). At rho = 3 the LP is infeasible; its dual is a pattern
     of rootless J-trees, which cannot occur in finite graphs, so the local method stops there.
   - **Leftover bound.** For idrule on a subcubic F: |J| + sum_C (l(root_C) - 1) + sum_R (s - l)
     = sum_P q(p), with q(p) = 2 s_J - l_J + l - s <= 3, so |P| >= |V3(F)| / 4 (V3 = vertices of
     degree 3). Checked numerically (min of |P| - |V3|/4 over 600 instances: 0.25).
9. **Uniform dual, reduction for rho = 13/4.** With y = 1/rho on all of U,
   rho LP_U >= |U| - (1/3) sum_v (L_v - rho)^+. For the hub rule (hub_all) this reduces
   |D| <= rho x(V) to |Z| + |P| - |H_W| >= (1/3) [sum_H (L_w - rho) + (4 - rho) |U3|], where
   Z = U n N(H) minus H and U3 = non-hub U-vertices of U-degree 3. For rho = 13/4 the subcubic
   interior is paid by |P| >= |V3(F)|/4, and what is left is a purely combinatorial inequality on
   the hub structure: 3|Z| + 3|H_U| + |H|/4 >= sum_H L_w + (3/4)(|Bd| + |U3 n Z|), with Bd the
   U'-vertices of U-degree 3 next to Z. It holds when Z-vertices have few U-neighbours (bipartite
   hub graph, e(B) <= 2.4 |Z|). It fails for "busy" Z-vertices (U-degree 3, next to U'-vertices of
   U-degree 3). Off the plane the hub rule itself is bad there (about 3.6 against LP_U). In the
   plane, Euler's formula limits such configurations (pockets force U-degree 2 vertices). A proof
   needs Euler charges together with the LP accounting.
10. **Busy Z, cleanup, other rules, and four certificate LPs (2026-10-28).**
   - **Busy Z (busy_z.py).** Rail cycle with tripod Z-vertices on both sides and hub chains on the
     tripods; planar, girth 5. Against LP_U, hub_all and hubrule reach 23/7 (slope over K = 6, 12);
     against the full LP only 2.53. So the U-only route cannot prove 13/4 for hub_all.
   - **Cleanup (round_exp.hubrule_clean).** A W-hub leaves D when every U-neighbour has a
     T-neighbour. Busy Z drops to 3.0 against LP_U. The uniform dual still fails there (slack -6 at
     13/4, diamond_check.py), so any proof needs a non-uniform dual.
   - **Other rules (clean_battery.py, uhub_cluster.py).** All against LP_U unless noted.
     R2 (round_exp.uhub_idrule): U-hubs join, idrule on the subcubic rest, W-hubs never join. At
     most 2.8 on the batteries and 2.57 on busy Z, but 3.054 on hosts built around a dodecahedral
     cluster of U-hubs. R12 (round_exp.hubrule_r12): vertices of Q = Z + H_U minus N(T) next to a
     heavy hub (>= 4 Q-neighbours) select one of maximum load, the rest runs idrule on the subcubic
     G[Q_l]. At most 3.0 everywhere (2.6, 2.57, 3.0 full LP on hub-dense graphs, 3.0 busy Z, 2.8
     clusters). hubrule_clean: at most 3.0 everywhere.
   - **Certificate LPs.** All use vertex types, arc transfers, A/B versions for (Y - 1)^+, rows
     over 4-multisets with nonnegative coefficients for unbounded hub degrees, and Euler terms
     lam (deg/2 - c) on chosen subgraphs (c = 3/2 bipartite, 5/3 otherwise). Max margin at 13/4
     (negative = no certificate):
     discharge_h.py (min-identifier selection) -0.36; discharge_h2.py (max-load selection, Euler
     between rich Q and heavy hubs) -0.094; discharge_r2.py (R2, y up to 1, eight Euler families)
     -0.53 for g = 5 and -0.18 for g = 8; discharge_r12.py (R12 without U-hubs) -0.115 (-0.06 at
     3.5). Binding configurations, in order: a Q-vertex owing overclaim shares to busy hubs while
     paying a private light hub; cubic G[Q] with private light hubs (needs positive y on Z1);
     U-hub clusters and isolated U-vertices with two hubs and a W3; monotone Q_l-paths with Q_h
     pendants on heavy hubs (locally 3.5, but the light hubs that put the path into Z bring extra
     Z1/T structure that the types do not see).
   - **Lessons.** Duals with y <= 1/3 cannot certify rules that leave hub-covered vertices to
     idrule (subdivided triangulation: R2 has ratio 2.25, the best y <= 1/3 dual only shows 4.5).
     Vertex-only Euler terms charge vertices of degree 1 and 2, and the LP has no way to route face
     surplus to them. Each obstruction needs types that see one more layer (hub loads at radius 2,
     the other neighbours of light hubs, or incident face lengths).
11. **Rule R13 and a certificate at 13/4 without U-hubs (2026-10-28).**
   - **R13 (round_exp.hubrule_r13).** As R12, but a vertex of Q_h with a neighbour in T2 does not
     select. Every remaining selection is the one R12 makes, so R13 is never worse than R12. On the
     local configuration that binds the R12 certificate (heavy hubs on Q_h-vertices whose three
     Q_l-neighbours lie on monotone Q_l-paths), R12 pays 13 per 16 U-vertices against a local
     LP_U of 4, that is 13/4, and R13 pays 12, that is 3. (At full density the configuration
     violates Euler's bound once the light hubs are counted, so it is a local pattern only.)
     Batteries (uonly, direct, dense): at most 3.0, as R12.
   - **Certificate (discharge_r13.py), U-only LP, no U-hubs.** Additions to discharge_r12.py, each
     worth its share:
     - Euler families with c = 5/3 through Z: "Z" (Z = Q + Z1 and all W-hubs, edges inside Z and
       from Z to hubs) and "ZU" (also U'). Every U-neighbour of a hub lies in Z, so every hub has
       degree >= 4 and needs no row; a Q_l-vertex has >= 1 light hub;
     - Z1 rows, and positive y on Z1: a Z1-vertex pays rho/3 y to each of its hubs, which covers
       the extra overclaim of light hubs (at most 3 Q-neighbours);
     - leaves: an isolated Q_l-vertex with one light hub leaves the Z-families and pays 7/18 nu to
       its hub; every light hub returns nu/9 to each other Q-neighbour (hub rows checked for all
       mixes of at most 3 Q-neighbours, with degree >= 4).
     Max margin at 13/4: R12 -0.089 (Euler families on Q only), -0.051 (Z-families and Z1 rows),
     -0.050 (positive y on Z1); R13 -0.012, -0.0025 (leaves), **+0.0075** (light hub returns).
     The threshold of the R13 certificate lies between 3.20 (-0.0028) and 3.25.
   - **Instance check (check_r13.py).** Types and y = (1 - eps)/3 from the LP solution on random
     and adversarial planar girth-5 instances (no U-hubs): every type occurs in the LP, and the
     largest |D'|/dual(y) found is 3.0, below 3.25. This tests the type model, it is not a proof.
   - **U-hubs (discharge_r13u.py to r13z.py).** A U-hub is split into a vertex part and a hub
     part. A heavy U-hub's hub part is a heavy hub whose members are N(h) n Q plus its own vertex
     part; its row carries the whole overclaim and the Euler term of h. A light U-hub's vertex
     part is an ordinary Q-type over its <= 3 Q-neighbours without Euler terms, and its Euler
     term is its light-hub budget. Max margin at 13/4: -0.40 (4-sub-multiset hub rows force
     every member to pay rho/3 y to each heavy hub, so U-hubs with >= 4 heavy hubs get y = 0),
     -0.24 (load buckets 4, 5, >= 6, exact member rows for loads 4 and 5), -0.18 (heavy W-hub
     edges credited to the vertex part), -0.145 (hub-side Euler halves inside the bucket-6
     bounds; selector counts c in {1, 2} change nothing), -0.123 (r13y: exact count KU of heavy
     U-hubs in N[h], since KU - 1 <= a_h <= load of the selected hub; light U-hubs in Q_h get
     nu/2 per heavy W-hub edge; a vertex of degree 1 in a family leaves it and pays nu/2 to its
     neighbour), -0.099 (r13z: a third Euler family HU = G[heavy U-hubs]).
   - **Soundness fixes (discharge_r13v7.py, argument in SOUNDNESS.md).** Writing out the charge
     argument row by row turned up five places in r13z where a row claimed more than the charges
     give. (1) The own vertex part of a
     heavy U-hub has no edge to its hub part, yet r13z gave it a member bound with a half-edge
     nu/2 at load >= 6. It now has its own kinds (selects itself with c = 1 or 2, or not), it is a
     member of every row of its hub part, and its bound has no Euler half. (2) The coefU row
     counted nu/2 in Z and ZU for an extra heavy U-hub neighbour, but that half-edge is already
     used in the bucket-6 rows of the hub part; only nu_HU/2 is free. (3) A Q_h vertex may have
     light W-hub neighbours that its type does not count, so a counted family degree of 1 is a
     lower bound only, and the leaf term becomes min(-1/2, 1 - g/(g-2)). (4) The same holds for a
     Q_l vertex next to a light U-hub, whose leaf term becomes min(-7/18, 1 - g/(g-2) + 2/9).
     (5) A Q_l vertex with P-neighbours whose only other Z-neighbours are W-hubs recorded only "at
     least one W-hub", yet its Z-row used the leaf term; with two W-hubs the true term is
     1 - g/(g-2) + 2/9 = -4/9 < -7/18 at g = 5. The type now records the exact number (1 or >= 2).
     Problem (3) made v6f invalid, not only unproved: an adversarial referee pass (AI agent, code
     only) built a 10-vertex tree on which the v6f solution leaves a Q_h vertex at charge -0.085.
     The referee found the same five problems and nothing further; its instances are regression
     tests in charge_check.py, and v7 passes them.
     The LP has 44,138 variables and 149,023 rows. All values of the table below pass the exact
     check with r13v7 as well (certified margins 0.0012, 0.0018, 0.0004, 0.0020, 0.0014, 0.0028,
     0.0009 for g = 5, 6, 7, 8, 10, 14, 16), so the table is unchanged.
   - **Thresholds with U-hubs (r13z, rechecked with r13v7; Euler constant g/(g-2), GIRTH=g).** The
     whole model only uses girth >= 5 apart from this constant. Feasible values checked in exact
     rational arithmetic (cert_exact.py: rational coefficients, solution rounded to 1e-9 after
     solving with all rows tightened by 1e-6, derived bounds recomputed exactly, all rows
     checked):

     | g | feasible (exact) | infeasible (float) | (3g-2)/(g-2) |
     |---|---|---|---|
     | 5 | 3.87 | 3.85 | 4.34 |
     | 6 | 3.46 | 3.45 | 4 |
     | 7 | 3.38 | 3.35 | 3.80 |
     | 8 | 3.35 | 3.30 | 3.67 |
     | 10 | 3.31 | 3.30 | 3.50 |
     | 14 | 3.29 | 3.28 (margin about 0) | 3.34 |
     | 16 | 3.28 | | 3.29 |
     | 1000 | 3.30 (float) | 3.25 | 3.01 |

     If the certificate is sound, R13 gives ratio rho_g + eps below (3g-2)/(g-2) for
     5 <= g <= 16.
   - **Instance check with U-hubs (check_r13z.py).** Types including heavy U-hub vertex parts and
     light U-hub variants, y from the LP solution at rho = 4.0 (g = 5), adversarial search over U
     and identifiers on 13 instance families with up to 21 U-hubs: every type occurs in the LP and
     the largest |D'|/dual(y) is 3.0. This checks type coverage and the dual bound, not the
     charge bookkeeping of the rows.
   - **Charge-level check (charge_check.py).** With the exact v7 solution, the actual final charge
     of every vertex and of both parts of every heavy U-hub (actual transfers, payments,
     overclaims, Euler terms from actual degrees with leaves and light-hub returns) is at least the
     certified margin on adversarial instances of the 13 families (g = 5 at 3.87; g = 6 at 3.46 on
     the families of girth >= 6); light W-hubs end >= 0, the Euler sums are <= 0, and the total
     matches rho dual(y) - |D'| plus the Euler sums. The minimum always equals the margin.
   - **Why 13/4 fails with U-hubs.** Take a cluster of heavy U-hubs of load 4 whose Q-neighbours
     are all heavy U-hubs. After its overclaim share a vertex keeps at most rho (1 + 2 eps)/9,
     which is rho/5 at eps = 2/5, while a hub selected by one vertex needs 1. Radius-1 types (and
     the selector counts c) cannot exclude clusters where every hub is selected exactly once, so
     these rows need rho >= 5 (1 - (nu_Z + nu_ZU + nu_HU)/3). The pattern is not global: R13 stays at
     most 2.8 on the U-hub cluster hosts (uhub_cluster.py), at most 1.93 on {5,4}-patches with
     searched identifiers (pent_growth.py), and near 1.1 there under radial or geodesic
     rankings, since patches of the hyperbolic tiling have most of their vertices on the boundary.
   - **Still missing:** 13/4 with U-hubs, and a review of SOUNDNESS.md by a person. (Exact
     feasibility, the written argument and the charge-level check are done.)

## Plan

- **L1 (literature).** Read the girth-5 paper cited in [1], the square-grid lower bound
  [12, Sec. 4], and the lower bound 7 of [5], to see whether
  any of them has a lower-bound idea beyond homogeneous graphs.
- **U1 (upper bound, main line).** Combine the fractional solution of [1] with identifier-based
  rules on the low-degree part, in place of threshold rounding. Target: below 13/3 for g = 5 and
  below 4 for g = 6. Stretch goal: 3+eps for all g >= 5, which would settle OP7 for every g >= 5
  at once. Steps:
  - done (2026-10-28): the case G[U] of maximum degree <= 2, for the hub rule (Hub Lemma,
    observation 7). The face-charging idea for idrule itself is no longer needed;
  - done (2026-10-28): hub-free subcubic case with ratio 3.1305 (local certificate, observation
    8); reduction of rho = 13/4 to a hub inequality (observation 9);
  - done (2026-10-28): busy-Z search (hub_all is above 13/4 against LP_U, the cleanup fixes it);
    rules R2 and R12; four certificate LPs and their obstructions (observation 10);
  - done (2026-10-28): rule R13 and its certificate at 13/4 without U-hubs (observation 11);
  - done (2026-10-29): U-hubs in the certificate at rho_g below (3g-2)/(g-2) for 5 <= g <= 15
    (3.9 at g = 5, 3.5 at g = 6), observation 11;
  - next: (a) consolidate rho_g: exact rational certificate, charge-level instance check,
    soundness write-up, fine bisection per g; (b) target theorem ratio 13/4 + eps for all g >= 5
    (beats (3g-2)/(g-2) for 5 <= g <= 17): the heavy U-hub clusters need either a rule change
    that makes a hub selected by one vertex rare locally, or an argument that is not local
    (counting over the cluster); (c) if both fail, a certificate against the full LP;
  - prove the honeycomb rule bound exactly (is the worst case 3, or 23/8 as in the search?);
  - extend to 3-regular planar graphs of girth >= 5, then to bounded degree, then to the general
    case with hubs, where the fractional solution of [1] takes over;
  - check every rule numerically on planar girth >= 5 graphs (random, tilings such as Cairo and
    honeycomb, fans of pentagons, high-degree hubs), with adversarial orderings.
- **B1 (lower bound side).** Prove the barrier of observation 1, including the unbounded-degree
  case. Search periodic planar girth >= 5 graphs (strips and Z^2 tilings) for gamma(Q) above
  3 times gamma per period; any hit is a new lower bound. If the barrier holds, the answer is
  probably 3 for all g >= 5, and the work shifts fully to U1.
- **Lean.** Formalize what is combinatorial: the counting bound for the rule, the rounding
  inequality, and the barrier lemma.

## Importance if it works

OP7 is a stated open problem of a fresh paper with a small community. Any improvement on either
side would be modest to solid. Settling the infimum as 3 for all g >= 5 would be significant within
this niche.

## References

1. S. Amiri and S. Siebertz. Almost optimal constant-round approximation of dominating set in graph
   classes with excluded minors. arXiv:2610.09618, 2026.
2. M. Åstrand, V. Polishchuk, J. Rybicki, J. Suomela, and J. Uitto. Local algorithms in (weakly)
   coloured graphs. arXiv:1002.0125, 2010.
3. T. Picavet. Almost tight distributed approximation for domination in sparse graph classes.
   arXiv:2610.31203, 2026.
4. C. Lenzen and S. Wenning. Tight bounds for constant-round domination on graphs of high girth and
   low expansion. arXiv:2408.12998, SSS 2024.
5. M. Hilke, C. Lenzen, and J. Suomela. Brief announcement: Local approximability of minimum
   dominating set on planar graphs. PODC 2014.

[12] is the square-grid paper cited as [12] in [1].
