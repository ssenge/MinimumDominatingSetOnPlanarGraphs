# Minimum Dominating Set on Planar Graphs: a smaller round exponent for optimal constant-round domination

This repository contains machine-checked proofs (Lean 4 + Mathlib) and simulation code for an
improvement of the deterministic LOCAL $(7+\varepsilon)$-approximation of minimum dominating set
on planar graphs from [1].

## Background

**The problem.** A set $D$ of vertices of a graph $G$ is *dominating* if every vertex lies in $D$
or has a neighbour in $D$. The domination number $\gamma(G)$ is the minimum size of a dominating
set, and minimum dominating set (MDS) asks for one. Relaxing the integer program
$\min\sum_v x_v$ subject to $\sum_{u\in N[v]}x_u\ge 1$ for every $v$ from $x_v\in\{0,1\}$ to
$x_v\ge 0$ gives the fractional domination number $\gamma_f(G)\le\gamma(G)$.

![(a) a dominating set; (b) the fractional optimum of the 5-cycle; (c) the radius-1 and radius-2 views of a vertex](figures/basics.svg)

MDS is NP-hard, even on planar graphs of maximum degree 3 [7]. It is a set cover problem whose
sets are the closed neighbourhoods $N[v]$. The greedy algorithm, which repeatedly adds a vertex that
dominates the most undominated vertices, therefore achieves ratio $1+\ln(\Delta+1)$ on graphs of
maximum degree $\Delta$ [8], and by the standard reduction from set cover, ratio
$(1-\varepsilon)\ln n$ is NP-hard [9]. Planar graphs are much easier: the layering technique of [10]
gives a polynomial-time $(1+\varepsilon)$-approximation for every fixed $\varepsilon>0$.

**Distributed setting.** In distributed computing the input graph is the network itself. Every
vertex is a processor that initially knows only its identifier and its neighbours, and it decides
whether it belongs to $D$ by exchanging messages with its neighbours. Dominating sets arise in this
form as cluster heads in wireless ad hoc and sensor networks, where every node needs a coordinator
within one hop and no node knows the whole topology.

In the LOCAL model [11], computation proceeds in synchronous rounds. In every round each vertex
sends a message of arbitrary size to each neighbour and performs arbitrary local computation. After
$T$ rounds a vertex knows exactly its radius-$T$ neighbourhood (panel (c) above). So a $T$-round
algorithm is a function from radius-$T$ neighbourhoods to outputs, and the number of rounds
measures how far a vertex has to look. A constant-round algorithm is local in the strongest sense:
- its running time does not depend on the size of the network;
- a change in the graph affects only the outputs within constant distance;
- on graphs of bounded degree it yields a sublinear-time algorithm that decides the output of a
  single vertex by exploring its neighbourhood [12].

### Standard distributed algorithms

**Parallel greedy.** The greedy algorithm adds one vertex at a time. Its direct distributed version
lets a vertex join when its *span*, the number of undominated vertices in its closed neighbourhood,
is the largest within distance 2. Then vertices that join in the same round do not compete for the
same undominated vertices. This can still take $\Omega(n)$ rounds, for example on a caterpillar
whose spine vertices have decreasing spans, because then only one vertex joins per round. The
algorithm of [15] removes this bottleneck by rounding spans up to powers of 2, so that many vertices
tie. Every round has three steps:
1. the vertices whose rounded span is maximal within distance 2 become candidates;
2. every undominated vertex counts the candidates that dominate it;
3. every candidate $v$ joins with probability $1/\mathrm{med}(v)$, where $\mathrm{med}(v)$ is the
   median of these counts over the undominated vertices that $v$ dominates.

The expected size of the result is $O(\log\Delta)\gamma(G)$, and the algorithm terminates in
$O(\log n\log\Delta)$ rounds with high probability.

**LP relaxation and rounding.** A fractional dominating set $x$ becomes a dominating set in two
rounds:
1. every vertex joins independently with probability $\min\lbrace 1,x_v\ln(\Delta+1)\rbrace$;
2. every vertex that is still undominated joins as well.

Since $\sum_{u\in N[v]}x_u\ge1$, a vertex remains undominated after step 1 with probability at most
$e^{-\ln(\Delta+1)}=1/(\Delta+1)$. Every vertex dominates at most $\Delta+1$ vertices, so
$n/(\Delta+1)\le\gamma_f(G)$, and the expected size is at most
$\ln(\Delta+1)\sum_v x_v+\gamma_f(G)$. In [13], covering and packing LPs are solved within a factor
$1+\varepsilon$ in $O(\log n/\varepsilon)$ rounds. Together with a rounding of this kind, this gives
an $O(\log\Delta)$-approximation of MDS in $O(\log n)$ rounds. In the same paper it was shown that
every polylogarithmic approximation, even a randomized one, needs
$\Omega(\min\lbrace\log\Delta/\log\log\Delta,\sqrt{\log n/\log\log n}\rbrace)$ rounds. So on general
graphs no constant-round algorithm has a constant ratio.

**Planar graphs in a constant number of rounds.** Sparse classes behave differently. The algorithm
of [14] has two steps:
1. every vertex $v$ whose open neighbourhood cannot be dominated by six vertices other than $v$
   joins $D$, which needs only the radius-2 neighbourhood of $v$;
2. every vertex that is still undominated adds a vertex of its closed neighbourhood that dominates
   the most undominated vertices.

It runs in six rounds and has ratio 130 on planar graphs [14]. Planarity enters only in the
analysis, which shows that step 1 selects fewer than $3\gamma(G)$ vertices outside a minimum
dominating set. This raised the question of the best ratio that a constant number of rounds can
achieve on planar graphs; see the Summary below for the answer.

**Cluster-and-solve.** Ratios close to the optimum need a global view of larger regions. Algorithms
of this kind on sparse classes [4, 3] work in three steps:
1. partition the graph into clusters of small radius such that few edges run between clusters;
2. let one vertex of every cluster collect the cluster and solve it exactly;
3. combine the local solutions.

The quality of the result depends on the weight of the edges between clusters, and the number of
rounds on the cluster radius. In [4], this gives a $(1+\varepsilon)$-approximation of MDS on planar
graphs in $O(\log^{\ast} n)$ rounds. A common way to build the clusters is repeated star contraction.
Every cluster picks a neighbouring cluster to merge with, such that the merges form vertex-disjoint
stars, and every star becomes one cluster. This at most triples the radius:

![a star of parts of radius at most r becomes one part of radius at most 3r+1](figures/radius.svg)

If every level multiplies the radius by 3 and the expected weight between clusters by $q$, then an
$\varepsilon$-fraction is reached after $L\approx\ln(1/\varepsilon)/\ln(1/q)$ levels. This takes
$3^L\approx(1/\varepsilon)^{\kappa}$ rounds with $\kappa=\ln 3/\ln(1/q)$, and this exponent is what
we improve.

## Summary

In [2] it was shown that no deterministic constant-round LOCAL algorithm approximates minimum
dominating set on planar graphs within $7-\varepsilon$. In [1] this bound was matched. For every
$\varepsilon>0$, the algorithm of [1] returns a dominating set of
size at most $(7+\varepsilon)\gamma(G)$ in

$$T_0 + O\big((c_0/\varepsilon)^{\kappa}\big) \text{ rounds},\qquad \kappa=\frac{\ln 3}{\ln(1/q)},\quad q=\frac{23}{24},\quad \kappa\approx 25.81 .$$

Open Problem 4 of [1] asks whether the exponent $\kappa$ can be substantially reduced.

We change one step of the clustering procedure of [1], a star contraction in the spirit of
[3, 4]: how the stars are chosen in Algorithm 1 (`RandomCluster`). Everything else carries over unchanged, including the radius recursion, the
view radius, the derandomisation and the rounding. **For planar graphs the exponent drops from
25.81 to below 5.89.**

| analysis | per-level contracted fraction $f$ | exponent $\kappa=\ln 3/\ln\frac{1}{1-f}$ |
|---|---|---|
| [1] (heaviest-edge stars) | $1/24\approx 0.0417$ | $25.81$ |
| random centres, orientation bound (Thm 1), $p=3/8$ | $1935/12288\approx 0.1575$ | $<6.42$ |
| random centres, planar bound (Thm 2), $p=1/2$ (one fair coin, as in [1]) | $175/1152\approx 0.1519$ | $<6.7$ |
| random centres, planar bound (Thm 2), $p=3/8$ (three fair coins) | $357115/2097152\approx 0.1703$ | $5.88<\kappa<5.89$ |
| random centres, planar bound (Thm 2), $p=21/64$ (six fair coins) | $\approx 0.1718$ | $\approx 5.83$ |

![Round exponents for planar graphs: proved upper bounds above the axis, limits of the analyses below](figures/exponents.svg)

Above the axis: proved exponents. Below the axis: the smallest exponent that each kind of analysis
can give (see [Limits of the approach](#limits-of-the-approach)).

$\kappa$ is the exponent of $1/\varepsilon$ in the number of rounds, so lowering it is a
polynomial speed-up. At $\varepsilon=0.01$, the term $(1/\varepsilon)^\kappa$ shrinks from about
$10^{52}$ to about $10^{12}$. For every target ratio in $(7,8]$, the algorithm of [1] is the
only one known, so this is the fastest known algorithm in that range.

## The rule

Fix a level $t$, and let $Q$ be the quotient graph of the current parts, weighted by the number of
edges between parts.

1. Every part becomes a **centre** independently with probability $p$. It reads $b$ fair coins of
   its leader, so $p=m/2^b$.
2. Every non-centre part that has a centre neighbour in $Q$ **joins its heaviest centre
   neighbour**. Ties are broken by identifier.
3. Each centre, together with the parts that joined it, forms one new part.

![One level of the rule on a quotient of total weight 28: centres, joins, new parts](figures/level.svg)

In this example the join edges carry weight 13. Two edges between leaves of the same star, of
weights 2 and 3, also become internal, so the weight between parts drops from 28 to 10.

The new parts are vertex-disjoint stars in $Q$, so the radius recursion $r_t=3r_{t-1}+1$ and the
round bound of [1] still hold. Every join edge becomes internal. Hence the cut weight drops by
at least

$$\mathrm{gain}(C)=\sum_{P\notin C}\ \max_{X\in C\cap N(P)} w(PX).$$

Write $s=1-p$ and $g(d)=1-s^d$.

## Results

### Theorem 1 (bounded out-degree orientation)

Suppose the edges of $Q$ can be oriented so that every vertex has out-degree at most $k$. Then

$$\mathbb{E}[\mathrm{gain}(C)]\ \ge\ f_k(p)\,w(Q),\qquad f_k(p)=\frac{(1-p)\big(1-(1-p)^k\big)}{k}.$$

In a proper minor-closed class of edge density $a$, such an orientation exists with
$k=\lceil a\rceil$ [5]. With $p=1/2$, we have $f_{\lceil a\rceil}(1/2)\ge 1/(8a)$, so the new
exponent is never worse than that of [1]. As the density grows, it becomes smaller by a factor
approaching 8.

| density $a$ | [1] | ours, $p=1/2$ | ours, best dyadic $p$ | ratio |
|---|---|---|---|---|
| 1 | 8.23 | 3.82 | 3.82 | 2.2× |
| 2 | 17.02 | 5.29 | 5.14 | 3.3× |
| 3 (planar, via Theorem 1) | 25.81 | 6.97 | 6.41 | 4.0× |
| 6 | 52.18 | 12.84 | 10.08 | 5.2× |
| 10 | 87.34 | 21.44 | 14.80 | 5.9× |
| 100 | 878.34 | 219.17 | 115.67 | 7.6× |

The same substitution also improves the other guarantees of [1, Thm. 6.2] for every proper
minor-closed class:
- the deterministic $(1+\varepsilon)$-approximation of the fractional domination number;
- the randomised algorithm with expected size $(1+\varepsilon)\gamma$;
- the ratio $2a+1+\varepsilon$.

### Theorem 2 (sharper count for planar graphs)

Let $Q$ be a simple planar graph, and let $p\in[21/64,1]$. Then

$$\mathbb{E}[\mathrm{gain}(C)]\ \ge\ \varphi(p)\,w(Q),\qquad \varphi(p)=\frac{(1-p)\big(3-2(1-p)^3-(1-p)^6\big)}{9}.$$

$\varphi$ is maximised at $s^3=(\sqrt{37}-4)/7$, that is $p\approx 0.3324$, where
$\varphi\approx 0.17182$ and $\kappa\approx 5.827$.

**Proof idea.**

1. *Layer cake (exact).* Let $Q_\tau$ be the subgraph of edges of weight at least $\tau$, and let
   $d_\tau(P)$ be the degree of $P$ in it. Then
   $\mathbb{E}[\mathrm{gain}]=s\int_0^\infty\sum_P g(d_\tau(P))\,d\tau$. Every $Q_\tau$ is planar.
2. *Two degree facts.* Let $G$ be a simple planar graph with degrees $d_v$ and $n'$ non-isolated
   vertices. Then
   - (A) $|E|\le\sum_v\min(d_v,3)$;
   - (B) $2|E|\le\sum_v\min(d_v,6)+2n'$.

   Both follow from $e(H)\le 3|H|$ and from the bound for bipartite planar graphs.
3. *Pointwise certificate.* Let $a=(8g(3)-5g(6))/9$ and $b=(g(6)-g(3))/3$. Then for every $d\ge0$,
   $$g(d)\ \ge\ a\min(d,3)+b\big(\min(d,6)+2[d\ge1]\big),$$
   with equality at $d\in\{0,3,6\}$. Summing over all vertices and applying (A) and (B) gives
   $$\sum_v g(d_v)\ \ge\ (a+2b)\,|E|=\frac{3-2s^3-s^6}{9}\,|E|.$$
4. Integrate over $\tau$.

The count is optimal for its inputs. Over degree sequences constrained only by (A) and (B), the
infimum of $\sum_v g(d_v)/|E|$ is exactly $(3-2s^3-s^6)/9$, and the certificate is the dual
solution of that linear program.

### Limits of the approach

- **Join edges only.** Consider the Apollonian network obtained from $K_4$ by inserting a vertex
  into every face ten times (118,100 vertices). There, the expected join gain of the rule is at
  most $0.17401\,w$ for every $p$. Hence no analysis that counts only join edges gets this rule
  below $\kappa\approx 5.74$. Theorem 2 reaches $0.17182$.
- **All internal edges.** Even counting edges between leaves of the same star, $K_{2,n}$ limits
  the rule to $1/(3\sqrt3)+1/n\approx 0.1925$ per level. So every analysis of this rule has
  $\kappa\ge 5.14$.
- **Any star contraction.** On the square grid, a single level of star contraction internalises
  at most a $2/5$ fraction of the edges. So with radius growth 3, any analysis that bounds each
  level by its worst case has $\kappa\ge\ln 3/\ln(5/3)\approx 2.15$.

## Plugging the rule into the algorithm of [1]

Numbering refers to [1]. In Algorithm 1 (`RandomCluster`), lines 6–13 are replaced by the rule
above.

- **Lemma 4.1** (partition, radius, dependence on coins). The proof only uses that the new parts are
  vertex-disjoint stars whose leaves are adjacent to their centre in $Q$.
- **Lemmas 4.2 and 4.3.** Fix the coins of earlier levels. Then $Q$ is a fixed simple planar graph,
  and the centre events are independent. Theorem 2 gives
  $\mathbb{E}[\mathrm{cut}_t\mid\mathcal F_{t-1}]\le(1-\varphi(p))\,\mathrm{cut}_{t-1}$, and
  Theorem 1 gives the analogous bound for general classes. Corollary 4.4 follows verbatim, and
  Lemma 4.2 is no longer needed.
- **Lemma 4.5** (view radius $\rho_t=2(3^t-1)$) is unchanged. The new part of a vertex is
  determined by the centre status and the join choices of the parts that the same view reveals.
- **Theorem 5.4** keeps the round bound $T_{\mathcal C}+9\cdot 3^L$. It uses $bL$ fair coins per
  vertex instead of $L$.
- **Theorem 6.1** (the derandomisation of [6]) needs only a fixed finite number of fair coins per
  vertex, which still holds.
- **Theorem 6.2 and Corollary 8.1** hold with $q'=1-\varphi(p)$:
  - $p=3/8$ gives $q'=1740037/2097152$;
  - $p=1/2$ gives $q'=977/1152$.

## Machine-checked proofs (`lean/`)

Lean 4 (`leanprover/lean4:v4.36.0-rc1`) with Mathlib; the exact Mathlib revision is pinned in
`lean/lake-manifest.json`. Every theorem below depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry`.

The random centre set is modelled exactly: `E p A f` is the expectation of `f D` over a random
subset `D ⊆ A` that contains each element independently with probability `p`.

`lean/Op4/RandomCentres.lean` (Theorem 1):
- `gain_eq_join_edges`: the gain is the weight of a set of pairwise distinct edges.
- `vertex_bound`: $|A|\cdot\mathbb{E}[\max_{x\in C_A}w(x)]\ge g(|A|)\sum_{x\in A}w(x)$.
- `random_centres`: Theorem 1, with the orientation as a hypothesis. `arcs_eq_half_total` shows
  that for an orientation, the arc sum equals $w(Q)$.
- `f_three_eighths`, `f_le`: $f_3(3/8)=1935/12288$, and $f_3\le 63/400$ for every $p$.
- `kappa_new`, `kappa_paper`, and the related exponent bounds: $6.4<\kappa'<6.42$ and
  $25<\kappa_{\mathrm{AS}}<26$.

`lean/Op4/Sharper.lean` (Theorem 2):
- `sharper`: Theorem 2, in a discrete form of the layer cake. The proof is by induction on the
  support: subtract the smallest positive weight $t$ from every edge, and the gain splits into $t$
  times the join indicator plus the gain of the remaining weights.
- `degree_lemma`: the degree inequality, derived from (A), (B) and a pointwise certificate.
- `cert_three_eighths`, `cert_half`: the certificates for $p=3/8$ and $p=1/2$.
- `f_sharper`, `f_sharper_half`: $\varphi(3/8)=357115/2097152$ and $\varphi(1/2)=175/1152$.
- `kappa_sharper`, `kappa_sharper_half`: $5.88<\kappa'<5.89$, and $\kappa'<6.7$ for $p=1/2$.

**Not formalised.** Mathlib has no notion of planarity, so the following are stated as hypotheses:
- Facts (A) and (B), on every symmetric weighting whose support lies in that of $w$;
- the existence of an out-degree-3 orientation (Euler's formula plus [5]).

The integration into [1], which reuses the proofs of [1], is not formalised either.

Build:

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Simulations and numerical checks (`sim/`)

Requires Python 3 with `numpy` and `scipy`.

- `sim/rules.py`: one level of contraction under several star-selection rules on planar families
  (Delaunay triangulations, triangular and square grids, $K_{2,n}$, stacked triangulations, cubic
  graphs, adversarial weightings). Run as `python3 rules.py [seed] [adv]`.
- `sim/levels.py`: the original heaviest-edge selection of [1] and rank-based variants.
- `sim/mpx.py`: one-shot local clustering by capped exponential shifts. This is a negative
  result: it cuts a constant fraction of the edges on a "tree ladder" for every radius.
- `sim/tight/cert.py`: exact rational check of the certificate at $p=3/8$ and $p=21/64$, and of
  the resulting exponents.
- `sim/tight/deglp.py`: the degree-only linear program under (A) and (B), whose optimum equals
  $(3-2s^3-s^6)/9$.
- `sim/tight/apo.py`: the Apollonian limit for join-edge analyses.
- `sim/tight/sanity.py`: checks (A), (B) and the degree inequality on many planar graphs and random
  subgraphs.

## Open questions

- What is the worst case of the expected gain of the uniform rule on planar graphs? At the best
  $p$, it lies between $0.1718$ (Theorem 2) and $0.1741$ (Apollonian networks).
- Can ratio $7+\varepsilon$ be reached in $\mathrm{poly}(1/\varepsilon)$ rounds with an exponent
  close to 2? This is equivalent to a deterministic $(1+\varepsilon)$-approximation of the
  fractional domination number on planar graphs [1, Open Problem 3].

## References

1. S. Amiri and S. Siebertz. Almost optimal constant-round approximation of dominating set in graph
   classes with excluded minors. arXiv:2610.09618, 2026.
2. M. Hilke, C. Lenzen, and J. Suomela. Brief announcement: Local approximability of minimum
   dominating set on planar graphs. PODC 2014.
3. R. Levi and D. Ron. A quasi-polynomial time partition oracle for graphs with an excluded minor.
   ACM Trans. Algorithms 11(3), 2015.
4. A. Czygrinow, M. Hańćkowiak, and W. Wawrzyniak. Fast distributed approximations in planar graphs.
   DISC 2008.
5. S. L. Hakimi. On the degrees of the vertices of a directed graph. J. Franklin Inst.
   279(4):290–308, 1965.
6. F. Kuhn. The Price of Locality: Exploring the Complexity of Distributed Coordination Primitives.
   PhD thesis, ETH Zurich, 2005.
7. M. R. Garey and D. S. Johnson. Computers and Intractability: A Guide to the Theory of
   NP-Completeness. W. H. Freeman, 1979.
8. D. S. Johnson. Approximation algorithms for combinatorial problems. J. Comput. System Sci.
   9(3):256–278, 1974.
9. I. Dinur and D. Steurer. Analytical approach to parallel repetition. STOC 2014.
10. B. S. Baker. Approximation algorithms for NP-complete problems on planar graphs. J. ACM
    41(1):153–180, 1994.
11. N. Linial. Locality in distributed graph algorithms. SIAM J. Comput. 21(1):193–201, 1992.
12. M. Parnas and D. Ron. Approximating the minimum vertex cover in sublinear time and a connection
    to distributed algorithms. Theoret. Comput. Sci. 381(1–3):183–196, 2007.
13. F. Kuhn, T. Moscibroda, and R. Wattenhofer. Local computation: Lower and upper bounds. J. ACM
    63(2), 2016.
14. C. Lenzen, Y.-A. Oswald, and R. Wattenhofer. What can be approximated locally? Case study:
    Dominating sets in planar graphs. SPAA 2008.
15. L. Jia, R. Rajaraman, and T. Suel. An efficient distributed algorithm for constructing small
    dominating sets. Distributed Computing 15(4):193–205, 2002.

## Citation

Until the paper appears, please cite this repository:

> *Random centres lower the round exponent of optimal constant-round planar domination.*
> GitHub repository, https://github.com/ssenge/MinimumDominatingSetOnPlanarGraphs, 2026.
