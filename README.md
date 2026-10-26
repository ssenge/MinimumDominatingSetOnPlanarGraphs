# Minimum Dominating Set on Planar Graphs: a smaller round exponent for optimal constant-round domination

Sebastian Senge, first published 26 October 2026. A paper is in preparation.

This repository contains machine-checked proofs (Lean 4 + Mathlib) and simulation code for an
improvement of the deterministic LOCAL $(7+\varepsilon)$-approximation of minimum dominating set
on planar graphs by Amiri and Siebertz [AS26].

## Summary

Hilke, Lenzen and Suomela [HLS14] showed that no deterministic constant-round LOCAL algorithm
approximates minimum dominating set on planar graphs within $7-\varepsilon$. Amiri and Siebertz
[AS26] matched this bound. For every $\varepsilon>0$, their algorithm returns a dominating set of
size at most $(7+\varepsilon)\gamma(G)$ in

$$T_0 + O\big((c_0/\varepsilon)^{\kappa}\big) \text{ rounds},\qquad \kappa=\frac{\ln 3}{\ln(1/q)},\quad q=\frac{23}{24},\quad \kappa\approx 25.81 .$$

Their Open Problem 4 asks whether the exponent $\kappa$ can be substantially reduced.

We change one step of their clustering procedure, a star contraction in the spirit of
[LR15, CHW08]: how the stars are chosen in Algorithm 1 (`RandomCluster`). Everything else carries over unchanged, including the radius recursion, the
view radius, the derandomisation and the rounding. **For planar graphs the exponent drops from
25.81 to below 5.89.**

| analysis | per-level contracted fraction $f$ | exponent $\kappa=\ln 3/\ln\frac{1}{1-f}$ |
|---|---|---|
| Amiri–Siebertz (heaviest-edge stars) | $1/24\approx 0.0417$ | $25.81$ |
| random centres, orientation bound (Thm 1), $p=3/8$ | $1935/12288\approx 0.1575$ | $<6.42$ |
| random centres, planar bound (Thm 2), $p=1/2$ (one fair coin, as in [AS26]) | $175/1152\approx 0.1519$ | $<6.7$ |
| random centres, planar bound (Thm 2), $p=3/8$ (three fair coins) | $357115/2097152\approx 0.1703$ | $5.88<\kappa<5.89$ |
| random centres, planar bound (Thm 2), $p=21/64$ (six fair coins) | $\approx 0.1718$ | $\approx 5.83$ |

$\kappa$ is the exponent of $1/\varepsilon$ in the number of rounds, so lowering it is a
polynomial speed-up. At $\varepsilon=0.01$, the term $(1/\varepsilon)^\kappa$ shrinks from about
$10^{52}$ to about $10^{12}$. For every target ratio in $(7,8]$, the algorithm of [AS26] is the
only one known, so this is the fastest known algorithm in that range.

## The rule

Fix a level $t$, and let $Q$ be the quotient graph of the current parts, weighted by the number of
edges between parts.

1. Every part becomes a **centre** independently with probability $p$. It reads $b$ fair coins of
   its leader, so $p=m/2^b$.
2. Every non-centre part that has a centre neighbour in $Q$ **joins its heaviest centre
   neighbour**. Ties are broken by identifier.
3. Each centre, together with the parts that joined it, forms one new part.

The new parts are vertex-disjoint stars in $Q$, so the radius recursion $r_t=3r_{t-1}+1$ and the
round bound of [AS26] still hold. Every join edge becomes internal. Hence the cut weight drops by
at least

$$\mathrm{gain}(C)=\sum_{P\notin C}\ \max_{X\in C\cap N(P)} w(PX).$$

Write $s=1-p$ and $g(d)=1-s^d$.

## Results

### Theorem 1 (bounded out-degree orientation)

Suppose the edges of $Q$ can be oriented so that every vertex has out-degree at most $k$. Then

$$\mathbb{E}[\mathrm{gain}(C)]\ \ge\ f_k(p)\,w(Q),\qquad f_k(p)=\frac{(1-p)\big(1-(1-p)^k\big)}{k}.$$

In a proper minor-closed class of edge density $a$, such an orientation exists with
$k=\lceil a\rceil$ (Hakimi). With $p=1/2$, we have $f_{\lceil a\rceil}(1/2)\ge 1/(8a)$, so the new
exponent is never worse than that of [AS26]. As the density grows, it becomes smaller by a factor
approaching 8.

| density $a$ | [AS26] | ours, $p=1/2$ | ours, best dyadic $p$ | ratio |
|---|---|---|---|---|
| 1 | 8.23 | 3.82 | 3.82 | 2.2× |
| 2 | 17.02 | 5.29 | 5.14 | 3.3× |
| 3 (planar, via Theorem 1) | 25.81 | 6.97 | 6.41 | 4.0× |
| 6 | 52.18 | 12.84 | 10.08 | 5.2× |
| 10 | 87.34 | 21.44 | 14.80 | 5.9× |
| 100 | 878.34 | 219.17 | 115.67 | 7.6× |

The same substitution also improves the other guarantees of [AS26, Thm. 6.2] for every proper
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

## Plugging the rule into Amiri–Siebertz

Numbering refers to [AS26]. In Algorithm 1 (`RandomCluster`), lines 6–13 are replaced by the rule
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
- **Theorem 6.1** (Kuhn's derandomisation) needs only a fixed finite number of fair coins per
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
- the existence of an out-degree-3 orientation (Euler's formula plus Hakimi's theorem).

The integration into [AS26], which reuses their proofs, is not formalised either.

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
- `sim/levels.py`: the original heaviest-edge selection of [AS26] and rank-based variants.
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
  fractional domination number on planar graphs [AS26, Open Problem 3].

## References

- [AS26] S. Amiri and S. Siebertz. Almost optimal constant-round approximation of dominating set in
  graph classes with excluded minors. arXiv:2610.09618, 2026.
- [CHW08] A. Czygrinow, M. Hańćkowiak, and W. Wawrzyniak. Fast distributed approximations in planar
  graphs. DISC 2008.
- [H65] S. L. Hakimi. On the degrees of the vertices of a directed graph. J. Franklin Inst.
  279(4):290–308, 1965.
- [HLS14] M. Hilke, C. Lenzen, and J. Suomela. Brief announcement: Local approximability of minimum
  dominating set on planar graphs. PODC 2014.
- [K05] F. Kuhn. The Price of Locality: Exploring the Complexity of Distributed Coordination
  Primitives. PhD thesis, ETH Zurich, 2005.
- [LR15] R. Levi and D. Ron. A quasi-polynomial time partition oracle for graphs with an excluded
  minor. ACM Trans. Algorithms 11(3), 2015.

## Citation

Until the paper appears, please cite this repository:

> Sebastian Senge. *Random centres lower the round exponent of optimal constant-round planar
> domination.* GitHub repository, https://github.com/ssenge/MinimumDominatingSetOnPlanarGraphs, 2026.
