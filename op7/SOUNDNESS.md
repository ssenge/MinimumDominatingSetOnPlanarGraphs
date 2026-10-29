# Soundness of the R13 certificate (discharge_r13v7.py and discharge_r13v8.py)

This note explains why a feasible solution of the LP in `discharge_r13v7.py` proves the bound
|D'| <= ρ LP_U for rule R13. It goes through every row family of the LP and states which local
inequality the row encodes and why that inequality holds. Section 10 covers the current version
`discharge_r13v8.py`, which changes three things in v7; each makes the LP easier and keeps it
sound.

Status: written with AI assistance and not yet reviewed by a person. Writing it out found five
places in the previous version `discharge_r13z.py` where a row claimed more charge than the
argument gives; v7 fixes them (section 9). The v7 values pass the exact check with v7, and the v8
values of the README table pass it with v8.

Line numbers in sections 4 to 8 refer to `discharge_r13v7.py`.

## 1. Statement

Let g >= 5 and C = g/(g-2), so 1 < C <= 5/3. Let G be a planar graph of girth at least g with
distinct identifiers, and let x be a fractional dominating set of G. Rule R13 (see `README.md`)
computes D1, U and D' from x and the identifiers. Let

  LP_U = min x(N[U]) subject to x(N[u]) >= 1 for u in U and 0 <= x <= 1/3.

**Theorem.** If the LP `discharge_r13v7.py` or `discharge_r13v8.py`, run with `GIRTH=g` at ratio
ρ, has a solution with margin tmarg >= 0, then |D'| <= ρ LP_U for every such G, x and identifier
assignment.

`cert_exact.py` checks such solutions in exact rational arithmetic. For v8 these are
(g, ρ) = (5, 3.52), (6, 3.24), (7, 3.17), (8, 3.15), (10, 3.14), (12, 3.14), (16, 3.14) and
(30, 3.14); for v7 they are (5, 3.87), (6, 3.46), (7, 3.38), (8, 3.35), (10, 3.31), (14, 3.29) and
(16, 3.28). A certificate for g also covers every larger girth. If x is a
(1 + δ)-approximation of the fractional optimum, then LP_U <= x(V minus D1) and
|D1| <= 3 x(D1), so R13 outputs a dominating set of size at most max(3, ρ)(1 + δ) γ(G)
(Lemma 1(f) shows it dominates).

## 2. Notation

As in R13: H is the set of hubs (vertices with at least 4 neighbours in U), W-hubs are hubs
outside U, U-hubs are hubs inside U. U' = U minus N[H], T = idrule(G[U']), P = U' minus T,
Z = U minus U', Q = Z minus N(T), Z1 = Z ∩ N(T). For a hub w, a_w = |N(w) ∩ Q|; w is heavy if
a_w >= 4 and light otherwise. Q_h is the set of vertices of Q with a heavy hub in their closed
neighbourhood, Q_l = Q minus Q_h, T2 = idrule(G[Q_l]). A vertex of Q_h without a neighbour in
T2 selects a heavy hub of maximum load in its closed neighbourhood, and S is the set of selected
hubs. D' = T ∪ T2 ∪ S.

The load bucket of a heavy hub is 4, 5 or 6, where 6 stands for a load of 6 or more. The
selector count of a selected hub is the number of vertices that select it, capped at 2.

idrule on a graph F of maximum degree 3: J is the set of vertices with fewer smaller than larger
neighbours, R the set of vertices outside J without a neighbour in J, and idrule(F) = J ∪ R. Every
vertex outside idrule(F) has a neighbour in J.

## 3. Structure of R13

**Lemma 1.**
(a) A vertex that is not a hub has at most 3 neighbours in U. So G[U'] and G[Q_l] have maximum
    degree at most 3.
(b) No vertex of U' is a hub or adjacent to a hub. Every U-hub lies in Q. Every neighbour of a
    hub that lies in U lies in Z.
(c) Every Q-neighbour of a heavy hub lies in Q_h. A heavy U-hub lies in Q_h, has no neighbour in
    Q_l, and therefore selects.
(d) A vertex of Z1 is not a hub, has a neighbour in T and has a hub neighbour.
(e) Every hub neighbour of a Q_l vertex is light. A Q_l vertex that is not a U-hub and has no U-hub
    neighbour has a W-hub neighbour.
(f) D1 ∪ D' dominates G.

*Proof.* (a) holds by the definition of a hub; a vertex of Q_l that is a hub is light, so it has at
most 3 neighbours in Q. (b) U' = U minus N[H]. A U-hub h lies in Z, and it has no neighbour in
U' (a vertex of U' is not adjacent to a hub), so none in T and h ∈ Q. A U-neighbour of a hub lies
in N(H), so not in U'. (c) If q ∈ Q is adjacent to a heavy hub w, then w ∈ N[q] and q ∈ Q_h. A heavy
U-hub h lies in Q by (b) and h ∈ N[h], so h ∈ Q_h; its Q-neighbours lie in Q_h, so it has no
neighbour in Q_l ⊇ T2. (d) U-hubs have no neighbour in T by (b). A vertex of Z lies in N[H], so a
vertex of Z that is not a hub has a hub neighbour. (e) A heavy hub in N(q) would put q into Q_h.
The vertex q lies in N[H]. (f) D1 dominates V minus U. T dominates U', Z1 ⊆ N(T), T2 dominates Q_l,
and a vertex of Q_h either has a neighbour in T2 or selects a hub in its closed neighbourhood. ∎

## 4. Dual and charges

The LP dual of LP_U is max Σ_{u ∈ U} y_u − (1/3) Σ_v s_v subject to Y(v) − s_v <= 1, s >= 0 and
y >= 0, where Y(v) = y(N[v] ∩ U). For any y >= 0 the choice s_v = (Y(v) − 1)^+ is feasible, so by
weak duality

  dual(y) = Σ_{u ∈ U} y_u − (1/3) Σ_v (Y(v) − 1)^+ <= LP_U.

The certificate sets y_u = (1 − ε_t)/3, where t is the type of u (section 7) and ε_t ∈ [0, 1] is an
LP variable. Give every vertex v the initial charge

  c0(v) = ρ y_v [v ∈ U] − (ρ/3)(Y(v) − 1)^+ − [v ∈ D'].

Then Σ_v c0(v) = ρ dual(y) − |D'|, and the theorem follows from Σ_v c0(v) >= 0. The proof moves
charge between vertices (transfers that sum to zero) and adds Euler terms whose total is at most
0 (section 5). Every row of the LP says that some vertex, or some part of a U-hub, ends with charge
at least tmarg >= 0.

### 4.1 Who pays the overclaim

The overclaim of v is (Y(v) − 1)^+. Since y <= 1/3, a vertex with at most 3 vertices in N[v] ∩ U
has no overclaim.

- A vertex v ∈ U that is not a hub has at most 3 U-neighbours. It pays its own overclaim. With
  fewer than 3 U-neighbours there is none. With exactly 3, its charge ρ y_v − (ρ/3)(Y(v) − 1)^+ is
  the minimum of the version without overclaim (row "A") and the version

    ρ y_v − (ρ/3)(Y(v) − 1) = 2ρ/9 − (2ρ/9) ε_v + (ρ/9) Σ_{u ∈ N(v) ∩ U} ε_u    (row "B").

  The term (ρ/9) ε_u of each U-neighbour u enters through the B version of the lower-bound
  variable of that edge (section 6), with a lower bound on ε_u in place of ε_u.
- A vertex outside U that is not a hub has at most 3 U-neighbours and no overclaim.
- For a hub w, Lemma 1(b) splits N[w] ∩ U into Q-neighbours, Z1-neighbours and w itself if
  w ∈ U. Write Y_Q(w) = y(N(w) ∩ Q) and Y_1(w) = y(N(w) ∩ Z1). Since (a + b − 1)^+ <= (a − 1)^+ + b
  for b >= 0,

    (Y(w) − 1)^+ <= (Y_Q(w) + [w ∈ U] y_w − 1)^+ + Y_1(w).

  Every Z1-vertex pays (ρ/3) y_z to each of its hub neighbours, which covers the term Y_1(w) of
  every hub. The first term is paid as follows.
  - A light W-hub has a_w <= 3, so Y_Q(w) <= 1 and the first term is 0.
  - A light U-hub h: the first term is the overclaim of h over N[h] ∩ Q, at most 4 vertices. The
    vertex part of h pays it like a non-hub vertex with a_h U-neighbours (B row if a_h = 3).
  - A heavy hub (W or U): its hub row pays the first term (section 8.5).

### 4.2 Who pays for D'

T is paid by the A and B rows of U'-vertices (constant inT), T2 by the rows of Q_l-vertices
(including light U-hubs in Q_l), and S by the rows of the heavy hubs (constant "kept"). By Lemma 1
no other vertex lies in D': vertices of Z1, Q_h-vertices that are not heavy hubs, and light
W-hubs are not in D'. A light U-hub is in D' only if it lies in T2, and its Q_l-row pays for that.

### 4.3 U-hubs in two parts

The charge of a U-hub h is split into a vertex part and a hub part.

- **Heavy U-hub.** The vertex part gets ρ y_h and pays the heavy hubs in N[h], its own hub part
  included (section 8.4). The cost of h ∈ S sits in the hub part, which gets −(ρ/3)(Y_Q(h) + y_h − 1)^+ − [h ∈ S] and the payments of its members. Its members
  are the Q-neighbours of h plus its own vertex part; the own vertex part is a member without an
  edge.
- **Light U-hub.** The vertex part is a Q_h- or Q_l-type over its Q-neighbours (flag "U") with its
  overclaim over N[h] ∩ Q. Its Euler term in Z and ZU is the light-hub budget (section 5.3); in Q_h
  the vertex part also claims the halves of its heavy W-hub edges and its B-term (section 8.3).

## 5. Euler terms

### 5.1 The families

For a family F (a subgraph of G) and a weight ν_F >= 0, the rows add ν_F t_F(v) to the charge of
each vertex v, for a number t_F(v) given by the type. The proof needs Σ_v t_F(v) <= 0 for every
family. There are four families in v7; v8 adds a fifth, Zh (section 10).

- **Z**: the vertices of Z and all hubs; the edges inside Z and the edges between Z and hubs.
  Edges between two W-hubs are not in Z.
- **ZU**: Z plus the vertices of U', with the edges inside U' and between U' and Z added.
- **HU**: the subgraph induced by the heavy U-hubs.
- **B**: the edges between heavy hubs and rich vertices. A rich vertex is a vertex of Q_h that is
  not a heavy hub and has at least 3 heavy hubs in its neighbourhood. B is bipartite and G has
  girth at least 5, so B has girth at least 6. (In all seven certified solutions λ = 0, so B plays
  no role in the certified values.)

Each family is planar of girth at least g, and B has girth at least 6. For a planar graph with
girth at least k, |E| <= k/(k-2) (|V| − 2) if it has a cycle, and |E| <= |V| − 1 otherwise. So
Σ_v (deg(v)/2 − k/(k-2)) <= 0. The constants are C for Z, ZU and HU and 3/2 for B.

### 5.2 Leaves

**Lemma 2.** Let F be planar of girth at least g. Put τ(v) = 0 if deg_F(v) = 0, τ(v) = −1/2 if
deg_F(v) = 1, and τ(v) = deg_F(v)/2 − C otherwise. Then Σ_v τ(v) <= 0.

*Proof.* Let L be the set of degree-1 vertices, V2 the vertices of degree at least 2, e(L) the
number of edges inside L and e(L, V2) the number between L and V2. Then
Σ τ = e(V2) + e(L, V2)/2 − C |V2| − (e(L, V2) + 2 e(L))/2 = e(V2) − C|V2| − e(L), which is at most
0 by the edge bound for G[V2]. ∎

So a row may use any t_F(v) <= τ(v). In particular a counted degree d that is only a lower bound
on deg_F(v) is safe when d >= 2 (d/2 − C <= deg_F(v)/2 − C) or d = 0 with no edges at all. When
d = 1 is a lower bound only, the vertex is a leaf or has degree at least 2, so
t = min(−1/2, 1 − C) is safe. When d = 1 is exact, t = −1/2. (This is the "leaf pays ν/2 to its
neighbour" rule of the code comments.)

For B the code uses the plain term λ(deg_B/2 − 3/2) without a leaf rule; at degree 1 this is
−λ, below τ.

### 5.3 Light hubs

In the families Z and ZU a light hub w (W or U) gives 1/9 to each neighbour in Q_l. Let θ(v) be
τ(v) plus 1/9 for every light hub neighbour if v ∈ Q_l, θ(w) = τ(w) − (1/9)|N(w) ∩ Q_l| for a light
hub w, and θ = τ otherwise. This only moves amounts between vertices, so Σ θ = Σ τ <= 0.

A light hub w has at least 4 neighbours in U, all in Z (Lemma 1(b)), so deg_Z(w) >= 4 and the
same in ZU. It has at most 3 Q-neighbours. So θ(w) >= 2 − C − 3/9 = 5/3 − C >= 0. A light U-hub
in Q_h with k heavy W-hub neighbours has deg_Z(h) >= 4 + k, since those hubs are not in U, so
θ(h) >= k/2. Its vertex part claims this k/2 (lines 386 to 389).

A light W-hub is not in D'. Its overclaim is paid by its Z1-neighbours (section 4.1), so its final
charge is ν_Z θ_Z(w) + ν_ZU θ_ZU(w) >= 0. This is the only row that is checked by hand and not in
the LP. The code comment at lines 424 to 426 writes it as k1 · 7/18 − k2/9 + (4 − k1)/2 − 5/3 >= 0, the same
inequality after moving the leaves of section 5.2.

A Q_l-vertex that is a leaf of F has θ = −1/2 + 1/9 = −7/18; a non-leaf Q_l-vertex with j light
hub neighbours has θ = deg/2 − C + j/9.

## 6. Transfers

Charge moves only along edges of G[U] and from payers to heavy hubs. In every case the amount
depends only on data that both sides see, and both sides use the same LP variable with opposite
signs, so all transfers sum to zero.

**Lower-bound variables.** A row does not contain the transfers themselves but variables
m(type or class, slot, version) with m <= (amount received on that edge) for every neighbour type
that is consistent with the slot. The A version bounds the transfer, the B version the transfer
plus (ρ/9) ε_u of the neighbour u (section 4.1), where ε_u is replaced by a lower bound (the
smallest ε over the class or base type of u). Extra constraints for neighbour types that do not
occur only make the rows harder.

The edge kinds (lines 209 to 309):

- **U'-U'.** Arc transfers with the slot model of the subcubic idrule certificate
  (`discharge_a2.py`; the amounts are LP variables of v7), keyed by the ordered pair of U'-types; the slot of the edge at v is (direction, neighbour in J, neighbour's
  degree in G[U']), which both sides know. The type filter `ok` only drops impossible
  configurations: a larger neighbour of degree at most 2 that has a smaller neighbour is not in J.
- **Q_l-Q_l.** The same arc transfers on G[Q_l], keyed by the base type (the variants n, u, U of a
  Q_l-type share them), with the smallest ε over the variants in the B bound.
- **P-Q_h, P-Q_l** by (full U'-type, Q-class); **Q_h-Q_h, Q_h-Q_l** by classes; **Z1-U', Z1-Q_h,
  Z1-Q_l, Z1-Z1** by (full Z1-type, class or type). Between two vertices of the same Q_h-class, or
  of the same Z1-type, there is no transfer.
- **No transfer** on edges to the vertex part of a heavy U-hub (from Q_h or Z1), on edges from Z1
  to a light U-hub, and between heavy U-hubs. The rows on both sides contain no variable for these
  edges (on the Q_h and Z1 side a variable m <= 0, with the B bound of the U-hub's ε).

U-hubs have no U'-neighbours, and U'-vertices in T have no Q-neighbours (Lemma 1), so these are all
edges of G[U].

**An unrealizable slot.** A smaller neighbour of degree 1 in G[U'] (or G[Q_l]) has no smaller and
one larger neighbour, so it lies in J. The slot ('i', 0, 1), a smaller neighbour outside J of
degree 1, therefore never occurs. The LP has no transfer constraint for the 356 lower-bound
variables with this slot (160 on U'-types, 196 on Q_l base types), so they sit at their upper bound
50, and the rows of the types that contain this slot hold trivially. That is sound because those
types do not occur.

**Payments to heavy hubs** (lines 310 to 353). A Q_h-vertex q that selects pays gs to its selected
hub and gn to each other heavy hub in N(q); if q has a T2-neighbour it does not select and pays gn
to all of them. The vertex part of a heavy U-hub pays hs to its selected hub and hn to each of the
other K − 1 heavy hubs in N[h], its own hub part included when h does not select itself. On the hub
side the member bound M(kind, rich, bucket, version) is at most the payment, plus λ/2 for a rich
member (the hub's half of the B-edge), plus ν_f/2 for f ∈ {Z, ZU} at bucket 6 (the hub's half of
the member edge), minus (ρ/9)(1 − ε) in the B version (the member's share of the hub's overclaim).
The own vertex part of a heavy U-hub has kinds own_s1, own_s2 (selects itself, with selector count)
and own_n, and its bound has no Euler half, since it has no edge to its hub part.

A payment can be negative; nothing in the argument needs a sign.

## 7. Types and coverage

Every vertex of U gets one type (the classification in `check_r13z.py` follows these
definitions). The proof is a counting argument, so the types need not be local. Counts marked "capped" stand for that value or more.

- ('U', fs, nh, nl, nz): a vertex of U'. fs is the tuple of idrule slots over its U'-neighbours,
  nh, nl, nz the numbers of Q_h-, Q_l- and Z1-neighbours. If nh + nl > 0 the vertex is in P.
- ('L', fs, np, nh, nz, nlh, hk): a vertex of Q_l. fs over its Q_l-neighbours, np, nh, nz the
  numbers of P-, Q_h- and Z1-neighbours. hk = "U" for a light U-hub (np = nz = 0: U-hubs have no
  U'-neighbours, and its Z1-neighbours are not slots); "u" if a light U-hub is among its
  Q-neighbours; "n" otherwise. For "n", nlh = 1 means at least one W-hub, except when the vertex
  has no Z-neighbour in U (no fs, nh, nz): then nlh is the exact number of W-hubs, capped at 2.
- ('H', us, ch, hk, ab, c): a vertex of Q_h that is not a heavy U-hub. us lists its U-neighbours as
  P, Qh, QlT (in T2), QlP, Z1 or Hh (heavy U-hub); 1 + ch is the number of heavy hubs in N(q), ch
  capped at 3; ab is the bucket of the selected hub (of the heaviest hub if q does not select);
  c is the selector count of the selected hub, 0 if q has a T2-neighbour. hk = "U" for a light
  U-hub, whose us lists only its Q-neighbours.
- ('HH', KW, KU, ss, ab, c): the vertex part of a heavy U-hub h. KW is the number of heavy W-hubs
  in N(h), capped at 3; KU the number of heavy U-hubs in N[h], h included; ss = 1 if h selects
  itself; ab and c as above. All heavy U-hubs in N(h) are Q-neighbours, so KU − 1 <= a_h <= the
  load of the selected hub. KU is capped at 6 only for ab = 6.
- ('Z', sl, nhub): a vertex of Z1. sl lists its U-neighbours as T, P, Qh, Ql, Z1, Hh, Hl (light
  U-hub), with at least one T; nhub is the number of hubs in N(z), capped at 3.

The LP enumerates all tuples within these ranges (lines 107 to 157), so every vertex has a type in
the LP. Some enumerated types cannot occur (section 6); their rows are harmless. `check_r13z.py` also confirms this on adversarial instances.

## 8. The rows

Every row has the form (charge expression) − tmarg >= (constant). In each case below, the charge
expression is a lower bound on the final charge of the vertex or part, given that the transfers
are at least their lower-bound variables and the Euler terms are at most θ.

### 8.1 U'-vertices (lines 354 to 370)

Charge ρ y_v − inT plus transfers on all edges plus ν_ZU t_ZU(v). A U'-vertex lies only in ZU, and
its ZU-degree is its U-degree len(fs) + nh + nl + nz, which is exact (no hub neighbours). So
t_ZU = −1/2 at degree 1 and d/2 − C otherwise. B row when it has 3 U-neighbours.

### 8.2 Q_l-vertices (lines 398 to 433)

Charge ρ y_v − inT plus transfers plus Euler terms in Z and ZU. Types "n" and "u" count the
degree d = len(fs) + nh + nz + nW in Z (plus np in ZU), where nW = nlh for "n" and nW = 0 for "u".
This is a lower bound; the uncounted edges go to W-hubs, which are light (Lemma 1(e)).

- d >= 2: t = d/2 − C + j/9, where j is a lower bound on the number of light hubs in N(v): nlh for
  "n" (at least one W-hub by Lemma 1(e)), 1 for "u" (the light U-hub).
- d = 1, type "n": then v has no Z-neighbour in U and nlh = 1 is exact, so v is a leaf of the
  family; t = −7/18.
- d = 1, type "u": the counted edge goes to the light U-hub; uncounted light W-hubs may exist. If
  there are none, v is a leaf with t = −7/18. Otherwise deg >= 2 and v gets 1/9 from at least two
  light hubs, so θ >= 1 − C + 2/9. The row uses min(−7/18, 1 − C + 2/9).
- Type "U" (a light U-hub in Q_l) has no Euler term.

B row when the vertex has 3 U-neighbours (for "U": 3 Q-neighbours, section 4.1).

### 8.3 Q_h-vertices (lines 371 to 397)

Charge ρ y_q minus the payments gs and ch · gn (or (1 + ch) gn when q has a T2-neighbour), plus
transfers, plus Euler terms.

- hk = "n": the counted Z-degree is d = #Qh + #QlT + #QlP + #Z1 + 1 + ch (heavy U-hub neighbours
  are among the 1 + ch heavy hubs and are not counted twice), plus #P in ZU. Uncounted edges go to
  light W-hubs. So t = d/2 − C for d >= 2 and t = min(−1/2, 1 − C) for d = 1.
- hk = "U": no Z-term; instead (1 + ch − #Hh)/2 per family from the heavy W-hub edges (section
  5.3).
- Rich vertices (1 + ch >= 3) get λ((1 + ch)/2 − 3/2), their B-degree.
- ch = 3 stands for at least 3 further heavy hubs. Each one beyond costs gn and adds 1/2 to the
  degree in Z, ZU and B; row "coef" says gn <= (λ + ν_Z + ν_ZU)/2, so the row for ch = 3 covers all
  larger values. For hk = "U" all heavy U-hub neighbours are among us, so the extra hubs can be
  taken to be W-hubs, whose edge half at h is free.

B row when q has 3 U-neighbours.

### 8.4 Vertex parts of heavy U-hubs (lines 434 to 449)

Charge ρ y_h − hs − (K − 1) hn, with K = KW + KU, plus

- KW/2 per family Z, ZU: the edges to heavy W-hubs. The hub part counts only its Q-member edges,
  and W-hubs are not in U, so these halves are free. Row "coefW" (hn <= (ν_Z + ν_ZU)/2) covers
  KW > 3.
- ν_HU t_HU with HU-degree KU − 1: −1/2 at degree 1 (exact: KU is capped only for ab = 6, so HU-degree 1 means KU = 2 exactly), (KU − 1)/2 − C
  otherwise, nothing at degree 0. For KU = 6 with ab = 6 (at least 6), row "coefU" says
  hn <= ν_HU/2 for each further heavy U-hub neighbour. Only the HU half is free: the Z and ZU halves
  of an edge between two heavy U-hubs belong to the two hub parts (fix 2 in section 9).

The overclaim of h is paid by the hub part, so there is no B row.

### 8.5 Heavy hubs (lines 450 to 479)

For a heavy W-hub, or the hub part of a heavy U-hub, with members M_1, ..., M_r (its Q-neighbours,
plus the own vertex part for a U-hub) the final charge is at least

  Σ_i (received payment_i) − (ρ/3)(Σ_i y_i − 1)^+ − kept + ν_Z θ_Z + ν_ZU θ_ZU + λ τ_B,

where kept = 1 if the hub is selected. Here θ_Z, θ_ZU >= a/2 − C with a the load: the hub has a
member edges in Z and ZU. For a U-hub this is only the share a/2 − C of deg_Z(h)/2 − C; the rest of
deg_Z(h) belongs to the vertex part (section 8.4) or is unused.

- **Bucket 4 and 5** (load exactly 4 or 5): one row for every multiset of member kinds of size a
  (W-hub) or a plus the own kind (U-hub). The selector count c in the kinds must equal the number
  of selectors in the multiset, capped at 2. Euler term (a/2 − C) per family. The B version adds
  ρ/3 and uses the B member bounds; the A version covers Σ y_i <= 1.
- **Bucket 6** (load at least 6): rows over 4-multisets of Q-member kinds (plus the own kind for a
  U-hub), with Euler term −C per family; the half 1/2 of each member edge sits in the member bound
  M, and M >= 0 for every Q-member kind at bucket 6. Choose 4 Q-members S: a Q-member selector if there is one (the only one if c = 1; if the only
  selector is the own vertex part, S needs none) and a rich member if there is one. This is possible since there
  are at least 6 Q-members. Then the real charge is at least the row for S plus the M of the
  members outside S, which are at least 0. The rows check c consistently: for c = 1, exactly one
  selector in the multiset.
- The B-family term: −3/2 λ if some member is rich, plus λ/2 inside each rich member's M; this is
  exactly λ(deg_B/2 − 3/2). At bucket 6, S contains a rich member if the hub has one.

### 8.6 Z1-vertices (lines 480 to 493)

Charge ρ y_z − nhub (ρ/3) y_z (the overclaim payments of section 4.1) plus transfers plus Euler
terms. The Z-degree is nhub + #Qh + #Ql + #Z1 (U-hub neighbours count among the hubs), plus #T +
#P in ZU; at degree 1 this is exact (nhub = 1), so t = −1/2. Row "coef" for nhub = 3: each further
hub costs (ρ/9)(1 − ε) and adds 1/2 per family. B row when z has 3 U-neighbours.

## 9. The five fixes of v7

Writing sections 5 to 8 showed five places where `discharge_r13z.py` (v6f) claimed more than the
argument gives.

1. The own vertex part of a heavy U-hub was a member kind with the bucket-6 half ν/2 in its bound,
   but there is no edge between the vertex part and the hub part. v7 gives it the own kinds of
   section 6, always includes it in its hub part's rows, and drops the half.
2. Row coefU credited (ν_Z + ν_ZU)/2 for each heavy U-hub neighbour beyond the fifth. Those halves
   belong to the hub parts at both ends. v7 keeps only ν_HU/2.
3. A Q_h-vertex with counted Z-degree 1 got the leaf term −1/2, but it may have light W-hub
   neighbours that its type does not record. v7 uses min(−1/2, 1 − C). This one made v6f
   invalid, not just unproved: on a tree with 10 vertices (a Q_h-vertex q1 adjacent to a heavy
   W-hub of load 4 and to a light W-hub) the v6f solution leaves q1 with charge −0.085, far
   below the margin. The instance is a regression test in `charge_check.py`.
4. The same for a Q_l-vertex of type "u", which does not record its W-hubs. v7 uses
   min(−7/18, 1 − C + 2/9).
5. A Q_l-vertex of type "n" with P-neighbours but no other neighbour in Z recorded only "at least
   one W-hub", and its Z-row still used the leaf term −7/18. With two W-hubs its term is
   1 − C + 2/9, which is −4/9 < −7/18 for g = 5. v7 records the exact number of W-hubs (1, or at
   least 2) for every Q_l-vertex without Z-neighbours in U.

An independent adversarial referee pass (an AI agent that read only the code of v6f) found the
same five problems, with explicit instances for 3, 2 and 4, and no further invalid row; its own
charge simulation found no negative charge with v7. A second referee pass checked this note
against the v7 code, found no soundness problem and pointed out wording gaps, which are fixed.

All table values stay feasible in exact arithmetic with v7; the certified margins are 0.0012,
0.0018, 0.0004, 0.0020, 0.0014, 0.0028 and 0.0009 for g = 5, 6, 7, 8, 10, 14 and 16.

## 10. Version 8

`discharge_r13v8.py` differs from v7 in three places.

1. **A heavy U-hub is one entity.** In v7 the vertex part and the hub part of a heavy U-hub h
   each had to end with at least the margin, but only their sum enters Σ_v c0(v). In v8 the vertex
   part is a member of its own hub part, with kind (ss, c, KW, KU, bucket), and its member bound is
   its whole net charge:

     M_own <= ρ y_h − (payments of h to the other heavy hubs in N[h]) + (ν_Z + ν_ZU + ν_Zh) KW/2
              + ν_HU t_HU(h).

   If h selects itself it pays hn to the other K − 1 heavy hubs; otherwise it pays hs to its
   selected hub and hn to the other K − 2. Its payment to its own hub part is internal and
   dropped. The B version subtracts (ρ/9)(1 − ε_h), the share of y_h in the overclaim of h. Rows
   coefW and coefU still cover KW > 3 and KU > 6. For loads 4 and 5 the member multiset is exact,
   so the number of heavy U-hub members equals KU − 1, and a row uses only own kinds with that
   KU. For load at least 6, the 4 sampled Q-members contain at most KU − 1 heavy U-hubs. The rows
   "HH" of v7 are gone; sections 8.4 and 8.5 merge into one hub row per heavy U-hub.
2. **The family Zh.** Its vertices are Q_h and the heavy W-hubs, and its edges are all edges of G
   between them except edges between two W-hubs. It is a subgraph of G, so Lemma 2 applies with
   the constant C. The degrees its rows use are exact, except at ch = 3, KW = 3 and load bucket 6,
   where they are lower bounds and the rows coef, coefW and the member halves pay for the rest.
   - A vertex of Q_h that is not a heavy U-hub has Zh-degree #Qh + 1 + ch. Its Q_h-neighbours are
     its Qh slots (light U-hubs in Q_h included) and its heavy U-hub neighbours, which are among
     its 1 + ch heavy hubs; heavy W-hubs are the rest of those. For ch <= 2 this is exact, so the
     leaf term −1/2 is exact; row "coef" adds ν_Zh/2 for each heavy hub beyond the fourth.
   - A heavy hub has Zh-degree at least its load a, since all its Q-neighbours lie in Q_h (Lemma
     1(c)). The hub rows use a/2 − C, or ν_Zh/2 per sampled member at bucket 6, as for Z.
   - A heavy U-hub h also has its KW heavy W-hub edges in Zh; its vertex part claims those halves.
   - A light U-hub in Q_h is in Zh with its own term (#Qh + 1 + ch)/2 − C. Its light-hub budget
     lives only in Z and ZU.
   Q_l, Z1, U' and light W-hubs are not in Zh.
3. **Light-hub returns.** A light hub has θ >= 2 − C − k r when it gives r to each of its
   k <= 3 Q_l-neighbours, so r = (2 − C)/3 keeps θ >= 0. This is 1/9 at g = 5 and 1/6 at g = 6.
   In section 8.2, 1/9 becomes r: leaves get −1/2 + r, non-leaves d/2 − C + j r, and the leaf term
   of type "u" is min(−1/2 + r, 1 − C + 2r).

`charge_check.py` checks v8 with a heavy U-hub as one entity and with the family Zh. With the
exact solutions at (5, 3.52) and (6, 3.24), the smallest charge on the same instance families and
on the regression trees again equals the certified margin, and light hubs end at 0 or more.
The certified margin is 0.002441 for every g from 10 to 30; the binding rows there do not involve
C.

## 11. Summary of the proof

Fix G, x and the identifiers. Give every vertex of U the type of section 7 and set
y = (1 − ε_t)/3 from the LP solution. Split the charge c0 as in section 4 and apply the transfers
of section 6. Each vertex, part of a U-hub and light hub ends with a charge at least the left side
of its row (sections 5.3 and 8), so at least tmarg >= 0. The Euler terms added along the way sum to
ν_Z Σ θ_Z + ν_ZU Σ θ_ZU + ν_HU Σ t_HU + λ Σ τ_B (+ ν_Zh Σ t_Zh in v8) <= 0 (Lemma 2 and section 5.3), and the transfers sum
to 0. So Σ_v c0(v) >= 0, that is |D'| <= ρ dual(y) <= ρ LP_U. ∎

## 12. What is checked and what is not

- Checked by machine: feasibility of the LP for the table values, in exact rational arithmetic
  (`cert_exact.py`); on instances, that every type that occurs is in the LP and that
  |D'| <= ρ dual(y) for the y of the LP solution (`check_r13z.py`).
- Checked by machine on instances (`charge_check.py`): the actual final charge of every vertex and
  of both parts of every heavy U-hub (v7) or of every heavy U-hub as one entity (v8), computed from the exact solution with the actual transfers,
  payments, overclaims and Euler terms (actual degrees, leaves and light-hub returns), is at least
  the certified margin; every light W-hub ends with at least 0; every light U-hub keeps its budget;
  every family has Euler sum at most 0; and the total equals ρ dual(y) − |D'| plus the Euler sums.
  This held in adversarial searches over U and the identifiers on 13 families of planar graphs of
  girth 5 (g = 5, ρ = 3.87 for v7 and 3.52 for v8) and on the families of girth at least 6
  (g = 6, ρ = 3.46 for v7 and 3.24 for v8), and for v8 also on random trees and on subdivided
  planar graphs (girth 10, 15 and 30) at (5, 3.52), (7, 3.17), (8, 3.15) and (10, 3.14). The smallest
  charge found always equals the certified margin, since some rows are tight. Doubling ν_Z in the
  solution makes charges negative, so the check does see the Euler terms.
- Checked by argument only: this note, that is, that each row family encodes the local
  inequality stated here and that the type enumeration covers every vertex. Two AI referee passes
  checked v7 (section 9). One AI referee pass checked the v8 changes of section 10 against the
  code, re-checked the stored solutions in exact arithmetic and ran adversarial searches on
  trees at g = 5, 6 and 10; it found no soundness problem, only wording (fixed) and the missing
  instances of girth >= 7 in `charge_check.py` (added). The slot model of the idrule part comes from `discharge_a2.py`.
- Limits: no review by a person; the instance checks cover finite families only; and an AI
  referee can share blind spots with the AI that wrote the argument.
