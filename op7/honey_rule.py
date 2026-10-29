"""Quick test: id-orientation rule on the honeycomb (girth 6, 3-regular, gamma = n/4).

Rule: v joins if at most one neighbour has a smaller identifier; every vertex that is still
undominated joins as well. Reports |D| / (n/4) (an upper bound on the ratio, since gamma >= n/4)
over random, lexicographic and locally optimized adversarial orderings on a brick-wall torus.
"""
import random
import sys


def honeycomb(W, H):
    """Brick-wall honeycomb on a W x H torus (W, H even): (x, y) ~ (x +- 1, y), and
    (x, y) ~ (x, y + 1) when x + y is even."""
    idx = lambda x, y: (x % W) * H + (y % H)
    adj = [set() for _ in range(W * H)]
    for x in range(W):
        for y in range(H):
            v = idx(x, y)
            adj[v].add(idx(x + 1, y)); adj[idx(x + 1, y)].add(v)
            if (x + y) % 2 == 0:
                adj[v].add(idx(x, y + 1)); adj[idx(x, y + 1)].add(v)
    return [sorted(a) for a in adj]


def rule(adj, rank):
    n = len(adj)
    D = [sum(rank[u] < rank[v] for u in adj[v]) <= 1 for v in range(n)]
    dom = [D[v] or any(D[u] for u in adj[v]) for v in range(n)]
    return sum(D) + sum(not d for d in dom)


def main(W=24, H=24, iters=20000, seed=1):
    rng = random.Random(seed)
    adj = honeycomb(W, H)
    n = len(adj)
    best = 0
    for trial in range(20):
        rank = list(range(n)); rng.shuffle(rank)
        best = max(best, rule(adj, rank))
    print(f"random orders: max ratio {best / (n / 4):.3f}")
    for name, key in (("lex x,y", lambda v: (v // H, v % H)), ("lex y,x", lambda v: (v % H, v // H)),
                      ("diag", lambda v: (v // H + v % H, v // H))):
        rank = sorted(range(n), key=key)
        rank = [rank.index(v) for v in range(n)]
        print(f"{name}: ratio {rule(adj, rank) / (n / 4):.3f}")
    # local search: swap ranks to maximize |D|
    rank = list(range(n)); rng.shuffle(rank)
    cur = rule(adj, rank)
    for it in range(iters):
        a, b = rng.randrange(n), rng.randrange(n)
        rank[a], rank[b] = rank[b], rank[a]
        new = rule(adj, rank)
        if new >= cur:
            cur = new
        else:
            rank[a], rank[b] = rank[b], rank[a]
    print(f"adversarial local search: ratio {cur / (n / 4):.3f}")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
