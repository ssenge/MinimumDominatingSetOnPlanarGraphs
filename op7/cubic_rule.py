"""Check |D| <= 3n/4 for the rule on cubic graphs: join if at most one neighbour is smaller, then
add every vertex that is still undominated. Random cubic graphs, random and adversarial orders."""
import random
import networkx as nx

from honey_rule import rule


def check(adj, rank):
    n = len(adj)
    d = rule(adj, rank)
    assert 4 * d <= 3 * n, (n, d)
    return d / n


rng = random.Random(7)
worst = 0
for trial in range(300):
    n = rng.choice([8, 10, 12, 16, 20, 30, 50])
    G = nx.random_regular_graph(3, n, seed=rng.randrange(10**9))
    adj = [sorted(G[v]) for v in range(n)]
    rank = list(range(n)); rng.shuffle(rank)
    cur = check(adj, rank)
    for it in range(3000):
        a, b = rng.randrange(n), rng.randrange(n)
        rank[a], rank[b] = rank[b], rank[a]
        new = check(adj, rank)
        if new >= cur:
            cur = new
        else:
            rank[a], rank[b] = rank[b], rank[a]
    worst = max(worst, cur)
print(f"max |D|/n = {worst:.4f} (bound 0.75), ratio vs n/4 = {4 * worst:.3f}")
