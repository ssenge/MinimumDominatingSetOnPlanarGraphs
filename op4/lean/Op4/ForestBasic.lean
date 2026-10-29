import Mathlib

/-!
# Paths in forests

Basic facts about paths in a forest (`G.IsAcyclic`), used for Theorem `thm:forests`:
* `path_eq`: two paths with the same ends are equal;
* `append_isPath`: two paths that meet at a common end without turning back form a path;
* `dist_eq_length`: a path is a shortest walk;
* `dist_getVert`: the distance between two vertices of a path is the difference of their indices.
-/

namespace Op4

namespace Forest

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- In a forest, two paths with the same ends are equal. -/
lemma path_eq (hG : G.IsAcyclic) {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩)

/-- In a forest, two paths that meet at a common end without turning back form a path. -/
lemma append_isPath (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) (hj : p.Nil ∨ q.Nil ∨ p.penultimate ≠ q.snd) :
    (p.append q).IsPath := by
  rw [hG.isPath_iff_isChain] at hp hq ⊢
  rw [Walk.edges_append, List.isChain_append]
  refine ⟨hp, hq, fun a ha b hb hab => ?_⟩
  subst hab
  have hpn : ¬ p.Nil := fun h' => by rw [← Walk.edges_eq_nil] at h'; simp [h'] at ha
  have hqn : ¬ q.Nil := fun h' => by rw [← Walk.edges_eq_nil] at h'; simp [h'] at hb
  rw [List.getLast?_eq_some_getLast (Walk.edges_eq_nil.not.mpr hpn), Option.mem_def,
    Option.some.injEq, Walk.getLast_edges_eq_mk_penultimate_end] at ha
  rw [List.head?_eq_some_head (Walk.edges_eq_nil.not.mpr hqn), Option.mem_def,
    Option.some.injEq, Walk.head_edges_eq_mk_start_snd, ← ha] at hb
  rcases Sym2.eq_iff.1 hb with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact (Walk.adj_snd hqn).ne h2.symm
  · rcases hj with h | h | h
    · exact hpn h
    · exact hqn h
    · exact h h2.symm

/-- In a forest, a path is a shortest walk. -/
lemma dist_eq_length (hG : G.IsAcyclic) {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    G.dist u v = p.length := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  rw [← hlen, path_eq hG hq hp]

/-- In a forest, the distance between two vertices of a path is the difference of their indices. -/
lemma dist_getVert (hG : G.IsAcyclic) {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i k : ℕ}
    (hk : i + k ≤ p.length) : G.dist (p.getVert i) (p.getVert (i + k)) = k := by
  have h := dist_eq_length hG ((hp.drop i).take k)
  have hl : ((p.drop i).take k).length = k := by rw [Walk.take_length, Walk.drop_length]; omega
  rw [hl, Walk.drop_getVert] at h
  exact h

end Forest

end Op4
