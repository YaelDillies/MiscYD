import Mathlib.Combinatorics.SimpleGraph.Coloring

open scoped Finset

namespace SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {d : ℕ}

open scoped Classical in
/-- A bipartite simple graph whose induced subgraphs all have average degree at most `2 * d` can be
oriented in such a way that all edges have outdegree at most `d`. -/
lemma exists_orientation_of_average_degree_le (hGcolorable : G.Colorable 2)
    (hGdeg : ∀ s : Finset V, #(G.induce s).edgeFinset ≤ d * #s) :
    ∃ r : V → V → Prop, Irreflexive r ∧ IsAsymm _ r := sorry

end SimpleGraph
