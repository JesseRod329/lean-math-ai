import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- The problem of enumerating minimal redundant sets in split and co-bipartite graphs is intractable. -/
theorem minimal_redundant_sets_intractable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Not (∃ (P : ℕ → Prop), (∀ n, P n → ∃ (alg : ℕ → ℕ) (P Juntament : ℕ → Prop),
    (∀ n, P n ↔ P n := by sorry