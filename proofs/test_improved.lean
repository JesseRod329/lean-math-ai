import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-
Theorem: Every connected graph with n vertices has at least n-1 edges.
-/

example (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableEq V] [Fintype (G.edgeSet)] :
    G.edgeSet.ncard ≥ Fintype.card V - 1 := by
  sorry -- Proof goes here