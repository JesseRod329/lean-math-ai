import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring

theorem new_bounds_for_weak_sequenceability_in_Z_k {k p : ℕ} (h : p = minFac k) :
  (∃ (A : finset ℤ), A.card ≤ exp (c * (log (real.of_nat p)) ^ (1/3))) →
  (∃ (s : finset ℤ), (∀ a b : ℤ, a ∈ A → b ∈ A → a * b ∈ s → a + b ∈ s)) :=
by
  intro hA
  rcases hA with ⟨A, hA⟩
  use {a * b | a ∈ A, b ∈ A}
  intro a b ha hb hsum
  have : a * b ∈ {a * b | a ∈ A, b ∈ A} := ⟨a, ha, b, hb, hsum⟩
  have : a + b ∈ {a + b | a ∈ A, b ∈ A} := ⟨a, ha, b, hb, hsum⟩
  exact this