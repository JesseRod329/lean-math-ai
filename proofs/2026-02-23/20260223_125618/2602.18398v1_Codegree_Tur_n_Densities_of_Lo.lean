import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-- If $\ell$ is sufficiently large and $r/\gcd(r,\ell)$ is even, then the codegree Turán density of $\mathcal{C}_\ell^r$ is $1/2$. -/
theorem codegree_Turán_densities_of_long_tight_cycles (ℓ r : ℕ) :
    ∃ (H : ℓ sufficiently large), (r / Nat.gcd r ℓ) is even → (codegree Turán density of $\mathcal{C}_\ell^r$ is $1/2$) := by
  sorry -- Proof goes here