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

/-- If $\ell$ is sufficiently large and $r/\gcd(r,\ell)$ is odd, then the codegree Turán density of $\mathcal{C}_\ell^r$ can be at most $1/3$. -/
theorem codegree_Turán_density_of_ℓ_sufficiently_large_and_r_odd_gcd :
  ∃ (ℓ : ℕ) (r : ℕ), 
  ℓ is sufficiently large ∧ 
  r / gcd(r, ℓ) is odd ∧ 
  the codegree Turán density of $\mathcal{C}_\ell^r$ can be at most 1/3 :=
begin
  sorry -- This is where the proof would go if fully completed