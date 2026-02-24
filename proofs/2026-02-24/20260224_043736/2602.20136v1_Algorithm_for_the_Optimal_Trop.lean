import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- An explicit algorithm is provided to solve the idempotent analogue of the discrete Monge-Kantorovich optimal mass transportation problem with the tropical (max-plus) semiring. -/
theorem optimal_tropical_plan_algorithm:
  ∃ (T : Type) [LinearOrder T], (⊔ + ⊥ : T → T → T) = (λ x y, max x y) ∧ (λ x y, x + y) = (λ x y, x + y) :=
begin
  sorry -- Proof goes here
end