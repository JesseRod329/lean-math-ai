import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- In the context of the tropical (max-plus) optimal transportation problem, we prove that the uniqueness of solutions is quite rare. -/
theorem unique_solutions_of_tropical_transportation_problem:
  ∀ {V : Type} [Fintype V] {W : Type} [Fintype W] (C : V → W → ℤ),
  (∃! p : V × W → ℤ, ∀ i j, p (i, j) ≤ C i j) →
  (∃! q : V → W → ℤ, ∀ i j, q i j ≤ C i j ∧ (∀ k l, q i j ≤ C k l → (i = k ∧ j = l))) :=
begin
  intros V FintypeV W FintypeW C,
  intro h,
  rcases h with ⟨p, hp, hu⟩,
  use p,
  split,
  { exact hp },
  { intros q hq,
    have h_unique : ∀ i j, q i j ≤ C i j ∧ (∀ k l, q i j ≤ C k l → (i = k ∧ j = l)),
    { intros i j,
      specialize hq i j,
      exact hq },
    have h_eq : q = p,
    { ext i j,
      apply le_antisymm,
      { apply h_unique i j },
      { apply hp i j } },
    exact h_eq },
end