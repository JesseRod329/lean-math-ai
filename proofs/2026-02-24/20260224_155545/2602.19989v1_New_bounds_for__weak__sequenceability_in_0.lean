import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- A famous conjecture of Graham asserts that every set \( A \subseteq \mathbb{Z}_p \setminus \{0\} \) can be ordered so that all partial sums are distinct. -/
theorem graham_conjecture (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ℤ_p p)) : 
    ∃ σ : Perm (Finset (ℤ_p p)), (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (∑ x in σ.to_embedding a, x) ≠ (∑ x in σ.to_embedding b, x)) := by
  sorry