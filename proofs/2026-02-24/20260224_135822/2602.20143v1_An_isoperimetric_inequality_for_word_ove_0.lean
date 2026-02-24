import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Let \( A \) and \( B \) be sets of words of length \( n \) over some finite alphabet. Suppose that no suffix of a word in \( A \) coincides with a prefix of a word in \( B \). Then we show that the product of densities of \( A \) and \( B \) is upper bounded by \( 1/n \). -/
theorem an_isoperimetric_inequality_for_word_overlap (A B : Type) [Fintype A] [Fintype B] (n : ℕ) (h : ∀ a ∈ A, ∀ b ∈ B, ¬ a.reverse ++ b.reverse = b.reverse ++ a) :
    (Fintype.card A * Fintype.card B) / n ≤ 1 :=
begin
  sorry -- Proof goes here