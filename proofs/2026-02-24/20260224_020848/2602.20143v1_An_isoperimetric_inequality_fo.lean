import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Let \( A \) and \( B \) be sets of words of length \( n \) over some finite alphabet. Suppose that no suffix of a word in \( A \) coincides with a prefix of a word in \( B \). Then we show that the product of densities of \( A \) and \( B \) is upper bounded by \( \frac{1}{n} \). This bound is sharp up to a factor of \( e \). -/
theorem an_isoperimetric_inequality_for_word_overlap {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (A B : Finset (Fin n → 𝕜)) (h : ∀ a ∈ A, ∀ b ∈ B, ∀ i j, a i ≠ b j) :
  (A.card / (n : ℝ)) * (B.card / (n : ℝ)) ≤ 1 / n := by
  sorry -- Proof goes here