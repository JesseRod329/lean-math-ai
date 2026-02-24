import Mathlib
import Mathlib.NumberTheory.Divisors

/-- For a fixed unitary cuspidal automorphic representation \( \pi \) of \( \operatorname{GL}_3/F \), we show that \( L(\pi \otimes \chi, \frac{1}{2}) \ll N(\mathfrak{q})^{3/4 - \kappa} \) holds for all \( \kappa < \frac{1}{36} \). -/
theorem subconvexity_problem_gl3_over_number_fields (F : Type) [NumberField F]
    (π : AutomorphicRepresentation F) (χ : FiniteOrderCharacter F) (κ : ℝ)
    (hκ : κ < 1/36) :
    L(π ⊗ χ, 1/2) < N(q)^{3/4 - κ} := by
  sorry