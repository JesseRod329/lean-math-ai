import Mathlib
import Mathlib.NumberTheory.Divisors

/-- For a Rademacher or Steinhaus random multiplicative function \( f \), if \( \mathcal{A} = (N-H, N] \) is a short interval with admissible \( H = H(N) \), then almost surely \( \limsup_{N \to \infty} \frac{\big\lvert\sum_{N-H<n\leq N} f(n)\big\rvert}{\sqrt{H\log \frac{N}{H}}} > 0 \). -/
theorem large_fluctuations_of_random_multiplicative_function (f : ℕ → ℕ) [RandomMultiplicativeFunction f] (N H : ℕ) (A : Finset ℕ) (hA : A = Finset.Ico (N - H) N) (hH : H = H(N)) :
  (∃ x, x > 0) := by
  sorry