import Mathlib
import Mathlib.NumberTheory.Divisors

/-- In the case when \(\mathcal A = (N-H, N]\) is a short interval with admissible \(H=H(N)\), we show that almost surely
\[
\limsup_{N\to\infty} \frac{\big\lvert\sum_{N-H<n\leq N} f(n)\big\rvert}{\sqrt{H\log \frac{N}H{}}}>0.
\]
-/
theorem large_fluctuations_of_random_multiplicative_functions (N H : ℕ) (f : ℕ → ℝ) (A : (r : ℕ+) → Multiset ℕ+) :
  ∃ (C : ℝ), 0 < C ∧ ∀ (N : ℕ), ∀ (H : ℕ+) (A : Multiset ℕ+),
    (∑ n in (finset.Ico (N - H) N), f n) / (sqrt (H * log (N / H))) < C :=
by
  sorry