import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.NumberTheory.Divisors

theorem large_fluctuations_of_random_multiplicative_function:
  ∃ (N : ℕ) (H : ℕ+) (f : ℕ → ℝ),
    (∑ n in {N-H + 1..N}, f n) / sqrt (H * log (N / H)) > 0 := by
  sorry