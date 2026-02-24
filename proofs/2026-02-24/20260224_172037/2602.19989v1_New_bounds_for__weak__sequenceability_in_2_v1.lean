import Mathlib
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.Divisors

/-- For cyclic groups, the best known result is due to Bedert and Kravitz in [4], who proved - using a rectification and a two-step probabilistic approach - that the conjecture holds for any subset $A \subseteq \mathbb{Z}_k \setminus \{0\}$ such that $$ |A| \le \exp\!\big(c(\log p)^{1/4}\big), $$ for some constant $c>0$, where $p$ denotes the least prime divisor of $k$.

In this paper, we improve their bound using a rectification argument again, followed by a one-shot probabilistic approach, showing that the conjecture holds whenever $$|A| \le \exp\!\big(c(\log p)^{1/3}\big), $$ thus improving the exponent $1/4$ from [4]. -/
theorem new_bounds_for_weak_sequenceability_in_Zk (k : ℕ) (A : Finset ℤ) (hA : A ⊆ ℤ) (hA0 : 0 ∉ A) (hA1 : A ≠ ∅) :
    |A| ≤ exp (c * (log (least_prime_divisor k))^(1/3)) := by
  sorry