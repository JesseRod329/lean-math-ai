import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-- A famous conjecture of Graham asserts that every set \( A \subseteq \mathbb{Z}_p \setminus \{0\} \) can be ordered so that all partial sums are distinct. Although this conjecture was recently proved for sufficiently large primes by Pham and Sauermann in [16], it remains open for general abelian groups, even in the cyclic case \(\mathbb{Z}_k\).

For cyclic groups, the best known result is due to Bedert and Kravitz in [4], who proved - using a rectification and a two-step probabilistic approach - that the conjecture holds for any subset \( A \subseteq \mathbb{Z}_k \setminus \{0\} \) such that 
\[ |A| \le \exp\!\big(c(\log p)^{1/4}\big), \]
for some constant \( c>0 \), where \( p \) denotes the least prime divisor of \( k \).

In this paper, we improve their bound using a rectification argument again, followed by a one-shot probabilistic approach, showing that the conjecture holds whenever 
\[ |A| \le \exp\!\big(c(\log p)^{1/3}\big), \]
thus improving the exponent \( 1/4 \) from [4].

Moreover, the same one-shot approach adapts to the \( t \)-weak setting: by imposing all local constraints at once and applying the Lovász Local Lemma, we obtain the existence of a \( t \)-weak sequencing whenever 
\[ t \le \exp\!\big(c(\log p)^{1/4}\big). \]
-/

theorem new_bounds_for_weak_sequenceability_in_Z_k {k p : ℕ} (h : p = minFac k) :
  (∃ (A : finset ℤ), A.card ≤ exp (c * (log (real.of_nat p)) ^ (1/3))) →
  (∃ (s : finset ℤ), (∀ a b : ℤ, a ∈ A → b ∈ A → a * b ∈ s → a + b ∈ s)) :=
by sorry