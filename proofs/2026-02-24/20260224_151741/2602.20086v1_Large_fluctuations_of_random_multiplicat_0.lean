-- STATUS: TEMPLATE_FALLBACK
import Mathlib
import Mathlib.NumberTheory.Divisors

/-- Let \( f \) be a Rademacher or Steinhaus random multiplicative function. For various arithmetically interesting subsets \( \mathcal{A} \subseteq [1, N] \cap \mathbb{N} \) such that the distribution of \( \sum_{n \in \mathcal{A}} f(n) \) is approximately Gaussian, we develop a general framework to understand the large fluctuations of the sum. This extends the general central limit theorem framework of Soundararajan and Xu.

In the case when \( \mathcal{A} = (N-H, N] \) is a short interval with admissible \( H = H(N) \), we show that almost surely
\[
\limsup_{N \to \infty} \frac{\big\lvert\sum_{N-H < n \leq N} f(n)\big\rvert}{\sqrt{H \log \frac{N}{H}}} > 0.
\]

When \( \mathcal{A} \) is the set of values of an admissible polynomial \( P \in \mathbb{Z}[x] \), we extend work of Klurman, Shkredov, and Xu, as well as Chinis and the author, showing that almost surely
\[
\limsup_{N \to \infty} \frac{\big\lvert\sum_{n \leq N} f(P(n))\big\rvert}{\sqrt{N \log \log N}} > 0,
\]
even when \( P \) is a product of linear factors over \( \mathbb{Q} \). In this case, we also establish the corresponding almost sure upper bound, matching the law of iterated logarithm.

An important ingredient in our work is bounding the Kantorovich-Wasserstein distance by means of a quantitative martingale central limit theorem.
-/
theorem large_fluctuations_of_random_multiplicative_functions : Prop := by
  sorry