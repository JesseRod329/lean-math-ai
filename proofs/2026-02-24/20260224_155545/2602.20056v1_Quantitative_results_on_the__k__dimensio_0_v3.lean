import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors

/-- For all \( k \geq 2 \), we provide almost-sharp quantitative results for the \( k \)-dimensional Duffin-Schaeffer conjecture. In particular, for \( \psi : \mathbb{N} \to [0, 1/2] \) such that \( \sum_{q \in \mathbb{N}} \left( \frac{\psi(q) \varphi(q)}{q} \right)^k \) diverges, \( Q \geq 1 \) and \( \alpha \in \mathbb{R} \), we denote by \( S_k(\alpha, Q) \) the number of pairs \( (a, q) \in \mathbb{Z}^k \times \mathbb{N} \) with \( q \leq Q \), \( \gcd(a_i, q) = 1 \) for each \( i \in \{1, \dots, k\} \), satisfying \( \| q \alpha - a \|_{\infty} < \psi(q) \). Defining \( \Psi_k(Q) = \sum_{q \leq Q} \left( \frac{2 \psi(q) \varphi(q)}{q} \right)^k \), we show that for all \( \varepsilon > 0 \) and almost all \( \alpha \) one has \( S_k(\alpha, Q) = \Psi_k(Q) + O_{\varepsilon, k}(\Psi(Q)^{1/2 + \varepsilon}) \). -/
theorem k_dimensional_duffin_schaeffer (k : ℕ) (ψ : ℕ → ℝ) (Q : ℕ) (α : ℝ) (h1 : k ≥ 2)
    (h2 : ∑ q in finset.range (Q + 1), (ψ (q * q) * φ (q * q) / (q * q)) ^ k = ∞)
    (h3 : ∀ ε > 0, ∃ δ > 0, ∀ f : ℕ → ℝ, (∑ q in finset.range (Q + 1), (ψ (q * q) * φ (q * q) / (q * q)) ^ k) ≥ δ →
        ∀ a : ℤ^k, ∑ q in finset.range (Q + 1), (2 * ψ (q * q) * φ (q * q) / (q * q)) ^ k ≥ δ →
        |q * α - a| ≤ ε) :
    S_k(α, Q) = Ψ_k(Q) + O(Ψ(Q)^{1/2 + ε}) := by
  sorry