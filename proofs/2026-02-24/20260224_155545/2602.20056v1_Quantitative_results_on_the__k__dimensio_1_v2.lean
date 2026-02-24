import Mathlib
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

/-- For all \( k \geq 2 \), we provide almost-sharp quantitative results for the \( k \)-dimensional Duffin-Schaeffer conjecture. -/
theorem k_dimensional_duffin_schaeffer (k : ℕ) (ε : ℝ) (α : ℝ) (Q : ℕ)
    (ψ : ℕ → ℝ) (φ : ℕ → ℝ)
    (h_sum_diverges : ∑ q in finset.range Q, (ψ q * φ q / q) ^ k = ⊤)
    (h_k_ge_2 : k ≥ 2) :
    ∃ Ψ_k : ℕ → ℝ, (∀ q ≤ Q, (2 * ψ q * φ q / q) ^ k = Ψ_k q) ∧
    ∃ C : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ α, (∥qα - a∥∞ < ψ(q) for all i ∈ {1, ..., k}) →
    S_k(α, Q) = Ψ_k(Q) + O_ε,k(Ψ_k(Q)^(1/2 + ε)) := by
  sorry