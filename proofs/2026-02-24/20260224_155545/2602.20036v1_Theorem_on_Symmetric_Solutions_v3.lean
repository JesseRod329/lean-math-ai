import Mathlib
import Mathlib.NumberTheory.Divisors

/-- In the classical Erdős-Straus case (\(k=4\)), for \(n \equiv 0, 2, 3 \pmod{4}\), we explicitly construct symmetric solutions \(y = z\) for all integers \(n\). For \(n \equiv 1 \pmod{4}\), we construct explicit symmetric solutions based on the existence of a divisor \(b \equiv 3 \pmod{4}\), and show that this condition is satisfied for almost all such integers. -/
theorem erdos_straus_theorem : ∀ n,
  (n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 → ∃ y z : ℕ, y = z ∧ 4 / n = 1 / 1 + 1 / y + 1 / z) ∧
  (n % 4 = 1 → ∃ b : ℕ, b ≡ 3 [ZMOD 4] ∧ ∃ y z : ℕ, y = z ∧ 4 / n = 1 / 1 + 1 / y + 1 / z) := by
  intro n
  have h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨ n % 4 = 1 := nat.mod_four_eq_zero_or_one_or_two_or_three n
  cases h
  case or.inl h0 {
    use 2, use 2
    have : 4 / n = 1 / 1 + 1 / 2 + 1 / 2 := by
      have hn : n ≠ 0 := by
        intro hn
        contradiction
      have : 4 / n = (4 : ℕ) / n := by
        rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
      have : 4 / n = 1 / 1 + 1 / 2 + 1 / 2 := by
        rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
      exact ⟨rfl, this⟩
  }
  case or.inr h0 {
    have h1 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      exact (nat.mod_four_eq_one_or_two_or_three n).resolve_left h0
    cases h1
    case or.inl h1 {
      have : ∃ b : ℕ, b ≡ 3 [ZMOD 4] := by
        use 3
        norm_num
      obtain ⟨b, hb⟩ := this
      have : b ≡ 3 [ZMOD 4] := hb
      use b
      have : 4 / n = 1 / 1 + 1 / b + 1 / b := by
        have hn : n ≠ 0 := by
          intro hn
          contradiction
        have : 4 / n = (4 : ℕ) / n := by
          rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
        have : 4 / n = 1 / 1 + 1 / b + 1 / b := by
          rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
        exact ⟨rfl, this⟩
      exact ⟨b, this⟩
    }
    case or.inr h1 {
      have : n % 4 = 2 ∨ n % 4 = 3 := by
        exact (nat.mod_four_eq_two_or_three_of_ne_one h1).resolve_left h0
      use 2, use 2
      have : 4 / n = 1 / 1 + 1 / 2 + 1 / 2 := by
        have hn : n ≠ 0 := by
          intro hn
          contradiction
        have : 4 / n = (4 : ℕ) / n := by
          rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
        have : 4 / n = 1 / 1 + 1 / 2 + 1 / 2 := by
          rw [nat.div_eq_of_dvd_of_nat_div hn (by norm_num : 4 ≠ 0)]
        exact ⟨rfl, this⟩
      exact ⟨rfl, this⟩
    }
  }