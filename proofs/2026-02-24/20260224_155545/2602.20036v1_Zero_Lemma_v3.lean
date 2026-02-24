import Mathlib
import Mathlib.NumberTheory.Divisors

/-- For any fixed pair (x,t), if \(F(n_0)=0\) for some \(n_0\) in the domain of \(F\), then \(n_0\) is necessarily the upper bound of \(D_{x,t}^{(k)}\), and such zeros of \(F\) yield explicit symmetric solutions with \(y=z\). -/
theorem Zero_Lemma (x t : ℕ) (F : ℕ → ℤ) (n_0 : ℕ) (hF : F n_0 = 0) :
    (∃ D : Multiset ℕ, (∀ n ∈ D, F n = 0) ∧ D.card = n_0 ∧ (∀ n, F n = 0 → n ≤ n_0)) ∧
    (∀ n, F n = 0 → ∃ y z, y = z ∧ n = (x : ℕ) * y) :=
begin
  have h1 : ∃ D : Multiset ℕ, (∀ n ∈ D, F n = 0) ∧ D.card = n_0 ∧ (∀ n, F n = 0 → n ≤ n_0),
  { use {n_0},
    split,
    { intros n hn,
      rw hn,
      exact hF },
    split,
    { refl },
    { intros n hn,
      exact le_of_eq (by rw hF) } },
  have h2 : ∀ n, F n = 0 → ∃ y z, y = z ∧ n = (x : ℕ) * y,
  { intros n hn,
    use n,
    use n,
    split,
    { refl },
    { rw hF at hn,
      exact hn } },
  exact ⟨h1, h2⟩
end