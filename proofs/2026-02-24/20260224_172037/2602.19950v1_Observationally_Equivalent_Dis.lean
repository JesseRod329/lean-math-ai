import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Two distributions over choice rules are observationally equivalent if and only if they can be obtained from one another via a finite sequence of simple swapping transforms. -/
theorem observationally_equivalent_distributions :
    ∀ (D1 D2 : Type), ∃ (T : Type), ∀ (R1 : D1 → ChoiceRule), ∀ (R2 : D2 → ChoiceRule),
    (∃ (seq : List (D1 × D1)), (∀ (d1 d1' : D1), (d1, d1') ∈ seq → R1 d1 = R1 d1') ∧ (∀ (d2 d2' : D2), (d2, d2') ∈ seq → R2 d2 = R2 d2')) ↔
    (∃ (seq : List (D2 × D2)), (∀ (d2 d2' : D2), (d2, d2') ∈ seq → R2 d2 = R2 d2') ∧ (∀ (d1 d1' : D1), (d1, d1') ∈ seq → R1 d1 = R1 d1')) := by
  intros D1 D2
  use (D1 × D2)
  split
  . intro h
    obtain ⟨seq, hseq⟩ := h
    use [(d1, d2) | (d1, d2) ∈ seq, (d2, d1) | (d2, d1) ∈ seq]
    split
    . intros d1 d1' hseq'
      exact hseq.1 hseq'
    . intros d2 d2' hseq'
      exact hseq.2 hseq'
  . intro h
    obtain ⟨seq, hseq⟩ := h
    use [(d1, d2) | (d1, d2) ∈ seq, (d2, d1) | (d2, d1) ∈ seq]
    split
    . intros d1 d1' hseq'
      exact hseq.1 hseq'
    . intros d2 d2' hseq'
      exact hseq.2 hseq'