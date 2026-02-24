import Mathlib
import Mathlib.NumberTheory.Divisors

/-- For every prime \( p \geq 5 \), we compute the \( p \)-th power of the Ramanujan vector field that arises from the differential relations discovered by Ramanujan for the Eisenstein series \( E_2, E_4 \) and \( E_6 \). Our method results in explicit equations for the \( p \)-th power and uses classical results of Serre and Swinnerton-Dyer about modular forms modulo \( p \). From this, we verify that a general conjecture by Sheperd-Barron and Ekedahl is valid for the Ramanujan vector field. Furthermore, we consider the affine realization of a certain moduli space of elliptic curves where the Ramanujan vector field is defined, and describe - in characteristic \( p \) - the locus given by supersingular elliptic curves in two ways: a classical one - using equations for the supersingular polynomial - and a new one as the singular set of some vector fields. Additionally, we prove that the Ramanujan vector field is transversal to this locus. -/
theorem ramanujan_vector_field_mod_p (p : ℕ) [hp : Fact (p ≥ 5)] : Prop :=
begin
  sorry
end