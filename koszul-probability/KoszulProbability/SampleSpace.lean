import KoszulProbability.Density

open scoped BigOperators
open Finset
namespace KoszulProbability

/-- All row-major coefficient lists in a labeled stratum. -/
abbrev Coefficients (p : ℕ) [Fact p.Prime] (a : Stratum) :=
  Fin (a.2.2 * (a.1*a.1)) → GaloisField p a.2.1

/-- The actual finite disjoint union of all presentations in the ball. -/
abbrev BallPoint (p : ℕ) [Fact p.Prime] (B : ℕ) :=
  (a : {a : Stratum // a ∈ indices B}) × Coefficients p a.val

lemma coefficients_card (p : ℕ) [Fact p.Prime] {a : Stratum} (he : 1 ≤ a.2.1) :
    Fintype.card (Coefficients p a) = p ^ exponent a := by
  simp only [Coefficients, Fintype.card_fun, Fintype.card_fin, field_card p he]
  rw [← pow_mul]
  congr 1
  simp [exponent, mul_assoc, pow_two]

/-- The denominator in the analytic proof is exactly the cardinality of the sample space. -/
theorem ballSize_eq_card (p : ℕ) [Fact p.Prime] (B : ℕ) :
    ballSize (p : ℝ) B = Fintype.card (BallPoint p B) := by
  classical
  rw [Fintype.card_sigma]
  push_cast
  unfold ballSize
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro a ha
  have he := (mem_indices.mp a.property).2.2.1
  rw [coefficients_card p he]
  simp [weight]

end KoszulProbability
