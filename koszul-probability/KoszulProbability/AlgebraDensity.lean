import KoszulProbability.SampleSpace
import KoszulProbability.Transport

open scoped BigOperators
open Finset Filter Topology
namespace KoszulProbability

noncomputable def coefficientMatrix (p : ℕ) [Fact p.Prime] (a : Stratum)
    (v : Coefficients p a) : Matrix (Fin a.2.2) (Fin (a.1*a.1)) (GaloisField p a.2.1) :=
  Matrix.of fun i j => v (finProdFinEquiv (i,j))

/-- A property of the actual algebra quotient, rather than a renamed determinant test. -/
def HasSquareZeroModel (p : ℕ) [Fact p.Prime] (a : Stratum) (v : Coefficients p a) : Prop :=
  ∃ e : Presentation.Quotient (coefficientMatrix p a v) ≃ₐ[GaloisField p a.2.1]
      SquareZero.Algebra (GaloisField p a.2.1) a.1,
    ∀ i : Fin a.1, e (Presentation.mk (coefficientMatrix p a v) (FreeAlgebra.ι _ i)) =
      TrivSqZeroExt.inr ((Pi.basisFun (GaloisField p a.2.1) (Fin a.1)) i)

noncomputable def modelCountInStratum (p : ℕ) [Fact p.Prime] (a : Stratum) : ℕ := by
  classical
  exact (Finset.univ.filter (HasSquareZeroModel p a)).card

noncomputable def modelCount (p B : ℕ) [Fact p.Prime] : ℕ :=
  ∑ a ∈ indices B, modelCountInStratum p a

lemma regular_le_model_top (p B : ℕ) [Fact p.Prime] :
    certifiedCount p B ≤ modelCountInStratum p (topIndex B) := by
  classical
  unfold certifiedCount regularCount modelCountInStratum
  simp only [topIndex]
  apply Finset.card_le_card
  intro v hv
  have hdet := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨Presentation.squareZeroEquiv (matrixOf (B*B) v) hdet, ?_⟩
  intro i
  exact Presentation.toSquare_generator (matrixOf (B*B) v) i

lemma certified_le_model (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    certifiedCount p B ≤ modelCount p B := by
  exact (regular_le_model_top p B).trans
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (top_mem hB))

lemma model_le_ball (p : ℕ) [Fact p.Prime] (B : ℕ) :
    (modelCount p B : ℝ) ≤ ballSize p B := by
  classical
  unfold modelCount ballSize
  push_cast
  apply Finset.sum_le_sum
  intro a ha
  have hc : modelCountInStratum p a ≤ Fintype.card (Coefficients p a) := Finset.card_filter_le _ _
  rw [coefficients_card p (mem_indices.mp ha).2.2.1] at hc
  unfold weight
  exact_mod_cast hc

/-- The actual presented algebras have square-zero models with probability tending to one. -/
theorem square_zero_algebra_density (p : ℕ) [Fact p.Prime] :
    Tendsto (fun B : ℕ => (modelCount p B : ℝ) / ballSize p B) atTop (𝓝 1) := by
  apply density_of_top_certificates (show 1 < (p : ℝ) by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · intro B hB
    exact (certified_lower p hB).trans (by exact_mod_cast certified_le_model p hB)
  · intro B _
    exact model_le_ball p B

/-- Explicit finite error bound for the same algebraic event. -/
theorem square_zero_algebra_error (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    1 - (modelCount p B : ℝ) / ballSize p B ≤
      (2*(B : ℝ)^4 + (B : ℝ)^2) / (p : ℝ)^B := by
  apply ball_failure_bound (show 1 < (p : ℝ) by exact_mod_cast (Fact.out : p.Prime).one_lt) hB
  exact (certified_lower p hB).trans (by exact_mod_cast certified_le_model p hB)

/-- An explicit free linear resolution certificate for the actual quadratic quotient.
The generator condition identifies the transported grading with the presentation grading. -/
def HasKoszulCertificate (p : ℕ) [Fact p.Prime] (a : Stratum) (v : Coefficients p a) : Prop :=
  ∃ e : Presentation.Quotient (coefficientMatrix p a v) ≃ₐ[GaloisField p a.2.1]
      SquareZero.Algebra (GaloisField p a.2.1) a.1,
    (∀ i : Fin a.1, e (Presentation.mk (coefficientMatrix p a v) (FreeAlgebra.ι _ i)) =
      TrivSqZeroExt.inr ((Pi.basisFun (GaloisField p a.2.1) (Fin a.1)) i)) ∧
    Transport.IsLinearResolution e

lemma certificate_iff_model (p : ℕ) [Fact p.Prime] (a : Stratum) (v : Coefficients p a) :
    HasKoszulCertificate p a v ↔ HasSquareZeroModel p a v := by
  constructor
  · rintro ⟨e,hgen,_⟩
    exact ⟨e,hgen⟩
  · rintro ⟨e,hgen⟩
    exact ⟨e,hgen,Transport.linear_resolution e⟩

noncomputable def koszulCertificateCount (p B : ℕ) [Fact p.Prime] : ℕ := by
  classical
  exact ∑ a ∈ indices B, (Finset.univ.filter (HasKoszulCertificate p a)).card

lemma certificateCount_eq (p B : ℕ) [Fact p.Prime] :
    koszulCertificateCount p B = modelCount p B := by
  classical
  simp only [koszulCertificateCount, modelCount, modelCountInStratum, certificate_iff_model]

/-- Main constructive theorem: explicit linear resolution certificates have density one. -/
theorem koszul_certificate_density (p : ℕ) [Fact p.Prime] :
    Tendsto (fun B : ℕ => (koszulCertificateCount p B : ℝ) / ballSize p B) atTop (𝓝 1) := by
  simpa only [certificateCount_eq] using square_zero_algebra_density p

end KoszulProbability
