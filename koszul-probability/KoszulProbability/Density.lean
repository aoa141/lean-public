import KoszulProbability.MatrixCounting
import KoszulProbability.Ball
import Mathlib.FieldTheory.Finite.GaloisField

open scoped BigOperators
open Finset Filter Topology
namespace KoszulProbability

noncomputable def regularCount (K : Type*) [Field K] [Fintype K] (d : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin (d*d) → K => (matrixOf d x).det ≠ 0).card

lemma regular_add_singular (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    regularCount K d + singularCount K d = (Fintype.card K)^(d*d) := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (d*d) → K)))
    (p := fun x => (matrixOf d x).det = 0)
  simpa [regularCount, singularCount, add_comm] using h

noncomputable instance finiteFieldFintype (p e : ℕ) [Fact p.Prime] : Fintype (GaloisField p e) :=
  Fintype.ofFinite _

/-- Actual count of invertible coefficient matrices in the largest stratum of the ball. -/
noncomputable def certifiedCount (p B : ℕ) [Fact p.Prime] : ℕ :=
  regularCount (GaloisField p B) (B*B)

lemma field_card (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    Fintype.card (GaloisField p B) = p^B := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p B (by omega)]

lemma top_card (p B : ℕ) : (p^B)^((B*B)*(B*B)) = p^(B^5) := by
  rw [← pow_mul]
  congr 1
  ring

lemma certified_lower (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (p : ℝ)^(B^5) * (1 - (B : ℝ)^2 / (p : ℝ)^B) ≤ certifiedCount p B := by
  have hc := regular_add_singular (GaloisField p B) (B*B)
  rw [field_card p hB, top_card] at hc
  have hcR : (certifiedCount p B : ℝ) + singularCount (GaloisField p B) (B*B) =
      (p : ℝ)^(B^5) := by exact_mod_cast hc
  have hs := singular_fraction_le (GaloisField p B) (B*B)
  rw [field_card p hB] at hs
  norm_cast at hs
  rw [top_card] at hs
  push_cast at hs
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmul := (div_le_iff₀ (pow_pos hp (B^5))).mp hs
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

lemma certified_upper (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (certifiedCount p B : ℝ) ≤ ballSize p B := by
  have hc := regular_add_singular (GaloisField p B) (B*B)
  rw [field_card p hB, top_card] at hc
  have hle : certifiedCount p B ≤ p^(B^5) := by unfold certifiedCount; omega
  have hleR : (certifiedCount p B : ℝ) ≤ (p : ℝ)^(B^5) := by exact_mod_cast hle
  exact hleR.trans (top_weight_le_ball (Nat.cast_nonneg p) hB)

/-- Density of explicit, invertible-matrix Koszul certificates in the presentation balls. -/
theorem certified_density (p : ℕ) [Fact p.Prime] :
    Tendsto (fun B : ℕ => (certifiedCount p B : ℝ) / ballSize p B) atTop (𝓝 1) := by
  apply density_of_top_certificates (show 1 < (p : ℝ) by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · intro B hB
    exact certified_lower p hB
  · intro B hB
    exact certified_upper p hB

end KoszulProbability
