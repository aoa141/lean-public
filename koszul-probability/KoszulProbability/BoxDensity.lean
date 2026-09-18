import KoszulProbability.BoxBall
import KoszulProbability.Transport
import KoszulProbability.Density

/-!
# Koszul density for presentations with coefficients in boxes of arbitrary fields

Over an infinite field there is no uniform measure on coefficient matrices. The honest
replacement is to count matrices whose entries lie in a finite box `S ⊆ K`, and to let the
box grow. Schwartz--Zippel holds on any box in any field, and the square-zero isomorphism
holds over any field, so the whole argument of the paper goes through.

We allow a family of fields `K e` with a box `S e ⊆ K e` at each level, so that the
finite-field theorem (`K e = GF(p^e)`, `S e = GF(p^e)`) and the fixed-infinite-field
theorem (`K e = K`, `S e` a growing box) are both instances of the same formal statement.
-/

open scoped BigOperators
open Finset Filter Topology

namespace KoszulProbability

section SingleBox
variable {F : Type*} [Field F]

/-- Number of singular `d × d` matrices with entries in the box `S`. -/
noncomputable def boxSingularCount (S : Finset F) (d : ℕ) : ℕ := by
  classical
  exact ((Fintype.piFinset fun _ : Fin (d * d) => S).filter
    fun f => (matrixOf d f).det = 0).card

/-- Number of nonsingular `d × d` matrices with entries in the box `S`. -/
noncomputable def boxRegularCount (S : Finset F) (d : ℕ) : ℕ := by
  classical
  exact ((Fintype.piFinset fun _ : Fin (d * d) => S).filter
    fun f => (matrixOf d f).det ≠ 0).card

/-- Schwartz--Zippel for square matrices with entries in a finite box `S` of any field. -/
theorem box_singular_fraction_le (S : Finset F) (d : ℕ) :
    (boxSingularCount S d : ℝ) / (S.card : ℝ) ^ (d * d) ≤ (d : ℝ) / S.card := by
  classical
  have h := MvPolynomial.schwartz_zippel_totalDegree (detPolynomial_ne_zero F d) S
  have hd := totalDegree_detPolynomial_le F d
  have h' : (boxSingularCount S d : ℚ≥0) / (S.card : ℚ≥0) ^ (d * d) ≤ (d : ℚ≥0) / S.card := by
    calc
      _ ≤ ((detPolynomial F d).totalDegree : ℚ≥0) / S.card := by
        simpa [boxSingularCount, eval_detPolynomial] using h
      _ ≤ _ := by gcongr
  have hh := (NNRat.cast_le (K := ℝ)).mpr h'
  simpa using hh

lemma boxSingular_add_regular (S : Finset F) (d : ℕ) :
    boxSingularCount S d + boxRegularCount S d = S.card ^ (d * d) := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Fintype.piFinset fun _ : Fin (d * d) => S) (p := fun f => (matrixOf d f).det = 0)
  simpa [boxSingularCount, boxRegularCount, Fintype.card_piFinset_const] using h

/-- Lower bound for nonsingular matrices in a nonempty box. -/
theorem boxRegularCount_lower (S : Finset F) (hS : 1 ≤ S.card) (d : ℕ) :
    (S.card : ℝ) ^ (d * d) * (1 - (d : ℝ) / S.card) ≤ boxRegularCount S d := by
  have hsumR : (boxSingularCount S d : ℝ) + boxRegularCount S d = (S.card : ℝ) ^ (d * d) := by
    exact_mod_cast boxSingular_add_regular S d
  have hs := box_singular_fraction_le S d
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hpow : (0 : ℝ) < (S.card : ℝ) ^ (d * d) := pow_pos hS0 _
  have hmul := (div_le_iff₀ hpow).mp hs
  have : (S.card : ℝ) ^ (d * d) * (1 - d / S.card)
      = (S.card : ℝ) ^ (d * d) - d / S.card * (S.card : ℝ) ^ (d * d) := by ring
  rw [this]
  linarith

/-- Over any field, singular matrices are negligible along any sequence of boxes whose size
tends to infinity. This is the measure-free content of "generic invertibility" that survives
over infinite fields. -/
theorem box_singular_fraction_tendsto_zero (S : ℕ → Finset F)
    (hS : Tendsto (fun j => (S j).card) atTop atTop) (d : ℕ) :
    Tendsto (fun j => (boxSingularCount (S j) d : ℝ) / ((S j).card : ℝ) ^ (d * d))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => (d : ℝ) / (S j).card) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hS)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun j => by positivity) (fun j => box_singular_fraction_le (S j) d)

end SingleBox

section Family
variable (K : ℕ → Type*) [∀ e, Field (K e)] (S : ∀ e, Finset (K e))

/-- Row-major coefficient lists of the stratum `a` with all entries in the level-`e` box. -/
def boxCoefficients (a : Stratum) : Finset (Fin (a.2.2 * (a.1 * a.1)) → K a.2.1) :=
  Fintype.piFinset fun _ => S a.2.1

/-- A point of the ball: a stratum together with a coefficient list. -/
abbrev BoxPoint := Σ a : Stratum, Fin (a.2.2 * (a.1 * a.1)) → K a.2.1

/-- The actual finite sample space: every stratum of radius `B`, every matrix with entries
in the box of its level. -/
def boxBall (B : ℕ) : Finset (BoxPoint K) :=
  (indices B).sigma fun a => boxCoefficients K S a

omit [∀ e, Field (K e)] in
lemma boxBall_card (B : ℕ) :
    ((boxBall K S B).card : ℝ) = boxBallSize (fun e => (S e).card) B := by
  simp only [boxBall, boxCoefficients, card_sigma, Fintype.card_piFinset_const, boxBallSize,
    boxWeight]
  push_cast
  rfl

/-- The coefficient matrix of a point. -/
noncomputable def boxMatrix (a : Stratum) (v : Fin (a.2.2 * (a.1 * a.1)) → K a.2.1) :
    Matrix (Fin a.2.2) (Fin (a.1 * a.1)) (K a.2.1) :=
  Matrix.of fun i j => v (finProdFinEquiv (i, j))

/-- The presented algebra of the point is isomorphic to the square-zero extension, with each
generator sent to its degree-one basis vector. -/
def BoxSquareZeroModel (x : BoxPoint K) : Prop :=
  ∃ e : Presentation.Quotient (boxMatrix K x.1 x.2) ≃ₐ[K x.1.2.1]
      SquareZero.Algebra (K x.1.2.1) x.1.1,
    ∀ i : Fin x.1.1, e (Presentation.mk (boxMatrix K x.1 x.2) (FreeAlgebra.ι _ i)) =
      TrivSqZeroExt.inr ((Pi.basisFun (K x.1.2.1) (Fin x.1.1)) i)

/-- Square-zero model together with the explicit free linear resolution over the presented
quotient. -/
def BoxKoszulCertificate (x : BoxPoint K) : Prop :=
  ∃ e : Presentation.Quotient (boxMatrix K x.1 x.2) ≃ₐ[K x.1.2.1]
      SquareZero.Algebra (K x.1.2.1) x.1.1,
    (∀ i : Fin x.1.1, e (Presentation.mk (boxMatrix K x.1 x.2) (FreeAlgebra.ι _ i)) =
      TrivSqZeroExt.inr ((Pi.basisFun (K x.1.2.1) (Fin x.1.1)) i)) ∧
    Transport.IsLinearResolution e

lemma boxCertificate_iff_model (x : BoxPoint K) :
    BoxKoszulCertificate K x ↔ BoxSquareZeroModel K x := by
  constructor
  · rintro ⟨e, hgen, _⟩
    exact ⟨e, hgen⟩
  · rintro ⟨e, hgen⟩
    exact ⟨e, hgen, Transport.linear_resolution e⟩

noncomputable def boxModelCount (B : ℕ) : ℕ := by
  classical
  exact ((boxBall K S B).filter (BoxSquareZeroModel K)).card

noncomputable def boxCertificateCount (B : ℕ) : ℕ := by
  classical
  exact ((boxBall K S B).filter (BoxKoszulCertificate K)).card

lemma boxCertificateCount_eq (B : ℕ) : boxCertificateCount K S B = boxModelCount K S B := by
  classical
  simp only [boxCertificateCount, boxModelCount, boxCertificate_iff_model]

/-- Every nonsingular top-stratum matrix gives a point with a square-zero model. -/
lemma boxRegular_le_model {B : ℕ} (hB : 1 ≤ B) :
    boxRegularCount (S B) (B * B) ≤ boxModelCount K S B := by
  classical
  unfold boxRegularCount boxModelCount
  apply Finset.card_le_card_of_injOn (fun v => (⟨(B, B, B * B), v⟩ : BoxPoint K))
  · intro v hv
    obtain ⟨hv, hdet⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sigma.mpr ⟨top_mem hB, hv⟩, ?_⟩
    exact ⟨Presentation.squareZeroEquiv (matrixOf (B * B) v) hdet,
      fun i => Presentation.toSquare_generator (matrixOf (B * B) v) i⟩
  · intro v _ w _ h
    simpa using h

lemma boxModel_le_ball (B : ℕ) : (boxModelCount K S B : ℝ) ≤ (boxBall K S B).card := by
  classical
  unfold boxModelCount
  exact_mod_cast Finset.card_filter_le _ _

lemma boxModel_lower {B : ℕ} (hB : 1 ≤ B) (hg : BoxGrowth (fun e => (S e).card) B) :
    ((S B).card : ℝ) ^ (B ^ 4) * (1 - (B : ℝ) ^ 2 / (S B).card) ≤ boxModelCount K S B := by
  have hS : 1 ≤ (S B).card := hg.1 B hB le_rfl
  have h1 := boxRegularCount_lower (S B) hS (B * B)
  have h2 : (boxRegularCount (S B) (B * B) : ℝ) ≤ boxModelCount K S B := by
    exact_mod_cast boxRegular_le_model K S hB
  have e1 : B * B * (B * B) = B ^ 4 := by ring
  have e2 : ((B * B : ℕ) : ℝ) = (B : ℝ) ^ 2 := by push_cast; ring
  rw [e1, e2] at h1
  exact h1.trans h2

/-- Explicit finite error bound for actual presented algebras with coefficients in boxes. -/
theorem box_square_zero_error {B : ℕ} (hB : 1 ≤ B) (hg : BoxGrowth (fun e => (S e).card) B) :
    1 - (boxModelCount K S B : ℝ) / (boxBall K S B).card ≤
      (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / (S B).card := by
  rw [boxBall_card]
  exact box_failure_bound _ hB hg (boxModel_lower K S hB hg)

/-- Density one of square-zero models, for any family of fields and boxes with the growth
condition and vanishing error term. -/
theorem box_square_zero_density
    (hg : ∀ᶠ B in atTop, BoxGrowth (fun e => (S e).card) B)
    (herr : Tendsto (fun B : ℕ => (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / ((S B).card : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun B => (boxModelCount K S B : ℝ) / (boxBall K S B).card) atTop (𝓝 1) := by
  have hfun : (fun B => (boxModelCount K S B : ℝ) / (boxBall K S B).card) =
      fun B => (boxModelCount K S B : ℝ) / boxBallSize (fun e => (S e).card) B := by
    funext B
    rw [boxBall_card]
  rw [hfun]
  apply box_density_of_top_certificates _ _ hg
  · intro B hB hgB
    exact boxModel_lower K S hB hgB
  · intro B _
    rw [← boxBall_card]
    exact boxModel_le_ball K S B
  · exact herr

/-- Main constructive theorem for boxes: explicit linear resolution certificates over the
presented quotients have density one. -/
theorem box_koszul_certificate_density
    (hg : ∀ᶠ B in atTop, BoxGrowth (fun e => (S e).card) B)
    (herr : Tendsto (fun B : ℕ => (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / ((S B).card : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun B => (boxCertificateCount K S B : ℝ) / (boxBall K S B).card) atTop (𝓝 1) := by
  simpa only [boxCertificateCount_eq] using box_square_zero_density K S hg herr

/-- Geometric boxes `|S e| = c^e`, `c ≥ 2`, in any family of fields: the paper's bound. -/
theorem geometric_box_error {c : ℕ} (hc : 2 ≤ c) (hS : ∀ e, 1 ≤ e → (S e).card = c ^ e)
    {B : ℕ} (hB : 1 ≤ B) :
    1 - (boxCertificateCount K S B : ℝ) / (boxBall K S B).card ≤
      (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / (c : ℝ) ^ B := by
  have h := box_square_zero_error K S hB (boxGrowth_geometric hc _ hS hB)
  rw [hS B hB] at h
  push_cast at h
  rwa [boxCertificateCount_eq]

/-- Geometric boxes in any family of fields: Koszul certificates have density one. -/
theorem geometric_box_density {c : ℕ} (hc : 2 ≤ c) (hS : ∀ e, 1 ≤ e → (S e).card = c ^ e) :
    Tendsto (fun B => (boxCertificateCount K S B : ℝ) / (boxBall K S B).card) atTop (𝓝 1) := by
  apply box_koszul_certificate_density
  · filter_upwards [eventually_ge_atTop 1] with B hB
    exact boxGrowth_geometric hc _ hS hB
  · have hc' : (1 : ℝ) < c := by exact_mod_cast (by omega : 1 < c)
    refine Tendsto.congr' ?_ (error_tends_to_zero hc')
    filter_upwards [eventually_ge_atTop 1] with B hB
    simp [hS B hB]

end Family

/-- A fixed field `K` with a growing box: the infinite-field version of the theorem. -/
theorem fixed_field_box_density (K : Type*) [Field K] (S : ℕ → Finset K)
    {c : ℕ} (hc : 2 ≤ c) (hS : ∀ e, 1 ≤ e → (S e).card = c ^ e) :
    Tendsto (fun B => (boxCertificateCount (fun _ => K) S B : ℝ) /
      (boxBall (fun _ => K) S B).card) atTop (𝓝 1) :=
  geometric_box_density (fun _ => K) S hc hS

/-- Sanity check: the finite-field theorem of the paper is the instance `S e = GF(p^e)`. -/
theorem galois_box_density (p : ℕ) [Fact p.Prime] :
    Tendsto (fun B => (boxCertificateCount (fun e => GaloisField p e) (fun _ => univ) B : ℝ) /
      (boxBall (fun e => GaloisField p e) (fun _ => univ) B).card) atTop (𝓝 1) :=
  geometric_box_density _ _ (Fact.out : p.Prime).two_le fun e he => by
    rw [card_univ, field_card p he]

/-- In that instance the sample space has exactly the cardinality used in `Ball.lean`. -/
theorem galois_boxBall_card (p : ℕ) [Fact p.Prime] (B : ℕ) :
    ((boxBall (fun e => GaloisField p e) (fun _ => univ) B).card : ℝ) = ballSize (p : ℝ) B := by
  rw [boxBall_card, ← boxBallSize_geometric]
  unfold boxBallSize
  apply Finset.sum_congr rfl
  intro a ha
  unfold boxWeight
  dsimp only
  rw [card_univ, field_card p (mem_indices.mp ha).2.2.1]

end KoszulProbability
