import KoszulProbability.Obstruction
import KoszulProbability.Presentation
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# The fixed-stratum obstruction: counting and the actual quotient

For two generators `x, y` and two quadratic relations `r, s` with coefficient vector
`c : Fin 8 → K` (`c 0..3` are the coefficients of `r` on `xx, xy, yx, yy`; `c 4..7` those of
`s`), the paper's `8 × 8` matrix `M(r,s)` has columns `xr, yr, xs, ys, rx, ry, sx, sy` in the
cubic-word basis `xxx, xxy, xyx, xyy, yxx, yxy, yyx, yyy`. This file proves:

* `cubicDet K` is a polynomial of total degree `≤ 8`, nonzero over every field, whose value at
  `c` is `det (cubicMatrix c)`;
* Schwartz--Zippel: at most an `8/|S|` fraction of `S^8` lies on `{Δ = 0}`, for any finite box
  `S` in any field (`obstruction_fraction_le`), in particular `8/q` over `GF(q)`;
* if `det (cubicMatrix c) ≠ 0` then every cubic product of generators vanishes in the actual
  presented quotient `Presentation.Quotient (relMatrix c)` (`cubic_products_vanish`), and the
  two relations are linearly independent (`rows_linearIndependent`).

Together with `no_nonnegative_inverse`, this leaves only the Hilbert-series step
`h_A(t) = 1 + 2t + 2t²` and its Euler-characteristic consequence as written mathematics.
-/

open scoped BigOperators Matrix
open Finset MvPolynomial

namespace KoszulProbability.Obstruction

section CubicMatrix
variable {R : Type*} [CommRing R]

/-- Columns `xr, yr, xs, ys, rx, ry, sx, sy`; rows `xxx, xxy, xyx, xyy, yxx, yxy, yyx, yyy`. -/
def cubicMatrix (c : Fin 8 → R) : Matrix (Fin 8) (Fin 8) R := !![
  c 0, 0, c 4, 0, c 0, 0, c 4, 0;
  c 1, 0, c 5, 0, 0, c 0, 0, c 4;
  c 2, 0, c 6, 0, c 1, 0, c 5, 0;
  c 3, 0, c 7, 0, 0, c 1, 0, c 5;
  0, c 0, 0, c 4, c 2, 0, c 6, 0;
  0, c 1, 0, c 5, 0, c 2, 0, c 6;
  0, c 2, 0, c 6, c 3, 0, c 7, 0;
  0, c 3, 0, c 7, 0, c 3, 0, c 7]

lemma cubicMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (c : Fin 8 → R) :
    (cubicMatrix c).map f = cubicMatrix (fun t => f (c t)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicMatrix]

/-- The witness `r = xx + yy`, `s = xy`. -/
def witnessCoeffs : Fin 8 → ℤ := ![1, 0, 0, 1, 0, 1, 0, 0]

lemma cubicMatrix_witness : cubicMatrix witnessCoeffs = cubicWitness := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CubicMatrix

section Polynomial
variable (K : Type*) [CommRing K]

/-- The determinant of `M(r,s)` as a polynomial in the eight coefficients. -/
noncomputable def cubicDet : MvPolynomial (Fin 8) K := (cubicMatrix fun t => X t).det

lemma eval_cubicDet (c : Fin 8 → K) : eval c (cubicDet K) = (cubicMatrix c).det := by
  unfold cubicDet
  rw [RingHom.map_det, RingHom.mapMatrix_apply, cubicMatrix_map]
  simp

/-- The determinant of the witness matrix is a unit in every commutative ring. -/
lemma det_witness_mul (K : Type*) [CommRing K] :
    (cubicWitness.map (Int.castRingHom K)).det * (cubicInverse.map (Int.castRingHom K)).det = 1 := by
  rw [← Matrix.det_mul, ← Matrix.map_mul, witness_inverse, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_one]

lemma cubicDet_ne_zero [Nontrivial K] : cubicDet K ≠ 0 := by
  intro h
  have he := eval_cubicDet K (fun t => (witnessCoeffs t : K))
  rw [h, map_zero] at he
  have hmap : cubicMatrix (fun t => (witnessCoeffs t : K)) =
      cubicWitness.map (Int.castRingHom K) := by
    rw [← cubicMatrix_witness, cubicMatrix_map]
    rfl
  have hunit := det_witness_mul K
  rw [← hmap, ← he, zero_mul] at hunit
  exact zero_ne_one hunit

lemma cubicMatrix_X_totalDegree_le [Nontrivial K] (i j : Fin 8) :
    (cubicMatrix (fun t => (X t : MvPolynomial (Fin 8) K)) i j).totalDegree ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [cubicMatrix]

lemma totalDegree_cubicDet_le [Nontrivial K] : (cubicDet K).totalDegree ≤ 8 := by
  classical
  unfold cubicDet
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  calc
    _ ≤ (∏ i : Fin 8, cubicMatrix (fun t => (X t : MvPolynomial (Fin 8) K)) (σ i) i).totalDegree := by
      simpa only [Units.smul_def] using totalDegree_smul_le (↑(Equiv.Perm.sign σ) : ℤ)
        (∏ i : Fin 8, cubicMatrix (fun t => (X t : MvPolynomial (Fin 8) K)) (σ i) i)
    _ ≤ ∑ i : Fin 8, (cubicMatrix (fun t => (X t : MvPolynomial (Fin 8) K)) (σ i) i).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _i : Fin 8, 1 := sum_le_sum fun i _ => cubicMatrix_X_totalDegree_le K _ _
    _ = 8 := by simp

end Polynomial

section Counting
variable {F : Type*} [Field F]

/-- Number of coefficient vectors in the box `S^8` on which `det M(r,s)` vanishes. -/
noncomputable def obstructionCount (S : Finset F) : ℕ := by
  classical
  exact ((Fintype.piFinset fun _ : Fin 8 => S).filter fun c => (cubicMatrix c).det = 0).card

/-- Schwartz--Zippel for the cubic determinant on any box: at most an `8/|S|` fraction. -/
theorem obstruction_fraction_le (S : Finset F) :
    (obstructionCount S : ℝ) / (S.card : ℝ) ^ 8 ≤ 8 / S.card := by
  classical
  have h := schwartz_zippel_totalDegree (cubicDet_ne_zero F) S
  have hd : ((cubicDet F).totalDegree : ℚ≥0) ≤ 8 := by exact_mod_cast totalDegree_cubicDet_le F
  have h' : (obstructionCount S : ℚ≥0) / (S.card : ℚ≥0) ^ 8 ≤ (8 : ℚ≥0) / S.card := by
    calc
      _ ≤ ((cubicDet F).totalDegree : ℚ≥0) / S.card := by
        simpa [obstructionCount, eval_cubicDet] using h
      _ ≤ _ := by gcongr
  have hh := (NNRat.cast_le (K := ℝ)).mpr h'
  simpa using hh

/-- Over a finite field: at most an `8/q` fraction of all `2 × 4` coefficient matrices. -/
theorem obstruction_fraction_le_field [Fintype F] :
    (obstructionCount (Finset.univ : Finset F) : ℝ) / (Fintype.card F : ℝ) ^ 8 ≤
      8 / Fintype.card F := by
  simpa [Finset.card_univ] using obstruction_fraction_le (Finset.univ : Finset F)

end Counting

section Quotient
variable {K : Type*} [Field K]
open KoszulProbability.Presentation

/-- The `2 × 4` relation matrix of a coefficient vector: rows `r`, `s`. -/
def relMatrix (c : Fin 8 → K) : Matrix (Fin 2) (Fin (2 * 2)) K :=
  !![c 0, c 1, c 2, c 3; c 4, c 5, c 6, c 7]

/-- Cubic monomials in the order `xxx, xxy, xyx, xyy, yxx, yxy, yyx, yyy`. -/
noncomputable def mono3 : Fin 8 → Free K 2 :=
  ![FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0,
    FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1,
    FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0,
    FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1,
    FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0,
    FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1,
    FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0,
    FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1]

/-- The linear map from cubic coordinates to the free algebra. -/
noncomputable def cubicMap : (Fin 8 → K) →ₗ[K] Free K 2 :=
  (Pi.basisFun K (Fin 8)).constr K mono3

lemma cubicMap_apply (v : Fin 8 → K) :
    cubicMap v = v 0 • mono3 0 + v 1 • mono3 1 + v 2 • mono3 2 + v 3 • mono3 3 +
      v 4 • mono3 4 + v 5 • mono3 5 + v 6 • mono3 6 + v 7 • mono3 7 := by
  simp [cubicMap, Module.Basis.constr_apply_fintype, Fin.sum_univ_eight]

lemma quadraticMap_two (v : Fin (2 * 2) → K) :
    quadraticMap K 2 v =
      v 0 • (FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0) + v 1 • (FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1) +
      v 2 • (FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0) + v 3 • (FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1) := by
  have h0 : finProdFinEquiv.symm (0 : Fin (2 * 2)) = ((0 : Fin 2), (0 : Fin 2)) := by decide
  have h1 : finProdFinEquiv.symm (1 : Fin (2 * 2)) = ((0 : Fin 2), (1 : Fin 2)) := by decide
  have h2 : finProdFinEquiv.symm (2 : Fin (2 * 2)) = ((1 : Fin 2), (0 : Fin 2)) := by decide
  have h3 : finProdFinEquiv.symm (3 : Fin (2 * 2)) = ((1 : Fin 2), (1 : Fin 2)) := by decide
  simp [quadraticMap, Module.Basis.constr_apply_fintype, Fin.sum_univ_four, h0, h1, h2, h3]

omit [Field K] in
lemma relMatrix_row_zero (c : Fin 8 → K) : (relMatrix c).row 0 = ![c 0, c 1, c 2, c 3] := by
  ext j
  fin_cases j <;> rfl

omit [Field K] in
lemma relMatrix_row_one (c : Fin 8 → K) : (relMatrix c).row 1 = ![c 4, c 5, c 6, c 7] := by
  ext j
  fin_cases j <;> rfl

lemma quadraticMap_vec (a b c d : K) :
    quadraticMap K 2 ![a, b, c, d] =
      a • (FreeAlgebra.ι K 0 * FreeAlgebra.ι K 0) + b • (FreeAlgebra.ι K 0 * FreeAlgebra.ι K 1) +
      c • (FreeAlgebra.ι K 1 * FreeAlgebra.ι K 0) + d • (FreeAlgebra.ι K 1 * FreeAlgebra.ι K 1) := by
  rw [quadraticMap_two]
  simp

/-- The listed relations, pushed to the quotient and expanded. -/
lemma mk_rel_zero (c : Fin 8 → K) :
    c 0 • (mk (relMatrix c) (FreeAlgebra.ι K 0) * mk (relMatrix c) (FreeAlgebra.ι K 0)) +
      c 1 • (mk (relMatrix c) (FreeAlgebra.ι K 0) * mk (relMatrix c) (FreeAlgebra.ι K 1)) +
      c 2 • (mk (relMatrix c) (FreeAlgebra.ι K 1) * mk (relMatrix c) (FreeAlgebra.ι K 0)) +
      c 3 • (mk (relMatrix c) (FreeAlgebra.ι K 1) * mk (relMatrix c) (FreeAlgebra.ι K 1)) = 0 := by
  have hr := row_vanishes (relMatrix c) 0
  rw [relMatrix_row_zero, quadraticMap_vec] at hr
  simpa only [map_add, map_smul, map_mul] using hr

lemma mk_rel_one (c : Fin 8 → K) :
    c 4 • (mk (relMatrix c) (FreeAlgebra.ι K 0) * mk (relMatrix c) (FreeAlgebra.ι K 0)) +
      c 5 • (mk (relMatrix c) (FreeAlgebra.ι K 0) * mk (relMatrix c) (FreeAlgebra.ι K 1)) +
      c 6 • (mk (relMatrix c) (FreeAlgebra.ι K 1) * mk (relMatrix c) (FreeAlgebra.ι K 0)) +
      c 7 • (mk (relMatrix c) (FreeAlgebra.ι K 1) * mk (relMatrix c) (FreeAlgebra.ι K 1)) = 0 := by
  have hs := row_vanishes (relMatrix c) 1
  rw [relMatrix_row_one, quadraticMap_vec] at hs
  simpa only [map_add, map_smul, map_mul] using hs

/-- Each column of `M(r,s)` is a cubic consequence of the listed relations. -/
lemma mk_col_zero (c : Fin 8 → K) (k : Fin 8) :
    mk (relMatrix c) (cubicMap fun u => cubicMatrix c u k) = 0 := by
  have hr := mk_rel_zero c
  have hs := mk_rel_one c
  fin_cases k
  · have := congrArg (fun z => mk (relMatrix c) (FreeAlgebra.ι K 0) * z) hr
    simp only [mul_add, mul_smul_comm, mul_zero, ← mul_assoc] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => mk (relMatrix c) (FreeAlgebra.ι K 1) * z) hr
    simp only [mul_add, mul_smul_comm, mul_zero, ← mul_assoc] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => mk (relMatrix c) (FreeAlgebra.ι K 0) * z) hs
    simp only [mul_add, mul_smul_comm, mul_zero, ← mul_assoc] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => mk (relMatrix c) (FreeAlgebra.ι K 1) * z) hs
    simp only [mul_add, mul_smul_comm, mul_zero, ← mul_assoc] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => z * mk (relMatrix c) (FreeAlgebra.ι K 0)) hr
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => z * mk (relMatrix c) (FreeAlgebra.ι K 1)) hr
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => z * mk (relMatrix c) (FreeAlgebra.ι K 0)) hs
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this
  · have := congrArg (fun z => z * mk (relMatrix c) (FreeAlgebra.ι K 1)) hs
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    simpa [cubicMap_apply, mono3, cubicMatrix, map_add, map_smul, map_mul] using this

/-- If `det M(r,s) ≠ 0`, every cubic monomial vanishes in the presented quotient. -/
theorem cubic_vanish (c : Fin 8 → K) (hc : (cubicMatrix c).det ≠ 0) (u : Fin 8) :
    mk (relMatrix c) (mono3 u) = 0 := by
  let f := (mk (relMatrix c)).toLinearMap.comp cubicMap
  have hspan : Submodule.span K (Set.range (cubicMatrix c)ᵀ.row) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact mk_col_zero c k
  rw [row_span_eq_top _ (by rwa [Matrix.det_transpose])] at hspan
  have := hspan (Submodule.mem_top : (Pi.basisFun K (Fin 8)) u ∈ ⊤)
  simpa [f, cubicMap, Module.Basis.constr_basis] using this

/-- **Cubic vanishing.** If `det M(r,s) ≠ 0`, all products of three generators are zero in the
actual quotient `T(V)/(r, s)`. -/
theorem cubic_products_vanish (c : Fin 8 → K) (hc : (cubicMatrix c).det ≠ 0) (i j k : Fin 2) :
    mk (relMatrix c) (FreeAlgebra.ι K i) * mk (relMatrix c) (FreeAlgebra.ι K j) *
      mk (relMatrix c) (FreeAlgebra.ι K k) = 0 := by
  rw [← map_mul, ← map_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact cubic_vanish c hc 0
  · exact cubic_vanish c hc 1
  · exact cubic_vanish c hc 2
  · exact cubic_vanish c hc 3
  · exact cubic_vanish c hc 4
  · exact cubic_vanish c hc 5
  · exact cubic_vanish c hc 6
  · exact cubic_vanish c hc 7

/-- If `det M(r,s) ≠ 0`, the two relations are linearly independent. -/
theorem rows_linearIndependent (c : Fin 8 → K) (hc : (cubicMatrix c).det ≠ 0) :
    LinearIndependent K ![(relMatrix c).row 0, (relMatrix c).row 1] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_contra hne
  have hv : (![s, 0, t, 0, 0, 0, 0, 0] : Fin 8 → K) ≠ 0 := by
    intro h0
    apply hne
    constructor
    · simpa using congrFun h0 0
    · simpa using congrFun h0 2
  have hmul : cubicMatrix c *ᵥ ![s, 0, t, 0, 0, 0, 0, 0] = 0 := by
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    have h2 := congrFun hst 2
    have h3 := congrFun hst 3
    simp [relMatrix] at h0 h1 h2 h3
    funext u
    fin_cases u <;> simp [cubicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;>
      first
      | linear_combination h0
      | linear_combination h1
      | linear_combination h2
      | linear_combination h3
  exact hc (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hv, hmul⟩)

end Quotient

end KoszulProbability.Obstruction
