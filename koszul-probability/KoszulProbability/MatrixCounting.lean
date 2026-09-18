import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open scoped BigOperators
open Finset MvPolynomial

namespace KoszulProbability

/-- Row-major coordinates for a square coefficient matrix. -/
def matrixOf {K : Type*} (d : ℕ) (x : Fin (d * d) → K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => x (finProdFinEquiv (i, j))

noncomputable def detPolynomial (K : Type*) [CommRing K] (d : ℕ) :
    MvPolynomial (Fin (d * d)) K :=
  Matrix.det (Matrix.of fun i j : Fin d => X (finProdFinEquiv (i, j)))

lemma eval_detPolynomial {K : Type*} [CommRing K] (d : ℕ) (x : Fin (d*d) → K) :
    eval x (detPolynomial K d) = (matrixOf d x).det := by
  unfold detPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [matrixOf, Matrix.map_apply]

lemma detPolynomial_ne_zero (K : Type*) [CommRing K] [Nontrivial K] (d : ℕ) :
    detPolynomial K d ≠ 0 := by
  intro h
  let x : Fin (d*d) → K := fun t =>
    if (finProdFinEquiv.symm t).1 = (finProdFinEquiv.symm t).2 then 1 else 0
  have hm : matrixOf d x = (1 : Matrix (Fin d) (Fin d) K) := by
    ext i j
    change (if (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 =
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 then (1 : K) else 0) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have he := eval_detPolynomial d x
  rw [h, map_zero, hm, Matrix.det_one] at he
  exact zero_ne_one he

lemma totalDegree_detPolynomial_le (K : Type*) [CommRing K] [Nontrivial K] (d : ℕ) :
    (detPolynomial K d).totalDegree ≤ d := by
  classical
  unfold detPolynomial
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ hσ
  calc
    _ ≤ (∏ i : Fin d, (X (finProdFinEquiv (σ i, i)) : MvPolynomial (Fin (d*d)) K)).totalDegree := by
      simpa only [Units.smul_def, Matrix.of_apply] using totalDegree_smul_le (↑(Equiv.Perm.sign σ) : ℤ)
        (∏ i : Fin d, (X (finProdFinEquiv (σ i, i)) : MvPolynomial (Fin (d*d)) K))
    _ ≤ ∑ i : Fin d, (X (finProdFinEquiv (σ i, i)) : MvPolynomial (Fin (d*d)) K).totalDegree :=
      totalDegree_finsetProd _ _
    _ = d := by simp

/-- Number of singular square coefficient matrices, represented in row-major coordinates. -/
noncomputable def singularCount (K : Type*) [Field K] [Fintype K] (d : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin (d*d) → K => (matrixOf d x).det = 0).card

/-- The finite-field determinant bound; no independence or genericity hypothesis is assumed. -/
theorem singular_fraction_le (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    (singularCount K d : ℝ) / (Fintype.card K : ℝ) ^ (d*d) ≤
      (d : ℝ) / Fintype.card K := by
  classical
  have h := schwartz_zippel_totalDegree (detPolynomial_ne_zero K d) (Finset.univ : Finset K)
  have hd := totalDegree_detPolynomial_le K d
  have h' : (singularCount K d : ℚ≥0) / (Fintype.card K : ℚ≥0) ^ (d*d) ≤
      (d : ℚ≥0) / Fintype.card K := by
    calc
      _ ≤ ((detPolynomial K d).totalDegree : ℚ≥0) / Fintype.card K := by
        simpa [singularCount, eval_detPolynomial] using h
      _ ≤ _ := by gcongr
  have hh := (NNRat.cast_le (K := ℝ)).mpr h'
  simpa using hh

end KoszulProbability
