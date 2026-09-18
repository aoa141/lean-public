import KoszulProbability.MatrixCounting
import KoszulProbability.SquareZero
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators
open Finset
namespace KoszulProbability

variable {K : Type*} [Field K] {d : ℕ}

/-- Invertibility really does imply that the listed rows span all quadratic coefficients. -/
theorem row_span_eq_top (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K (Set.range C.row) = ⊤ := by
  rw [← range_vecMulLinear]
  apply LinearMap.range_eq_top.mpr
  exact Matrix.vecMul_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC))

namespace Presentation
variable (K : Type*) [Field K] (n : ℕ)
abbrev Free := FreeAlgebra K (Fin n)
abbrev Coeff := Fin (n*n) → K

noncomputable def quadraticMap : Coeff K n →ₗ[K] Free K n :=
  (Pi.basisFun K (Fin (n*n))).constr K fun j =>
    FreeAlgebra.ι K (finProdFinEquiv.symm j).1 * FreeAlgebra.ι K (finProdFinEquiv.symm j).2

variable {K n} {m : ℕ}
def rel (C : Matrix (Fin m) (Fin (n*n)) K) (a b : Free K n) : Prop :=
  ∃ i, a = quadraticMap K n (C.row i) ∧ b = 0

abbrev Quotient (C : Matrix (Fin m) (Fin (n*n)) K) := RingQuot (rel C)
noncomputable def mk (C : Matrix (Fin m) (Fin (n*n)) K) :
    Free K n →ₐ[K] Quotient C := RingQuot.mkAlgHom K (rel C)

lemma row_vanishes (C : Matrix (Fin m) (Fin (n*n)) K) (i : Fin m) :
    mk C (quadraticMap K n (C.row i)) = 0 := by
  have h := RingQuot.mkAlgHom_rel K (show rel C (quadraticMap K n (C.row i)) 0 from ⟨i,rfl,rfl⟩)
  simpa [mk] using h

lemma all_quadratics_vanish (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0)
    (v : Coeff K n) : mk C (quadraticMap K n v) = 0 := by
  let f := (mk C).toLinearMap.comp (quadraticMap K n)
  have hspan : Submodule.span K (Set.range C.row) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact row_vanishes C i
  rw [row_span_eq_top C hC] at hspan
  exact hspan (Submodule.mem_top : v ∈ (⊤ : Submodule K (Coeff K n)))

lemma generators_mul_zero (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0)
    (i j : Fin n) : mk C (FreeAlgebra.ι K i) * mk C (FreeAlgebra.ι K j) = 0 := by
  have h := all_quadratics_vanish C hC ((Pi.basisFun K (Fin (n*n))) (finProdFinEquiv (i,j)))
  simpa only [quadraticMap, Module.Basis.constr_basis, Equiv.symm_apply_apply, map_mul] using h

noncomputable def freeToSquare : Free K n →ₐ[K] SquareZero.Algebra K n :=
  FreeAlgebra.lift K fun i => TrivSqZeroExt.inr ((Pi.basisFun K (Fin n)) i)

lemma freeToSquare_quadratic (v : Coeff K n) :
    freeToSquare (quadraticMap K n v) = 0 := by
  have h : freeToSquare.toLinearMap.comp (quadraticMap K n) = 0 := by
    apply (Pi.basisFun K (Fin (n*n))).ext
    intro j
    simp [quadraticMap, freeToSquare, TrivSqZeroExt.inr_mul_inr]
  exact LinearMap.congr_fun h v

noncomputable def toSquare (C : Matrix (Fin m) (Fin (n*n)) K) :
    Quotient C →ₐ[K] SquareZero.Algebra K n :=
  RingQuot.liftAlgHom K ⟨freeToSquare, by
    rintro a b ⟨i,rfl,rfl⟩
    simp [freeToSquare_quadratic]⟩

@[simp] lemma toSquare_generator (C : Matrix (Fin m) (Fin (n*n)) K) (i : Fin n) :
    toSquare C (mk C (FreeAlgebra.ι K i)) = TrivSqZeroExt.inr ((Pi.basisFun K (Fin n)) i) := by
  simp [toSquare, mk, freeToSquare]

noncomputable def radicalMap (C : Matrix (Fin m) (Fin (n*n)) K) :
    (Fin n → K) →ₗ[K] Quotient C :=
  (Pi.basisFun K (Fin n)).constr K fun i => mk C (FreeAlgebra.ι K i)

lemma radicalMap_mul_zero (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0)
    (u v : Fin n → K) : radicalMap C u * radicalMap C v = 0 := by
  classical
  simp only [radicalMap, Module.Basis.constr_apply_fintype]
  simp [Finset.sum_mul, Finset.mul_sum,
    generators_mul_zero C hC]

noncomputable def fromSquare (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0) :
    SquareZero.Algebra K n →ₐ[K] Quotient C :=
  TrivSqZeroExt.liftEquivOfComm ⟨radicalMap C, radicalMap_mul_zero C hC⟩

@[simp] lemma fromSquare_inr (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0)
    (v : Fin n → K) : fromSquare C hC (TrivSqZeroExt.inr v) = radicalMap C v := by
  simp [fromSquare, TrivSqZeroExt.liftEquivOfComm_apply]

lemma from_to (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0) :
    (fromSquare C hC).comp (toSquare C) = AlgHom.id K (Quotient C) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  change fromSquare C hC (toSquare C (mk C (FreeAlgebra.ι K i))) = _
  simp only [toSquare_generator, fromSquare_inr, radicalMap, Module.Basis.constr_basis]
  rfl

lemma to_from (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0) :
    (toSquare C).comp (fromSquare C hC) = AlgHom.id K (SquareZero.Algebra K n) := by
  apply TrivSqZeroExt.algHom_ext
  intro v
  change toSquare C (fromSquare C hC (TrivSqZeroExt.inr v)) = TrivSqZeroExt.inr v
  rw [fromSquare_inr]
  have h : (toSquare C).toLinearMap.comp (radicalMap C) = TrivSqZeroExt.inrHom K (Fin n → K) := by
    apply (Pi.basisFun K (Fin n)).ext
    intro i
    simp [radicalMap]
  exact LinearMap.congr_fun h v

/-- The algebra isomorphism from the actual presented quotient to the square-zero algebra. -/
noncomputable def squareZeroEquiv (C : Matrix (Fin (n*n)) (Fin (n*n)) K) (hC : C.det ≠ 0) :
    Quotient C ≃ₐ[K] SquareZero.Algebra K n :=
  AlgEquiv.ofAlgHom (toSquare C) (fromSquare C hC)
    (to_from C hC) (from_to C hC)

end Presentation
end KoszulProbability
