import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

namespace KoszulProbability
namespace SquareZero
open TrivSqZeroExt

variable (K : Type*) [Field K] (n : ℕ)
abbrev Algebra := TrivSqZeroExt K (Fin n → K)
abbrev Word (i : ℕ) := Fin i → Fin n
/-- Free module with basis the words of length i; basis vectors have internal degree i. -/
abbrev P (i : ℕ) := Word n i → Algebra K n

/-- The linear resolution differential. It multiplies the first letter into the coefficient. -/
def differential (i : ℕ) (f : P K n (i+1)) : P K n i :=
  fun w => inr (fun j => (f (Fin.cons j w)).fst)

lemma differential_add (i : ℕ) (f g : P K n (i+1)) :
    differential K n i (f+g) = differential K n i f + differential K n i g := by
  ext w <;> simp [differential]

lemma differential_smul (i : ℕ) (a : Algebra K n) (f : P K n (i+1)) :
    differential K n i (a • f) = a • differential K n i f := by
  ext w j <;> simp [differential, smul_eq_mul, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.snd_mul]

/-- An actual linear map over the square-zero algebra, not merely over the ground field. -/
def d (i : ℕ) : P K n (i+1) →ₗ[Algebra K n] P K n i where
  toFun := differential K n i
  map_add' := differential_add K n i
  map_smul' := differential_smul K n i

lemma d_squared (i : ℕ) (f : P K n (i+2)) : d K n i (d K n (i+1) f) = 0 := by
  ext w j <;> simp [d, differential]

/-- Every cycle in positive homological degree is a boundary, in all degrees. -/
theorem exact_at (i : ℕ) (f : P K n (i+1)) :
    d K n i f = 0 ↔ ∃ g : P K n (i+2), d K n (i+1) g = f := by
  constructor
  · intro hf
    have hfst : ∀ w, (f w).fst = 0 := by
      intro w
      have h := congrArg (fun z : P K n i => (z (Fin.tail w)).snd (w 0)) hf
      simpa [d, differential] using h
    let g : P K n (i+2) := fun w => inl ((f (Fin.tail w)).snd (w 0))
    refine ⟨g, ?_⟩
    ext w j <;> simp [d, differential, g, hfst]
  · rintro ⟨g, rfl⟩
    exact d_squared K n i g

def augmentation (f : P K n 0) : K := (f Fin.elim0).fst

theorem augmentation_surjective : Function.Surjective (augmentation K n) := by
  intro c
  exact ⟨fun _ => inl c, rfl⟩

theorem exact_at_zero (f : P K n 0) :
    augmentation K n f = 0 ↔ ∃ g : P K n 1, d K n 0 g = f := by
  constructor
  · intro hf
    have hfst : ∀ w, (f w).fst = 0 := by
      intro w
      have : w = Fin.elim0 := Subsingleton.elim _ _
      simpa [this, augmentation] using hf
    let g : P K n 1 := fun w => inl ((f Fin.elim0).snd (w 0))
    refine ⟨g, ?_⟩
    ext w j
    · simp [d, differential, hfst]
    · have : w = Fin.elim0 := Subsingleton.elim _ _
      simp [d, differential, g, this]
  · rintro ⟨g, rfl⟩
    simp [augmentation, d, differential]

/-- Each term is free as a module over A. -/
theorem terms_free (i : ℕ) : Module.Free (Algebra K n) (P K n i) := inferInstance

/-- Internal-degree j piece: coefficients have scalar degree 0 and radical degree 1. -/
def Homogeneous (i j : ℕ) (f : P K n i) : Prop :=
  (j ≠ i → ∀ w, (f w).fst = 0) ∧ (j ≠ i+1 → ∀ w, (f w).snd = 0)

/-- All differentials preserve internal degree. -/
theorem degree_preserving (i j : ℕ) (f : P K n (i+1))
    (hf : Homogeneous K n (i+1) j f) : Homogeneous K n i j (d K n i f) := by
  constructor
  · intro _ w
    rfl
  · intro hj w
    ext k
    exact hf.1 hj (Fin.cons k w)

/-- The standard free basis lies in internal degree equal to homological degree. -/
theorem basis_linear (i : ℕ) (w : Word n i) :
    Homogeneous K n i i ((Pi.basisFun (Algebra K n) (Word n i)) w) := by
  constructor
  · simp
  · intro _ v
    classical
    simp only [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp

/-- A bundled statement of the free, linear, exact augmented resolution in every degree. -/
theorem linear_resolution :
    Function.Surjective (augmentation K n) ∧
    (∀ f, augmentation K n f = 0 ↔ ∃ g, d K n 0 g = f) ∧
    (∀ i f, d K n i f = 0 ↔ ∃ g, d K n (i+1) g = f) ∧
    (∀ i, Module.Free (Algebra K n) (P K n i)) ∧
    (∀ i j f, Homogeneous K n (i+1) j f → Homogeneous K n i j (d K n i f)) ∧
    (∀ i w, Homogeneous K n i i ((Pi.basisFun (Algebra K n) (Word n i)) w)) :=
  ⟨augmentation_surjective K n, exact_at_zero K n, exact_at K n,
    terms_free K n, degree_preserving K n, basis_linear K n⟩

end SquareZero
end KoszulProbability
