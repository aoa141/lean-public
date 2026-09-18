import KoszulProbability.Presentation

namespace KoszulProbability.Transport
open TrivSqZeroExt

variable {K Q : Type*} [Field K] [Ring Q] [Algebra K Q] {n : ℕ}
variable (e : Q ≃ₐ[K] SquareZero.Algebra K n)

abbrev P (i : ℕ) := SquareZero.Word n i → Q

def toModel (i : ℕ) (f : P (Q := Q) (n := n) i) : SquareZero.P K n i := fun w => e (f w)
def fromModel (i : ℕ) (f : SquareZero.P K n i) : P (Q := Q) (n := n) i := fun w => e.symm (f w)

@[simp] lemma to_from (i : ℕ) (f : SquareZero.P K n i) :
    toModel e i (fromModel e i f) = f := by funext w; exact e.apply_symm_apply _
@[simp] lemma from_to (i : ℕ) (f : P (Q := Q) (n := n) i) :
    fromModel e i (toModel e i f) = f := by funext w; exact e.symm_apply_apply _

lemma toModel_injective (i : ℕ) : Function.Injective (toModel e i) := by
  intro f g h
  funext w
  exact e.injective (congrFun h w)

@[simp] lemma toModel_zero (i : ℕ) : toModel e i 0 = 0 := by funext w; exact map_zero e
@[simp] lemma toModel_add (i : ℕ) (f g : P (Q := Q) (n := n) i) :
    toModel e i (f+g) = toModel e i f + toModel e i g := by funext w; exact map_add e _ _
@[simp] lemma toModel_smul (i : ℕ) (a : Q) (f : P (Q := Q) (n := n) i) :
    toModel e i (a • f) = e a • toModel e i f := by funext w; exact map_mul e _ _

noncomputable def differential (i : ℕ) (f : P (Q := Q) (n := n) (i+1)) :
    P (Q := Q) (n := n) i := fromModel e i (SquareZero.d K n i (toModel e (i+1) f))

@[simp] lemma toModel_differential (i : ℕ) (f : P (Q := Q) (n := n) (i+1)) :
    toModel e i (differential e i f) = SquareZero.d K n i (toModel e (i+1) f) := to_from e i _

/-- A linear differential over the actual source algebra Q. -/
noncomputable def d (i : ℕ) : P (Q := Q) (n := n) (i+1) →ₗ[Q] P (Q := Q) (n := n) i where
  toFun := differential e i
  map_add' f g := by
    apply toModel_injective e i
    simp
  map_smul' a f := by
    apply toModel_injective e i
    simp

@[simp] lemma toModel_d (i : ℕ) (f : P (Q := Q) (n := n) (i+1)) :
    toModel e i (d e i f) = SquareZero.d K n i (toModel e (i+1) f) := to_from e i _

theorem exact_at (i : ℕ) (f : P (Q := Q) (n := n) (i+1)) :
    d e i f = 0 ↔ ∃ g : P (Q := Q) (n := n) (i+2), d e (i+1) g = f := by
  constructor
  · intro hf
    have hm : SquareZero.d K n i (toModel e (i+1) f) = 0 := by
      simpa using congrArg (toModel e i) hf
    obtain ⟨g,hg⟩ := (SquareZero.exact_at K n i _).mp hm
    refine ⟨fromModel e (i+2) g, toModel_injective e (i+1) ?_⟩
    simpa using hg
  · rintro ⟨g,rfl⟩
    apply toModel_injective e i
    simp [SquareZero.d_squared]

def augmentation (f : P (Q := Q) (n := n) 0) : K := SquareZero.augmentation K n (toModel e 0 f)

theorem augmentation_surjective : Function.Surjective (augmentation e) := by
  intro c
  obtain ⟨f,hf⟩ := SquareZero.augmentation_surjective K n c
  exact ⟨fromModel e 0 f, by simpa [augmentation] using hf⟩

theorem augmentation_smul (a : Q) (f : P (Q := Q) (n := n) 0) :
    augmentation e (a • f) = (e a).fst * augmentation e f := by
  simp [augmentation, SquareZero.augmentation, toModel_smul, smul_eq_mul]

theorem exact_at_zero (f : P (Q := Q) (n := n) 0) :
    augmentation e f = 0 ↔ ∃ g : P (Q := Q) (n := n) 1, d e 0 g = f := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := (SquareZero.exact_at_zero K n _).mp hf
    refine ⟨fromModel e 1 g, toModel_injective e 0 ?_⟩
    simpa using hg
  · rintro ⟨g,rfl⟩
    simp [augmentation, SquareZero.augmentation, SquareZero.d, SquareZero.differential]

def Homogeneous (i j : ℕ) (f : P (Q := Q) (n := n) i) : Prop :=
  SquareZero.Homogeneous K n i j (toModel e i f)

theorem degree_preserving (i j : ℕ) (f : P (Q := Q) (n := n) (i+1))
    (hf : Homogeneous e (i+1) j f) : Homogeneous e i j (d e i f) := by
  unfold Homogeneous
  rw [toModel_d]
  exact SquareZero.degree_preserving K n i j _ hf

theorem terms_free (i : ℕ) : Module.Free Q (P (Q := Q) (n := n) i) := inferInstance

theorem basis_linear (i : ℕ) (w : SquareZero.Word n i) :
    Homogeneous e i i ((Pi.basisFun Q (SquareZero.Word n i)) w) := by
  classical
  have h : toModel e i ((Pi.basisFun Q (SquareZero.Word n i)) w) =
      (Pi.basisFun (SquareZero.Algebra K n) (SquareZero.Word n i)) w := by
    funext v
    simp only [toModel, Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp
  unfold Homogeneous
  rw [h]
  exact SquareZero.basis_linear K n i w

/-- Free, linear, exact augmented resolution over the source algebra Q. -/
def IsLinearResolution : Prop :=
    Function.Surjective (augmentation e) ∧
    (∀ f, augmentation e f = 0 ↔ ∃ g, d e 0 g = f) ∧
    (∀ i f, d e i f = 0 ↔ ∃ g, d e (i+1) g = f) ∧
    (∀ i, Module.Free Q (P (Q := Q) (n := n) i)) ∧
    (∀ i j f, Homogeneous e (i+1) j f → Homogeneous e i j (d e i f)) ∧
    (∀ i w, Homogeneous e i i ((Pi.basisFun Q (SquareZero.Word n i)) w))

/-- Constructive transport, with no exactness or linearity assumptions. -/
theorem linear_resolution : IsLinearResolution e :=
  ⟨augmentation_surjective e, exact_at_zero e, exact_at e,
    terms_free, degree_preserving e, basis_linear e⟩

end KoszulProbability.Transport
