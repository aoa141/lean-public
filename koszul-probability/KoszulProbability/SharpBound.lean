import KoszulProbability.AlgebraDensity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A sharper error bound

The paper's bound `(2B⁴ + B²)/p^B` has two sources of slack.

* Schwartz--Zippel gives singular fraction `≤ B²/p^B` in the top stratum, but the exact
  count of invertible matrices over `GF(q)` gives singular fraction `≤ 1/(q - 1)`, with no
  polynomial factor.
* Every non-top stratum loses at least `B³` (not merely `B`) base-`p` digits.

Together these give `1 - M/W ≤ 1/(p^B - 1) + 2B⁴/p^(B³)`, which is `≤ 3/p^B` for `B ≥ 2`.
The exact count also gives a *lower* bound `1/p^B` on the singular fraction, used in
`Converse.lean` for the matching lower bound.
-/

open scoped BigOperators
open Finset Filter Topology

namespace KoszulProbability

section ExactCount

variable {K : Type*} [Field K] [Fintype K]

/-- Row-major coordinates form a bijection with square matrices. -/
def matrixOfEquiv (d : ℕ) : (Fin (d * d) → K) ≃ Matrix (Fin d) (Fin d) K where
  toFun := matrixOf d
  invFun M := fun t => M (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  left_inv x := by
    funext t
    show x (finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2)) = x t
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv M := by
    ext i j
    simp [matrixOf]

/-- Units of a monoid are the same as elements satisfying `IsUnit`. -/
noncomputable def unitsEquivIsUnit {M : Type*} [Monoid M] : Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv _ := Units.ext (IsUnit.unit_spec _)
  right_inv x := Subtype.ext x.2.unit_spec

/-- The exact number of invertible `d × d` matrices over a finite field. -/
theorem regularCount_eq (d : ℕ) :
    regularCount K d = ∏ i : Fin d, ((Fintype.card K) ^ d - (Fintype.card K) ^ (i : ℕ)) := by
  classical
  rw [← Matrix.card_GL_field]
  unfold regularCount
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ?_
  refine ((matrixOfEquiv d).subtypeEquiv
    (q := fun M : Matrix (Fin d) (Fin d) K => M.det ≠ 0) fun x => Iff.rfl).trans ?_
  refine (Equiv.subtypeEquivRight fun M => ?_).trans unitsEquivIsUnit.symm
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Weierstrass' product inequality. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi))
      (fun i hi => h1 i (mem_insert_of_mem hi))
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1), mul_nonneg ha0 hs0]

/-- The regular count as a real product, factored as `q^(d²)` times `∏ (1 - q^(i-d))`. -/
lemma regularCount_real (d : ℕ) :
    (regularCount K d : ℝ) =
      (Fintype.card K : ℝ) ^ (d * d) *
        ∏ i ∈ range d, (1 - (Fintype.card K : ℝ) ^ i / (Fintype.card K : ℝ) ^ d) := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [regularCount_eq, Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ d - Fintype.card K ^ i),
    Nat.cast_prod]
  rw [show (Fintype.card K : ℝ) ^ (d * d) = ∏ _i ∈ range d, (Fintype.card K : ℝ) ^ d by
    rw [prod_const, card_range, ← pow_mul]]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hle : Fintype.card K ^ i ≤ Fintype.card K ^ d :=
    Nat.pow_le_pow_right Fintype.card_pos (mem_range.mp hi).le
  rw [Nat.cast_sub hle]
  push_cast
  field_simp

/-- The singular fraction is at most `1/(q-1)`: no polynomial factor in `d`. -/
theorem singular_fraction_le_inv (d : ℕ) :
    (singularCount K d : ℝ) / (Fintype.card K : ℝ) ^ (d * d) ≤
      1 / ((Fintype.card K : ℝ) - 1) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card
  have hq0 : (0 : ℝ) < Fintype.card K := by linarith
  have hqd : (0 : ℝ) < (Fintype.card K : ℝ) ^ d := pow_pos hq0 _
  have hpow : (0 : ℝ) < (Fintype.card K : ℝ) ^ (d * d) := pow_pos hq0 _
  have hsum : (singularCount K d : ℝ) = (Fintype.card K : ℝ) ^ (d * d) - regularCount K d := by
    have := regular_add_singular K d
    have h' : (regularCount K d : ℝ) + singularCount K d = (Fintype.card K : ℝ) ^ (d * d) := by
      exact_mod_cast this
    linarith
  rw [hsum, regularCount_real]
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  have hprod := one_sub_sum_le_prod_one_sub (range d) (fun i => q ^ i / q ^ d)
    (fun i _ => by positivity)
    (fun i hi => by
      rw [div_le_one hqd]
      exact pow_le_pow_right₀ hq.le (mem_range.mp hi).le)
  have hgeom : ∑ i ∈ range d, q ^ i / q ^ d ≤ 1 / (q - 1) := by
    rw [← sum_div, geom_sum_eq hq.ne', div_div]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [pow_pos hq0 d]
  rw [sub_div, div_self hpow.ne', mul_div_cancel_left₀ _ hpow.ne']
  have : (1 : ℝ) - ∏ i ∈ range d, (1 - q ^ i / q ^ d) ≤ ∑ i ∈ range d, q ^ i / q ^ d := by
    linarith
  exact this.trans hgeom

/-- The singular fraction is at least `1/q` as soon as `d ≥ 1`. -/
theorem singular_fraction_ge {d : ℕ} (hd : 1 ≤ d) :
    1 / (Fintype.card K : ℝ) ≤ (singularCount K d : ℝ) / (Fintype.card K : ℝ) ^ (d * d) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card
  have hq0 : (0 : ℝ) < Fintype.card K := by linarith
  have hqd : (0 : ℝ) < (Fintype.card K : ℝ) ^ d := pow_pos hq0 _
  have hpow : (0 : ℝ) < (Fintype.card K : ℝ) ^ (d * d) := pow_pos hq0 _
  have hsum : (singularCount K d : ℝ) = (Fintype.card K : ℝ) ^ (d * d) - regularCount K d := by
    have := regular_add_singular K d
    have h' : (regularCount K d : ℝ) + singularCount K d = (Fintype.card K : ℝ) ^ (d * d) := by
      exact_mod_cast this
    linarith
  rw [hsum, regularCount_real]
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hlast : ∏ i ∈ range (d' + 1), (1 - q ^ i / q ^ (d' + 1)) ≤ 1 - 1 / q := by
    rw [prod_range_succ]
    have h1 : ∏ i ∈ range d', (1 - q ^ i / q ^ (d' + 1)) ≤ 1 := by
      apply prod_le_one
      · intro i hi
        rw [sub_nonneg, div_le_one hqd]
        exact pow_le_pow_right₀ hq.le ((mem_range.mp hi).le.trans (Nat.le_succ d'))
      · intro i _
        have : 0 ≤ q ^ i / q ^ (d' + 1) := by positivity
        linarith
    have h0 : 0 ≤ ∏ i ∈ range d', (1 - q ^ i / q ^ (d' + 1)) := by
      apply prod_nonneg
      intro i hi
      rw [sub_nonneg, div_le_one hqd]
      exact pow_le_pow_right₀ hq.le ((mem_range.mp hi).le.trans (Nat.le_succ d'))
    have h2 : q ^ d' / q ^ (d' + 1) = 1 / q := by
      rw [pow_succ]
      field_simp
    rw [h2]
    have : 0 ≤ 1 - 1 / q := by
      rw [sub_nonneg, div_le_one hq0]
      exact hq.le
    nlinarith
  rw [sub_div, div_self hpow.ne', mul_div_cancel_left₀ _ hpow.ne']
  linarith

end ExactCount

/-- Every stratum except the top one loses at least `B³` base-`p` digits. -/
lemma exponent_gap_cube {B : ℕ} (hB : 1 ≤ B) {a : Stratum}
    (ha : a ∈ indices B) (hne : a ≠ topIndex B) : exponent a + B ^ 3 ≤ B ^ 5 := by
  rcases a with ⟨n, e, m⟩
  obtain ⟨hn, hnB, he, heB, hmB, hmn⟩ := mem_indices.mp ha
  dsimp at hn hnB he heB hmB hmn
  have hn2 : n ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hnB 2
  have hB34 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB (by norm_num)
  dsimp [exponent]
  by_cases heq : e = B
  · subst e
    by_cases hmeq : m = B ^ 2
    · subst m
      have hnlt : n < B := by
        by_contra! h
        have : n = B := by omega
        subst n
        exact hne (by simp [topIndex, pow_two])
      have hn2gap : n ^ 2 + 1 ≤ B ^ 2 := by nlinarith
      have hh := Nat.mul_le_mul_left (B * B ^ 2) hn2gap
      nlinarith
    · have hm : m + 1 ≤ B ^ 2 := by omega
      have hh := Nat.mul_le_mul_left (B * B ^ 2) hm
      have hprod := Nat.mul_le_mul_left (B * m) hn2
      nlinarith
  · have he' : e + 1 ≤ B := by omega
    have hh := Nat.mul_le_mul_right (B ^ 2 * B ^ 2) he'
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left e hmB) hn2
    nlinarith

lemma off_top_weight_le_cube {p : ℝ} (hp : 1 ≤ p) {B : ℕ} (hB : 1 ≤ B)
    {a : Stratum} (ha : a ∈ (indices B).erase (topIndex B)) :
    weight p a ≤ p ^ (B ^ 5) / p ^ (B ^ 3) := by
  have hgap := exponent_gap_cube hB (mem_erase.mp ha).2 (mem_erase.mp ha).1
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  apply (le_div_iff₀ (pow_pos hp0 _)).mpr
  simpa [weight, ← pow_add] using (pow_le_pow_right₀ hp hgap)

/-- The mass outside the top stratum is at most `2B⁴/p^(B³)` times the top stratum. -/
theorem off_top_bound_cube {p : ℝ} (hp : 1 ≤ p) {B : ℕ} (hB : 1 ≤ B) :
    ballSize p B - p ^ (B ^ 5) ≤ (2 * (B : ℝ) ^ 4 / p ^ (B ^ 3)) * p ^ (B ^ 5) := by
  have heq : ballSize p B - p ^ (B ^ 5) = ∑ a ∈ (indices B).erase (topIndex B), weight p a := by
    rw [ballSize, ← sum_erase_add _ _ (top_mem hB)]
    simp [weight, exponent_top]
  rw [heq]
  calc
    _ ≤ ∑ _a ∈ (indices B).erase (topIndex B), p ^ (B ^ 5) / p ^ (B ^ 3) :=
      sum_le_sum fun _ ha => off_top_weight_le_cube hp hB ha
    _ = ((indices B).erase (topIndex B)).card * (p ^ (B ^ 5) / p ^ (B ^ 3)) := by simp
    _ ≤ (2 * (B : ℝ) ^ 4) * (p ^ (B ^ 5) / p ^ (B ^ 3)) := by
      gcongr
      exact_mod_cast (card_erase_le.trans (card_indices_le hB))
    _ = _ := by ring

/-- Abstract two-term failure bound: mass outside the top stratum is a `δ`-fraction of the top
stratum, and the good set misses at most an `ε`-fraction of the top stratum. -/
theorem failure_bound_two_terms {W T good ε δ : ℝ} (hT : 0 < T) (hTW : T ≤ W)
    (hoff : W - T ≤ δ * T) (hgood : T * (1 - ε) ≤ good) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    1 - good / W ≤ ε + δ := by
  have hW : 0 < W := lt_of_lt_of_le hT hTW
  have hnum : W - good ≤ (ε + δ) * W := by
    nlinarith [mul_le_mul_of_nonneg_left hTW (add_nonneg hε hδ)]
  have hid : 1 - good / W = (W - good) / W := by
    rw [sub_div, div_self hW.ne']
  rw [hid]
  exact (div_le_iff₀ hW).mpr hnum

/-- The certified count misses at most a `1/(p^B - 1)` fraction of the top stratum. -/
lemma certified_lower_sharp (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (p : ℝ) ^ (B ^ 5) * (1 - 1 / ((p : ℝ) ^ B - 1)) ≤ certifiedCount p B := by
  have hc := regular_add_singular (GaloisField p B) (B * B)
  rw [field_card p hB, top_card] at hc
  have hcR : (certifiedCount p B : ℝ) + singularCount (GaloisField p B) (B * B) =
      (p : ℝ) ^ (B ^ 5) := by exact_mod_cast hc
  have hs := singular_fraction_le_inv (K := GaloisField p B) (B * B)
  rw [field_card p hB] at hs
  push_cast at hs
  rw [← pow_mul, show B * (B * B * (B * B)) = B ^ 5 by ring] at hs
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmul := (div_le_iff₀ (pow_pos hp (B ^ 5))).mp hs
  nlinarith

/-- Sharp finite bound for the square-zero model event: `1/(p^B - 1) + 2B⁴/p^(B³)`. -/
theorem square_zero_algebra_error_sharp (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    1 - (modelCount p B : ℝ) / ballSize p B ≤
      1 / ((p : ℝ) ^ B - 1) + 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpB : (2 : ℝ) ≤ (p : ℝ) ^ B := by
    calc (2 : ℝ) = (2 : ℕ) := by norm_num
      _ ≤ ((p ^ B : ℕ) : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
      _ = (p : ℝ) ^ B := by push_cast; ring
  apply failure_bound_two_terms (T := (p : ℝ) ^ (B ^ 5)) (pow_pos hp0 _)
    (top_weight_le_ball hp0.le hB)
  · have := off_top_bound_cube hp.le hB
    linarith
  · exact (certified_lower_sharp p hB).trans (by exact_mod_cast certified_le_model p hB)
  · apply div_nonneg zero_le_one; linarith
  · positivity

/-- For `B ≥ 2`, the sharp bound is at most `3/p^B`. -/
lemma two_mul_pow_four_le {p B : ℕ} (hp : 2 ≤ p) (hB : 2 ≤ B) :
    2 * B ^ 4 * p ^ B ≤ p ^ (B ^ 3) := by
  rcases Nat.lt_or_ge B 3 with h3 | h3
  · have hB2 : B = 2 := by omega
    subst hB2
    have h6 : 2 ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left hp 6
    calc 2 * 2 ^ 4 * p ^ 2 = 2 ^ 5 * p ^ 2 := by ring
      _ ≤ 2 ^ 6 * p ^ 2 := by gcongr <;> norm_num
      _ ≤ p ^ 6 * p ^ 2 := by gcongr
      _ = p ^ (2 ^ 3) := by ring
  · have hB4 : B ^ 4 < 2 ^ (4 * B) := by
      rw [pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num]
      calc B ^ 4 < (2 ^ B) ^ 4 := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
        _ = 16 ^ B := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 : 2 * B ^ 4 * p ^ B ≤ 2 * 2 ^ (4 * B) * p ^ B := by gcongr
    have h2 : 2 * 2 ^ (4 * B) * p ^ B ≤ p * p ^ (4 * B) * p ^ B := by
      gcongr
    have h3' : p * p ^ (4 * B) * p ^ B = p ^ (5 * B + 1) := by ring
    have h4 : 5 * B + 1 ≤ B ^ 3 := by
      have h9 : 9 ≤ B * B := by nlinarith [Nat.mul_le_mul h3 h3]
      have h9B : 9 * B ≤ B * B * B := Nat.mul_le_mul_right B h9
      have : B ^ 3 = B * B * B := by ring
      omega
    calc 2 * B ^ 4 * p ^ B ≤ p ^ (5 * B + 1) := by rw [← h3']; exact h1.trans h2
      _ ≤ p ^ (B ^ 3) := Nat.pow_le_pow_right (by omega) h4

theorem square_zero_algebra_error_three (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 2 ≤ B) :
    1 - (modelCount p B : ℝ) / ballSize p B ≤ 3 / (p : ℝ) ^ B := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpB : (2 : ℝ) ≤ (p : ℝ) ^ B := by
    calc (2 : ℝ) = (2 : ℕ) := by norm_num
      _ ≤ ((p ^ B : ℕ) : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
      _ = (p : ℝ) ^ B := by push_cast; ring
  have h := square_zero_algebra_error_sharp p (by omega : 1 ≤ B)
  have h1 : 1 / ((p : ℝ) ^ B - 1) ≤ 2 / (p : ℝ) ^ B := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have h2 : 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) ≤ 1 / (p : ℝ) ^ B := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := two_mul_pow_four_le (Fact.out : p.Prime).two_le hB
    have hR : (2 : ℝ) * (B : ℝ) ^ 4 * (p : ℝ) ^ B ≤ (p : ℝ) ^ (B ^ 3) := by exact_mod_cast this
    linarith
  calc _ ≤ _ := h
    _ ≤ 2 / (p : ℝ) ^ B + 1 / (p : ℝ) ^ B := add_le_add h1 h2
    _ = 3 / (p : ℝ) ^ B := by ring

end KoszulProbability
