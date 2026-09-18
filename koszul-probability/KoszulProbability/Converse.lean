import KoszulProbability.SharpBound

/-!
# The converse in the top stratum, and a two-sided bound

`Presentation.squareZeroEquiv` shows that an invertible relation matrix gives a
generator-preserving square-zero model. Here we prove the converse: if the presented quotient
has a generator-preserving square-zero model, the relation matrix is invertible.

The proof is a small explicit representation. If `det C = 0` there is a nonzero vector `φ`
on quadratic coordinates with `C *ᵥ φ = 0`. Sending the generator `x_i` to the matrix
`E_{s,i} + ∑_k φ(k,i) E_{k,t}` (indices `Fin n ⊕ Bool`, source `s = inr false`, target
`t = inr true`) gives `x_i x_j ↦ φ(i,j) E_{s,t}`, so every listed relation maps to
`(C *ᵥ φ)_a E_{s,t} = 0` and the representation descends to the quotient. There some product
`x̄_i x̄_j` is nonzero, which is impossible in a square-zero model.

Consequently the square-zero count in the top stratum is *exactly* the number of invertible
matrices, and the exact `GL` count gives a matching lower bound on the failure probability:

  `(1 - 2B⁴/p^(B³)) / p^B ≤ 1 - M/W ≤ 1/(p^B - 1) + 2B⁴/p^(B³)`,

so `p^B (1 - M/W) → 1`.
-/

open scoped BigOperators Matrix
open Finset Filter Topology

namespace KoszulProbability
namespace Presentation

variable {K : Type*} [Field K] {n : ℕ}

/-- Index type of the representation: middle `inl i`, source `inr false`, target `inr true`. -/
abbrev RepIdx (n : ℕ) := Fin n ⊕ Bool

/-- The matrix representing the generator `x_i`: `E_{s,i} + ∑_k φ(k,i) E_{k,t}`. -/
noncomputable def repGen (φ : Coeff K n) (i : Fin n) : Matrix (RepIdx n) (RepIdx n) K :=
  Matrix.single (Sum.inr false) (Sum.inl i) 1 +
    ∑ k : Fin n, Matrix.single (Sum.inl k) (Sum.inr true) (φ (finProdFinEquiv (k, i)))

lemma repGen_mul (φ : Coeff K n) (i j : Fin n) :
    repGen φ i * repGen φ j =
      Matrix.single (Sum.inr false) (Sum.inr true) (φ (finProdFinEquiv (i, j))) := by
  classical
  have h1 : Matrix.single (Sum.inr false : RepIdx n) (Sum.inl i : RepIdx n) (1 : K) *
      Matrix.single (Sum.inr false : RepIdx n) (Sum.inl j : RepIdx n) (1 : K) = 0 := by simp
  have h2 : ∀ l : Fin n, Matrix.single (Sum.inr false : RepIdx n) (Sum.inl i) (1 : K) *
      Matrix.single (Sum.inl l) (Sum.inr true) (φ (finProdFinEquiv (l, j))) =
      if l = i then Matrix.single (Sum.inr false) (Sum.inr true) (φ (finProdFinEquiv (i, j)))
      else 0 := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg hl]
      simp [Ne.symm hl]
  have h3 : ∀ k : Fin n, Matrix.single (Sum.inl k : RepIdx n) (Sum.inr true)
      (φ (finProdFinEquiv (k, i))) * Matrix.single (Sum.inr false) (Sum.inl j) (1 : K) = 0 :=
    fun k => by simp
  have h4 : ∀ k l : Fin n, Matrix.single (Sum.inl k : RepIdx n) (Sum.inr true : RepIdx n)
      (φ (finProdFinEquiv (k, i))) *
      Matrix.single (Sum.inl l : RepIdx n) (Sum.inr true : RepIdx n)
        (φ (finProdFinEquiv (l, j))) = 0 :=
    fun k l => Matrix.single_mul_single_of_ne _ _ _ _ Sum.inr_ne_inl _
  simp only [repGen, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul, h1, h2, h3, h4,
    Finset.sum_const_zero, add_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The representation of the free algebra determined by `φ`. -/
noncomputable def rep (φ : Coeff K n) : Free K n →ₐ[K] Matrix (RepIdx n) (RepIdx n) K :=
  FreeAlgebra.lift K (repGen φ)

@[simp] lemma rep_ι (φ : Coeff K n) (i : Fin n) : rep φ (FreeAlgebra.ι K i) = repGen φ i := by
  simp [rep]

/-- A quadratic element with coefficient vector `v` maps to `(v ⬝ᵥ φ) E_{s,t}`. -/
lemma rep_quadratic (φ v : Coeff K n) :
    rep φ (quadraticMap K n v) =
      Matrix.single (Sum.inr false) (Sum.inr true) (v ⬝ᵥ φ) := by
  classical
  simp only [quadraticMap, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, map_sum, map_smul, map_mul, rep_ι, repGen_mul, Prod.mk.eta,
    Equiv.apply_symm_apply, Matrix.smul_single, smul_eq_mul, dotProduct]
  exact (map_sum (Matrix.singleAddMonoidHom (Sum.inr false) (Sum.inr true) :
    K →+ Matrix (RepIdx n) (RepIdx n) K) (fun x => v x * φ x) univ).symm

lemma rep_row_zero {m : ℕ} (C : Matrix (Fin m) (Fin (n * n)) K) (φ : Coeff K n)
    (hφ : C *ᵥ φ = 0) (i : Fin m) : rep φ (quadraticMap K n (C.row i)) = 0 := by
  rw [rep_quadratic]
  have : C.row i ⬝ᵥ φ = 0 := congrFun hφ i
  rw [this, Matrix.single_zero]

/-- The representation descends to the presented quotient when `C *ᵥ φ = 0`. -/
noncomputable def repQuot {m : ℕ} (C : Matrix (Fin m) (Fin (n * n)) K) (φ : Coeff K n)
    (hφ : C *ᵥ φ = 0) : Quotient C →ₐ[K] Matrix (RepIdx n) (RepIdx n) K :=
  RingQuot.liftAlgHom K ⟨rep φ, by
    rintro a b ⟨i, rfl, rfl⟩
    simp [rep_row_zero C φ hφ]⟩

lemma repQuot_mk {m : ℕ} (C : Matrix (Fin m) (Fin (n * n)) K) (φ : Coeff K n)
    (hφ : C *ᵥ φ = 0) (a : Free K n) : repQuot C φ hφ (mk C a) = rep φ a := by
  simp [repQuot, mk]

/-- **Converse.** A generator-preserving square-zero model forces the relation matrix to be
invertible. -/
theorem det_ne_zero_of_model (C : Matrix (Fin (n * n)) (Fin (n * n)) K)
    (e : Quotient C ≃ₐ[K] SquareZero.Algebra K n)
    (hgen : ∀ i : Fin n, e (mk C (FreeAlgebra.ι K i)) =
      TrivSqZeroExt.inr ((Pi.basisFun K (Fin n)) i)) :
    C.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨φ, hφ0, hφ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨t, ht⟩ : ∃ t, φ t ≠ 0 := by
    by_contra! h
    exact hφ0 (funext h)
  have hzero : mk C (FreeAlgebra.ι K (finProdFinEquiv.symm t).1) *
      mk C (FreeAlgebra.ι K (finProdFinEquiv.symm t).2) = 0 := by
    apply e.injective
    rw [map_mul, hgen, hgen, map_zero, TrivSqZeroExt.inr_mul_inr]
  have h := congrArg (repQuot C φ hφ) hzero
  rw [map_mul, repQuot_mk, repQuot_mk, map_zero, rep_ι, rep_ι, repGen_mul, Prod.mk.eta,
    Equiv.apply_symm_apply] at h
  have h' := congrFun (congrFun h (Sum.inr false)) (Sum.inr true)
  rw [Matrix.single_apply_same, Matrix.zero_apply] at h'
  exact ht h'

end Presentation

/-- In the top stratum, square-zero models are exactly the invertible matrices. -/
theorem model_top_eq_certified (p B : ℕ) [Fact p.Prime] :
    modelCountInStratum p (topIndex B) = certifiedCount p B := by
  classical
  apply le_antisymm
  · unfold certifiedCount regularCount modelCountInStratum
    simp only [topIndex]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨e, hgen⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Presentation.det_ne_zero_of_model _ e hgen⟩
  · exact regular_le_model_top p B

lemma model_stratum_le_weight (p : ℕ) [Fact p.Prime] {B : ℕ} {a : Stratum}
    (ha : a ∈ indices B) : (modelCountInStratum p a : ℝ) ≤ weight p a := by
  classical
  have hc : modelCountInStratum p a ≤ Fintype.card (Coefficients p a) := Finset.card_filter_le _ _
  rw [coefficients_card p (mem_indices.mp ha).2.2.1] at hc
  unfold weight
  exact_mod_cast hc

/-- Outside the top stratum the model count is at most the off-top mass. -/
lemma modelCount_le_certified_add (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (modelCount p B : ℝ) ≤ certifiedCount p B + (ballSize p B - (p : ℝ) ^ (B ^ 5)) := by
  have heq : ballSize p B - (p : ℝ) ^ (B ^ 5) =
      ∑ a ∈ (indices B).erase (topIndex B), weight p a := by
    rw [ballSize, ← sum_erase_add _ _ (top_mem hB)]
    simp [weight, exponent_top]
  rw [heq]
  unfold modelCount
  rw [← sum_erase_add _ _ (top_mem hB), model_top_eq_certified]
  push_cast
  rw [add_comm]
  gcongr with a ha
  exact model_stratum_le_weight p (mem_erase.mp ha).2

/-- Singular top-stratum matrices are at least a `1/p^B` fraction of the top stratum. -/
lemma singular_top_lower (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (p : ℝ) ^ (B ^ 5) / (p : ℝ) ^ B ≤ singularCount (GaloisField p B) (B * B) := by
  have hs := singular_fraction_ge (K := GaloisField p B) (d := B * B) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [field_card p hB] at hs
  push_cast at hs
  rw [← pow_mul, show B * (B * B * (B * B)) = B ^ 5 by ring] at hs
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpB : (0 : ℝ) < (p : ℝ) ^ B := pow_pos hp _
  have hT : (0 : ℝ) < (p : ℝ) ^ (B ^ 5) := pow_pos hp _
  rw [le_div_iff₀ hT] at hs
  rw [div_le_iff₀ hpB]
  calc (p : ℝ) ^ (B ^ 5) = (1 / (p : ℝ) ^ B * (p : ℝ) ^ (B ^ 5)) * (p : ℝ) ^ B := by
        field_simp
    _ ≤ _ := by gcongr

/-- **Lower bound.** The square-zero failure probability is at least
`(1 - 2B⁴/p^(B³)) / p^B`. -/
theorem square_zero_algebra_error_lower (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 1 ≤ B) :
    (1 - 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) / (p : ℝ) ^ B ≤
      1 - (modelCount p B : ℝ) / ballSize p B := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hsplit : (certifiedCount p B : ℝ) + singularCount (GaloisField p B) (B * B) =
      (p : ℝ) ^ (B ^ 5) := by
    have hc := regular_add_singular (GaloisField p B) (B * B)
    rw [field_card p hB, top_card] at hc
    unfold certifiedCount
    exact_mod_cast hc
  have hsing := singular_top_lower p hB
  have hM := modelCount_le_certified_add p hB
  have hoff := off_top_bound_cube hp.le hB
  have hTW : (p : ℝ) ^ (B ^ 5) ≤ ballSize p B := top_weight_le_ball hp0.le hB
  set T : ℝ := (p : ℝ) ^ (B ^ 5) with hT
  set W : ℝ := ballSize p B with hW
  set δ : ℝ := 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) with hδ
  have hT0 : 0 < T := pow_pos hp0 _
  have hW0 : 0 < W := lt_of_lt_of_le hT0 hTW
  have hδ0 : 0 ≤ δ := by positivity
  have hpB : (0 : ℝ) < (p : ℝ) ^ B := pow_pos hp0 _
  -- W - M ≥ T - G = S ≥ T / p^B
  have hWM : T / (p : ℝ) ^ B ≤ W - modelCount p B := by linarith
  -- T ≥ (1 - δ) W
  have hTW' : (1 - δ) * W ≤ T := by nlinarith
  have hid : 1 - (modelCount p B : ℝ) / W = (W - modelCount p B) / W := by
    rw [sub_div, div_self hW0.ne']
  rw [hid, div_le_div_iff₀ hpB hW0]
  have : T ≤ (W - modelCount p B) * (p : ℝ) ^ B := by
    rw [div_le_iff₀ hpB] at hWM
    exact hWM
  nlinarith

/-- For `B ≥ 2` the failure probability of the square-zero event lies between
`1/(2p^B)` and `3/p^B`. -/
theorem square_zero_algebra_error_two_sided (p : ℕ) [Fact p.Prime] {B : ℕ} (hB : 2 ≤ B) :
    1 / (2 * (p : ℝ) ^ B) ≤ 1 - (modelCount p B : ℝ) / ballSize p B ∧
      1 - (modelCount p B : ℝ) / ballSize p B ≤ 3 / (p : ℝ) ^ B := by
  refine ⟨?_, square_zero_algebra_error_three p hB⟩
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpB : (2 : ℝ) ≤ (p : ℝ) ^ B := by
    calc (2 : ℝ) = (2 : ℕ) := by norm_num
      _ ≤ ((p ^ B : ℕ) : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
      _ = (p : ℝ) ^ B := by push_cast; ring
  have hlow := square_zero_algebra_error_lower p (by omega : 1 ≤ B)
  have hδ : 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) ≤ 1 / 2 := by
    have := two_mul_pow_four_le (Fact.out : p.Prime).two_le hB
    have hR : (2 : ℝ) * (B : ℝ) ^ 4 * (p : ℝ) ^ B ≤ (p : ℝ) ^ (B ^ 3) := by exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hp0 (B ^ 3)]
  have hpBpos : (0 : ℝ) < (p : ℝ) ^ B := by linarith
  calc 1 / (2 * (p : ℝ) ^ B) = (1 / 2) / (p : ℝ) ^ B := by field_simp
    _ ≤ (1 - 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) / (p : ℝ) ^ B := by
      gcongr
      linarith
    _ ≤ _ := hlow

/-- **Asymptotics.** The square-zero failure probability is asymptotic to `p^{-B}`. -/
theorem square_zero_failure_asymptotic (p : ℕ) [Fact p.Prime] :
    Tendsto (fun B : ℕ => (p : ℝ) ^ B * (1 - (modelCount p B : ℝ) / ballSize p B))
      atTop (𝓝 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have h4 : Tendsto (fun B : ℕ => 2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B)) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_const_div_const_pow_of_one_lt 4 hp).const_mul 2
  have h0 : Tendsto (fun B : ℕ => (2 : ℝ) / (p : ℝ) ^ B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hp)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun B : ℕ => 1 - 2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B))
    (h := fun B : ℕ => 1 + (2 / (p : ℝ) ^ B + 2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B)))
  · simpa using tendsto_const_nhds.sub h4
  · simpa using tendsto_const_nhds.add (h0.add h4)
  · filter_upwards [eventually_ge_atTop 2] with B hB
    have hlow := square_zero_algebra_error_lower p (by omega : 1 ≤ B)
    have hpB : (0 : ℝ) < (p : ℝ) ^ B := pow_pos hp0 _
    have hcube : (p : ℝ) ^ B ≤ (p : ℝ) ^ (B ^ 3) :=
      pow_le_pow_right₀ hp.le (Nat.le_self_pow (by norm_num) B)
    have hδ : 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) ≤ 2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B) := by
      rw [mul_div_assoc]
      gcongr
    rw [div_le_iff₀ hpB] at hlow
    linarith
  · filter_upwards [eventually_ge_atTop 2] with B hB
    have hup := square_zero_algebra_error_sharp p (by omega : 1 ≤ B)
    have hpB : (2 : ℝ) ≤ (p : ℝ) ^ B := by
      calc (2 : ℝ) = (2 : ℕ) := by norm_num
        _ ≤ ((p ^ B : ℕ) : ℝ) := by
          exact_mod_cast (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
        _ = (p : ℝ) ^ B := by push_cast; ring
    have hpB0 : (0 : ℝ) < (p : ℝ) ^ B := by linarith
    -- p^B / (p^B - 1) ≤ 1 + 2/p^B
    have h1 : (p : ℝ) ^ B * (1 / ((p : ℝ) ^ B - 1)) ≤ 1 + 2 / (p : ℝ) ^ B := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      have : (1 + 2 / (p : ℝ) ^ B) * ((p : ℝ) ^ B - 1) =
          (p : ℝ) ^ B - 1 + 2 - 2 / (p : ℝ) ^ B := by
        field_simp
        ring
      rw [this]
      have : 2 / (p : ℝ) ^ B ≤ 1 := by
        rw [div_le_one hpB0]; exact hpB
      linarith
    -- p^B · 2B⁴/p^(B³) ≤ 2B⁴/p^B  since p^(B³) ≥ p^(2B)
    have h2 : (p : ℝ) ^ B * (2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) ≤
        2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B) := by
      have h2B : B + B ≤ B ^ 3 := by
        have h4 : 4 ≤ B * B := by nlinarith
        calc B + B = 2 * B := by ring
          _ ≤ (B * B) * B := by nlinarith
          _ = B ^ 3 := by ring
      have hcube : (p : ℝ) ^ B * (p : ℝ) ^ B ≤ (p : ℝ) ^ (B ^ 3) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hp.le h2B
      rw [mul_div_assoc, ← mul_assoc, mul_comm ((p : ℝ) ^ B) 2, mul_assoc]
      gcongr
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hpB0]
      calc (p : ℝ) ^ B * (B : ℝ) ^ 4 * (p : ℝ) ^ B = (B : ℝ) ^ 4 * ((p : ℝ) ^ B * (p : ℝ) ^ B) := by ring
        _ ≤ (B : ℝ) ^ 4 * (p : ℝ) ^ (B ^ 3) := mul_le_mul_of_nonneg_left hcube (by positivity)
    have hfail : 0 ≤ 1 - (modelCount p B : ℝ) / ballSize p B := by
      have := square_zero_algebra_error_lower p (by omega : 1 ≤ B)
      have hδ : 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3) ≤ 1 / 2 := by
        have := two_mul_pow_four_le (Fact.out : p.Prime).two_le hB
        have hR : (2 : ℝ) * (B : ℝ) ^ 4 * (p : ℝ) ^ B ≤ (p : ℝ) ^ (B ^ 3) := by exact_mod_cast this
        rw [div_le_iff₀ (by positivity)]
        nlinarith [pow_pos hp0 (B ^ 3)]
      have : 0 ≤ (1 - 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) / (p : ℝ) ^ B := by
        apply div_nonneg _ hpB0.le
        linarith
      linarith
    calc (p : ℝ) ^ B * (1 - (modelCount p B : ℝ) / ballSize p B)
        ≤ (p : ℝ) ^ B * (1 / ((p : ℝ) ^ B - 1) + 2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) :=
          mul_le_mul_of_nonneg_left hup hpB0.le
      _ = (p : ℝ) ^ B * (1 / ((p : ℝ) ^ B - 1)) +
          (p : ℝ) ^ B * (2 * (B : ℝ) ^ 4 / (p : ℝ) ^ (B ^ 3)) := by ring
      _ ≤ 1 + 2 / (p : ℝ) ^ B + 2 * ((B : ℝ) ^ 4 / (p : ℝ) ^ B) := by linarith
      _ = _ := by ring

end KoszulProbability
