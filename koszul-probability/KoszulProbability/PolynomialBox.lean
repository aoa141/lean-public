import KoszulProbability.BoxDensity

/-!
# Polynomial boxes

The growth condition `BoxGrowth` does not require exponential boxes. Boxes of polynomial size
`|S_e| = e^k` satisfy it at every radius for every `k`, and for `k ≥ 5` the error term
`(2B⁴ + B²)/B^k` tends to zero. So the box density theorem holds for polynomial boxes;
the boxes need only grow faster than `B⁴`, not faster than every polynomial.

The key inequality is `e^(B⁴) · B ≤ B^(B⁴)` for `1 ≤ e < B`, a two-term binomial estimate.
-/

open scoped BigOperators
open Finset Filter Topology

namespace KoszulProbability

/-- Two-term binomial lower bound `(a+1)^(N+1) ≥ a^(N+1) + (N+1) a^N`. -/
lemma pow_succ_ge_binomial (a N : ℕ) : a ^ (N + 1) + (N + 1) * a ^ N ≤ (a + 1) ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hexp : (a + 1) * (a ^ (N + 1) + (N + 1) * a ^ N) =
        a ^ (N + 2) + (N + 2) * a ^ (N + 1) + (N + 1) * a ^ N := by ring
    calc a ^ (N + 2) + (N + 2) * a ^ (N + 1)
        ≤ a ^ (N + 2) + (N + 2) * a ^ (N + 1) + (N + 1) * a ^ N := Nat.le_add_right _ _
      _ = (a + 1) * (a ^ (N + 1) + (N + 1) * a ^ N) := hexp.symm
      _ ≤ (a + 1) * (a + 1) ^ (N + 1) := Nat.mul_le_mul_left _ ih
      _ = (a + 1) ^ (N + 2) := by ring

/-- For `1 ≤ e < B`: `e^(B⁴) · B ≤ B^(B⁴)`. -/
lemma pow_mul_le_pow_of_lt {e B : ℕ} (heB : e < B) : e ^ (B ^ 4) * B ≤ B ^ (B ^ 4) := by
  obtain ⟨a, rfl⟩ : ∃ a, B = a + 1 := ⟨B - 1, by omega⟩
  have hea : e ≤ a := by omega
  obtain ⟨N, hN⟩ : ∃ N, (a + 1) ^ 4 = N + 1 :=
    ⟨(a + 1) ^ 4 - 1, by have := Nat.one_le_pow 4 (a + 1) (by omega); omega⟩
  rw [hN]
  have h1 : e ^ (N + 1) * (a + 1) ≤ a ^ (N + 1) * (a + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hea _)
  have hsq : a * a ≤ N + 1 := by
    rw [← hN]
    calc a * a ≤ (a + 1) ^ 2 := by nlinarith
      _ ≤ (a + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : a ^ (N + 2) ≤ (N + 1) * a ^ N := by
    calc a ^ (N + 2) = (a * a) * a ^ N := by ring
      _ ≤ (N + 1) * a ^ N := Nat.mul_le_mul_right _ hsq
  have h2 : a ^ (N + 1) * (a + 1) ≤ (a + 1) ^ (N + 1) := by
    calc a ^ (N + 1) * (a + 1) = a ^ (N + 2) + a ^ (N + 1) := by ring
      _ ≤ (N + 1) * a ^ N + a ^ (N + 1) := Nat.add_le_add_right h3 _
      _ = a ^ (N + 1) + (N + 1) * a ^ N := by ring
      _ ≤ (a + 1) ^ (N + 1) := pow_succ_ge_binomial a N
  exact h1.trans h2

/-- Polynomial boxes `q e = e^k` satisfy the growth condition at every radius. -/
theorem boxGrowth_polynomial (k : ℕ) (q : ℕ → ℕ) (hq : ∀ e, 1 ≤ e → q e = e ^ k)
    {B : ℕ} (hB : 1 ≤ B) : BoxGrowth q B := by
  refine ⟨fun e he _ => ?_, fun e he heB => ?_⟩
  · rw [hq e he]
    exact Nat.one_le_pow _ _ he
  · rw [hq e he, hq B hB]
    have h := pow_mul_le_pow_of_lt heB
    calc (e ^ k) ^ (B ^ 4) * B ^ k = (e ^ (B ^ 4) * B) ^ k := by ring
      _ ≤ (B ^ (B ^ 4)) ^ k := Nat.pow_le_pow_left h k
      _ = (B ^ k) ^ (B ^ 4) := by ring

section Family
variable (K : ℕ → Type*) [∀ e, Field (K e)] (S : ∀ e, Finset (K e))

/-- Polynomial boxes `|S_e| = e^k` in any family of fields: the finite bound
`(2B⁴ + B²)/B^k`. -/
theorem polynomial_box_error (k : ℕ) (hS : ∀ e, 1 ≤ e → (S e).card = e ^ k)
    {B : ℕ} (hB : 1 ≤ B) :
    1 - (boxCertificateCount K S B : ℝ) / (boxBall K S B).card ≤
      (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / (B : ℝ) ^ k := by
  have h := box_square_zero_error K S hB (boxGrowth_polynomial k _ hS hB)
  rw [hS B hB] at h
  push_cast at h
  rwa [boxCertificateCount_eq]

/-- The error term for polynomial boxes tends to zero as soon as `k ≥ 5`. -/
lemma polynomial_error_tendsto_zero {k : ℕ} (hk : 5 ≤ k) :
    Tendsto (fun B : ℕ => (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / (B : ℝ) ^ k) atTop (𝓝 0) := by
  have h3 : Tendsto (fun B : ℕ => (3 : ℝ) / (B : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
  · filter_upwards with B
    positivity
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hB0 : (0 : ℝ) < B := by linarith
    rw [div_le_div_iff₀ (by positivity) hB0]
    have h5 : (B : ℝ) ^ 5 ≤ (B : ℝ) ^ k := pow_le_pow_right₀ hB1 hk
    have h35 : (B : ℝ) ^ 3 ≤ (B : ℝ) ^ 5 := pow_le_pow_right₀ hB1 (by norm_num)
    nlinarith

/-- Polynomial boxes `|S_e| = e^k`, `k ≥ 5`, in any family of fields: Koszul certificates
have density one. -/
theorem polynomial_box_density {k : ℕ} (hk : 5 ≤ k) (hS : ∀ e, 1 ≤ e → (S e).card = e ^ k) :
    Tendsto (fun B => (boxCertificateCount K S B : ℝ) / (boxBall K S B).card) atTop (𝓝 1) := by
  apply box_koszul_certificate_density
  · filter_upwards [eventually_ge_atTop 1] with B hB
    exact boxGrowth_polynomial k _ hS hB
  · refine Tendsto.congr' ?_ (polynomial_error_tendsto_zero hk)
    filter_upwards [eventually_ge_atTop 1] with B hB
    simp [hS B hB]

end Family

/-- A fixed field with polynomial boxes, e.g. `S_e = {0, 1, …, e^5 - 1}` in `ℚ`. -/
theorem fixed_field_polynomial_box_density (K : Type*) [Field K] (S : ℕ → Finset K)
    {k : ℕ} (hk : 5 ≤ k) (hS : ∀ e, 1 ≤ e → (S e).card = e ^ k) :
    Tendsto (fun B => (boxCertificateCount (fun _ => K) S B : ℝ) /
      (boxBall (fun _ => K) S B).card) atTop (𝓝 1) :=
  polynomial_box_density (fun _ => K) S hk hS

end KoszulProbability
