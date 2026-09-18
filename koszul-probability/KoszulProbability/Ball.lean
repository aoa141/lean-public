import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators
open Finset Filter Topology
namespace KoszulProbability

/-- `(n,e,m)` labels n generators, the field of order p^e, and m ordered relations. -/
abbrev Stratum := ℕ × ℕ × ℕ

def indices (B : ℕ) : Finset Stratum :=
  ((Icc 1 B) ×ˢ ((Icc 1 B) ×ˢ (Icc 0 (B^2)))).filter fun a => a.2.2 ≤ a.1^2

def topIndex (B : ℕ) : Stratum := (B, B, B*B)
def exponent (a : Stratum) : ℕ := a.2.1 * a.2.2 * a.1^2
noncomputable def weight (p : ℝ) (a : Stratum) : ℝ := p ^ exponent a
noncomputable def ballSize (p : ℝ) (B : ℕ) : ℝ := ∑ a ∈ indices B, weight p a

lemma mem_indices {a : Stratum} {B : ℕ} : a ∈ indices B ↔
    1 ≤ a.1 ∧ a.1 ≤ B ∧ 1 ≤ a.2.1 ∧ a.2.1 ≤ B ∧ a.2.2 ≤ B^2 ∧ a.2.2 ≤ a.1^2 := by
  simp [indices, and_assoc]

lemma top_mem {B : ℕ} (hB : 1 ≤ B) : topIndex B ∈ indices B := by
  simp [mem_indices, topIndex, hB, pow_two]

lemma exponent_top (B : ℕ) : exponent (topIndex B) = B^5 := by
  simp [exponent, topIndex]
  ring

lemma card_indices_le {B : ℕ} (hB : 1 ≤ B) : (indices B).card ≤ 2 * B^4 := by
  calc
    _ ≤ ((Icc 1 B) ×ˢ ((Icc 1 B) ×ˢ (Icc 0 (B^2)))).card := card_filter_le _ _
    _ = B * (B * (B^2+1)) := by simp
    _ ≤ 2 * B^4 := by nlinarith [sq_nonneg (B-1 : ℤ)]

/-- Every stratum except the unique largest one loses at least B coefficient bits in base p. -/
lemma exponent_gap {B : ℕ} (hB : 1 ≤ B) {a : Stratum}
    (ha : a ∈ indices B) (hne : a ≠ topIndex B) : exponent a + B ≤ B^5 := by
  rcases a with ⟨n,e,m⟩
  obtain ⟨hn, hnB, he, heB, hmB, hmn⟩ := mem_indices.mp ha
  dsimp at hn hnB he heB hmB hmn
  have hn2 : n^2 ≤ B^2 := Nat.pow_le_pow_left hnB 2
  have hB2 : B ≤ B^2 := by nlinarith
  have hB3 : B ≤ B^3 := by nlinarith
  have hB4 : B ≤ B^4 := by nlinarith [sq_nonneg (B^2-B : ℤ)]
  dsimp [exponent]
  by_cases heq : e = B
  · subst e
    by_cases hmeq : m = B^2
    · subst m
      have hnlt : n < B := by
        by_contra! h
        have : n = B := by omega
        subst n
        exact hne (by simp [topIndex, pow_two])
      have hn2gap : n^2 + 1 ≤ B^2 := by nlinarith
      have hh := Nat.mul_le_mul_left (B * B^2) hn2gap
      nlinarith
    · have hm : m + 1 ≤ B^2 := by omega
      have hh := Nat.mul_le_mul_left (B * B^2) hm
      have hprod := Nat.mul_le_mul_left (B*m) hn2
      nlinarith
  · have he' : e + 1 ≤ B := by omega
    have hh := Nat.mul_le_mul_right (B^2 * B^2) he'
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left e hmB) hn2
    nlinarith

lemma weight_nonneg {p : ℝ} (hp : 0 ≤ p) (a : Stratum) : 0 ≤ weight p a :=
  pow_nonneg hp _

lemma top_weight_le_ball {p : ℝ} (hp : 0 ≤ p) {B : ℕ} (hB : 1 ≤ B) :
    p^(B^5) ≤ ballSize p B := by
  have := Finset.single_le_sum (fun a (_ : a ∈ indices B) => weight_nonneg hp a) (top_mem hB)
  simpa [ballSize, weight, exponent_top] using this

lemma off_top_weight_le {p : ℝ} (hp : 1 ≤ p) {B : ℕ} (hB : 1 ≤ B)
    {a : Stratum} (ha : a ∈ (indices B).erase (topIndex B)) :
    weight p a ≤ p^(B^5) / p^B := by
  have hgap := exponent_gap hB (mem_erase.mp ha).2 (mem_erase.mp ha).1
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  apply (le_div_iff₀ (pow_pos hp0 B)).mpr
  simpa [weight, ← pow_add] using (pow_le_pow_right₀ hp hgap)

/-- The mass outside the top stratum, relative to that stratum, is exponentially small. -/
theorem off_top_bound {p : ℝ} (hp : 1 ≤ p) {B : ℕ} (hB : 1 ≤ B) :
    ballSize p B - p^(B^5) ≤ (2*(B : ℝ)^4) * (p^(B^5) / p^B) := by
  have heq : ballSize p B - p^(B^5) = ∑ a ∈ (indices B).erase (topIndex B), weight p a := by
    rw [ballSize, ← sum_erase_add _ _ (top_mem hB)]
    simp [weight, exponent_top]
  rw [heq]
  calc
    _ ≤ ∑ _a ∈ (indices B).erase (topIndex B), p^(B^5) / p^B :=
      sum_le_sum fun _ ha => off_top_weight_le hp hB ha
    _ = ((indices B).erase (topIndex B)).card * (p^(B^5) / p^B) := by simp
    _ ≤ (2*(B : ℝ)^4) * (p^(B^5) / p^B) := by
      gcongr
      exact_mod_cast (card_erase_le.trans (card_indices_le hB))

/-- A transfer lemma for any success event containing the nonsingular top-stratum matrices. -/
theorem ball_failure_bound {p : ℝ} (hp : 1 < p) {B : ℕ} (hB : 1 ≤ B)
    {good : ℝ} (hgood : p^(B^5) * (1 - (B : ℝ)^2 / p^B) ≤ good) :
    1 - good / ballSize p B ≤ (2*(B : ℝ)^4 + (B : ℝ)^2) / p^B := by
  have hp0 : 0 < p := by linarith
  have ht : 0 < p^(B^5) := pow_pos hp0 _
  have hw := top_weight_le_ball (le_of_lt hp0) hB
  have hw0 : 0 < ballSize p B := lt_of_lt_of_le ht hw
  have ho := off_top_bound (le_of_lt hp) hB
  have hq : 0 < p^B := pow_pos hp0 _
  have herr : 0 ≤ (2*(B : ℝ)^4 + (B : ℝ)^2) / p^B := by positivity
  have hnum : ballSize p B - good ≤
      p^(B^5) * ((2*(B : ℝ)^4 + (B : ℝ)^2) / p^B) := by
    simp only [div_eq_mul_inv] at hgood ho ⊢
    nlinarith
  have hnum2 := hnum.trans (mul_le_mul_of_nonneg_right hw herr)
  have hid : 1 - good / ballSize p B = (ballSize p B - good) / ballSize p B := by
    rw [sub_div, div_self (ne_of_gt hw0)]
  rw [hid]
  exact (div_le_iff₀ hw0).mpr (by nlinarith [hnum2])

lemma error_tends_to_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (fun B : ℕ => (2*(B : ℝ)^4 + (B : ℝ)^2) / p^B) atTop (𝓝 0) := by
  have h4 := (tendsto_pow_const_div_const_pow_of_one_lt 4 hp).const_mul 2
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 hp
  simpa [add_div, mul_div_assoc] using h4.add h2

/-- The growing-ball density theorem, for every success predicate with the stated finite bound. -/
theorem density_of_top_certificates {p : ℝ} (hp : 1 < p) (good : ℕ → ℝ)
    (hlo : ∀ B : ℕ, 1 ≤ B → p^(B^5) * (1 - (B : ℝ)^2 / p^B) ≤ good B)
    (hhi : ∀ B, 1 ≤ B → good B ≤ ballSize p B) :
    Tendsto (fun B => good B / ballSize p B) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun B : ℕ => 1 - (2*(B : ℝ)^4 + (B : ℝ)^2) / p^B)
    (h := fun _ => 1)
  · simpa using tendsto_const_nhds.sub (error_tends_to_zero hp)
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have := ball_failure_bound hp hB (hlo B hB)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have hw := top_weight_le_ball (show 0 ≤ p by linarith) hB
    have hw0 : 0 < ballSize p B := lt_of_lt_of_le (pow_pos (by linarith) _) hw
    exact (div_le_one hw0).mpr (hhi B hB)

end KoszulProbability
