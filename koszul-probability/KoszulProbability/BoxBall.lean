import KoszulProbability.Ball

/-!
# Growing balls of boxes in arbitrary fields

The finite-field ball weights the stratum `(n,e,m)` by `p^(e·m·n²) = (p^e)^(m·n²)`, the
number of `m × n²` matrices over `GF(p^e)`. Nothing in the concentration argument uses that
the coefficient set is a whole field: it only uses that the level-`e` coefficient box has
`q e` elements, that the box at the top level dominates, and Schwartz--Zippel on a box.

This file isolates that part. `BoxGrowth q B` is the explicit hypothesis under which every
non-top stratum weighs at most `1/q B` of the top stratum, so that the finite failure bound
`(2B⁴ + B²)/q B` of the paper holds verbatim.
-/

open scoped BigOperators
open Finset Filter Topology

namespace KoszulProbability

/-- Abstract concentration lemma. If one weight `w t` dominates each other weight by a factor
`Q`, and `good` covers all but a `D/Q` fraction of `w t`, then `good` covers all but an
`(N + D)/Q` fraction of the total, where `N` bounds the number of other weights. -/
theorem failure_bound_of_weights {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {t : ι} (ht : t ∈ s) (htpos : 0 < w t)
    {Q N D : ℝ} (hQ : 0 < Q) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hoff : ∀ a ∈ s.erase t, w a ≤ w t / Q) (hcard : ((s.erase t).card : ℝ) ≤ N)
    {good : ℝ} (hgood : w t * (1 - D / Q) ≤ good) :
    1 - good / (∑ a ∈ s, w a) ≤ (N + D) / Q := by
  have hsplit : ∑ a ∈ s, w a = w t + ∑ a ∈ s.erase t, w a := by
    rw [← sum_erase_add _ _ ht, add_comm]
  have hrest : ∑ a ∈ s.erase t, w a ≤ N / Q * w t := by
    calc ∑ a ∈ s.erase t, w a ≤ ∑ _a ∈ s.erase t, w t / Q := sum_le_sum hoff
      _ = ((s.erase t).card : ℝ) * (w t / Q) := by simp
      _ ≤ N * (w t / Q) := by gcongr
      _ = N / Q * w t := by ring
  have hrest0 : 0 ≤ ∑ a ∈ s.erase t, w a :=
    sum_nonneg fun a ha => hw a (mem_erase.mp ha).2
  have hWt : w t ≤ ∑ a ∈ s, w a := by rw [hsplit]; linarith
  have hW0 : 0 < ∑ a ∈ s, w a := lt_of_lt_of_le htpos hWt
  have hgood' : w t - D / Q * w t ≤ good := by
    have : w t * (1 - D / Q) = w t - D / Q * w t := by ring
    linarith
  have hnum : (∑ a ∈ s, w a) - good ≤ (N + D) / Q * w t := by
    rw [hsplit]
    have : (N + D) / Q * w t = N / Q * w t + D / Q * w t := by ring
    linarith
  have hcoef : 0 ≤ (N + D) / Q := div_nonneg (add_nonneg hN hD) hQ.le
  have hnum2 : (∑ a ∈ s, w a) - good ≤ (N + D) / Q * ∑ a ∈ s, w a :=
    hnum.trans (mul_le_mul_of_nonneg_left hWt hcoef)
  have hid : 1 - good / ∑ a ∈ s, w a = ((∑ a ∈ s, w a) - good) / ∑ a ∈ s, w a := by
    rw [sub_div, div_self (ne_of_gt hW0)]
  rw [hid]
  exact (div_le_iff₀ hW0).mpr hnum2

/-- Weight of the stratum `(n,e,m)` when the level-`e` box has `q e` elements:
the number of `m × n²` matrices with entries in that box. -/
noncomputable def boxWeight (q : ℕ → ℕ) (a : Stratum) : ℝ :=
  (q a.2.1 : ℝ) ^ (a.2.2 * (a.1 * a.1))

/-- Total number of points in the radius-`B` ball of boxes. -/
noncomputable def boxBallSize (q : ℕ → ℕ) (B : ℕ) : ℝ :=
  ∑ a ∈ indices B, boxWeight q a

/-- Growth condition on box sizes at radius `B`: boxes up to level `B` are nonempty, and
every lower-level box is small enough that the whole stratum `(B, e, B²)` weighs at most
`1/q B` of the top stratum. -/
def BoxGrowth (q : ℕ → ℕ) (B : ℕ) : Prop :=
  (∀ e, 1 ≤ e → e ≤ B → 1 ≤ q e) ∧
  ∀ e, 1 ≤ e → e < B → (q e) ^ (B ^ 4) * q B ≤ (q B) ^ (B ^ 4)

lemma boxWeight_nonneg (q : ℕ → ℕ) (a : Stratum) : 0 ≤ boxWeight q a :=
  pow_nonneg (Nat.cast_nonneg _) _

lemma boxWeight_top (q : ℕ → ℕ) (B : ℕ) : boxWeight q (topIndex B) = (q B : ℝ) ^ (B ^ 4) := by
  show (q B : ℝ) ^ (B * B * (B * B)) = _
  congr 1
  ring

lemma stratum_exponent_le {B : ℕ} {a : Stratum} (ha : a ∈ indices B) :
    a.2.2 * (a.1 * a.1) ≤ B ^ 4 := by
  obtain ⟨n, e, m⟩ := a
  obtain ⟨_, hnB, _, _, hmB, _⟩ := mem_indices.mp ha
  dsimp only at hnB hmB ⊢
  have hn2 : n * n ≤ B * B := Nat.mul_le_mul hnB hnB
  calc m * (n * n) ≤ B ^ 2 * (B * B) := Nat.mul_le_mul hmB hn2
    _ = B ^ 4 := by ring

/-- In the top level `e = B`, every stratum other than the top one loses a full factor `q B`. -/
lemma stratum_exponent_gap {B : ℕ} (hB : 1 ≤ B) {a : Stratum} (ha : a ∈ indices B)
    (hne : a ≠ topIndex B) (he : a.2.1 = B) : a.2.2 * (a.1 * a.1) + 1 ≤ B ^ 4 := by
  obtain ⟨n, e, m⟩ := a
  obtain ⟨_, hnB, _, _, hmB, hmn⟩ := mem_indices.mp ha
  dsimp only at hnB hmB hmn he ⊢
  have hn2 : n * n ≤ B * B := Nat.mul_le_mul hnB hnB
  rcases Nat.lt_or_ge m (B ^ 2) with hm | hm
  · have hm1 : m + 1 ≤ B * B := by rw [pow_two] at hm; omega
    have h1 : (m + 1) * (B * B) ≤ (B * B) * (B * B) := Nat.mul_le_mul_right _ hm1
    have h2 : m * (n * n) ≤ m * (B * B) := Nat.mul_le_mul_left _ hn2
    have h3 : 1 ≤ B * B := Nat.mul_le_mul hB hB
    have h4 : (B * B) * (B * B) = B ^ 4 := by ring
    nlinarith
  · have hm' : m = B ^ 2 := le_antisymm hmB hm
    have hsq : B ^ 2 ≤ n ^ 2 := hm' ▸ hmn
    have hBn : B ≤ n := le_of_not_gt fun h => by nlinarith [Nat.mul_le_mul h h]
    have hnB' : n = B := le_antisymm hnB hBn
    exact absurd (by simp [topIndex, hnB', hm', he, pow_two]) hne

lemma boxWeight_off_top {q : ℕ → ℕ} {B : ℕ} (hB : 1 ≤ B) (hg : BoxGrowth q B) {a : Stratum}
    (ha : a ∈ (indices B).erase (topIndex B)) :
    boxWeight q a ≤ (q B : ℝ) ^ (B ^ 4) / q B := by
  obtain ⟨hne, ha⟩ := mem_erase.mp ha
  have hqB : (1 : ℝ) ≤ q B := by exact_mod_cast hg.1 B hB le_rfl
  have hqB0 : (0 : ℝ) < q B := by linarith
  rw [le_div_iff₀ hqB0]
  have hmem := mem_indices.mp ha
  have he1 : 1 ≤ a.2.1 := hmem.2.2.1
  have heB : a.2.1 ≤ B := hmem.2.2.2.1
  have hqe : (1 : ℝ) ≤ q a.2.1 := by exact_mod_cast hg.1 _ he1 heB
  unfold boxWeight
  rcases eq_or_lt_of_le heB with he | he
  · have hgap := stratum_exponent_gap hB ha hne he
    rw [he]
    calc (q B : ℝ) ^ (a.2.2 * (a.1 * a.1)) * q B
        = (q B : ℝ) ^ (a.2.2 * (a.1 * a.1) + 1) := by rw [pow_succ]
      _ ≤ (q B : ℝ) ^ (B ^ 4) := pow_le_pow_right₀ hqB hgap
  · have hle := stratum_exponent_le ha
    have hgrow : (q a.2.1 : ℝ) ^ (B ^ 4) * q B ≤ (q B : ℝ) ^ (B ^ 4) := by
      exact_mod_cast hg.2 _ he1 he
    calc (q a.2.1 : ℝ) ^ (a.2.2 * (a.1 * a.1)) * q B
        ≤ (q a.2.1 : ℝ) ^ (B ^ 4) * q B :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hqe hle) hqB0.le
      _ ≤ _ := hgrow

lemma boxWeight_top_le_ball (q : ℕ → ℕ) {B : ℕ} (hB : 1 ≤ B) :
    (q B : ℝ) ^ (B ^ 4) ≤ boxBallSize q B := by
  have := Finset.single_le_sum (fun a (_ : a ∈ indices B) => boxWeight_nonneg q a) (top_mem hB)
  rwa [boxWeight_top] at this

/-- The finite failure bound of the paper, for boxes satisfying the growth condition. -/
theorem box_failure_bound (q : ℕ → ℕ) {B : ℕ} (hB : 1 ≤ B) (hg : BoxGrowth q B) {good : ℝ}
    (hgood : (q B : ℝ) ^ (B ^ 4) * (1 - (B : ℝ) ^ 2 / q B) ≤ good) :
    1 - good / boxBallSize q B ≤ (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / q B := by
  have hqB : (1 : ℝ) ≤ q B := by exact_mod_cast hg.1 B hB le_rfl
  have hqB0 : (0 : ℝ) < q B := by linarith
  have hcard : (((indices B).erase (topIndex B)).card : ℝ) ≤ 2 * (B : ℝ) ^ 4 := by
    exact_mod_cast card_erase_le.trans (card_indices_le hB)
  have h := failure_bound_of_weights (indices B) (boxWeight q)
    (Q := (q B : ℝ)) (N := 2 * (B : ℝ) ^ 4) (D := (B : ℝ) ^ 2) (good := good)
    (fun a _ => boxWeight_nonneg q a) (top_mem hB)
    (by rw [boxWeight_top]; exact pow_pos hqB0 _) hqB0
    (by positivity) (by positivity)
    (fun a ha => by rw [boxWeight_top]; exact boxWeight_off_top hB hg ha) hcard
    (by rw [boxWeight_top]; exact hgood)
  exact h

/-- Density one along growing balls of boxes, whenever the growth condition holds eventually
and the finite bound tends to zero. -/
theorem box_density_of_top_certificates (q : ℕ → ℕ) (good : ℕ → ℝ)
    (hg : ∀ᶠ B in atTop, BoxGrowth q B)
    (hlo : ∀ B, 1 ≤ B → BoxGrowth q B →
      (q B : ℝ) ^ (B ^ 4) * (1 - (B : ℝ) ^ 2 / q B) ≤ good B)
    (hhi : ∀ B, 1 ≤ B → good B ≤ boxBallSize q B)
    (herr : Tendsto (fun B : ℕ => (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / q B) atTop (𝓝 0)) :
    Tendsto (fun B => good B / boxBallSize q B) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun B : ℕ => 1 - (2 * (B : ℝ) ^ 4 + (B : ℝ) ^ 2) / q B)
    (h := fun _ => 1)
  · simpa using tendsto_const_nhds.sub herr
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1, hg] with B hB hgB
    have := box_failure_bound q hB hgB (hlo B hB hgB)
    linarith
  · filter_upwards [eventually_ge_atTop 1, hg] with B hB hgB
    have hqB : (1 : ℝ) ≤ q B := by exact_mod_cast hgB.1 B hB le_rfl
    have hw := boxWeight_top_le_ball q hB
    have hw0 : 0 < boxBallSize q B := lt_of_lt_of_le (pow_pos (by linarith) _) hw
    exact (div_le_one hw0).mpr (hhi B hB)

/-- Geometric boxes `q e = c^e` satisfy the growth condition at every radius. -/
theorem boxGrowth_geometric {c : ℕ} (hc : 2 ≤ c) (q : ℕ → ℕ) (hq : ∀ e, 1 ≤ e → q e = c ^ e)
    {B : ℕ} (hB : 1 ≤ B) : BoxGrowth q B := by
  refine ⟨fun e he _ => ?_, fun e he heB => ?_⟩
  · rw [hq e he]
    exact Nat.one_le_pow _ _ (by omega)
  · rw [hq e he, hq B hB, ← pow_mul, ← pow_mul, ← pow_add]
    apply Nat.pow_le_pow_right (by omega)
    have h2 : (e + 1) * B ^ 4 ≤ B * B ^ 4 := Nat.mul_le_mul_right _ heB
    have h3 : B ≤ B ^ 4 := by
      calc B = B * 1 := (mul_one B).symm
        _ ≤ B * B ^ 3 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hB)
        _ = B ^ 4 := by ring
    nlinarith

/-- The finite-field weights of `Ball.lean` are the geometric boxes `q e = p^e`. -/
lemma boxBallSize_geometric (p : ℕ) (B : ℕ) :
    boxBallSize (fun e => p ^ e) B = ballSize (p : ℝ) B := by
  unfold boxBallSize ballSize
  apply Finset.sum_congr rfl
  intro a _
  unfold boxWeight weight exponent
  push_cast
  rw [← pow_mul]
  congr 1
  ring

end KoszulProbability
