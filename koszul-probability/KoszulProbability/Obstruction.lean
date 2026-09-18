import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace KoszulProbability.Obstruction

/-- Columns xr, yr, xs, ys, rx, ry, sx, sy for r=xx+yy, s=xy.
Rows xxx,xxy,xyx,xyy,yxx,yxy,yyx,yyy. -/
def cubicWitness : Matrix (Fin 8) (Fin 8) ℤ := !![
  1,0,0,0,1,0,0,0;
  0,0,1,0,0,1,0,0;
  0,0,0,0,0,0,1,0;
  1,0,0,0,0,0,0,1;
  0,1,0,0,0,0,0,0;
  0,0,0,1,0,0,0,0;
  0,0,0,0,1,0,0,0;
  0,1,0,0,0,1,0,0]

/-- An inverse over the integers is stronger than checking rank over a single finite field. -/
def cubicInverse : Matrix (Fin 8) (Fin 8) ℤ := !![
  1,0,0,0,0,0,-1,0;
  0,0,0,0,1,0,0,0;
  0,1,0,0,1,0,0,-1;
  0,0,0,0,0,1,0,0;
  0,0,0,0,0,0,1,0;
  0,0,0,0,-1,0,0,1;
  0,0,1,0,0,0,0,0;
  -1,0,0,1,0,0,1,0]

theorem witness_inverse : cubicWitness * cubicInverse = 1 := by
  decide +kernel

/-- A nonnegative Hilbert series cannot be the reciprocal of 1-2t+2t². -/
theorem no_nonnegative_inverse (b : ℕ → ℤ)
    (h0 : b 0 = 1) (_h1 : b 1 = 2)
    (hrec : ∀ i, b (i+2) = 2 * b (i+1) - 2 * b i)
    (hpos : ∀ i, 0 ≤ b i) : False := by
  have h2 := hrec 0
  have h3 := hrec 1
  have h4 := hrec 2
  norm_num at h2 h3 h4
  linarith [hpos 4]

end KoszulProbability.Obstruction
