# Quadratic presentation balls and Koszul density

This accompanies the paper *Counting Quadratic Presentations over Finite Fields: A Growing-Ball Koszul Density Theorem* (A. Olivares Acosta, 2026). It studies Koszul density in a specified finite-field counting model.

For a **fixed prime** `p`, the radius-`B` ball contains every labeled matrix presentation with:

- `1 ≤ n ≤ B` generators;
- coefficient field `GF(p^e)`, `1 ≤ e ≤ B`;
- `0 ≤ m ≤ n²` ordered quadratic relations;
- every `m × n²` coefficient matrix, including dependent rows.

Every presentation has equal weight. This is not uniform sampling of triples, relation subspaces, or algebra isomorphism classes.

The project proves an actual algebraic probability statement: the proportion of these presentations whose quotient is isomorphic to `k ⊕ k^n`, with each generator sent to its degree-one basis vector, tends to one. The finite failure bound is

```
(2 * B^4 + B^2) / p^B.
```

Such algebras have square-zero augmentation ideal. The project also constructs their explicit free linear resolution in all homological degrees. This yields the paper's Koszul probability corollary.

The exact count of invertible matrices over `GF(q)` gives a sharp two-sided bound for the square-zero event `M`:

```
(1 - 2B⁴/p^(B³)) / p^B  ≤  1 - M/W  ≤  1/(p^B - 1) + 2B⁴/p^(B³),
```

so `1/(2p^B) ≤ 1 - M/W ≤ 3/p^B` for `B ≥ 2` and `p^B · (1 - M/W) → 1`. The lower bound uses the converse of the square-zero model theorem: in the top stratum a generator-preserving square-zero model exists **iff** `det C ≠ 0` (`Converse.lean`).

The same argument works for coefficients drawn from finite **boxes** `S_e ⊆ K_e` in an arbitrary family of fields, in particular from a fixed infinite field such as `ℚ`, `ℝ`, or `ℂ`. Under the growth condition `|S_e|^(B⁴) · |S_B| ≤ |S_B|^(B⁴)` for `e < B` (satisfied by `|S_e| = c^e`, `c ≥ 2`, and also by polynomial boxes `|S_e| = e^k` for every `k`), the failure bound is `(2B⁴ + B²)/|S_B|`; for `|S_e| = e^k` it is `(2B⁴ + B²)/B^k`, which tends to zero for `k ≥ 5`. The finite-field theorem is the instance `S_e = GF(p^e)`, and Lean checks this.

The reason for the limit is concentration on the largest stratum `(n,e,m)=(B,B,B²)`. It does **not** establish generic Koszulity for every fixed `(n,m)`. The paper proves the opposite limit for `(n,m)=(2,2)`. The growing-ball theorem is elementary and its sampling bias is part of its statement.

## Build

From this directory:

```sh
lake build
lake env lean Audit.lean
```

Lean is pinned to `leanprover/lean4:v4.33.1`. Mathlib is pinned to tag `v4.33.1`; `lake-manifest.json` locks its commit and all transitive dependencies. A fresh checkout can run `lake update` and, if needed, `lake exe cache get` to fetch dependencies and compiled mathlib artifacts before building. No global default toolchain needs to be changed.

## Formal statements

| File | What Lean verifies |
| --- | --- |
| `MatrixCounting.lean` | Nonzero determinant polynomial, degree bound, actual singular-matrix count, Schwartz–Zippel probability estimate. |
| `Ball.lean` | Index triples, exact weight sum, off-top exponent gap, explicit error bound, and polynomial/exponential limit. |
| `Density.lean` | `certified_density`: unconditional density of nonsingular top-stratum matrices over `GaloisField p B`, assuming only that `p` is prime. |
| `SampleSpace.lean` | Actual finite disjoint union of coefficient spaces; `ballSize_eq_card` identifies its cardinality with the analytic denominator. |
| `SquareZero.lean` | Actual free `A`-modules, `A`-linear differentials, exactness at every positive degree and at augmentation, surjectivity of augmentation, and internal-degree conditions. Bundled as `SquareZero.linear_resolution`. |
| `Presentation.lean` | Actual quotient of the free associative algebra by listed quadratic relations, row span, vanishing of quadratic products, and `Presentation.squareZeroEquiv` with a proved inverse. |
| `Transport.lean` | Transports the explicit free linear resolution to the actual source quotient; verifies exactness, freeness, augmentation and degree conditions there. |
| `AlgebraDensity.lean` | `square_zero_algebra_density` and `square_zero_algebra_error`: density one and the explicit finite bound for actual presented algebras with a generator-preserving square-zero model. `koszul_certificate_density` additionally includes the constructive free linear resolution over the presented quotient itself. |
| `Obstruction.lean` | Kernel-checked integer inverse of the two-generator cubic witness and the impossible nonnegative reciprocal coefficients. |
| `BoxBall.lean` | Abstract concentration lemma `failure_bound_of_weights`; box weights, the growth condition `BoxGrowth`, the finite bound `box_failure_bound`, the limit `box_density_of_top_certificates`, and `boxGrowth_geometric`. |
| `BoxDensity.lean` | Actual sample space `boxBall` of matrices with entries in boxes of an arbitrary family of fields; Schwartz–Zippel on a box; `box_square_zero_error`, `box_koszul_certificate_density`; corollaries `geometric_box_error`, `geometric_box_density`, `fixed_field_box_density`; the finite-field instance `galois_box_density`, `galois_boxBall_card`; and the measure-free `box_singular_fraction_tendsto_zero`. |
| `SharpBound.lean` | Exact count of invertible matrices via mathlib's `Matrix.card_GL_field` (`regularCount_eq`); singular fraction between `1/q` and `1/(q-1)` (`singular_fraction_ge`, `singular_fraction_le_inv`); the `B³` stratum gap; sharp upper bound `square_zero_algebra_error_sharp` and `square_zero_algebra_error_three` (`≤ 3/p^B` for `B ≥ 2`). |
| `Converse.lean` | `Presentation.det_ne_zero_of_model`: a generator-preserving square-zero model forces `det C ≠ 0` (explicit matrix representation). Hence `model_top_eq_certified`, the lower bound `square_zero_algebra_error_lower`, the two-sided bound `square_zero_algebra_error_two_sided`, and `square_zero_failure_asymptotic`: `p^B · (1 − M/W) → 1`. |
| `PolynomialBox.lean` | Polynomial boxes `|S_e| = e^k` satisfy the growth condition for every `k` (`boxGrowth_polynomial`); `polynomial_box_error`, `polynomial_box_density` (`k ≥ 5`), `fixed_field_polynomial_box_density`. |
| `ObstructionDensity.lean` | The cubic determinant `cubicDet` of the actual `8 × 8` matrix `M(r,s)`: nonzero over every field, degree `≤ 8`, Schwartz–Zippel bound `8/|S|` (`obstruction_fraction_le`, `obstruction_fraction_le_field`); for `det ≠ 0`, all cubic products of generators vanish in the actual quotient (`cubic_products_vanish`) and the two relations are independent (`rows_linearIndependent`). |

There are no `sorry`, `admit`, or project-specific axioms. `Audit.lean` checks the main dependency chains. Standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) are expected. The small integer matrix check uses `decide +kernel`, not an external numeric computation accepted as an axiom.

## Exact formalization boundary

The strongest asymptotic theorem is **about the actual algebra quotient and a generator-preserving algebra isomorphism**, not merely an abstract success predicate supplied with its own probability estimate. The file `Ball.lean` contains a conditional transfer lemma, but `Density.lean` and `AlgebraDensity.lean` discharge its assumptions for concrete finite counts.

The theorem `koszul_certificate_density` counts presentations with an actual constructive free linear resolution certificate over their quotient algebra. `Transport.linear_resolution` verifies the transfer of the explicit resolution, including its internal-degree conditions. The generator-preserving isomorphism identifies the pulled-back grading with the presentation grading.

There is no general `IsKoszul` predicate or graded Tor library here. `HasKoszulCertificate` is an explicitly defined **sufficient certificate**, not a purported characterization of all Koszul algebras. It requires both the algebra isomorphism and the checked exact free linear resolution.

For the fixed-`(2,2)` obstruction, Lean verifies the counting half: outside a set of at most `8q⁷` coefficient vectors (Schwartz–Zippel on the cubic determinant, `ObstructionDensity.lean`), all cubic products of generators vanish in the actual presented quotient and the two relations are linearly independent. The remaining written step is that these facts give Hilbert series `1 + 2t + 2t²`, whose Euler-characteristic contradiction with a linear resolution is the arithmetic fact `Obstruction.no_nonnegative_inverse`.
