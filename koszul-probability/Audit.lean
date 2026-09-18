import KoszulProbability

-- Expected only Lean's standard logical axioms, never sorryAx or project-specific axioms.
#print axioms KoszulProbability.singular_fraction_le
#print axioms KoszulProbability.certified_density
#print axioms KoszulProbability.ballSize_eq_card
#print axioms KoszulProbability.Presentation.squareZeroEquiv
#print axioms KoszulProbability.SquareZero.linear_resolution
#print axioms KoszulProbability.square_zero_algebra_density
#print axioms KoszulProbability.square_zero_algebra_error
#print axioms KoszulProbability.Obstruction.witness_inverse
#print axioms KoszulProbability.Obstruction.no_nonnegative_inverse

#print axioms KoszulProbability.Transport.linear_resolution
#print axioms KoszulProbability.koszul_certificate_density

#print axioms KoszulProbability.box_failure_bound
#print axioms KoszulProbability.box_singular_fraction_tendsto_zero
#print axioms KoszulProbability.box_square_zero_error
#print axioms KoszulProbability.box_koszul_certificate_density
#print axioms KoszulProbability.geometric_box_error
#print axioms KoszulProbability.geometric_box_density
#print axioms KoszulProbability.fixed_field_box_density
#print axioms KoszulProbability.galois_box_density
#print axioms KoszulProbability.galois_boxBall_card

-- Sharper and two-sided bounds, converse, asymptotics
#print axioms KoszulProbability.regularCount_eq
#print axioms KoszulProbability.singular_fraction_le_inv
#print axioms KoszulProbability.square_zero_algebra_error_sharp
#print axioms KoszulProbability.square_zero_algebra_error_three
#print axioms KoszulProbability.Presentation.det_ne_zero_of_model
#print axioms KoszulProbability.model_top_eq_certified
#print axioms KoszulProbability.square_zero_algebra_error_lower
#print axioms KoszulProbability.square_zero_algebra_error_two_sided
#print axioms KoszulProbability.square_zero_failure_asymptotic

-- Polynomial boxes
#print axioms KoszulProbability.boxGrowth_polynomial
#print axioms KoszulProbability.polynomial_box_error
#print axioms KoszulProbability.polynomial_box_density
#print axioms KoszulProbability.fixed_field_polynomial_box_density

-- Fixed-stratum obstruction: counting and the actual quotient
#print axioms KoszulProbability.Obstruction.cubicDet_ne_zero
#print axioms KoszulProbability.Obstruction.totalDegree_cubicDet_le
#print axioms KoszulProbability.Obstruction.obstruction_fraction_le
#print axioms KoszulProbability.Obstruction.obstruction_fraction_le_field
#print axioms KoszulProbability.Obstruction.cubic_products_vanish
#print axioms KoszulProbability.Obstruction.rows_linearIndependent
