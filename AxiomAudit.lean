import EtzionSilbersteinCounterexample

/-! Trusted-base audit for every major stage of the formalization. -/

set_option autoImplicit false

open EtzionSilbersteinCounterexample

#print axioms boundTerm_values
#print axioms etzionSilbersteinBound_eq_three
#print axioms det_ne_zero_iff_rank_eq_five
#print axioms IsRankFiveCode.rank_eq_five
#print axioms Construction.code_finrank
#print axioms Construction.code_supported
#print axioms Construction.code_full_rank
#print axioms exists_root_monic_cubic
#print axioms exists_cubic_generalized_eigenvector
#print axioms eval_determinantPolynomial
#print axioms eval₂_determinantPolynomial_cubic
#print axioms determinantPolynomial_isHomogeneous
#print axioms hasseWeil_nonzero_zero
#print axioms anisotropic_not_absolutely_irreducible_no_cubic_zero
#print axioms no_supported_anisotropic_pencil
#print axioms determinant_zero_of_topColumn_dependence
#print axioms code_finrank_le_two
#print axioms optimalDimension_F169
#print axioms counterexample_to_universal_attainment
#print axioms counterexample_summary
