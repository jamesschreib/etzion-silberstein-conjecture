# Formalization boundary

The formal result is `counterexample_summary` in
`EtzionSilbersteinCounterexample.lean`. It proves:

- a supported full-rank code of dimension two exists over `F169`;
- every such code has dimension at most two;
- the Etzion--Silberstein numerical bound for `(3,3,5,5,5)` at distance five
  is three.

Thus the optimum is two and the bound is three.

## What Lean checks

`EtzionSilbersteinCounterexample.lean` first defines the diagram, support,
codes, optimality, the canonical
field `GaloisField 13 2`, and its degree-three and degree-five extensions. The
five deletion counts and their minimum are proved by kernel reduction with
`decide`, not `native_decide`. It also proves that the determinant-nonzero
condition used in the code definition gives matrix rank exactly five.

Its construction section constructs the two-dimensional code from multiplication
by `a + b alpha` in a degree-five extension. Lean checks its dimension, Ferrers
support, and nonzero determinant property.

Its cubic-extension section proves without custom axioms that every monic cubic over
`F169` has a root in the chosen cubic extension. It derives an eigenvector for
every `3 x 3` matrix there, then the generalized eigenvector statement needed
for a pair of first-column coefficient matrices.

Its arithmetic-geometry section defines the determinant polynomial as an actual
`MvPolynomial (Fin 3) F169`. Lean proves its evaluation formula and homogeneity
of degree five. Absolute irreducibility means irreducibility after mapping
coefficients to `AlgebraicClosure F169`.

Its upper-bound section extracts three linearly independent matrices from any code
of dimension at least three. Lean checks that:

1. their determinant pencil is anisotropic over `F169`;
2. Ferrers support makes the first top-column coefficient matrix injective;
3. the cubic-extension eigenvector makes the first two full columns dependent;
4. the extended determinant therefore vanishes;
5. this contradicts the arithmetic-geometry consequence below.

The theorem `code_finrank_le_two` is derived at the end of this chain. It is
not assumed.

## The two mathematical axioms

Mathlib 4.30.0 does not provide the required plane-curve Hasse--Weil and
geometric factorization APIs. They are isolated as follows.

### `hasseWeil_nonzero_zero`

An absolutely irreducible homogeneous ternary quintic over `F169` has a
nonzero `F169`-zero. This packages normalization, the plane-quintic genus bound
`g <= 6`, and the numerical Hasse--Weil lower bound of 14 rational points.

### `anisotropic_not_absolutely_irreducible_no_cubic_zero`

An anisotropic homogeneous ternary quintic over `F169` which is not absolutely
irreducible has no nonzero zero over the degree-three extension. This packages
the paper's remaining geometric factorization branch: base irreducibility
from the low-degree-factor argument, geometric reducedness in characteristic
13, the transitive Frobenius orbit of five conjugate lines, and the
coprime-degree linear-disjointness conclusion.

Both assumptions quantify over arbitrary ternary polynomials. They do not
refer to matrices, Ferrers support, rank-metric codes, code dimension, or the
counterexample theorem.

## Axiom audit

`AxiomAudit.lean` verifies that the construction, cubic-extension algebra,
determinant evaluation, and homogeneity results use only Lean's standard
foundational axioms (`propext`, `Classical.choice`, and `Quot.sound`). The upper
bound and final theorem add exactly the two named assumptions above.

There are no `sorry` declarations, unsafe proof shortcuts, or `native_decide`
uses in the formalization.
