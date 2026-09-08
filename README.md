# The Etzion-Silberstein conjecture

The conjecture states that its dimension bound for Ferrers-diagram rank-metric codes is attained over every finite field.

For the diagram with column heights $(3,3,5,5,5)$ over $\mathbb F_{169}$ at minimum rank distance $5$, the maximum code dimension is $2$, below the conjectured bound of $3$.

Proof: [proof.pdf](proof.pdf).

The counterexample is fully formalized in Lean, conditional on `hasseWeil_nonzero_zero` and `anisotropic_not_absolutely_irreducible_no_cubic_zero`.
Run `lake build` to verify; see [FORMALIZATION.md](FORMALIZATION.md) for details.

Posed by Etzion and Silberstein in 2009. Disproven Aug 9, 2026.
