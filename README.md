# Counterexample to the Etzion--Silberstein Conjecture

The Etzion--Silberstein conjecture states that its dimension bound for
Ferrers-diagram rank-metric codes is attained over every finite field.

It fails over $F=\mathbb F_{169}$ at minimum rank distance $5$ for the
Ferrers diagram $\mathcal D$ with column heights $(3,3,5,5,5)$:

$$
\kappa_F(\mathcal D,5)=2<3=\nu_{\min}(\mathcal D,5).
$$

The two-dimensional code consists of the multiplication maps by
$a+b\alpha$ on $\mathbb F_{169^5}$ in the power basis
$1,\alpha,\ldots,\alpha^4$.

The proof is in [`proof.pdf`](proof.pdf).
Formalized in Lean 4.30 using Hasse--Weil and Frobenius-factorization axioms.

## Lean formalization

Under exactly the two arithmetic-geometry axioms stated below, the Lean 4
formalization checks the numerical bound, the two-dimensional
multiplication code, the cubic-extension eigenvector argument, the reduction
from a hypothetical three-dimensional code to a determinant-quintic zero, and
the final strict gap.

It deliberately assumes only two polynomial-level arithmetic-geometry
bridges: the required Hasse--Weil consequence for absolutely irreducible plane
quintics, and the Frobenius-factorization consequence for anisotropic
non-absolutely-irreducible quintics. Neither axiom mentions Ferrers diagrams,
codes, dimensions, or the desired upper bound.

See [FORMALIZATION.md](FORMALIZATION.md) for the exact trust boundary and
module-by-module proof map. With Lean 4.30.0 and the pinned Mathlib checkout,
run `lake build`. `AxiomAudit.lean` prints the assumptions of every major theorem.
