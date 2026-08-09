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
$1,\alpha,\ldots,\alpha^4$. The proof that dimension $3$ is impossible is
in [proof.pdf](proof.pdf).

Formalized in Lean 4.30, including the bound computation and two-dimensional
multiplication-code construction; `quinticObstruction_external` isolates the
geometric upper bound. Reproduce the verification by running `lake build`.
