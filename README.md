# Counterexample to the Etzion--Silberstein conjecture

For a Ferrers diagram $\mathcal D$ with column heights $c_1,\ldots,c_n$,
the Etzion--Silberstein bound for a linear rank-metric code of minimum rank
distance $d$ is

$$
\dim C\leq \nu_{\min}(\mathcal D,d),
\qquad
\nu_{\min}(\mathcal D,d)
=\min_{0\leq j<d}
\sum_{i=1}^{n-j}\max\{0,c_i-d+1+j\}.
$$

The conjecture asserted that this bound is attained over every finite field
for every Ferrers diagram.

Take

$$
F=\mathbb F_{169},\qquad n=d=5,
\qquad (c_1,c_2,c_3,c_4,c_5)=(3,3,5,5,5).
$$

The five terms in the bound are

$$
(\nu_0,\nu_1,\nu_2,\nu_3,\nu_4)=(3,4,5,4,3),
$$

so $\nu_{\min}(\mathcal D,5)=3$.

## Counterexample construction

Let $K=\mathbb F_{169^5}=F(\alpha)$ and use the power basis
$1,\alpha,\alpha^2,\alpha^3,\alpha^4$. For $a,b\in F$, let
$M_{a+b\alpha}$ be the matrix of multiplication by $a+b\alpha$ on $K$, and
set

$$
C_0=\{M_{a+b\alpha}:a,b\in F\}.
$$

This code has dimension $2$. Its first two columns represent

$$
(a+b\alpha)\cdot 1=a+b\alpha,
\qquad
(a+b\alpha)\cdot\alpha=a\alpha+b\alpha^2,
$$

so they have no entries below the first three rows, exactly as required by
the Ferrers diagram. Every nonzero matrix in $C_0$ is invertible because it
represents multiplication by a nonzero field element.

The determinant-quintic argument in [proof.pdf](proof.pdf) shows that no
three-dimensional supported code can have all its nonzero matrices
invertible. Therefore

$$
\boxed{
\kappa_{\mathbb F_{169}}(\mathcal D,5)
=2<3=\nu_{\min}(\mathcal D,5)
},
$$

disproving universal attainment of the Etzion--Silberstein bound.

Formalized in Lean 4.30. The bound computation and two-dimensional
multiplication-code construction are checked in Lean; the geometric upper
bound is exposed as the named input `quinticObstruction_external` and proved
mathematically in [proof.pdf](proof.pdf), whose source is
[proof.tex](proof.tex). The exact trusted base is reported by
`AxiomAudit.lean`.

Reproduce the verification by running `lake build`.
