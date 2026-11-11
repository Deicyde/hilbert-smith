---
article_id: af_c686bd2c7b2aa2403e3cf272
declaration: def
origin: background
statement: formalized
lean: HSP.cxProd
---

# Tensor product of complexes

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. Their tensor product $C\otimes E$ is the complex in $\mathcal B''$ with
$$(C\otimes E)_r=\bigoplus_{p+q=r}C_p\boxtimes E_q,$$
and differential $d\boxtimes1+(-1)^p\,1\boxtimes d$ on $C_p\boxtimes E_q$. For chain maps $f:C\to C'$ and $g:E\to E'$, the chain map $f\otimes g$ is $f_p\boxtimes g_q$ on $C_p\boxtimes E_q$.

**Remark (not formalized).** For $C$ in $\operatorname{Kar}\mathcal B$ and $E$ in $C_\mathbb Z(\mathbb Q)$, the pairing is the [box product](box-dual.md) and $C\otimes E$ lies in $\operatorname{Kar}C_\mathbb Z(\mathcal B)$; for $C$ and $E$ in $\mathbb Q$ it is the [tensor product of based vector spaces](based-tensor.md).

*Proof sketch.* (Proof obligations.) $d^2=0$: the terms $d^2\boxtimes1$ and $1\boxtimes d^2$ vanish, and the two mixed terms $(-1)^{p}d\boxtimes d$ and $(-1)^{p-1}d\boxtimes d$ cancel. $f\otimes g$ commutes with the differentials because $f$ and $g$ do and the sign depends only on $p$.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Duality pairings](duality-pairing.md)
- [Tensor product of based vector spaces](based-tensor.md)
