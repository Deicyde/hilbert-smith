---
article_id: af_127eb654b5a919a78f7ece7d
declaration: lemma
origin: bridged
---

# Corner duality

Let $\mathcal A$ be a duality category and $\operatorname{Kar}\mathcal A$ its [idempotent completion with the induced duality](../../l-theory/base/categories/karoubi-duality.md). Let $(\mathcal C,\Phi)$ be a strict $N$-dimensional symmetric Poincaré complex in $\operatorname{Kar}\mathcal A$, concentrated in $[0,N]$, with a chosen homotopy inverse $\Phi^{-1}$ of $\Phi:\mathcal C^{N-*}\to\mathcal C$. Suppose:
- $E:\mathcal C\to\mathcal C$ is a chain map with $E^2\simeq E$ and $E\Phi\simeq\Phi E^*$;
- $(D,\iota,r)$ is a splitting of $E$, as in [Splitting](homotopy-idempotent-splitting.md) applied to $\mathcal P=\operatorname{Kar}\mathcal A$: $D$ is concentrated in $[0,N]$, $r\iota\simeq1$ and $\iota r\simeq E$;
- $q$ is a natural automorphism of the identity functor of $\operatorname{Kar}\mathcal A$ with $q_{M^*}=(q_M)^*$ (an invertible, self-adjoint, central scalar).

Then $\phi_D=q^{-1}r\Phi r^*$ is a strict $N$-dimensional symmetric Poincaré structure on $D$, with homotopy inverse $b_D=q\,\iota^*\Phi^{-1}\iota$.

*Proof sketch.*
1. $r$ is a chain map, so $\phi_D$ is a cycle, and $\mathcal T(q^{-1}r\Phi r^*)=q^{-1}r(\mathcal T\Phi)r^*=\phi_D$ because $q$ is central and self-adjoint, where $\mathcal T$ is [the structure involution](../../l-theory/base/complexes/structure-involution.md) (written $T$ by its owner; in this chapter $T$ is the control space).
2. $\phi_Db_D\simeq r\Phi E^*\Phi^{-1}\iota\simeq rE\iota\simeq1$.
3. $b_D\phi_D\simeq\iota^*\Phi^{-1}E\Phi r^*\simeq\iota^*E^*r^*\simeq1$.

## Sources

- HS paper, Section 5.

## Depends on

- [Splitting a homotopy idempotent](homotopy-idempotent-splitting.md)
- [Strict Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)

## Proof depends on

- [The involution T](../../l-theory/base/complexes/structure-involution.md)
