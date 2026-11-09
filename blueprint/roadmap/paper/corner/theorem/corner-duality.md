---
article_id: af_127eb654b5a919a78f7ece7d
declaration: lemma
origin: bridged
---

# Corner duality

In addition to the data of [Splitting](homotopy-idempotent-splitting.md), suppose:
- $\Phi:\mathcal C^{N-*}\to\mathcal C$ is a strict symmetric Poincaré equivalence with chosen homotopy inverse $\Phi^{-1}$;
- $E\Phi\simeq\Phi E^*$;
- $q$ is an invertible, self-adjoint, central scalar.

Then $\phi_D=q^{-1}r\Phi r^*$ is a strict symmetric Poincaré structure on $D$, with homotopy inverse $b_D=q\,\iota^*\Phi^{-1}\iota$.

*Proof sketch.*
1. $T(r\Phi r^*)=r(T\Phi)r^*=r\Phi r^*$.
2. $\phi_Db_D\simeq r\Phi E^*\Phi^{-1}\iota\simeq rE\iota\simeq1$.
3. $b_D\phi_D\simeq\iota^*\Phi^{-1}E\Phi r^*\simeq\iota^*E^*r^*\simeq1$.

## Sources

- HS paper, Section 5.

## Depends on

- [Splitting a homotopy idempotent](homotopy-idempotent-splitting.md)
- [Strict Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
