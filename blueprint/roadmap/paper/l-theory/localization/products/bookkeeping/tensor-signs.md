---
article_id: af_b0df903ab30a706f2bc030f8
declaration: instance
origin: background
statement: formalized
lean: HSP.tensorSignsDownInt
---

# Signs for tensor products of chain complexes

For chain complexes indexed by $\mathbb Z$ with differentials of degree $-1$, the signs $\varepsilon(p)=(-1)^p$ are compatible with the complex shape: $\varepsilon(p+q)=\varepsilon(p)\varepsilon(q)$, $\varepsilon(p+1)=-\varepsilon(p)$, and adding a fixed degree preserves the relation "$q=p-1$" between degrees. These are the signs of $1\boxtimes d$ on $C_p\boxtimes E_q$ in a [tensor product of complexes](../complex-product.md).

*Proof sketch.* $(-1)^{p+q}=(-1)^p(-1)^q$ and $(-1)^{p+1}=-(-1)^p$; and $q=p-1$ if and only if $q+r=(p+r)-1$.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign convention, split out.

## Depends on

