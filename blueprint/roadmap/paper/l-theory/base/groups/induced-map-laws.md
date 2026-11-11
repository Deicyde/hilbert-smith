---
article_id: af_8b5d05d62331fff058a01a8b
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPoincare.map_cobordant
---

# Duality functors on cobordism classes

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md) and use the [images](../pairs/functor-poincare.md) $(FC,F_\%\phi)$ of strict $k$-dimensional symmetric Poincaré complexes. Then:
1. if $(C,\phi)$ is [cobordant](../pairs/cobordism.md) to $(C',\phi')$, then $(FC,F_\%\phi)$ is cobordant to $(FC',F_\%\phi')$;
2. the image of $(C,\phi)\oplus(C',\phi')$ is cobordant to $(FC,F_\%\phi)\oplus(FC',F_\%\phi')$, with the sums of [Sums of Poincaré complexes](../pairs/sum-of-poincare.md).

*Proof sketch.* (1) A cobordism goes, by [Duality functors carry pairs to pairs](../pairs/functor-pair.md), to a pair with boundary $(F(C\oplus C'),F_\%(\phi\oplus(-\phi')))$. The canonical isomorphism $u:FC\oplus FC'\cong F(C\oplus C')$ carries $F_\%\phi\oplus(-F_\%\phi')$ to that structure, so [Transport of pairs along isomorphisms](../pairs/pair-transport.md) ($s=1$) makes it a cobordism. (2) [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md) with $h=u^{-1}$ and $\chi=0$.

## Sources

- New: direct from the definitions

## Depends on

- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [Sums of Poincaré complexes](../pairs/sum-of-poincare.md)
- [Cobordism](../pairs/cobordism.md)

## Proof depends on

- [Duality functors carry pairs to pairs](../pairs/functor-pair.md)
- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md)
