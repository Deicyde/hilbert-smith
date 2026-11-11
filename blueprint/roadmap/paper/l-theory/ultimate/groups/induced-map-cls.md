---
article_id: af_09ef95516f47e482e4aa7404
declaration: lemma
origin: background
statement: formalized
lean: HSP.ultL.map_cls
proof: formalized
---

# The induced map commutes with cls

For a duality functor $F:\mathcal A\to\mathcal A'$, $F_*\circ\mathrm{cls}=\mathrm{cls}\circ F_*$, where on the right $F_*:L^p_k(\mathcal A)\to L^p_k(\mathcal A')$ is the induced homomorphism.

*Proof sketch.* [The induced map at each stage](induced-map-level.md) with $j=0$, since $C_{\mathbb Z^0}F=F$.

## Sources

- New: stage $0$ of the induced map.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [The class map](ultimate-cls.md)
- [The projective L-group](../../base/groups/projective-l-group.md)

## Proof depends on

- [The induced map at each stage](induced-map-level.md)
- [Transport of L-groups along an equality of degrees](../../base/groups/l-group-cast.md)
