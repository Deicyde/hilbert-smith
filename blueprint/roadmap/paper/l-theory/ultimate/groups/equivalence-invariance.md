---
article_id: af_739df4be205d664bfb747f86
declaration: lemma
origin: background
statement: formalized
lean: HSP.ultL.map_inverse
proof: formalized
---

# Equivalence invariance on ultimate L

Let $F:\mathcal A\to\mathcal B$ and $G:\mathcal B\to\mathcal A$ be duality functors with unitary natural isomorphisms $\mathrm{id}_{\mathcal A}\cong G\circ F$ and $F\circ G\cong\mathrm{id}_{\mathcal B}$. Then $F_*:\mathbb L_k(\mathcal A)\to\mathbb L_k(\mathcal B)$ is an isomorphism with inverse $G_*$. (Lean: $\mathcal A$ and $\mathcal B$ have the same universe levels, as for the [induced map](induced-map.md).)

*Proof sketch.* [Functoriality on ultimate L](induced-map-comp.md) gives $G_*F_*=(GF)_*$, [Unitary invariance on ultimate L](unitary-invariance.md) gives $(GF)_*=(\mathrm{id}_{\mathcal A})_*$, and [Identity on ultimate L](induced-map-id.md) gives $(\mathrm{id}_{\mathcal A})_*=\mathrm{id}$. The composite $F_*G_*$ is the same with the roles exchanged.

## Sources

- New: the argument of [Equivalence invariance](../../base/groups/equivalence-invariance.md), on $\mathbb L$.

## Depends on

- [Induced map on ultimate L](induced-map.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)

## Proof depends on

- [Functoriality on ultimate L](induced-map-comp.md)
- [Unitary invariance on ultimate L](unitary-invariance.md)
- [Identity on ultimate L](induced-map-id.md)
