---
article_id: af_08e42a676dcf962f98b8b40e
declaration: lemma
origin: bridged
---

# Cuts commute with forgetting

Let $\Delta_T:\mathbb L_N(\mathcal B_{\mathbf G,Z}(T\times S^n))\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ and $\Delta_{\mathbf 1}:\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n))\to\mathbb L_4(\mathcal V_{\mathbf 1})$ be the iterated cuts, $U$ as in [Scalar image](scalar-image.md), and $U_T:\mathcal A_{\mathbf G}(T)\to\mathcal V_{\mathbf 1}$ forget the group and the labels. Then $U_{T*}\Delta_T=\Delta_{\mathbf 1}U_*$.

*Proof sketch.* Induct on the cuts. Each cut is an excision boundary $\partial_{A,B}$ followed by relabeling and component projection.
1. $U$ carries the excisive pair of each cut over $T\times S$ into the one over $S$ ([pushforward](../../categories/functors/push-support.md) and [forgetting the group](../../categories/functors/forget-group-support.md) preserve supports).
2. [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md) commutes $U_*$ past $\partial_{A,B}$.
3. Relabeling and projection commute with $U$ as functors, hence on $\mathbb L$ ([Functoriality](../../l-theory/ultimate/groups/induced-map.md)).

## Sources

- HS paper, Section 12.

## Depends on

- [Iterated cut](iterated-cut.md)
- [Forgetting the group](../../categories/functors/forget-group.md)

## Proof depends on

- [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md)
- [Naturality of the ultimate boundary](../../l-theory/ultimate/boundary/ultimate-boundary-naturality.md)
- [Functoriality](../../l-theory/ultimate/groups/induced-map.md)
- [Pushforward preserves support](../../categories/functors/push-support.md)
- [Forgetting the group preserves support](../../categories/functors/forget-group-support.md)
