---
article_id: af_bf9fbf4ec088f1ac32a10325
declaration: def
origin: bridged
statement: formalized
lean: HSP.Evaluation.germ
---
# The labelled-model class

Let $n\ge1$ and $R>0$, put $N=n+4$, and let $Z_0\subseteq S^n$ be the [exterior](../corner/exterior.md) for $n$ and $R$, in the [round sphere](../corner/round-sphere.md). For continuous $c:\mathbb T^n\to S^n$, the *labelled-model class* (or *germ*) $\mathfrak m_c\in\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n))$ is the image, under the map induced by the quotient functor $\mathcal A_{\mathbf 1}(S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ of the [exterior quotient](../categories/supports/exterior-quotient.md), of $\mathrm{cls}[D_i,\varphi_i]$ for the [labelled model](labelled-model.md) with labels $c$. Here the strict complex $(D_i,\varphi_i)$ in $\mathcal A_{\mathbf 1}(S^n)$ is read in $\mathrm{Kar}\,\mathcal A_{\mathbf 1}(S^n)$ through the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md) $M\mapsto(M,1)$, so that its class lies in $L^p_N(\mathcal A_{\mathbf 1}(S^n))$, where [cls](../l-theory/ultimate/groups/ultimate-cls.md) is defined. The labelled model, and so the germ, is formed from a local datum $A$ at the prime $p$; the germ depends on $A$, $R$ and $c$.

## Sources
- HS paper, Section 10 (the scalar class of a labelling).
## Depends on
- [Labelled model](labelled-model.md)
- [The exterior](../corner/exterior.md)
- [The round sphere](../corner/round-sphere.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md)
- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)

## Depends on

- [The quotient duality functor](../l-theory/base/categories/quotient-duality-functor.md)
