---
article_id: af_bc2cc5b4de160cc639604c8b
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.IsCompressedRep
---
# Morphisms represented by compressed matrices

Let $C$ be the [compressed complex](compressed-complex.md). A morphism $f:C_r\to C_s$ of the [asymptotic category](../categories/asymptotic/asymptotic-category.md) $\mathcal A_{\mathbf 1}(T\times S^n)$, for the [trivial group sequence](../categories/asymptotic/trivial-group-sequence.md), is *represented* by rational matrices $m_i$, from the retained cells of degree $r$ to those of degree $s$, if $f$ is the class $[(m_i)_i]$ of the sequence $(m_i)$. The hom type is that of the asymptotic category: classes of sequences of matrices whose propagation tends to $0$, composed levelwise; so a represented morphism has $\operatorname{prop}(m_i)\to0$.

## Sources
- HS paper, Section 10.

## Depends on

- [Compressed complex](compressed-complex.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
