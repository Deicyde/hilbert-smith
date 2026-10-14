---
article_id: af_72fcbb88fffe18a27b6f8054
declaration: theorem
origin: cited
---

# Witt localization

For every open $U \subset X$ and every $r \in \Z$, there is a
natural long exact sequence
$\cdots \to W_r(\Bcat(U)) \to W_r(\Bcat(X)) \to
W_r(\Bcat(X)/\Bcat(U)) \xrightarrow{\partial} W_{r-1}(\Bcat(U)) \to
\cdots$. The sequence is natural for $\Pcat \to \T$ and for
pushforwards $g : X \to X'$ with $g(U) \subset U'$.

*Proof sketch.* Apply Balmer--Walter Theorem 2.1 with
$\mathcal J = \Bcat(U)$ and $\mathcal K = \Bcat(X)$: the support
characterization makes $\mathcal J$ a saturated duality-stable
thick subcategory; the categories are essentially small; morphism
groups are real vector spaces so $2$ is bijective; and
(TR4$^+$) passes to full triangulated subcategories and
localizations. The Verdier quotient has full kernel and
duality-stable denominators. Naturality follows because the
functors preserve support subcategories, and the boundary map
commutes since both routes use the same transported symmetric-cone
diagram.

## Sources

- [Preprint source map: `thm:witt-localization`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)
- [Objects supported in an open set](compact-support.md)

## Proof depends on

- [Objects supported in an open set](compact-support.md)
- [Balmer--Walter localization](../background/balmer-walter.md)
