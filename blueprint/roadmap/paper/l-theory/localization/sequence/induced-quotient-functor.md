---
article_id: af_aa43946a9bccd98da26199f7
declaration: def
origin: background
---

# Functor induced on quotients

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be as in [Decorated quotient L-group](decorated-l-group.md), and let $(F,\xi):\mathcal A\to\mathcal A'$ be a duality functor with $FV\in\mathcal U'$ for every $V\in\mathcal U$. Then $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$, $\bar FM=FM$, $\bar F[f]=[Ff]$, with $\bar\xi_M=[\xi_M]$, is a duality functor, strict if $F$ is, and $\bar F\circ q=q'\circ F$ and $\mathrm{Kar}\,\bar F\circ\mathrm{Kar}\,q=\mathrm{Kar}\,q'\circ\mathrm{Kar}\,F$ as duality functors.

*Proof sketch.* If $f=ba$ factors through $V\in\mathcal U$, then $Ff=F(b)F(a)$ factors through $FV\in\mathcal U'$, so $\bar F$ is well defined on classes. Linearity, naturality of $\bar\xi$ and $\bar\xi_M^*=\bar\xi_{M^*}$ are the images of the same facts for $F$. Both composites agree on objects and on morphisms by definition, and on the completion $(M,e)\mapsto(FM,[Fe])$ with duality data $[\xi_M\circ F(e^*)]$ on both sides.

## Sources

- New: the universal property of the quotient by an ideal

## Depends on

- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
