---
article_id: af_a11ff9d619ebc99ebb60d602
declaration: lemma
origin: background
---

# Equivalence invariance for decorated groups

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be as in [Decorated objects](decorated-object.md). Let $F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ and $G:\mathcal A'/\mathcal U'\to\mathcal A/\mathcal U$ be duality functors with unitary natural isomorphisms $\eta:\mathrm{id}\cong G\circ F$ and $\varepsilon:F\circ G\cong\mathrm{id}$. Assume that $\mathrm{Kar}\,F$ and $\mathrm{Kar}\,G$ carry decorated objects to decorated objects. Then the [decorated induced maps](decorated-induced-map.md) satisfy $G^{\mathrm{im}}_*\circ F^{\mathrm{im}}_*=\mathrm{id}$ and $F^{\mathrm{im}}_*\circ G^{\mathrm{im}}_*=\mathrm{id}$.

*Proof sketch.* (1) $\mathrm{Kar}\,\eta$, with components $(\mathrm{Kar}\,\eta)_{(M,e)}=GF(e)\circ\eta_M\circ e$, is a unitary natural isomorphism $\mathrm{id}\cong\mathrm{Kar}\,G\circ\mathrm{Kar}\,F$; unitarity holds componentwise because it holds for $\eta$. The same holds for $\varepsilon$. (2) By hypothesis $\mathrm{Kar}\,F$ and $\mathrm{Kar}\,G$ restrict to duality functors between $\mathrm{Dec}(\mathcal A/\mathcal U)$ and $\mathrm{Dec}(\mathcal A'/\mathcal U')$, and the components of $\mathrm{Kar}\,\eta$ and $\mathrm{Kar}\,\varepsilon$ at decorated objects are maps of the full subcategories. So the restricted data satisfy the hypotheses of [Equivalence invariance](../../base/groups/equivalence-invariance.md) in the duality categories $\mathrm{Dec}(\mathcal A/\mathcal U)$ and $\mathrm{Dec}(\mathcal A'/\mathcal U')$, which gives both identities.

## Sources

- New: [Equivalence invariance](../../base/groups/equivalence-invariance.md), applied to the categories of decorated objects

## Depends on

- [Decorated induced map](decorated-induced-map.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)

## Proof depends on

- [Equivalence invariance](../../base/groups/equivalence-invariance.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
