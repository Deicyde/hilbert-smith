---
article_id: af_19957d9b93ca4a3f45de56a6
---

# The graph corner

This chapter turns a strict Poincaré complex over $T\times S^n$ that carries a graph-type homotopy action into a class over $T$. The divisibility theorem applies to that class. Its scalar image is the class of the original complex.

The setting is fixed in [Standing data](standing-data.md): a prime $p$, cyclic groups $G_i$ with surjections $\chi_i$ onto $C_p$ (both written additively), a nonempty compact metric space $T$ with a free isometric $C_p$-action, and $n$, $R$, $s$. The sets it uses need only part of these data, so other chapters can use them for an empty $T$: the [round sphere](round-sphere.md) $(S^n,d_S)$, the [exterior](exterior.md) $Z_0$ and $Z=T\times Z_0$ ([closed](exterior-closed.md)), and the [cut sets](cut-sets.md), the cube faces $A_m,B_m,Y_m$ along which the [iterated cut](theorem/iterated-cut.md) and the [scalar iterated cut](theorem/scalar-iterated-cut.md) run ([cut flag](cut-flag.md), [exterior lies in the first cut](exterior-first-cut.md)). A matrix of [graph type](actions/graph-type.md) $c\in C_p$ moves $T$-labels by $c$ and sphere labels a little; types add under composition ([calculus of graph types](actions/graph-type-calculus.md)). A [graph-type homotopy action](actions/graph-type-action.md) is a family of such matrices satisfying the group relations up to homotopy and modulo the exterior. Only first-order homotopies are given, with no higher coherence.

[Induction](actions/induction.md) copies a complex onto $|G_i|$ sheets, with sheet $s$ moved by $\chi_i(s)$. [Sheet translation](actions/sheet-translation.md) is the key computation: a matrix of graph type $\chi_i(g)$ followed by the sheet shift $R_{-g}$ becomes a controlled equivariant matrix. The [average](actions/average.md) $E=q^{-1}\sum_g A_g\otimes R_{-g}$ has propagation at most the largest graph defect, independent of $|G_i|$ ([Average propagation](actions/average-propagation.md)). It is therefore a duality-compatible homotopy idempotent ([Average is a compatible idempotent](actions/average-compatible-idempotent.md)).

[Splitting](theorem/homotopy-idempotent-splitting.md) gives $D$ in $[0,N]$, [corner duality](theorem/corner-duality.md) gives the strict form $q^{-1}r\Phi r^*$, and [the corner class](theorem/corner-class.md) is $\mathfrak d$. [Corner identification](theorem/corner-identification.md) is an abstract criterion for a corner to be isometric to a given complex. The [scalar image](theorem/scalar-image.md) applies it after [forgetting $T$ and the group](theorem/scalar-forget.md). Combined with [cuts commuting with forgetting](theorem/cuts-commute-forgetting.md) and the divisibility theorem, this proves [Theorem A](theorem/theorem-a.md).

Theorem A rests on three open statements: [idempotent splitting](theorem/kb-idempotent-splitting.md), through the corner class; [Lemma U](../l-theory/comparison/lemma-u.md), through divisibility and the tail signature; and [lifting](../l-theory/localization/boundary/lift-to-pair.md), through the cut boundaries of the iterated cuts and through divisibility.

## Sections

- [The round sphere](round-sphere.md)
- [The exterior](exterior.md)
- [The exterior is closed](exterior-closed.md)
- [The cut sets](cut-sets.md)
- [The cut flag](cut-flag.md)
- [The exterior lies in the first cut](exterior-first-cut.md)
- [Standing data](standing-data.md)
- [Graph-type actions and induction](actions/README.md)
- [The corner and Theorem A](theorem/README.md)

## Sources

- HS paper, Sections 5 and 11.
