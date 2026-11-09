---
article_id: af_19957d9b93ca4a3f45de56a6
---

# The graph corner

This chapter turns a strict Poincaré complex over $T\times S^n$ that carries a graph-type homotopy action into a class over $T$. The divisibility theorem applies to that class. Its scalar image is the class of the original complex.

The setting is fixed in [Standing data](standing-data.md): a prime $p$, cyclic groups $G_i$ with characters $\chi_i$ onto $C_p$, a compact metric space $T$ with a free isometric $C_p$-action, and the exterior $Z=T\times Z_0$. A matrix of [graph type](actions/graph-type.md) $c\in C_p$ moves $T$-labels by $c$ and sphere labels a little. A [graph-type homotopy action](actions/graph-type-action.md) is a family of such matrices satisfying the group relations up to homotopy and modulo the exterior. Only first-order homotopies are given, with no higher coherence.

[Induction](actions/induction.md) copies a complex onto $|G_i|$ sheets, with sheet $s$ moved by $\chi(s)$. [Sheet translation](actions/sheet-translation.md) is the key computation: a graph-type-$g$ matrix followed by the right sheet shift $R_{g^{-1}}$ becomes a controlled equivariant matrix. The [average](actions/average.md) $E=q^{-1}\sum_g A_g\otimes R_{g^{-1}}$ has propagation at most the largest graph defect, independent of $|G_i|$ ([Average propagation](actions/average-propagation.md)). It is therefore a duality-compatible homotopy idempotent ([Average is a compatible idempotent](actions/average-compatible-idempotent.md)).

[Splitting](theorem/homotopy-idempotent-splitting.md) gives $D$ in $[0,N]$, [corner duality](theorem/corner-duality.md) gives the strict form $q^{-1}r\Phi r^*$, and [the corner class](theorem/corner-class.md) is $\mathfrak d$. [Corner identification](theorem/corner-identification.md) is an abstract criterion for a corner to be isometric to a given complex. The [scalar image](theorem/scalar-image.md) applies it after forgetting $T$ and the group. Combined with [cuts commuting with forgetting](theorem/cuts-commute-forgetting.md) and the divisibility theorem, this proves [Theorem A](theorem/theorem-a.md).

## Sections

- [Standing data](standing-data.md)
- [Graph-type actions and induction](actions/README.md)
- [The corner and Theorem A](theorem/README.md)

## Sources

- HS paper, Sections 5 and 11.
