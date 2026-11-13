---
article_id: af_7686f80717562a7313f0e6bc
declaration: lemma
origin: background
---

# Iterated induced quotient functors

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations, $(F,\xi):\mathcal A\to\mathcal A'$ a duality functor with $FV\in\mathcal U'$ for every $V\in\mathcal U$, and $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ the [functor induced on quotients](../decorations/induced-quotient-functor.md). For $j\ge0$ let $F^{(j)}:C_{\mathbb Z^j}\mathcal A/C_{\mathbb Z^j}\mathcal U\to C_{\mathbb Z^j}\mathcal A'/C_{\mathbb Z^j}\mathcal U'$ be the functor induced in the same way by the [iterated bounded extension](../../bounded/categories/bounded-functor-iter.md) $C_{\mathbb Z^j}F$, and let $e_j$, $e'_j$ be the isomorphisms of [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md) for the two filtrations. Then
$$e'_j\circ F^{(j)}=C_{\mathbb Z^j}(\bar F)\circ e_j$$
as duality functors, duality data included.

*Proof sketch.* Induction on $j$. (0) $C_{\mathbb Z^j}F$ applies $F$ entrywise, so it carries $C_{\mathbb Z^j}\mathcal U$ into $C_{\mathbb Z^j}\mathcal U'$, and $F^{(j)}$ is defined. For $j=0$, $e_0$ and $e'_0$ are identities and $F^{(0)}=\bar F$. (1) With $\tilde e_j$, $\tilde e'_j$ the entrywise quotient functors of that article, $\tilde e'_j\circ F^{(j+1)}=C_\mathbb Z(F^{(j)})\circ\tilde e_j$: both are the identity on objects, both send the class of $(f_{mn})$ to the matrix of classes $([C_{\mathbb Z^j}F(f_{mn})])$, and both have the diagonal duality data $([(C_{\mathbb Z^j}\xi)_{M_n}])_n$. (2) Then
$$e'_{j+1}F^{(j+1)}=C_\mathbb Z(e'_j)\,C_\mathbb Z(F^{(j)})\,\tilde e_j=C_\mathbb Z(e'_jF^{(j)})\,\tilde e_j=C_\mathbb Z(C_{\mathbb Z^j}\bar F\circ e_j)\,\tilde e_j=C_{\mathbb Z^{j+1}}\bar F\circ e_{j+1},$$
by [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md) (twice) and the induction hypothesis.

## Sources

- New: from the definitions, by the induction of [Iterated quotient functors](quotient-functor-level.md).

## Depends on

- [Functor induced on quotients](../decorations/induced-quotient-functor.md)
- [Iterated bounded extension](../../bounded/categories/bounded-functor-iter.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)

## Proof depends on

- [Bounded extension is functorial](../../bounded/categories/bounded-functor-comp.md)
