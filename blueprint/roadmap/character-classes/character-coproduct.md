---
article_id: af_6db0b577286e606ab495a56a
declaration: lemma
origin: cited
---

# Character coproducts

There are canonical isomorphisms
$Rq_*\underline\C_{W^+} \simeq \mathcal H \simeq
\bigoplus_{\lambda \in \Lambda} \mathcal H_\lambda$, where
$\mathcal H = q_*\underline\C_{W^+}$ and
$\mathcal H_\lambda = \ker(T - M_\lambda)$ for the shift operator
$T$ and scalar multiplication $M_\lambda$. For every continuous
$t : Y \to X$ to a compact Hausdorff space and every
$D \subset \Lambda$, the natural map
$\bigoplus_{\lambda \in D} Rt_*\mathcal H_\lambda \to
Rt_*\mathcal H_D$ is an isomorphism in the bounded-below derived
category; the left sum is a coproduct in the ambient derived
category.

*Proof sketch.* The orbit pullback gives the first isomorphism by
additivity. Stalks are locally constant functions on $G/H$,
factoring through finite cyclic quotients, which diagonalize since
$z^{p^j}-1$ has distinct roots. For the derived sum, sections over
a compact set involve finitely many indices, so global sections
commute with sums and sums of soft sheaves are soft; proper base
change identifies stalk cohomology, and termwise sums compute
derived coproducts.

## Sources

- [Preprint source map: `lem:character-coproduct`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Rational orbit pullback](../local-tests/orbit-injectivity.md)
- [Stacks derived facts](../background/stacks-derived.md)
- [Sheaf cohomology bounds](../background/sheaf-cohomology-bounds.md)
