---
article_id: af_d1f52d172a4a78c42c217880
declaration: theorem
origin: background
---

# Symmetric forms and orthogonal sums

Let $C$ be an additive category with a duality: a contravariant
additive endofunctor $D$ with a biduality natural isomorphism
$\varpi : \mathrm{Id} \Rightarrow D \circ D^{\mathrm{op}}$. A
symmetric form on $X$ is a morphism $\alpha : X \to DX$ equal to
its own transpose $\varpi_X \gg D(\alpha)$; it is nonsingular
when $\alpha$ is an isomorphism. The orthogonal sum
$\alpha \perp \beta$ of symmetric forms on $X$ and $Y$ is the
biproduct form on $X \boxplus Y$, via the canonical
identification $D(X \boxplus Y) \cong DX \boxplus DY$.
Orthogonal sums of (nonsingular) symmetric forms are
(nonsingular) symmetric.

Cited as the foundation for the triangular Witt layer: the
doubling and cone arguments manipulate symmetric forms and
their orthogonal sums throughout.

*Proof sketch.* The transpose is involutive by naturality of
$\varpi$; the biproduct identification is natural, so the
matrix of the transpose is the transpose of the matrix, and a
diagonal of symmetric entries is symmetric. A diagonal of
isomorphisms is an isomorphism, so nonsingularity is
preserved.

## Sources

- [Background map: `Balmer2000` §1](../../sources/background.md)

## Depends on

This node has no prerequisites.
