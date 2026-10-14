---
article_id: af_09a9b62dbca1aed1b1121eb3
declaration: theorem
origin: cited
---

# Dense doubling

Let $\mathcal A \subset \mathcal C$ be a full replete triangulated
subcategory stable under duality, dense in the sense that each
object of $\mathcal C$ is a summand of an object of $\mathcal A$.
In every degree, the inclusion
$\iota : W_r(\mathcal A) \to W_r(\mathcal C)$ has kernel and
cokernel annihilated by $2$: there is a homomorphism
$d : W_r(\mathcal C) \to W_r(\mathcal A)$ with
$\iota d = 2\,\mathrm{id}$ and $d\iota = 2\,\mathrm{id}$. No closure
of $\mathcal A$ under arbitrary summands is required.

*Proof sketch.* Density gives $y \oplus y[1] \in \mathcal A$ for all
$y$ (cone on $0_y \oplus \mathrm{id}_z$). Double a form as
$D(q) = q \perp q \perp H(x[1])$, whose underlying object lies in
$\mathcal A$ by the shift observation. Neutrality descends: given a
lagrangian for $q$, an explicit lagrangian for
$D(q) \perp H(z)$ is built and verified to lie in $\mathcal A$
using only fullness and triangles. The hyperbolic summands are
neutral on both sides, giving the two doubling identities.

## Sources

- [Preprint source map: `thm:dense-doubling`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.
