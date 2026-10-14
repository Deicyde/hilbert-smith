---
article_id: af_e22d1466e0bda1104753e376
declaration: lemma
origin: cited
---

# Two endpoint forms

Let $(A, \alpha)$ be a symmetric degree-$r$ form in $\T(X)$ or
$\Pcat(X)$, and $i_t : X \to I \times X$ the endpoint inclusions.
There is a neutral degree-$r$ form on
$E \boxtimes A \simeq (i_0)_*A \oplus (i_1)_*A$ whose two diagonal
forms are $c(i_0)_*\alpha$ and $-c(i_1)_*\alpha$ for a common
nonzero real scalar $c$. There are no off-diagonal terms.

*Proof sketch.* Compact-support cohomology of the interval triangle
is the difference exact sequence, so the shifted dual of the
boundary has opposite nonzero endpoint coefficients. The product
morphism $u \boxtimes \alpha$ followed by the external-duality
comparison is symmetric; its symmetric cone is the required neutral
form. Disjoint closed slices force diagonality; precomposition with
$v \boxtimes 1$ determines each diagonal, and the suspension sign is
endpoint-independent.

## Sources

- [Preprint source map: `cat:endpoint-forms`](../../sources/preprint.md)

## Depends on

- [Test categories](test-categories.md)

## Proof depends on

- [Symmetric cone](symmetric-cone.md)
- [Products with the interval](interval-products.md)
- [Product shift sign](product-shift-sign.md)
