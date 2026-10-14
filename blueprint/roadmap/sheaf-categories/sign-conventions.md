---
article_id: af_74cf421fb6f0dc746bb44b47
declaration: lemma
origin: cited
---

# Sign conventions

With cochain shifts and the translated-duality convention, a
symmetric form of degree $r$ is equivalently a Koszul-symmetric
pairing $\beta : A \otimes A \to \omega_X[-r]$ with invertible
adjoint; the exactness sign of $\D_{X,r}$ is $(-1)^r$, and
$W_r = W^{-r}$. On an oriented $d$-manifold the orientation pairing
$1 \otimes 1 \mapsto 1$ is symmetric and positive with no extra
parity sign. The interval symmetric cone is the diagonal matrix
$\mathrm{diag}(1,-1)$, and the product cone is $(-1)^r$ times the
diagonal of pushed endpoint forms; reversing conventions may negate
both entries but keeps their relative sign opposite, so the
endpoint Witt-class equality is unaffected.

*Proof sketch.* Chain-level verification: the Hom shift comparison
is a chain map with the stated exponents; unshifted biduality is
tensor-symmetry evaluation; shifted biduality acquires
$(-1)^{j(j+1)/2}$; tensor--Hom adjunction identifies symmetry with
Koszul invariance. The cone identities plus the difference-map
normalization determine the endpoint matrices by precomposition.

## Sources

- [Preprint source map: unlabelled appendix §A.1, §A.3](../../sources/preprint.md)

## Depends on

- [Test categories](test-categories.md)
