---
article_id: af_3f6711b4b3434ab0b4e0670a
declaration: def
origin: cited
---

# Character classes

Fix a finite partition $\Lambda = D_0 \sqcup \cdots \sqcup
D_{m-1}$ and a compact test $t : Y \to X$ whose value $b_t$ has a
contractible neighborhood basis. The open projectors define
quotient endomorphisms $e_i$ of $A_t$ in
$\mathcal Q_U(X) = \T(X)/\T(U)$ satisfying
$e_ie_j = \delta_{ij}e_i$, $\sum_i e_i = \mathrm{id}$, and
$e_i^\dagger = e_i$. With the integral localization isomorphism
$\ell_U : E_d(X) \to W_d(\mathcal Q_U(X))$, the class
$z_i(t) \in E_d(X)$ is defined by
$\ell_U(z_i(t)) = [A_t,\alpha_t] +
[A_t,\alpha_t \circ (2e_i - \mathrm{id})]$.
The definition is independent of $U$.

*Well-definedness.* The twisted form is nonsingular and symmetric
since $2e_i - \mathrm{id}$ is a self-adjoint involution; no image
object for $e_i$ is needed. Independence of $U$ follows by
comparing through a smaller contractible neighborhood and using
injectivity of the localization maps.

## Sources

- [Preprint source map: `def:character-classes`](../../sources/preprint.md)

## Depends on

- [Contractible quotient](../sphere-lattice/contractible-quotient.md)
- [Germ description](../localization/germs.md)

## Proof depends on

- [Real orthogonality](orthogonality.md)
- [Character coproducts](character-coproduct.md)
