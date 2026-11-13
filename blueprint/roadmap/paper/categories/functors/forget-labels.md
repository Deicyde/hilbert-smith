---
article_id: af_2a17a828c567187315523309
declaration: def
origin: bridged
statement: formalized
lean: HSP.forgetLabels
---

# Forgetting labels

$\Phi:\mathcal A_{\mathbf G}(X)\to\mathcal V_{\mathbf G}$ is the duality functor $(n_i,x_i)\mapsto(n_i)$, $[u]\mapsto q(u_i)$, with the identity duality isomorphism, into the [point category](../asymptotic/point-quotient.md).

*Proof sketch.* The bases of $(n_i,x_i)$ and of $(n_i)$ are the same free $G_i$-sets $G_i\times\{1..n_i\}$, so each $u_i$ is a morphism of $\mathrm{Free}(\mathbb Q[G_i])$ and $u\mapsto(u_i)$ is a functor into the [sequence category](../asymptotic/point-sequence-category.md). If $u$ and $v$ are eventually equal, then $u_i-v_i=0$ for all but finitely many $i$, so $(u_i)-(v_i)$ factors through the [finite-support subcategory](../asymptotic/eventually-zero-subcategory.md) by the [point ideal](../asymptotic/point-ideal.md), and $q(u_i)=q(v_i)$ because two maps have the same class in the [quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md) exactly when their difference lies in the ideal. So $\Phi$ is well defined. It preserves composition and identities because $q$ does; since [every morphism is a class](../asymptotic/structure/class-surjective.md) $[u]$, it is additive and $\mathbb Q$-linear because $q$ is, and with $\xi$ the identity it preserves transposes, as the [duality](../../l-theory/base/categories/duality-category.md) of both sides is coordinatewise transposition.

## Sources

- HS paper, Section 3

## Depends on

- [Group sequence](../asymptotic/group-sequence.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [Point category](../asymptotic/point-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Finite-support subcategory](../asymptotic/eventually-zero-subcategory.md)
- [Point filtration](../asymptotic/point-filtration.md)
- [Sequence category](../asymptotic/point-sequence-category.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Point ideal](../asymptotic/point-ideal.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Free category of a finite group](../asymptotic/free-category.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
