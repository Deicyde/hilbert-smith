---
article_id: af_2a17a828c567187315523309
declaration: def
origin: bridged
statement: formalized
lean: HSP.forgetLabels
---

# Forgetting labels

$\Phi:\mathcal A_{\mathbf G}(X)\to\mathcal V_{\mathbf G}$ is the strict duality functor $(n_i,x_i)\mapsto(n_i)$, $[u]\mapsto q(u_i)$, into the [point category](../asymptotic/point-quotient.md).

*Proof sketch.* The bases of $(n_i,x_i)$ and of $(n_i)$ are the same free $G_i$-sets $G_i\times\{1..n_i\}$, so each $u_i$ is a morphism of $\mathrm{Free}(\mathbb Q[G_i])$. Eventually equal sequences differ in finitely many coordinates, so they have the same image in $\mathcal V_{\mathbf G}$ by the description of its morphisms in the [point category](../asymptotic/point-quotient.md), so $\Phi$ is well defined. It preserves composition, identities and transposes because $q$ does.

## Sources

- HS paper, Section 3

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)
- [Point category](../asymptotic/point-quotient.md)

