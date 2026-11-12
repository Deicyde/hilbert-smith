---
article_id: af_4bc353c8cf0f652df9086ae9
declaration: def
origin: bridged
statement: formalized
lean: HSP.extFunctor
---

# Induced functor on exterior quotients

Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor, and let $Z\subset X$ and $Z'\subset X'$ with $F(\mathcal A_Z)\subset\mathcal A_{Z'}$, that is, $F$ sends $Z$-supported objects to $Z'$-supported objects. The induced functor $\bar F:\mathcal B_{\mathbf G,Z}(X)\to\mathcal B_{\mathbf G',Z'}(X')$ on the [exterior quotients](exterior-quotient.md) is $M\mapsto F(M)$, $[u]\mapsto[F(u)]$. It is a strict duality functor, and $\bar F\circ q=q'\circ F$ for the quotient functors $q,q'$.

*Proof sketch.* If $u=ba$ through $W\in\mathcal A_Z$, then $F(u)=F(b)F(a)$ through $F(W)\in\mathcal A_{Z'}$, so $\bar F$ is well defined. It is $\mathbb Q$-linear and commutes with composition, identities and transposes because $F$ does.

## Sources

- HS paper, Section 2

## Depends on

- [Exterior quotient](exterior-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Strict duality functor](../../l-theory/base/categories/duality-functors/strict-duality-functor.md)
