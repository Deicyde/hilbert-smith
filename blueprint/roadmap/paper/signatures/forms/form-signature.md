---
article_id: af_9b40fb79be59c2d219b04f2f
declaration: def
origin: bridged
statement: formalized
lean: HSP.formSign
---

# The equivariant signature of an invariant form

Let $W$ be a real vector space, $b$ a bilinear form on $W$ and $\rho$ an action of a monoid $G$ on $W$ by linear maps. If $(W,b,\rho)$ has a [signature splitting](signature-splitting.md), fix one, $(V^+,V^-)$, and set
$$\mathrm{sign}_b(g)=\mathrm{tr}(\rho(g)|V^+)-\mathrm{tr}(\rho(g)|V^-)\in\mathbb R,\qquad g\in G.$$
Otherwise set $\mathrm{sign}_b=0$. The trace of an endomorphism of an infinite-dimensional space is taken to be $0$; the signature is only used for finite-dimensional $W$. When $W$ is finite-dimensional, $b$ is symmetric and nondegenerate and a finite group acts by $b$-isometries, the second case does not occur, since an invariant signature splitting then exists: average an inner product over the group and split $W$ into the positive and negative eigenspaces of $b$ relative to it.

## Sources

- HS paper, Section 3
- New: the representation ring is replaced by the character, and the class in $R_{\mathbb C}(G)$ by traces.

## Depends on

## Proof depends on

- [Signature splittings](signature-splitting.md)
