---
article_id: af_9b40fb79be59c2d219b04f2f
declaration: def
origin: bridged
statement: formalized
lean: HSP.formSign
---

# The equivariant signature of an invariant form

Let $W$ be a real vector space, $b$ a bilinear form on $W$ and $\rho$ an action of a monoid $G$ on $W$ by linear maps. If $(W,b,\rho)$ has a signature splitting, fix one, $(V^+,V^-)$, and set
$$\mathrm{sign}_b(g)=\mathrm{tr}(\rho(g)|V^+)-\mathrm{tr}(\rho(g)|V^-)\in\mathbb R,\qquad g\in G.$$
Otherwise set $\mathrm{sign}_b=0$. The trace of an endomorphism of an infinite-dimensional space is taken to be $0$; the signature is only used for finite-dimensional $W$. By [the existence lemma](../l-four/signature-splitting-exists.md), the second case does not occur for $(W,b,\rho)$ as there.

## Sources

- HS paper, Section 3
- New: the representation ring is replaced by the character, and the class in $R_{\mathbb C}(G)$ by traces.

## Depends on

- [Invariant signature splittings exist](../l-four/signature-splitting-exists.md)
