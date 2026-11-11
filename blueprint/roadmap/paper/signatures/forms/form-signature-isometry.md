---
article_id: af_9ef44c1f50fa213d869a398e
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.formSign_congr
---

# Isometry invariance

Let $W$, $W'$ be real vector spaces with $W$ finite-dimensional, $b$, $b'$ bilinear forms on $W$, $W'$ and $\rho$, $\rho'$ actions of a monoid $G$ on $W$, $W'$ by linear maps. If $e:W\to W'$ is a $G$-equivariant isometric isomorphism from $b$ to $b'$, then $\mathrm{sign}_b=\mathrm{sign}_{b'}$.

*Proof sketch.* Let $(V^+,V^-)$ be any splitting of $W$; by [independence](../l-four/signature-splitting-independence.md) for $W$, $\mathrm{sign}_b$ is computed from it. Then $(eV^+,eV^-)$ is a splitting of $W'$: it is invariant because $e$ is equivariant, and definite because $e$ is an isometry. $e$ restricts to $G$-isomorphisms $V^\pm\to eV^\pm$, so by conjugation invariance of the trace, $\mathrm{tr}(g|eV^\pm)=\mathrm{tr}(g|V^\pm)$. Conclude with [independence](../l-four/signature-splitting-independence.md) for $W'$. If $W$ has no splitting, neither has $W'$ (apply the same transport to $e^{-1}$), and both signatures are $0$.

## Sources

- New: transport of structure.

## Depends on

- [The equivariant signature](form-signature.md)

## Proof depends on

- [Independence](../l-four/signature-splitting-independence.md)
