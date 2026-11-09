---
article_id: af_9ef44c1f50fa213d869a398e
declaration: lemma
origin: background
---

# Isometry invariance

If $e:W\to W'$ is a $G$-equivariant isometry from $b$ to $b'$, then $\mathrm{sign}_b=\mathrm{sign}_{b'}$.

*Proof sketch.* Let $(V^+,V^-)$ be the chosen splitting of $W$. Then $(eV^+,eV^-)$ is a splitting of $W'$: it is invariant because $e$ is equivariant, and definite because $e$ is an isometry. $e$ restricts to $G$-isomorphisms $V^\pm\to eV^\pm$, so by conjugation invariance of the trace, $\mathrm{tr}(g|eV^\pm)=\mathrm{tr}(g|V^\pm)$. Conclude with [independence](../l-four/signature-splitting-independence.md) for $W'$.

## Sources

- New: transport of structure.

## Depends on

- [The equivariant signature](form-signature.md)

## Proof depends on

- [Independence](../l-four/signature-splitting-independence.md)
