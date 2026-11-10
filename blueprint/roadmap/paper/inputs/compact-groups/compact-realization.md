---
article_id: af_27bdd5a957d952afc09c5611
declaration: theorem
origin: background
not_ready: true
---

# Realization of characters of the dual

Let $A$ be a compact Hausdorff commutative topological group and $\widehat A$ its group of characters. Every homomorphism $\psi\colon\widehat A\to\mathbb T$ is of the form $\chi\mapsto\chi(a)$ for a unique $a\in A$.

*Proof sketch.* Uniqueness is the separation of points by characters. For existence, give the group of homomorphisms $\widehat A\to\mathbb T$ the topology of pointwise convergence; it is compact Hausdorff. The evaluation map from $A$ to it is a continuous injective homomorphism, so its image $E$ is a closed subgroup. If $E$ is proper, separation of points on the compact quotient by $E$ gives a nontrivial continuous character $\Lambda$ of that group that is trivial on $E$. The duality for the discrete group $\widehat A$ makes $\Lambda$ evaluation at some $\chi\in\widehat A$. Triviality on $E$ forces $\chi=1$, so $\Lambda=1$, a contradiction.

This proof rests on the open statements [characters separate points](characters-separate.md) and [characters of the dual of a discrete group](discrete-duality.md).

## Sources

- Published: L. Pontryagin (1934); G. B. Folland, A Course in Abstract Harmonic Analysis, Chapter 4 (not checked against the originals)

## Depends on

## Proof depends on

- [Characters separate points](characters-separate.md)
- [Characters of the dual of a discrete group](discrete-duality.md)
