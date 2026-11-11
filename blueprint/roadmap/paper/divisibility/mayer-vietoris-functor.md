---
article_id: af_a5d65d5ee00e0150652de164
declaration: def
origin: background
---

# Mayer-Vietoris functor

Let $\Lambda$ be a lattice. A *Mayer-Vietoris functor* on $\Lambda$ consists of the following data:
- abelian groups $F_k(S)$ for $S\in\Lambda$ and $k\in\mathbb Z$;
- homomorphisms $i_{S\le S'}:F_k(S)\to F_k(S')$ with $i_{S\le S}=\mathrm{id}$ and $i_{S'\le S''}i_{S\le S'}=i_{S\le S''}$;
- for all $A,B\in\Lambda$, homomorphisms $\partial_{A,B}:F_k(A\vee B)\to F_{k-1}(A\wedge B)$.

These satisfy middle exactness: if $\partial_{A,B}x=0$, then $x=i_{A\le A\vee B}(a)+i_{B\le A\vee B}(b)$ for some $a\in F_k(A)$ and $b\in F_k(B)$.

## Sources

- New: abstracts the hypotheses used in HS paper, Section 4.

## Depends on
