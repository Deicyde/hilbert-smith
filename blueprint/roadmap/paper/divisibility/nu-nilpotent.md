---
article_id: af_aee94f697c535a6c5504b087
declaration: theorem
origin: bridged
---

# Nilpotence

Let $\mathbf G$ be a group sequence and $X$ a compact metric space with an isometric $C_p$-action. Let $s\ge1$, and let $T_1,\dots,T_s$ be closed invariant subsets covering $X$, each with a continuous map $c_a:T_a\to C_p$ satisfying $c_a(gx)=g+c_a(x)$ for $g\in C_p$. Then $\nu_X^s=0$ on $\mathbb L_k(\mathcal A_X)$ for all $k$, with [$\nu$](permutation-nu.md) on the [support Mayer-Vietoris functor](support-mayer-vietoris.md).

*Proof sketch.*
1. For $S\subseteq T_a$ closed and invariant, $c_a|_S$ is a continuous equivariant map. [Local triviality](local-triviality.md) gives $\nu_S=0$.
2. [Abstract nilpotence](abstract-nilpotence.md) gives $\nu^s=0$ on $F_k(T_1\cup\dots\cup T_s)=\mathbb L_k(\mathcal A_X)$.

## Sources

- HS paper, Section 4 (Nilpotence).

## Depends on

- [The endomorphism $\nu$](permutation-nu.md)
- [Support Mayer-Vietoris functor](support-mayer-vietoris.md)

## Proof depends on

- [Local triviality](local-triviality.md)
- [Abstract nilpotence](abstract-nilpotence.md)
