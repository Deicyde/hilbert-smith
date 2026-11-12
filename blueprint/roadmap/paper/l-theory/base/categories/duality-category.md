---
article_id: af_7dca2f3e90dbd89bce73e302
declaration: class
origin: background
statement: formalized
lean: HSP.DualCat
---

# Small Q-linear category with strict duality

A *duality category* is a $\mathbb Q$-linear additive category $\mathcal A$ (composition is $\mathbb Q$-bilinear and $\mathcal A$ has all finite direct sums, including a zero object; its objects form a set and each $\mathrm{Hom}(M,N)$ is a set, with no further size condition) together with:
1. an object $M^*$ for each object $M$, and a map $f^*:N^*\to M^*$ for each map $f:M\to N$;
2. $(1_M)^*=1_{M^*}$ and $(gf)^*=f^*g^*$, so $*$ is a contravariant functor;
3. $(f+g)^*=f^*+g^*$ and $(cf)^*=c\,f^*$ for $c\in\mathbb Q$, so $*$ is $\mathbb Q$-linear;
4. $M^{**}=M$ for every object $M$;
5. $f^{**}=f$ for every $f:M\to N$, where both sides are maps $M\to N$ via the equalities $M^{**}=M$ and $N^{**}=N$ of item 4.

It follows that $0^*=0$, $(-f)^*=-f^*$ and $(f-g)^*=f^*-g^*$, and that if $M=N$ then the dual of the identification $M\to N$ is the identification $N^*\to M^*$.

## Sources

- [Ranicki 1992, §1](../../../../../sources/paper/ranicki-1992.md); [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 2 (duality as transpose on labeled bases)

## Depends on
