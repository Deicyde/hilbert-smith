---
article_id: af_260b6d618c2adfd3b7919d59
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.IsExteriorWitness
---

# Exterior witnesses

Let $X$ be as in [Graph-type matrices](graph-type.md), and let $Z\subseteq X$ be closed and invariant. A matrix $e:M\to M'$ is an *exterior witness of type $c$ with bound $\delta$* if $e=xy$, where:
- $y:M\to W$ and $x:W\to M'$ go through a finite labeled based module $W$, and every label $\mu_w$ of $W$ satisfies $d(\mu_w,z)\le\delta$ for some $z\in Z$;
- $y$ has graph type $0$ with bound $\delta$;
- $x$ has graph type $c$ with bound $\delta$.

The definition does not need $Z$ to be closed or invariant, the action to be isometric, $M$ and $M'$ to be finite, or $\delta\ge0$.

## Sources

- HS paper, Section 10 (band factorization).
- New: a witness is normalized to type $0$ on its first factor. Relabeling $W$ by an element of $C_p$ moves the type between the factors and keeps $W$ near $Z$, because $Z$ is invariant.

## Depends on

## Proof depends on

- [Graph-type matrices](graph-type.md)
