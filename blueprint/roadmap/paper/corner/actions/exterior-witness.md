---
article_id: af_260b6d618c2adfd3b7919d59
declaration: def
origin: bridged
---

# Exterior witnesses

Let $X$ be as in [Graph-type matrices](graph-type.md), and let $Z\subset X$ be closed and invariant. A matrix $e:M\to M'$ is an *exterior witness of type $c$ with bound $\delta$* if $e=xy$, where:
- $y:M\to W$ and $x:W\to M'$ go through a finite labeled based module $W$, and every label of $W$ lies within $\delta$ of $Z$;
- $y$ has graph type $1$ with bound $\delta$;
- $x$ has graph type $c$ with bound $\delta$.

## Sources

- HS paper, Section 10 (band factorization).
- New: a witness is normalized to type $1$ on its first factor. Relabeling $W$ by an element of $C_p$ moves the type between the factors and keeps $W$ near $Z$, because $Z$ is invariant.

## Depends on

- [Graph-type matrices](graph-type.md)
