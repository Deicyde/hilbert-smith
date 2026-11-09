---
article_id: af_d9f8e61313ad0ce35223caa8
declaration: lemma
origin: bridged
---

# Representatives act approximately

For a local datum, a compact $\mathbb Z_p$-invariant set $C\subseteq\Omega$ and $\varepsilon>0$, there is $L\ge1$ such that for all $\ell\ge L$, all $g,g'\in\mathbb Z/p^\ell\mathbb Z$ and all $x\in C$,
$$|r_\ell(g)\cdot(r_\ell(g')\cdot x)-r_\ell(g+g')\cdot x|<\varepsilon.$$

*Proof sketch.*
1. Uniformly small displacement near the identity, for the inclusion of $\Omega$ in $\mathbb R^n$, the compact set $C$ and $\delta=\varepsilon$, gives a neighbourhood $V$ of $0$; the basis property gives $L\ge1$ with $H_L\subseteq V$, hence $H_\ell\subseteq V$ for all $\ell\ge L$.
2. The left point equals $k\cdot y$ with $y=r_\ell(g+g')\cdot x\in C$, by invariance, and $k=r_\ell(g)+r_\ell(g')-r_\ell(g+g')\in H_\ell$ by the algebra of the representatives. So its distance from $y$ is less than $\varepsilon$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the finite quotients, display (8.9))

## Depends on

- [Local datum](../chart/local-datum.md)
- [Representatives of the finite quotients](representative-map.md)

## Proof depends on

- [Algebra of the representatives](representatives-algebra.md)
- [Uniformly small displacement near the identity](../subgroups/small-displacement.md)
- [The subgroups $H_j$ form a basis at $0$](../subgroups/padic-subgroups-basis.md)
