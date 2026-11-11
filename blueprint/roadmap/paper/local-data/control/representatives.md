---
article_id: af_d9f8e61313ad0ce35223caa8
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.rep_vadd_close
---

# Representatives act approximately

For a local datum, a compact $\mathbb Z_p$-invariant set $C\subseteq\Omega$ and $\varepsilon>0$, there is $L\ge1$ such that for all $i\ge L$, all $g,g'\in\mathbb Z/p^i\mathbb Z$ and all $x\in C$,
$$|r_i(g)\cdot(r_i(g')\cdot x)-r_i(g+g')\cdot x|<\varepsilon.$$

*Proof sketch.*
1. Uniformly small displacement near the identity, for the inclusion of $\Omega$ in $\mathbb R^n$, the compact set $C$ and $\delta=\varepsilon$, gives a neighbourhood $V$ of $0$; the basis property gives $L\ge1$ with $H_L\subseteq V$, hence $H_i\subseteq V$ for all $i\ge L$.
2. The left point equals $k\cdot y$ with $y=r_i(g+g')\cdot x\in C$, by invariance, and $k=r_i(g)+r_i(g')-r_i(g+g')\in H_i$ by the algebra of the representatives. So its distance from $y$ is less than $\varepsilon$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the finite quotients, display (8.9))

## Depends on

- [Local datum](../chart/local-datum.md)
- [Representatives of the finite quotients](representative-map.md)

## Proof depends on

- [Algebra of the representatives](representatives-algebra.md)
- [Uniformly small displacement near the identity](../subgroups/small-displacement.md)
- [The subgroups $H_j$ form a basis at $0$](../subgroups/padic-subgroups-basis.md)
