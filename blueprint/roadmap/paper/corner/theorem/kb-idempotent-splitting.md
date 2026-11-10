---
article_id: af_fafa31f8446d3766ff1249ad
declaration: theorem
origin: cited
---

# Idempotents split in the bounded homotopy category

Let $\mathcal P$ be an idempotent-complete additive category, $C$ a bounded $\mathbb Z$-graded chain complex in $\mathcal P$, and $E:C\to C$ a chain map with $E^2\simeq E$. Then there are a bounded complex $D'$ in $\mathcal P$ and chain maps $\iota':D'\to C$, $r':C\to D'$ with $r'\iota'\simeq1$ and $\iota'r'\simeq E$.

**Remark (not formalized).** *Status.* This is an open statement: the Lean states it now and proves it later.

*Planned route.* The citation proves that $D^b$ of an idempotent-complete exact category is idempotent complete. For $\mathcal P$ with the split exact structure, an acyclic complex has split short exact pieces, hence is contractible, so $D^b(\mathcal P)=K^b(\mathcal P)$ and the statement above follows.

*Known gaps.* An elementary proof still needs:
1. Coherence data: maps $E_k$ of degree $k$ on $C$, $1\le k\le\operatorname{length}(C)+1$, with $E_1$ a homotopy $E^2\simeq E$, making $Y=\bigoplus_{j\ge0}C[j]$ (degreewise finite) a complex under the twisted differential $d+\sum_k\alpha_k$, where $\alpha_1$ alternates $1-E$ and $E$. The first obstruction is the homotopy class of the cycle $EE_1-E_1E$; an arbitrary first-order homotopy need not kill it, so an elementary proof must construct such $E_k$.
2. Gaussian elimination degree by degree, giving $\iota,r$ between $Y$ and $C$ with $r\iota\simeq1$ and $\iota r\simeq E$.
3. [Trimming the top](trim-top.md), which applies to $Y$ although $Y$ is unbounded above.

Steps 2 and 3 are elementary. Making $E$ homotopic to a strict idempotent after adding a contractible complex is equivalent to the statement itself (mapping cylinder), so it is not a shortcut.

## Sources

- [Balmer and Schlichting 2001, Theorem 2.8](../../../../sources/paper/balmer-schlichting-2001.md) [U]
- HS paper, Section 5 (cites the same theorem).

## Depends on

- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
