---
declaration: theorem
origin: cited
---

# Idempotents split in the bounded homotopy category

Let $\mathcal P$ be an idempotent-complete additive category, $C$ a bounded $\mathbb Z$-graded chain complex in $\mathcal P$, and $E:C\to C$ a chain map with $E^2\simeq E$. Then there are a bounded complex $D'$ in $\mathcal P$ and chain maps $\iota':D'\to C$, $r':C\to D'$ with $r'\iota'\simeq1$ and $\iota'r'\simeq E$.

This is an open statement of the paper: the skeleton states it with its proof missing, and it is cited, not proved.

**Remark (not formalized).** The citation proves that $D^b$ of an idempotent-complete exact category is idempotent complete. For $\mathcal P$ with the split exact structure, an acyclic complex has split short exact pieces, hence is contractible, so $D^b(\mathcal P)=K^b(\mathcal P)$ and the statement above follows.

**Remark (not formalized): what an elementary proof still needs.**
1. Coherence data: maps $E_k$ of degree $k$ on $C$, $1\le k\le\operatorname{length}(C)+1$, with $E_1$ a homotopy $E^2\simeq E$, making $Y=\bigoplus_{j\ge0}C[j]$ (degreewise finite) a complex under the twisted differential $d+\sum_k\alpha_k$, where $\alpha_1$ alternates $1-E$ and $E$. The first obstruction is the homotopy class of the cycle $EE_1-E_1E$; an arbitrary first-order homotopy need not kill it. This is the missing step.
2. Gaussian elimination degree by degree, giving $\iota,r$ between $Y$ and $C$ with $r\iota\simeq1$ and $\iota r\simeq E$.
3. [Trimming the top](trim-top.md), which applies to $Y$ although $Y$ is unbounded above.

Steps 2 and 3 are elementary. Making $E$ homotopic to a strict idempotent after adding a contractible complex is equivalent to the statement itself (mapping cylinder), so it is not a shortcut.

## Sources

- [published: Balmer and Schlichting 2001, Theorem 2.8] [U]
- HS paper, Section 5 (cites the same theorem).

## Depends on

- [Idempotent completion with duality](../l-theory/base/karoubi-duality.md)
