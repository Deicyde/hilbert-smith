---
article_id: af_1c9edeee007516a3a5c094a1
declaration: lemma
origin: bridged
---

# Splitting a homotopy idempotent

Let $\mathcal P$ be an idempotent-complete additive category, $\mathcal C$ a complex in $\mathcal P$ concentrated in $[0,N]$, and $E$ a chain map with $E^2\simeq E$. Then there are a complex $D$ concentrated in $[0,N]$ and chain maps $\iota:D\to\mathcal C$, $r:\mathcal C\to D$ with $r\iota\simeq1$ and $\iota r\simeq E$.

This lemma rests on the open statement [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md); the rest of its proof is elementary.

*Proof sketch.*
1. Get a bounded $(D',\iota',r')$ ([Idempotents split](kb-idempotent-splitting.md)).
2. [Trim the top](trim-top.md) at $N$, then [the bottom](trim-bottom.md) at $0$, giving $D$ with $\pi j=1$, $j\pi\simeq1$ at each stage.
3. Transport: $\iota=\iota'j$, $r=\pi r'$; then $r\iota=\pi r'\iota'j\simeq\pi j=1$ and $\iota r=\iota'j\pi r'\simeq\iota'r'\simeq E$.
4. Reindex $D$ from $\mathbb Z$ to $\mathbb N$.

## Sources

- HS paper, Section 5.

## Depends on

- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)

## Proof depends on

- [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md)
- [Trimming the top](trim-top.md)
- [Trimming the bottom](trim-bottom.md)
