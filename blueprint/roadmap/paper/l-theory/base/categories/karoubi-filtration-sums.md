---
article_id: af_3c9216fbda7939e5ffdd6269
declaration: lemma
origin: bridged
---

# Filtrations are compatible with sums

For an involution-invariant Karoubi filtration and objects $M,N$, both of the following hold: every $q\in\mathcal D(M\oplus N)$ satisfies $q\le p\oplus p'$ for some $p\in\mathcal D(M)$ and $p'\in\mathcal D(N)$; and for all $p\in\mathcal D(M)$, $p'\in\mathcal D(N)$ some $q\in\mathcal D(M\oplus N)$ satisfies $p\oplus p'\le q$.

*Proof sketch.* (1) Any idempotent $e=ab$ on an object $L$ with $a:V\to L$, $b:L\to V$, $V\in\mathcal U$ satisfies $e\le p$ for some $p\in\mathcal D(L)$: factorization gives $p_1a=a$ and $bp_2=b$, and an upper bound $p$ of $p_1,p_2$ has $pe=e=ep$. (2) For $q$, apply factorization to the components $V\to M$, $V\to N$, $M\to V$, $N\to V$ of $q$'s splitting, and take upper bounds. (3) For $p\oplus p'$, apply (1) on $M\oplus N$; it factors through $E\oplus E'\in\mathcal U$.

## Sources

- New: the cofinality axiom of the cited definition follows from factorization and directedness

## Depends on

- [Involution-invariant Karoubi filtration](karoubi-filtration.md)
