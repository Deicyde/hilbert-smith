---
article_id: af_049a4cf3c67432c01e4c0e17
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Corner.cut_flag
---

# The cut flag

Let $n\ge1$ and $s>0$. For the [cut sets](cut-sets.md) and every $1\le m\le n$:
1. $A_m$ and $B_m$ are closed in $S^n$;
2. $A_m\cup B_m=Y_{m-1}$;
3. $A_m\cap B_m=Y_m$.

Moreover $Y_n=\{y_-,y_+\}$ and $y_-\ne y_+$.

*Proof sketch.*
1. $B_m$ is a product of closed intervals and points, hence compact, and $A_m$ is a closure. $Y_{m-1}$ is closed: it is $S^n$ for $m=1$, and a closed subset of the compact $B_{m-1}$ for $m\ge2$.
2. $B_m\subseteq Y_{m-1}$: for $m=1$ trivially, and for $m\ge2$ because $B_m$ is the face $x_{n-m+2}=s$ of $B_{m-1}$. Since $Y_{m-1}$ is closed, $A_m\subseteq Y_{m-1}$, and $Y_{m-1}\setminus B_m\subseteq A_m$; this gives item 2.
3. For $m=1$: a point of $B_1$ with $|x_k|<s$ for all $k$ has the open cube $(-s,s)^n$ as a neighbourhood that misses $S^n\setminus B_1$, so it is not in $A_1$; a point of $B_1$ with $|x_k|=s$ is the limit of the points obtained by moving $x_k$ outward, which lie outside $B_1$. For $m\ge2$, let $j=n-m+2$, the coordinate that is free on $B_{m-1}$ and equal to $s$ on $B_m$. If $x\in B_m$ has $|x_k|<s$ for all $k<j$, then near $x$ every point of $Y_{m-1}$ has $|x_j|=s$ and $x_j$ close to $s$, so $x_j=s$ and the point lies in $B_m$; hence $x\notin A_m$. If $|x_k|=s$ for some $k<j$, moving $x_j$ slightly below $s$ gives points of $Y_{m-1}\setminus B_m$ converging to $x$. This is item 3.
4. $Y_n=\{x\in[-s,s]\times\{s\}^{n-1}:|x_1|=s\}=\{y_-,y_+\}$, and $y_-\ne y_+$ because $s>0$.

## Sources

- New: the cube-face flag replaces the ball and hemisphere flag of HS paper, Section 12.

## Depends on

- [The cut sets](cut-sets.md)
