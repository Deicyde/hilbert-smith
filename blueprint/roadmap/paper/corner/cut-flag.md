---
article_id: af_049a4cf3c67432c01e4c0e17
declaration: lemma
origin: bridged
---

# The cut flag

In the [standing data](standing-data.md), for every $1\le m\le n$:
1. $A_m$ and $B_m$ are closed in $S^n$;
2. $A_m\cup B_m=Y_{m-1}$;
3. $A_m\cap B_m=Y_m$.

Moreover $Y_n=\{y_-,y_+\}$ and $y_-\ne y_+$.

*Proof sketch.*
1. $B_m$ is a product of closed intervals and points, hence compact, and $A_m$ is a closure. $Y_{m-1}$ is closed: it is $S^n$ for $m=1$, and a closed subset of the compact $B_{m-1}$ for $m\ge2$.
2. $B_m\subseteq Y_{m-1}$: for $m=1$ trivially, and for $m\ge2$ because $B_m$ is the face $x_{n-m+2}=s$ of $B_{m-1}$. Since $Y_{m-1}$ is closed, $A_m\subseteq Y_{m-1}$, and $Y_{m-1}\setminus B_m\subseteq A_m$; this gives item 2.
3. For $m=1$, $A_1$ is the complement of the open cube $(-s,s)^n$, which meets $B_1$ in $Y_1$. For $m\ge2$, $Y_{m-1}$ is the union of the faces $\{x\in B_{m-1}:x_k=\pm s\}$, $k\le n-m+2$, and $B_m$ is the face $x_{n-m+2}=s$. Every other face is the closure of its points with $x_{n-m+2}<s$, because $s>0$; so $A_m$ is the union of the other faces. A point of $B_m$ lies on another face exactly when $|x_k|=s$ for some $k\le n-m+1$, since $x_{n-m+2}=s\ne-s$. This is item 3.
4. $Y_n=\{x\in[-s,s]\times\{s\}^{n-1}:|x_1|=s\}=\{y_-,y_+\}$, and $y_-\ne y_+$ because $s>0$.

## Sources

- New: the cube-face flag replaces the ball and hemisphere flag of HS paper, Section 12.

## Depends on

- [Standing data](standing-data.md)
