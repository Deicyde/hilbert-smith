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
3. A point of $\mathbb R^n$ lies in the closure in $S^n$ of a set $W$ exactly when it lies in the closure in $\mathbb R^n$ of $W\cap\mathbb R^n$. For $m=1$, the complement of $B_1$ lies in the closed set where some $|x_k|\ge s$, so a point of $A_1\cap B_1$ has some $|x_k|=s$; conversely a point of $B_1$ with $|x_k|=s$ is a limit of points pushed out of $B_1$ along $x_k$. For $m\ge2$ put $c=n-m+2$. A point of $Y_{m-1}\setminus B_m$ has $x_c<s$, so it lies in the closed set of points with $|x_k|=s$ for some $k\le n-m+1$ or with $x_c=-s$; a point of $B_m$ has $x_c=s\ne-s$, since $s>0$. So $A_m\cap B_m\subseteq Y_m$. Conversely a point of $Y_m$ is the limit of the points obtained by lowering $x_c$ slightly below $s$, and these lie in $Y_{m-1}\setminus B_m$. This is item 3.
4. $Y_n=\{x\in[-s,s]\times\{s\}^{n-1}:|x_1|=s\}=\{y_-,y_+\}$, and $y_-\ne y_+$ because $s>0$.

## Sources

- New: the cube-face flag replaces the ball and hemisphere flag of HS paper, Section 12.

## Depends on

- [The cut sets](cut-sets.md)
