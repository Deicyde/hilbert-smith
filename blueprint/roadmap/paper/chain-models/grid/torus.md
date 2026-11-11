---
article_id: af_063cd7d7d852e62d8c45e2ca
declaration: abbrev
origin: background
statement: formalized
lean: HSP.ChainModels.Torus
---

# The torus

Let $n\in\mathbb N$. The torus is $\mathbb T^n=(\mathbb R/4\mathbb Z)^n$. Each $x\in\mathbb T^n$ has a unique lift $\tilde x\in[-2,2)^n$, and $q:\mathbb R^n\to\mathbb T^n$ is the quotient map, so $q(\tilde x)=x$; its restriction to $[-2,2]^n$ is the quotient $q:[-2,2]^n\to\mathbb T^n$. On $\mathbb R^n$, $|\cdot|$ is the Euclidean norm and $|\cdot|_\infty$ the maximum norm. The lift satisfies $|\tilde x_j|=d(x_j,0)$ for each $j$, hence $|\tilde x|_\infty=d_\infty(x,0)$, and $x\mapsto\tilde x$ is continuous at every $x$ with $d_\infty(x,0)<2$.

$\mathbb T^n$ carries two metrics: $d_\infty(x,y)=\max_jd(x_j,y_j)$, the maximum of the circle distances $d(s,t)=\min_{m\in\mathbb Z}|\tilde s-\tilde t+4m|$ on $\mathbb R/4\mathbb Z$, and $d_2(x,y)=\bigl(\sum_jd(x_j,y_j)^2\bigr)^{1/2}$, the quotient Euclidean metric. Then $d_\infty\le d_2\le\sqrt n\,d_\infty$. For $X\subseteq\mathbb T^n$ and $r\ge0$, $N_r(X)$ is the closed $d_\infty$-neighbourhood of $X$ of radius $r$: the points whose $d_\infty$-distance from $X$ is at most $r$.

*Proof sketch.* The lift lies in $[-2,2)^n$, where each coordinate is at most half the period from $0$, so $|\tilde x_j|$ is the circle distance; away from the seam $x_j=2$ the lift is a local inverse of $q$. (The comparison.) Each $d(x_j,y_j)^2$ is at most the sum of all of them, and the sum is at most $n\,d_\infty(x,y)^2$.

## Sources

- New: the torus closing of the chart cube $[-2,2]^n$.

## Depends on
