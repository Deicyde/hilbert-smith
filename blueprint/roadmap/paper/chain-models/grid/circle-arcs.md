---
article_id: af_5031a69da6488993372fc6d7
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.circleArc, HSP.ChainModels.shortestArc
---
# Closed arcs of the circle

For $a,\ell\in\mathbb R$, the *closed arc* from $a$ of length $\ell$ is the image in $\mathbb R/4\mathbb Z$ of the interval $[a,a+\ell]$ (empty if $\ell<0$).

For $Y\subseteq\mathbb R/4\mathbb Z$, a *shortest closed arc containing* $Y$ is defined as follows. If there are $a,\ell$ with $\ell\ge0$ such that the closed arc from $a$ of length $\ell$ contains $Y$ and $\ell\le\ell'$ for all $a',\ell'$ with $\ell'\ge0$ whose closed arc contains $Y$, it is the closed arc of such a pair $(a,\ell)$, fixed once and for all; otherwise it is the whole circle.

## Sources
- New.

## Depends on
