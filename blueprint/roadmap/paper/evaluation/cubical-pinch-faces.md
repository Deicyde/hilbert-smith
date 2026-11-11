---
article_id: af_15701fafd8b2751a7d3ac60f
declaration: lemma
origin: background
---
# The cubical pinch on the cube and outside it

Let $\kappa$ be the [cubical pinch](cubical-pinch.md) for $n$ and $s$, with $a=1/4$, $K=[-a,a]^n$ and lifts $\tilde x\in[-2,2)^n$. Then:
1. if $|\tilde x|_\infty\le a$, then $\kappa(x)=\tfrac sa\,\tilde x$; so $\kappa$ maps $K$ onto $[-s,s]^n$, and for each $k$ and sign it maps the face $K\cap\{\tilde x_k=\pm a\}$ onto the face $[-s,s]^n\cap\{z_k=\pm s\}$;
2. if $|\tilde x|_\infty\ge a$, then $\kappa(x)=\infty$ or $|\kappa(x)|_\infty\ge s$.

*Proof sketch.* (1) For $|\tilde x|_\infty\le a$, $(b-|\tilde x|_\infty)/(b-a)\ge1$, so $c_\kappa(\tilde x)=a/s$. (2) $c_\kappa\le a/s$, so where $c_\kappa(\tilde x)>0$, $|\kappa(x)|_\infty=|\tilde x|_\infty/c_\kappa(\tilde x)\ge a\cdot s/a=s$.

## Sources
- New.
## Depends on
- [Cubical pinch](cubical-pinch.md)
